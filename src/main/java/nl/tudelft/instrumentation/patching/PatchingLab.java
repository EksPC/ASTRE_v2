package nl.tudelft.instrumentation.patching;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Random;

/**
 * Lab 3, Automated Code Patching.
 *
 * This implementation keeps the Task 2 functionality, namely fitness computation,
 * Tarantula based fault localization and population initialization, and extends it
 * with the Task 3 EA loop, selection, mutation, stopping criteria and best patch
 * persistence.
 *
 * Important design choice:
 * The RERS buggy problems usually have only a small number of faulty operators.
 * Therefore, the EA should not mutate many operators at once. Broad mutation
 * breaks many passing tests. This version uses Tarantula to focus mutation on
 * suspicious operators and also creates one-change candidates around the current
 * best individual.
 */
public class PatchingLab {

    static final Random random = new Random(Long.getLong("patching.seed", 42L));

    static final int POPULATION_SIZE = Integer.getInteger("patching.populationSize", 30);
    static final int MAX_GENERATIONS = Integer.getInteger("patching.maxGenerations", 100);
    static final int MAX_SECONDS = Integer.getInteger("patching.maxSeconds", 300);
    static final int TOURNAMENT_SIZE = Integer.getInteger("patching.tournamentSize", 3);
    static final int ELITISM_COUNT = Math.max(1, Integer.getInteger("patching.elitismCount", 2));
    static final int TOP_K_SUSPICIOUS = Integer.getInteger("patching.topSuspicious", 20);
    static final int LOCAL_SEARCH_CANDIDATES = Integer.getInteger("patching.localSearchCandidates", 12);

    static final double MUTATION_RATE = Double.parseDouble(System.getProperty("patching.mutationRate", "0.10"));
    static final double CROSSOVER_RATE = Double.parseDouble(System.getProperty("patching.crossoverRate", "0.50"));
    static final double RANDOM_INDIVIDUAL_RATE = Double.parseDouble(System.getProperty("patching.randomIndividualRate", "0.10"));

    static final String[] NUMERIC_OPERATORS = {">", "<", ">=", "<=", "==", "!="};
    static final String[] BOOLEAN_OPERATORS = {"==", "!="};

    static boolean isFinished = false;
    static HashSet<String> encounteredErrors = new HashSet<>();

    static CoverageInfo coverageInfo;
    static Map<Integer, Double> tarantulaScores = new HashMap<>();
    static List<Integer> suspiciousOperatorIds = new ArrayList<>();

    static Individual[] population;
    static double[] fitnessScores;

    static Individual bestIndividual;
    static double bestFitness = -1.0;
    static int lastImprovementGeneration = 0;

    static CoverageInfo activeCoverage = null;
    static final HashSet<Integer> booleanOperatorIds = new HashSet<>();
    static final HashSet<Integer> numericOperatorIds = new HashSet<>();

    static class Individual implements Cloneable {
        String[] operators;
        double fitnessScore = -1.0;

        Individual(String[] operators) {
            this.operators = operators;
        }

        @Override
        public Individual clone() {
            Individual copy = new Individual(this.operators.clone());
            copy.fitnessScore = this.fitnessScore;
            return copy;
        }

        int countMutations(String[] original) {
            int count = 0;
            for (int i = 0; i < operators.length; i++) {
                if (!operators[i].equals(original[i])) {
                    count++;
                }
            }
            return count;
        }

        @Override
        public String toString() {
            return "Individual{fitness=" + String.format(Locale.US, "%.6f", fitnessScore)
                    + ", changedOperators=" + countMutations(OperatorTracker.operators) + "}";
        }
    }

    static class CoverageInfo {
        HashSet<Integer>[] operatorsPerTest;
        boolean[] testResults;
        int totalTests;
        int failingTestCount = 0;
        int passingTestCount = 0;

        @SuppressWarnings("unchecked")
        CoverageInfo(int numTests) {
            this.totalTests = numTests;
            this.operatorsPerTest = new HashSet[numTests];
            this.testResults = new boolean[numTests];

            for (int i = 0; i < numTests; i++) {
                this.operatorsPerTest[i] = new HashSet<>();
            }
        }

        void recordOperator(int testId, int operatorId) {
            if (testId >= 0 && testId < operatorsPerTest.length) {
                operatorsPerTest[testId].add(operatorId);
            }
        }

        void recordTestResult(int testId, boolean passed) {
            if (testId >= 0 && testId < testResults.length) {
                testResults[testId] = passed;
                if (passed) {
                    passingTestCount++;
                } else {
                    failingTestCount++;
                }
            }
        }
    }

    static void initialize() {
        System.out.println("\n=== Initialization Phase ===");
        System.out.println("Problem: " + OperatorTracker.problem.getClass().getSimpleName());
        System.out.println("Operators: " + OperatorTracker.operators.length);
        System.out.println("Tests: " + OperatorTracker.tests.size());

        coverageInfo = analyzeCoverage(OperatorTracker.operators);
        int baselinePassed = coverageInfo.passingTestCount;
        int baselineFailing = coverageInfo.failingTestCount;
        double baselineFitness = fitnessFromPassCount(baselinePassed, coverageInfo.totalTests);

        System.out.println("Baseline: " + baselinePassed + "/" + coverageInfo.totalTests
                + " passed, " + baselineFailing + " failing. Fitness: "
                + String.format(Locale.US, "%.6f", baselineFitness));

        tarantulaScores = computeTarantulaScores(coverageInfo);
        suspiciousOperatorIds = getSuspiciousOperatorIds(tarantulaScores, TOP_K_SUSPICIOUS);
        printFaultLocalizationResults();

        population = initializePopulation(POPULATION_SIZE);
        fitnessScores = new double[population.length];

        evaluatePopulation(population, fitnessScores);
        updateBestFromPopulation(population, 0);

        System.out.println("Initial best fitness: " + String.format(Locale.US, "%.6f", bestFitness));
        saveBestPatch(0);
    }

    static CoverageInfo analyzeCoverage(String[] operators) {
        String[] originalOperators = OperatorTracker.operators.clone();
        OperatorTracker.operators = operators.clone();

        CoverageInfo coverage = new CoverageInfo(OperatorTracker.tests.size());
        activeCoverage = coverage;

        for (int testId = 0; testId < OperatorTracker.tests.size(); testId++) {
            boolean passed = OperatorTracker.runTest(testId);
            coverage.recordTestResult(testId, passed);
        }

        activeCoverage = null;
        OperatorTracker.operators = originalOperators;

        return coverage;
    }

    static Map<Integer, Double> computeTarantulaScores(CoverageInfo coverage) {
        Map<Integer, Double> scores = new HashMap<>();
        int numOperators = OperatorTracker.operators.length;

        for (int opId = 0; opId < numOperators; opId++) {
            int failedExecuting = 0;
            int passedExecuting = 0;

            for (int testId = 0; testId < coverage.totalTests; testId++) {
                if (!coverage.operatorsPerTest[testId].contains(opId)) {
                    continue;
                }

                if (coverage.testResults[testId]) {
                    passedExecuting++;
                } else {
                    failedExecuting++;
                }
            }

            double failedRatio = coverage.failingTestCount == 0
                    ? 0.0
                    : (double) failedExecuting / coverage.failingTestCount;

            double passedRatio = coverage.passingTestCount == 0
                    ? 0.0
                    : (double) passedExecuting / coverage.passingTestCount;

            double denominator = failedRatio + passedRatio;
            double score = denominator == 0.0 ? 0.0 : failedRatio / denominator;

            scores.put(opId, score);
        }

        return scores;
    }

    static List<Integer> getSuspiciousOperatorIds(Map<Integer, Double> tarantula, int topK) {
        List<Integer> ids = new ArrayList<>(tarantula.keySet());

        ids.sort((a, b) -> Double.compare(
                tarantula.getOrDefault(b, 0.0),
                tarantula.getOrDefault(a, 0.0)
        ));

        if (ids.size() > topK) {
            return new ArrayList<>(ids.subList(0, topK));
        }

        return ids;
    }

    static void printFaultLocalizationResults() {
        System.out.println("\n=== Fault Localization Results ===");

        for (Integer opId : suspiciousOperatorIds) {
            System.out.printf(Locale.US,
                    "  [%d] Operator \"%s\" score %.4f%n",
                    opId,
                    OperatorTracker.operators[opId],
                    tarantulaScores.getOrDefault(opId, 0.0)
            );
        }
    }

    static Individual[] initializePopulation(int populationSize) {
        List<Individual> individuals = new ArrayList<>();
        String[] original = OperatorTracker.operators.clone();

        individuals.add(new Individual(original.clone()));

        /*
         * Very important:
         * Create one-change candidates for the most suspicious operators.
         * If the bug is a single wrong operator, this can find the repair quickly.
         */
        for (Integer suspiciousOpId : suspiciousOperatorIds) {
            for (String replacement : getOperatorChoicesFor(suspiciousOpId)) {
                if (replacement.equals(original[suspiciousOpId])) {
                    continue;
                }

                String[] candidate = original.clone();
                candidate[suspiciousOpId] = replacement;
                individuals.add(new Individual(candidate));

                if (individuals.size() >= populationSize) {
                    return individuals.toArray(new Individual[0]);
                }
            }
        }

        /*
         * Fill the rest with small focused mutations.
         * These individuals usually change only one or two suspicious operators.
         */
        while (individuals.size() < populationSize) {
            String[] candidate = original.clone();
            mutateFocusedOperators(candidate, 1 + random.nextInt(2));
            individuals.add(new Individual(candidate));
        }

        return individuals.toArray(new Individual[0]);
    }

    static void evaluatePopulation(Individual[] pop, double[] fitness) {
        for (int i = 0; i < pop.length; i++) {
            if (pop[i].fitnessScore >= 0.0) {
                fitness[i] = pop[i].fitnessScore;
            } else {
                fitness[i] = computeFitness(pop[i]);
                pop[i].fitnessScore = fitness[i];
            }
        }
    }

    static double computeFitness(Individual individual) {
        String[] originalOperators = OperatorTracker.operators.clone();
        OperatorTracker.operators = individual.operators.clone();

        List<Boolean> results = OperatorTracker.runAllTests();
        int passingTests = Collections.frequency(results, true);
        double fitness = fitnessFromPassCount(passingTests, results.size());

        OperatorTracker.operators = originalOperators;

        return fitness;
    }

    static double fitnessFromPassCount(int passingTests, int totalTests) {
        if (totalTests == 0) {
            return 0.0;
        }
        return (double) passingTests / totalTests;
    }

    static Individual tournamentSelection(Individual[] pop, double[] fitness) {
        int bestIndex = random.nextInt(pop.length);
        double bestScore = fitness[bestIndex];

        for (int i = 1; i < TOURNAMENT_SIZE; i++) {
            int candidateIndex = random.nextInt(pop.length);

            if (fitness[candidateIndex] > bestScore) {
                bestScore = fitness[candidateIndex];
                bestIndex = candidateIndex;
            }
        }

        return pop[bestIndex].clone();
    }

    static Individual crossover(Individual parentA, Individual parentB) {
        if (parentA.operators.length == 0 || random.nextDouble() > CROSSOVER_RATE) {
            return parentA.clone();
        }

        String[] child = new String[parentA.operators.length];
        int cutPoint = random.nextInt(parentA.operators.length);

        for (int i = 0; i < child.length; i++) {
            child[i] = i < cutPoint ? parentA.operators[i] : parentB.operators[i];
        }

        return new Individual(child);
    }

    static Individual[] nextGeneration(int generation) {
        List<Individual> next = new ArrayList<>();
        List<Integer> sortedIndices = sortedPopulationIndicesByFitness();

        int eliteLimit = Math.min(ELITISM_COUNT, population.length);
        for (int i = 0; i < eliteLimit; i++) {
            next.add(population[sortedIndices.get(i)].clone());
        }

        /*
         * Local search around the best known patch.
         * This is essential for this lab because the correct patch is usually a
         * small number of operator replacements, not a large random rewrite.
         */
        addLocalSearchCandidates(next);

        while (next.size() < population.length) {
            Individual child;

            if (random.nextDouble() < RANDOM_INDIVIDUAL_RATE) {
                child = bestIndividual == null
                        ? new Individual(OperatorTracker.operators.clone())
                        : bestIndividual.clone();
                mutateFocusedOperators(child.operators, 1 + random.nextInt(2));
                child.fitnessScore = -1.0;
            } else {
                Individual parentA = tournamentSelection(population, fitnessScores);
                Individual parentB = tournamentSelection(population, fitnessScores);
                child = crossover(parentA, parentB);
                mutateIndividual(child);
            }

            next.add(child);
        }

        return next.toArray(new Individual[0]);
    }

    static void addLocalSearchCandidates(List<Individual> next) {
        if (bestIndividual == null) {
            return;
        }

        int added = 0;

        for (Integer opId : suspiciousOperatorIds) {
            for (String replacement : getOperatorChoicesFor(opId)) {
                if (replacement.equals(bestIndividual.operators[opId])) {
                    continue;
                }

                Individual candidate = bestIndividual.clone();
                candidate.operators[opId] = replacement;
                candidate.fitnessScore = -1.0;
                next.add(candidate);
                added++;

                if (added >= LOCAL_SEARCH_CANDIDATES || next.size() >= population.length) {
                    return;
                }
            }
        }
    }

    static List<Integer> sortedPopulationIndicesByFitness() {
        List<Integer> indices = new ArrayList<>();

        for (int i = 0; i < population.length; i++) {
            indices.add(i);
        }

        indices.sort(Comparator.comparingDouble((Integer i) -> fitnessScores[i]).reversed());

        return indices;
    }

    static void mutateIndividual(Individual individual) {
        /*
         * Instead of scanning all 339 operators, mutate only a small number of
         * suspicious positions. The mutation rate controls how often the child is
         * changed at all and how many focused replacements are tried.
         */
        if (random.nextDouble() < MUTATION_RATE) {
            int numberOfChanges = 1;

            if (random.nextDouble() < MUTATION_RATE) {
                numberOfChanges = 2;
            }

            mutateFocusedOperators(individual.operators, numberOfChanges);
            individual.fitnessScore = -1.0;
        }
    }

    static void mutateFocusedOperators(String[] operators, int numberOfChanges) {
        if (suspiciousOperatorIds.isEmpty()) {
            return;
        }

        HashSet<Integer> alreadyMutated = new HashSet<>();

        for (int i = 0; i < numberOfChanges; i++) {
            int opId = pickSuspiciousOperator(alreadyMutated);
            if (opId < 0) {
                return;
            }

            alreadyMutated.add(opId);
            operators[opId] = randomReplacementFor(opId, operators[opId]);
        }
    }

    static int pickSuspiciousOperator(HashSet<Integer> excluded) {
        List<Integer> candidates = new ArrayList<>();

        for (Integer opId : suspiciousOperatorIds) {
            if (!excluded.contains(opId)) {
                candidates.add(opId);
            }
        }

        if (candidates.isEmpty()) {
            return -1;
        }

        /*
         * Biased selection:
         * Most of the time choose from the top five. Sometimes choose from the
         * full suspicious list for diversity.
         */
        int bound;
        if (random.nextDouble() < 0.75) {
            bound = Math.min(5, candidates.size());
        } else {
            bound = candidates.size();
        }

        return candidates.get(random.nextInt(bound));
    }

    static String randomReplacementFor(int opId, String current) {
        String[] choices = getOperatorChoicesFor(opId);
        String replacement = choices[random.nextInt(choices.length)];

        if (choices.length > 1) {
            while (replacement.equals(current)) {
                replacement = choices[random.nextInt(choices.length)];
            }
        }

        return replacement;
    }

    static String[] getOperatorChoicesFor(int opId) {
        if (booleanOperatorIds.contains(opId) && !numericOperatorIds.contains(opId)) {
            return BOOLEAN_OPERATORS;
        }

        return NUMERIC_OPERATORS;
    }

    static void updateBestFromPopulation(Individual[] pop, int generation) {
        for (Individual individual : pop) {
            if (individual.fitnessScore > bestFitness) {
                bestFitness = individual.fitnessScore;
                bestIndividual = individual.clone();
                lastImprovementGeneration = generation;

                System.out.println("New best fitness: " + String.format(Locale.US, "%.6f", bestFitness)
                        + " with " + bestIndividual.countMutations(OperatorTracker.operators)
                        + " changed operators");

                printChangedOperators(bestIndividual);
                saveBestPatch(generation);
            }
        }
    }

    static void printChangedOperators(Individual individual) {
        String[] original = OperatorTracker.operators;

        for (int i = 0; i < individual.operators.length; i++) {
            if (!individual.operators[i].equals(original[i])) {
                System.out.printf(Locale.US,
                        "  changed [%d]: %s -> %s, tarantula %.4f%n",
                        i,
                        original[i],
                        individual.operators[i],
                        tarantulaScores.getOrDefault(i, 0.0)
                );
            }
        }
    }

    static void run() {
        initialize();

        long startTime = System.currentTimeMillis();
        int generation = 0;

        while (!isFinished) {
            generation++;

            population = nextGeneration(generation);
            fitnessScores = new double[population.length];

            evaluatePopulation(population, fitnessScores);
            updateBestFromPopulation(population, generation);

            logGeneration(generation, startTime);

            if (bestFitness >= 1.0) {
                System.out.println("Stopping: all tests pass.");
                isFinished = true;
            }

            if (generation >= MAX_GENERATIONS) {
                System.out.println("Stopping: maximum generations reached.");
                isFinished = true;
            }

            long elapsedSeconds = (System.currentTimeMillis() - startTime) / 1000;
            if (elapsedSeconds >= MAX_SECONDS) {
                System.out.println("Stopping: time budget reached.");
                isFinished = true;
            }
        }

        saveBestPatch(generation);
        printFinalSummary(generation, startTime);
        OperatorTracker.executor.shutdownNow();
    }

    static void logGeneration(int generation, long startTime) {
        double currentGenerationBest = 0.0;

        for (double fitness : fitnessScores) {
            if (fitness > currentGenerationBest) {
                currentGenerationBest = fitness;
            }
        }

        long elapsedSeconds = (System.currentTimeMillis() - startTime) / 1000;

        System.out.printf(Locale.US,
                "GEN,%s,%d,%d,%.6f,%.6f,%.4f%n",
                OperatorTracker.problem.getClass().getSimpleName(),
                generation,
                elapsedSeconds,
                currentGenerationBest,
                bestFitness,
                MUTATION_RATE
        );
    }

    static void saveBestPatch(int generation) {
        if (bestIndividual == null) {
            return;
        }

        File directory = new File("patches");
        if (!directory.exists()) {
            directory.mkdirs();
        }

        String problemName = OperatorTracker.problem.getClass().getSimpleName();
        File outputFile = new File(directory, problemName + "_best_patch.txt");

        try (PrintWriter writer = new PrintWriter(new FileWriter(outputFile))) {
            writer.println("problem=" + problemName);
            writer.println("generation=" + generation);
            writer.println("fitness=" + String.format(Locale.US, "%.8f", bestFitness));
            writer.println("mutationRate=" + MUTATION_RATE);
            writer.println("crossoverRate=" + CROSSOVER_RATE);
            writer.println("populationSize=" + POPULATION_SIZE);
            writer.println("topSuspicious=" + TOP_K_SUSPICIOUS);
            writer.println();

            writer.println("originalOperators=" + Arrays.toString(OperatorTracker.operators));
            writer.println("patchedOperators=" + Arrays.toString(bestIndividual.operators));
            writer.println();

            writer.println("changedOperators:");
            for (int i = 0; i < bestIndividual.operators.length; i++) {
                if (!OperatorTracker.operators[i].equals(bestIndividual.operators[i])) {
                    writer.printf(Locale.US,
                            "%d: %s -> %s, tarantula=%.6f%n",
                            i,
                            OperatorTracker.operators[i],
                            bestIndividual.operators[i],
                            tarantulaScores.getOrDefault(i, 0.0)
                    );
                }
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    static void printFinalSummary(int generation, long startTime) {
        long elapsedSeconds = (System.currentTimeMillis() - startTime) / 1000;

        System.out.println("\n=== Final EA Summary ===");
        System.out.println("Problem: " + OperatorTracker.problem.getClass().getSimpleName());
        System.out.println("Generations: " + generation);
        System.out.println("Elapsed seconds: " + elapsedSeconds);
        System.out.println("Best fitness: " + String.format(Locale.US, "%.6f", bestFitness));

        if (bestIndividual != null) {
            System.out.println("Changed operators in best patch:");
            printChangedOperators(bestIndividual);
        }

        System.out.println("Patch written to patches/"
                + OperatorTracker.problem.getClass().getSimpleName()
                + "_best_patch.txt");
    }

    static boolean encounteredOperator(String operator, int left, int right, int operator_nr) {
        numericOperatorIds.add(operator_nr);

        if (activeCoverage != null) {
            activeCoverage.recordOperator(OperatorTracker.current_test, operator_nr);
        }

        String replacement = OperatorTracker.operators[operator_nr];

        if (replacement.equals("!=")) return left != right;
        if (replacement.equals("==")) return left == right;
        if (replacement.equals("<")) return left < right;
        if (replacement.equals(">")) return left > right;
        if (replacement.equals("<=")) return left <= right;
        if (replacement.equals(">=")) return left >= right;

        return evaluateNumeric(operator, left, right);
    }

    static boolean encounteredOperator(String operator, boolean left, boolean right, int operator_nr) {
        booleanOperatorIds.add(operator_nr);

        if (activeCoverage != null) {
            activeCoverage.recordOperator(OperatorTracker.current_test, operator_nr);
        }

        String replacement = OperatorTracker.operators[operator_nr];

        if (replacement.equals("!=")) return left != right;
        if (replacement.equals("==")) return left == right;

        return evaluateBoolean(operator, left, right);
    }

    static boolean evaluateNumeric(String operator, int left, int right) {
        if (operator.equals("!=")) return left != right;
        if (operator.equals("==")) return left == right;
        if (operator.equals("<")) return left < right;
        if (operator.equals(">")) return left > right;
        if (operator.equals("<=")) return left <= right;
        if (operator.equals(">=")) return left >= right;

        return false;
    }

    static boolean evaluateBoolean(String operator, boolean left, boolean right) {
        if (operator.equals("!=")) return left != right;
        if (operator.equals("==")) return left == right;

        return false;
    }

    public static void output(String out) {
        if (out.startsWith("Invalid")) {
            encounteredErrors.add(out);
        }
    }
}