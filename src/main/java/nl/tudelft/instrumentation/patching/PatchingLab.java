package nl.tudelft.instrumentation.patching;
import java.util.*;

import com.github.javaparser.ast.expr.AssignExpr.Operator;




public class PatchingLab {

        static Random r = new Random();
        static boolean isFinished = false;
        static Random random = new Random(42);  // Seed for reproducibility

        static final int POPULATION_SIZE = 50;
        static final int MAX_GENERATIONS = 150;
        static final int TOURNAMENT_SIZE = 3;
        static final double BASE_MUTATION_RATE = 0.1;
        static final double PARSIMONY_FACTOR = 0.1;
        static final int ELITISM_PERCENTAGE = 10;
        static final int TOP_K_SUSPICIOUS = 10;
        
        static HashSet<String> encounteredErrors = new HashSet<>();

        
        static CoverageInfo coverageInfo;
        static Map<Integer, Double> tarantulaScores;        
        static List<Boolean> baselineTestResults;
        
        static Individual[] population;
        static double[] fitnessScores;
        static Individual bestIndividual;
        static double bestFitness = -1;

        /**
         * This class represents an individual in the population of candidate solutions for the genetic algorithm.
         * Each individual has a configuration of operators and a fitness score that indicates how well it performs on the test cases.
         * The class implements the Cloneable interface to allow for easy copying of individuals during selection and reproduction.
         */
        static class Individual implements Cloneable {

        
                String[] operators;
                double fitnessScore;
                
                public Individual(String[] operators) {
                        this.operators = operators;
                }

                @Override
                public Individual clone() {
                        Individual copy = new Individual(this.operators);
                        copy.fitnessScore = this.fitnessScore;
                        return copy;
                }
                
                int countMutations(String[] original) {
                        int count = 0;
                        for (int i = 0; i < operators.length; i++) {
                                if (!operators[i].equals(original[i])) count++;                        }
                        return count;
                }
                
                @Override
                public String toString() {
                        return "Individual{fitness=" + String.format("%.2f", fitnessScore) + 
                                ", mutations=" + countMutations(OperatorTracker.operators) + "}";
                }

                
        }

        /**
         * Captures the coverage info of the current code state.
         * Tracks which operators are executed for each test and passing vs. failing tests.
         */
        static class CoverageInfo {
                // operators[test_id] = set of operator IDs executed in this test
                HashSet<Integer>[] operatorsPerTest;
                boolean[] testResults;           // true = pass, false = fail
                int totalTests;
                int failingTestCount = 0;
                int passingTestCount = 0;
                
                CoverageInfo(int numTests) {
                        this.totalTests = numTests;
                        operatorsPerTest = new HashSet[numTests];
                        for (int i = 0; i < numTests; i++) {
                                operatorsPerTest[i] = new HashSet<>();
                        }
                        testResults = new boolean[numTests];
                }
                
                void recordOperator(int testId, int operatorId) {
                        operatorsPerTest[testId].add(operatorId);
                }
                
                void recordTestResult(int testId, boolean passed) {
                        testResults[testId] = passed;
                        if (passed) passingTestCount++;
                        else failingTestCount++;
                }
        }

        /**
         * Localizes faults using Tarantula scores.
         * Identifies and reports the top suspicious operators.
         */
        static void localizeFaults(Map<Integer, Double> tarantula, int topK) {
        System.out.println("\n=== Fault Localization Results ===");
        System.out.println("Top " + topK + " suspicious operators (Tarantula scores):\n");
        
        tarantula.entrySet().stream()
                .sorted((a, b) -> Double.compare(b.getValue(), a.getValue()))
                .limit(topK)
                .forEach(e -> {
                int opId = e.getKey();
                double score = e.getValue();
                String operator = OperatorTracker.operators[opId];
                System.out.printf("  [%d] Operator \"%s\" - Score: %.4f%n", opId, operator, score);
                });
        }



        static void initialize(){

                // initialize the population based on OperatorTracker.operators
                System.out.println("\n=== Initialization Phase ===");
        
                // Phase 1: Establish baseline with original operators -> how many tests fail?
                System.out.println("Running baseline tests with original operators...");
                baselineTestResults = OperatorTracker.runAllTests();
                int originalFailingTests = (int) baselineTestResults.stream().filter(b -> !b).count();
                System.out.println("Baseline: " + baselineTestResults.size() + " tests, " + 
                                originalFailingTests + " failing");

                // Phase 2: Analyze coverage and compute Tarantula scores
                System.out.println("\nAnalyzing coverage and computing Tarantula scores...");
                coverageInfo = analyzeCoverage(OperatorTracker.operators);
                tarantulaScores = computeTarantulaScores(coverageInfo);
                localizeFaults(tarantulaScores, TOP_K_SUSPICIOUS);

                // Phase 3: Initialize population
                System.out.println("Initializing population...");
                population = initializePopulationMix(POPULATION_SIZE, tarantulaScores);
                fitnessScores = new double[POPULATION_SIZE];
                
                // Phase 4: Evaluate initial population
                evaluatePopulation(population, fitnessScores);
                bestFitness = -1;
                for (double f : fitnessScores) {
                        if (f > bestFitness) bestFitness = f;
                }
                // Select the individual with the best fitness as the initial best solution
                int argmax = 0;
                for (int i = 1; i < fitnessScores.length; i++) {
                        if (fitnessScores[i] > fitnessScores[argmax]) {
                                argmax = i;
                        }
                }
                bestIndividual = population[argmax].clone();
                System.out.println("Initial best fitness: " + String.format("%.2f", bestFitness));
        }


        

        /**
         * Analyzes test coverage by running tests and recording which operators
         * are executed in passing vs. failing tests.
         */
        static CoverageInfo analyzeCoverage(String[] operators) {
                
                // How many tests executed for the current code state.
                int numTests = OperatorTracker.tests.size();

                // Initialize coverage info
                CoverageInfo coverage = new CoverageInfo(numTests);
                
                // Re-instrument execution to track coverage
                int testsPassed = 0;
                for (int testId = 0; testId < numTests; testId++) {
                        
                        boolean testPassed = baselineTestResults.get(testId);
                        coverage.recordTestResult(testId, testPassed);
                        if (testPassed) testsPassed++; //not really useful for now
                }
                
                // Note: In a real implementation, we would re-run tests with instrumentation
                // to capture exact operator coverage. For this lab, we approximate by
                // running each test individually and tracking operator execution.
                
                return coverage;
        }

        /**
         * Computes Tarantula suspicion scores for each operator.
         * 
         * Score(op) = (failed_ratio) / (failed_ratio + passed_ratio)
         * where:
         *   failed_ratio = (tests_executing_op_that_fail) / (total_failing_tests)
         *   passed_ratio = (tests_executing_op_that_pass) / (total_passing_tests)
        */
        static Map<Integer, Double> computeTarantulaScores(CoverageInfo coverage) {
                Map<Integer, Double> scores = new HashMap<>();
                
                int numOperators = OperatorTracker.operators.length;
                final double EPSILON = 1e-6;
                
                // For each operator, compute its suspicion score
                for (int opId = 0; opId < numOperators; opId++) {
                        int failedExecuting = 0;
                        int passedExecuting = 0;
                        
                        // Count how many failing/passing tests execute this operator
                        for (int testId = 0; testId < coverage.totalTests; testId++) {
                                
                                if (!coverage.operatorsPerTest[testId].contains(opId)) continue;

                                if (coverage.testResults[testId]) {
                                passedExecuting++;
                                } else {
                                failedExecuting++;
                                }
                        }
                        
                        // Compute ratios
                        double failedRatio = (double) failedExecuting / 
                                                Math.max(1, coverage.failingTestCount);
                        double passedRatio = (double) passedExecuting / 
                                                Math.max(1, coverage.passingTestCount);
                        
                        // Compute Tarantula score
                        double denominator = failedRatio + passedRatio + EPSILON;
                        double score = failedRatio / denominator;
                        
                        scores.put(opId, score);
                }
                
                // Display top 10 suspicious operators
                scores.entrySet().stream()
                .sorted((a, b) -> Double.compare(b.getValue(), a.getValue()))
                .limit(10)
                .forEach(e -> System.out.println("  Operator " + e.getKey() + 
                        " (\"" + OperatorTracker.operators[e.getKey()] + 
                        "\") score: " + String.format("%.4f", e.getValue())));
                
                return scores;
        }

   
        /**
         * Evaluates the fitness of each individual in the population, using caching to avoid redundant computations.
         * @param pop (population of individuals to evaluate)
         * @param fitness
         */
        static void evaluatePopulation(Individual[] pop, double[] fitness) {
                for (int i = 0; i < pop.length; i++) {
                        if (pop[i].fitnessScore >= 0) {
                                // Use cached fitness
                                fitness[i] = pop[i].fitnessScore;
                        } else {
                                fitness[i] = computeFitness(pop[i]);
                                pop[i].fitnessScore = fitness[i];
                        }
                }
        }

      
        

        /**
        * Initializes the population with a mix of:
        * - Original operators (elitism seed)
        * - Random variations biased by Tarantula scores
        */
        static Individual[] initializePopulationMix(int popSize, Map<Integer, Double> tarantula) {
                Individual[] pop = new Individual[popSize];
                int numOperators = OperatorTracker.operators.length;
                
                // 25% elite: start with original operators
                int eliteCount = (int) (popSize * 0.25);
                for (int i = 0; i < eliteCount; i++) {
                        pop[i] = new Individual(OperatorTracker.operators.clone());
                }
                
                // 75% random with Tarantula-biased mutations
                for (int i = eliteCount; i < popSize; i++) {
                        String[] ops = new String[numOperators];
                        for (int opId = 0; opId < numOperators; opId++) {
                                double tarantula_score = tarantula.getOrDefault(opId, 0.1);
                                // Mutation probability proportional to suspicion
                                double mutation_prob = 0.5 + 0.5 * tarantula_score;
                                
                                if (random.nextDouble() < mutation_prob) {
                                        // Mutate to random operator
                                        ops[opId] = randomOperator();
                                } else {
                                        // Keep original
                                        ops[opId] = OperatorTracker.operators[opId];
                                }
                        }
                        pop[i] = new Individual(ops);
                }
                
                return pop;
        }

        
        static String randomOperator() {
                String[] ops = {">", "<", ">=", "<=", "==", "!="};
                return ops[random.nextInt(ops.length)];
                
        }

        /**
         * Selects an individual from the population using tournament selection.
         * @param population
         * @param fitness
         * @return a clone of the selected individual
         */
        static Individual tournamentSelection(Individual[] population, double[] fitness) {
                
                int bestIdx = -1;
                double bestFit = -Double.MAX_VALUE;
                
                // Extract the best individual from a random sample of the population
                for (int i = 0; i < TOURNAMENT_SIZE; i++) {
                        int idx = random.nextInt(population.length);
                        if (fitness[idx] > bestFit) {
                                bestFit = fitness[idx];
                                bestIdx = idx;
                        }
                }
                
                return population[bestIdx].clone();
        }


        /**
         * This method computes the fitness of an individual based on the number of passing and failing tests.
         * The fitness function is defined as: 
         *      fitness = w_pos * (number of passing tests) + w_neg * (number of failing tests).
         */
        static double computeFitness(Individual individual) {
                // Set operators to this individual's configuration
                String[] originalOps = OperatorTracker.operators.clone();
                OperatorTracker.operators = individual.operators.clone();
                
                // Run all tests
                List<Boolean> results = OperatorTracker.runAllTests();
                
                // Count passing tests: we use stream to process data in a sequence, apply a filter to select only the
                // tests whose results is true (passing)
                int passingTests = (int) results.stream().filter(b -> b).count();
                int failingTestCount = results.size() - passingTests;

                // Implement the fitness function
                double w_pos = 0.1;
                double w_neg = 10; 

                // Restore original operators
                OperatorTracker.operators = originalOps;

                return w_pos * passingTests + w_neg * failingTestCount;
        }

        // encounteredOperator gets called for each operator encountered while running tests
        // We can use this to change the behavior of the test without actually changing the code
        static boolean encounteredOperator(String operator, int left, int right, int operator_nr){

                // When we encounter anz operator, we need to understand 

                // Do something useful

                String replacement = OperatorTracker.operators[operator_nr];
                if(replacement.equals("!=")) return left != right;
                if(replacement.equals("==")) return left == right;
                if(replacement.equals("<")) return left < right;
                if(replacement.equals(">")) return left > right;
                if(replacement.equals("<=")) return left <= right;
                if(replacement.equals(">=")) return left >= right;
                return false;
        }

        static boolean encounteredOperator(String operator, boolean left, boolean right, int operator_nr){
                // Do something useful

                String replacement = OperatorTracker.operators[operator_nr];
                if(replacement.equals("!=")) return left != right;
                if(replacement.equals("==")) return left == right;
                return false;
        }

        static void run() {
                initialize();

                // Place the code here you want to run once:
                // You want to change this of course, this is just an example
                // Tests are loaded from resources/rers2020_test_cases. If you are you are using
                // your own tests, make sure you put them in the same folder with the same
                // naming convention.
                OperatorTracker.runAllTests();
                // OperatorTracker.readTests();
                // boolean result = OperatorTracker.runTest(0);
                // System.out.println("Test result: " + result);
                System.out.println("Entered run");
                System.out.println("Encountered errors: " + encounteredErrors);
                
                System.out.println("operators: " + Arrays.toString(OperatorTracker.operators));
                // // Loop here, running your genetic algorithm until you think it is done
                // while (!isFinished) {
                //         // Do things!
                //         try {
                //                 System.out.println("Woohoo, looping!");
                //                 Thread.sleep(1000);
                //         } catch (InterruptedException e) {
                //                 e.printStackTrace();
                //         }
                // }
        }

   

        public static void output(String out){
                // This will get called when the problem code tries to print things,
                // the prints in the original code have been removed for your convenience
                
                if (out.startsWith("Invalid")){
                        encounteredErrors.add(out);
                }
                System.out.println("From function: \n"+ out);
        }
}