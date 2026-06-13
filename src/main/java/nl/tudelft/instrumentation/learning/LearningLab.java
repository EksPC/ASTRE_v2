package nl.tudelft.instrumentation.learning;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;

/**
 * You should write your own solution using this class.
 */
public class LearningLab {
    static Random r = new Random();
    static int traceLength = 10;
    static boolean isFinished = false;

    static ObservationTable observationTable;
    static EquivalenceChecker equivalenceChecker;

    private static final String RESULTS_DIRECTORY = "learning_results";

    static void run() {
        isFinished = false;
        long startTime = System.currentTimeMillis();
        String problemName = LearningTracker.getProblemName();
        int wDepth = Integer.getInteger("learning.w", defaultWDepth(problemName));
        List<String> stateLog = new ArrayList<>();
        stateLog.add("time_ms,states");

        SystemUnderLearn sul = new RersSUL();
        observationTable = new ObservationTable(LearningTracker.inputSymbols, sul);
        equivalenceChecker = new WMethodEquivalenceChecker(
                sul,
                LearningTracker.inputSymbols,
                wDepth,
                observationTable,
                observationTable
        );

        observationTable.print();
        MealyMachine hypothesis = observationTable.generateHypothesis();
        recordStateCount(stateLog, startTime, hypothesis);
        hypothesis.writeToDot(resultPath(problemName, "initial.dot"));

        while (!isFinished) {
            Optional<Word<String>> closed = observationTable.checkForClosed();
            if (closed.isPresent()) {
                observationTable.addToS(closed.get());
                continue;
            }

            Optional<Word<String>> consistent = observationTable.checkForConsistent();
            if (consistent.isPresent()) {
                observationTable.addToE(consistent.get());
                continue;
            }

            hypothesis = observationTable.generateHypothesis();
            recordStateCount(stateLog, startTime, hypothesis);
            hypothesis.writeToDot(resultPath(problemName, "latest.dot"));

            Optional<Word<String>> counterExample = equivalenceChecker.verify(hypothesis);
            if (!counterExample.isPresent()) {
                isFinished = true;
            } else {
                System.out.println("Counterexample: " + counterExample.get());
                boolean changed = addCounterExamplePrefixes(counterExample.get());
                if (!changed) {
                    addCounterExampleExtensions(counterExample.get());
                }
            }
        }

        hypothesis.writeToDot(resultPath(problemName, "final.dot"));
        writeStateLog(problemName, stateLog);
        System.out.printf("Finished learning %s with %d states using W-method depth %d.%n",
                problemName, hypothesis.getStates().length, wDepth);
        LearningTracker.shutdown();
    }

    private static boolean addCounterExamplePrefixes(Word<String> counterExample) {
        boolean changed = false;
        List<Word<String>> before = observationTable.getAccessSequences();
        List<String> symbols = counterExample.asList();

        for (int i = 1; i <= symbols.size(); i++) {
            Word<String> prefix = new Word<>(symbols.subList(0, i));
            if (!before.contains(prefix)) {
                changed = true;
            }
            observationTable.addToS(prefix);
        }

        return changed;
    }

    private static void addCounterExampleExtensions(Word<String> counterExample) {
        for (String symbol : LearningTracker.inputSymbols) {
            observationTable.addToS(counterExample.append(symbol));
        }
    }

    private static int defaultWDepth(String problemName) {
        if ("ProblemPin".equals(problemName)) {
            return 4;
        }
        return 3;
    }

    private static void recordStateCount(List<String> stateLog, long startTime, MealyMachine hypothesis) {
        long elapsed = System.currentTimeMillis() - startTime;
        stateLog.add(elapsed + "," + hypothesis.getStates().length);
    }

    private static String resultPath(String problemName, String suffix) {
        ensureResultsDirectoryExists();
        return RESULTS_DIRECTORY + File.separator + problemName + "_" + suffix;
    }

    private static void writeStateLog(String problemName, List<String> stateLog) {
        ensureResultsDirectoryExists();
        File output = new File(RESULTS_DIRECTORY, problemName + "_states.csv");

        try (BufferedWriter writer = new BufferedWriter(new FileWriter(output))) {
            for (String line : stateLog) {
                writer.write(line);
                writer.newLine();
            }
        } catch (IOException e) {
            throw new RuntimeException("Could not write state log for " + problemName, e);
        }
    }

    private static void ensureResultsDirectoryExists() {
        File directory = new File(RESULTS_DIRECTORY);
        if (!directory.exists() && !directory.mkdirs()) {
            throw new RuntimeException("Could not create directory " + RESULTS_DIRECTORY);
        }
    }

    /**
     * Method that is used for catching the output from standard out.
     *
     * @param out the string that has been outputted in the standard out.
     */
    public static void output(String out) {
        // System.out.println(out);
    }
}