package nl.tudelft.instrumentation.learning;

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

    static void run() {

        SystemUnderLearn sul = new RersSUL();
        observationTable = new ObservationTable(LearningTracker.inputSymbols, sul);
        equivalenceChecker = new RandomWalkEquivalenceChecker(sul, LearningTracker.inputSymbols, 100, 1000);
        // equivalenceChecker = new WMethodEquivalenceChecker(sul, LearningTracker.inputSymbols, 1, observationTable, observationTable);

        observationTable.print();
        MealyMachine hypothesis = observationTable.generateHypothesis();
        hypothesis.writeToDot("hypothesis.dot");

        // Place here your code to learn a model of the RERS problem.
        // Implement the checks for consistent and closed in the observation table.
        // Use the observation table and the equivalence checker to implement the L* learning algorithm.
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

            // Table is now closed and consistent — generate hypothesis and check equivalence.
            hypothesis = observationTable.generateHypothesis();
            Optional<Word<String>> counterExample = equivalenceChecker.verify(hypothesis);
            if (!counterExample.isPresent()) {
                isFinished = true;
            } else {
                // Add all prefixes of the counter-example to S to guarantee convergence.
                List<String> symbols = counterExample.get().asList();
                for (int i = 1; i <= symbols.size(); i++) {
                    observationTable.addToS(new Word<>(symbols.subList(0, i)));
                }
            }
        }

        hypothesis.writeToDot("hypothesis.dot");
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