package nl.tudelft.instrumentation.fuzzing;
import java.util.*;

import com.github.javaparser.utils.Pair;


/**
 * You should write your own solution using this class.
 */
public class FuzzingLab {
        static Random r = new Random();
        
        // For each target loop, store the lowest distance achieved to guide the hill climbing
        static Pair<List<String>, Double> bestTraceAndDistance; 
        static List<String> currentTrace;
        static double currentTotalTraceDistance;
        static double bestDistance;
        static String currentTarget;
        static boolean targetReached;
        static int iterationWithoutImprovement = 0;

        // Maps the number of iterations done for each branch
        static Map<String, Integer> failedIterationMap;
        static int maxIterationWithoutImprovement = 50;

        static int traceLength = 10;
        static boolean isFinished = false;
        static int discoveredBranches = 0;
        static int totalErrors = 0;
        static Set<Integer> uniqueErrorIds = new HashSet<>();

        // RANDOM FUZZER REPORTING ONLY
        static Set<String> totalVisitedBranches = new HashSet<>();
        static Set<String> currentTraceBranches = new HashSet<>();
        static int bestSingleTraceBranchCount = 0;
        static List<String> bestSingleTrace = new ArrayList<>();
        
        static final double K = 1.0;

        // Needed to keep track of the branches not reached yet.      
        static Map<String, Double> bestBranchDistances = new HashMap<>();

        // Stores the best trace observed so far for each branch target. Linked to bestBranchDistance
        static Map<String, List<String>> bestTrace = new HashMap<>();
        
        public static void setErrorCount(int count){
                totalErrors = count;
        }

        static void initialize(String[] inputSymbols){
                // Initialise a random trace from the input symbols of the problem.
                currentTrace = generateRandomTrace(inputSymbols);
                currentTotalTraceDistance = 0.0;
                failedIterationMap = new HashMap<>();

                totalVisitedBranches.clear();
                currentTraceBranches.clear();
                bestSingleTraceBranchCount = 0;
                bestSingleTrace = new ArrayList<>();
                uniqueErrorIds.clear();
        }

        /**
         * Write your solution that specifies what should happen when a new branch has been found.
         */
        static void encounteredNewBranch(MyVar condition, boolean value, int line_nr){ 
                discoveredBranches++;
                
                if (discoveredBranches % 10000 == 0) {
                        System.out.println("Found branch: " + discoveredBranches);
                }

                boolean oppositeValue = !value;
        
                double distanceToTakenBranch = branchDistance(condition, value);
                double distanceToOppositeBranch = branchDistance(condition, oppositeValue);
        
                currentTotalTraceDistance += distanceToOppositeBranch;

                String takenKey = line_nr + ":" + value;
                String oppositeKey = line_nr + ":" + oppositeValue;

                // RANDOM FUZZER REPORTING ONLY
                totalVisitedBranches.add(takenKey);
                currentTraceBranches.add(takenKey);
        
                updateBestDistance(takenKey, distanceToTakenBranch);
                updateBestDistance(oppositeKey, distanceToOppositeBranch);
                
                updateBestTrace();
        }

        static double branchDistance(MyVar condition, boolean targetValue) {
                if (targetValue) {
                        return distanceToTrue(condition);
                }

                return distanceToFalse(condition);
        }

        static double distanceToTrue(MyVar condition) {
                if (condition == null) {
                        return 1.0;
                }

                String operator = condition.operator;

                if (operator == null || operator.equals("")) {
                        return booleanDistance(valueOf(condition), true);
                }

                switch (operator) {
                        case "==":
                                return equalityDistance(condition);

                        case "!=":
                                return inequalityDistance(condition);

                        case "<":
                                return lessThanDistance(condition);

                        case "<=":
                                return lessThanOrEqualDistance(condition);

                        case ">":
                                return greaterThanDistance(condition);

                        case ">=":
                                return greaterThanOrEqualDistance(condition);

                        case "&&":
                                return normalize(distanceToTrue(condition.left))
                                                + normalize(distanceToTrue(condition.right));

                        case "||":
                                return Math.min(
                                                normalize(distanceToTrue(condition.left)),
                                                normalize(distanceToTrue(condition.right))
                                );

                        case "XOR": // I actually am unsure if this is the correct operator?
                                return Math.min(
                                                normalize(distanceToTrue(condition.left))
                                                                + normalize(distanceToFalse(condition.right)),
                                                normalize(distanceToFalse(condition.left))
                                                                + normalize(distanceToTrue(condition.right))
                                );

                        case "!":
                                return distanceToFalse(condition.left);

                        default:
                                return booleanDistance(valueOf(condition), true);
                }
        }

        static double distanceToFalse(MyVar condition) {
                if (condition == null) {
                        return 1.0;
                }

                String operator = condition.operator;

                if (operator == null || operator.equals("")) {
                        return booleanDistance(valueOf(condition), false);
                }

                switch (operator) {
                        case "==":
                                return inequalityDistance(condition);

                        case "!=":
                                return equalityDistance(condition);

                        case "<":
                                return greaterThanOrEqualDistance(condition);

                        case "<=":
                                return greaterThanDistance(condition);

                        case ">":
                                return lessThanOrEqualDistance(condition);

                        case ">=":
                                return lessThanDistance(condition);

                        case "&&":
                                return Math.min(
                                                normalize(distanceToFalse(condition.left)),
                                                normalize(distanceToFalse(condition.right))
                                );

                        case "||":
                                return normalize(distanceToFalse(condition.left))
                                                + normalize(distanceToFalse(condition.right));

                        case "XOR": // I actually am unsure if this is the correct operator?
                                return Math.min(
                                                normalize(distanceToTrue(condition.left))
                                                                + normalize(distanceToTrue(condition.right)),
                                                normalize(distanceToFalse(condition.left))
                                                                + normalize(distanceToFalse(condition.right))
                                );

                        case "!":
                                return distanceToTrue(condition.left);

                        default:
                                return booleanDistance(valueOf(condition), false);
                }
        }

        static double equalityDistance(MyVar condition) {
                Object left = valueOf(condition.left);
                Object right = valueOf(condition.right);

                if (left == null && right == null) {
                        return 0.0;
                }

                if (left == null || right == null) {
                        return 1.0;
                }

                if (left instanceof Number && right instanceof Number) {
                        return Math.abs(toDouble(left) - toDouble(right));
                }

                if (left instanceof Boolean && right instanceof Boolean) {
                        return left.equals(right) ? 0.0 : 1.0;
                }

                return left.equals(right) ? 0.0 : 1.0;
        }

        static double inequalityDistance(MyVar condition) {
                Object left = valueOf(condition.left);
                Object right = valueOf(condition.right);

                if (left == null && right == null) {
                        return 1.0;
                }

                if (left == null || right == null) {
                        return 0.0;
                }

                if (left instanceof Number && right instanceof Number) {
                        return toDouble(left) == toDouble(right) ? 1.0 : 0.0;
                }

                return left.equals(right) ? 1.0 : 0.0;
        }

        static double lessThanDistance(MyVar condition) {
                double left = numericValueOf(condition.left);
                double right = numericValueOf(condition.right);

                if (left < right) {
                        return 0.0;
                }

                return left - right + K;
        }

        static double lessThanOrEqualDistance(MyVar condition) {
                double left = numericValueOf(condition.left);
                double right = numericValueOf(condition.right);

                if (left <= right) {
                        return 0.0;
                }

                return left - right;
        }

        static double greaterThanDistance(MyVar condition) {
                double left = numericValueOf(condition.left);
                double right = numericValueOf(condition.right);

                if (left > right) {
                        return 0.0;
                }

                return right - left + K;
        }

        static double greaterThanOrEqualDistance(MyVar condition) {
                double left = numericValueOf(condition.left);
                double right = numericValueOf(condition.right);

                if (left >= right) {
                        return 0.0;
                }

                return right - left;
        }

        static double booleanDistance(Object value, boolean targetValue) {
                if (value instanceof Boolean) {
                        boolean booleanValue = (Boolean) value;
                        return booleanValue == targetValue ? 0.0 : 1.0;
                }

                if (value instanceof Number) {
                        double numberValue = toDouble(value);

                        if (targetValue) {
                                return numberValue != 0.0 ? 0.0 : 1.0;
                        }

                        return numberValue == 0.0 ? 0.0 : 1.0;
                }

                if (value instanceof String) {
                        boolean nonEmpty = !((String) value).isEmpty();
                        return nonEmpty == targetValue ? 0.0 : 1.0;
                }

                return value != null && targetValue ? 0.0 : 1.0;
        }

        static Object valueOf(MyVar var) {
                if (var == null) {
                        return null;
                }

                if (var.type == TypeEnum.BOOL) {
                        return var.value;
                }

                if (var.type == TypeEnum.INT) {
                        return var.int_value;
                }

                if (var.type == TypeEnum.STRING) {
                        return var.str_value;
                }

                String operator = var.operator;

                if (operator == null || operator.equals("")) {
                        return null;
                }

                switch (operator) {
                        case "+":
                                return numericValueOf(var.left) + numericValueOf(var.right);

                        case "-":
                                return numericValueOf(var.left) - numericValueOf(var.right);

                        case "*":
                                return numericValueOf(var.left) * numericValueOf(var.right);

                        case "/":
                                double divisor = numericValueOf(var.right);
                                if (divisor == 0.0) {
                                        return Double.MAX_VALUE;
                                }
                                return numericValueOf(var.left) / divisor;

                        case "%":
                                double modulo = numericValueOf(var.right);
                                if (modulo == 0.0) {
                                        return Double.MAX_VALUE;
                                }
                                return numericValueOf(var.left) % modulo;

                        case "==":
                                return equalityDistance(var) == 0.0;

                        case "!=":
                                return inequalityDistance(var) == 0.0;

                        case "<":
                                return numericValueOf(var.left) < numericValueOf(var.right);

                        case "<=":
                                return numericValueOf(var.left) <= numericValueOf(var.right);

                        case ">":
                                return numericValueOf(var.left) > numericValueOf(var.right);

                        case ">=":
                                return numericValueOf(var.left) >= numericValueOf(var.right);

                        case "&&":
                                return asBoolean(valueOf(var.left)) && asBoolean(valueOf(var.right));

                        case "||":
                                return asBoolean(valueOf(var.left)) || asBoolean(valueOf(var.right));

                        case "XOR": // I actually am unsure if this is the correct operator?
                                return asBoolean(valueOf(var.left)) ^ asBoolean(valueOf(var.right));

                        case "!":
                                return !asBoolean(valueOf(var.left));

                        default:
                                return null;
                }
        }

        static double numericValueOf(MyVar var) {
                Object value = valueOf(var);

                if (value instanceof Number) {
                        return toDouble(value);
                }

                if (value instanceof Boolean) {
                        return (Boolean) value ? 1.0 : 0.0;
                }

                try {
                        return Double.parseDouble(String.valueOf(value));
                } catch (NumberFormatException e) {
                        return 0.0;
                }
        }

        static boolean asBoolean(Object value) {
                if (value instanceof Boolean) {
                        return (Boolean) value;
                }

                if (value instanceof Number) {
                        return toDouble(value) != 0.0;
                }

                if (value instanceof String) {
                        return !((String) value).isEmpty();
                }

                return value != null;
        }

        static double toDouble(Object value) {
                return ((Number) value).doubleValue();
        }

        static double normalize(double distance) {
                if (distance < 0.0) {
                        distance = 0.0;
                }

                return distance / (distance + 1.0);
        }

        static void updateBestDistance(String key, double distance) {
                if (!bestBranchDistances.containsKey(key) || distance < bestBranchDistances.get(key)) {
                        bestBranchDistances.put(key, distance);
                        bestTrace.put(key, currentTrace);

                        if(key.equals(currentTarget)){
                                targetReached = true;
                        }
                }
        }

        static void updateBestTrace(){
                if (bestTraceAndDistance == null || currentTotalTraceDistance < bestTraceAndDistance.b) {
                        bestTraceAndDistance = new Pair<>(currentTrace, currentTotalTraceDistance);
                        iterationWithoutImprovement = 0;
                }
        }

        // RANDOM FUZZER REPORTING ONLY
        static void updateBestRandomTrace() {
                if (currentTraceBranches.size() > bestSingleTraceBranchCount) {
                        bestSingleTraceBranchCount = currentTraceBranches.size();
                        bestSingleTrace = new ArrayList<>(currentTrace);
                }
        }

        /**
         * Method for fuzzing new inputs for a program.
         * @param inputSymbols the inputSymbols to fuzz from.
         * @param mutationNumber the number to decide which mutation operator to use, can be used for tuning the fuzzing strategy. 0 for even mutation, 1 for distance-based mutation, etc.
         * @return a fuzzed sequence
         */
        static List<String> fuzz(String[] inputSymbols, int mutationNumber) {
                if (currentTarget == null || bestTrace.get(currentTarget) == null){
                        return generateRandomTrace(inputSymbols);
                }

                switch (mutationNumber) {
                        case 0:
                                return mutateTraceEven(bestTrace.get(currentTarget), inputSymbols);
                        case 1:
                                return mutateTraceOnThreshold(bestTrace.get(currentTarget), inputSymbols);
                        case 2:
                                return mutateTraceOnStrategy(bestTrace.get(currentTarget), inputSymbols, "quadratic");
                        default:
                                return generateRandomTrace(inputSymbols);
                }
        }

        static List<String> mutateTraceOnStrategy(List<String> trace, String[] symbols, String strategy) {
                int numChangesToMake;

                switch (strategy) {
                        case "linear":
                                numChangesToMake = Math.max(1, Math.min(10, (int) (currentTotalTraceDistance / 10.0)));

                        case "adaptive":
                                if (currentTotalTraceDistance < 1.0) {
                                        numChangesToMake = 1;
                                } else if (currentTotalTraceDistance < 5.0) {
                                        numChangesToMake = Math.max(1, (int) currentTotalTraceDistance);
                                } else if (currentTotalTraceDistance < 20.0) {
                                        numChangesToMake = Math.max(3, (int) (currentTotalTraceDistance / 2.0));
                                } else {
                                        numChangesToMake = Math.max(5, Math.min(10, (int) (currentTotalTraceDistance / 10.0)));
                                }

                        case "quadratic":
                                double normalized = Math.min(1.0, currentTotalTraceDistance / 100.0);
                                numChangesToMake = Math.max(1, Math.min(10, (int) (Math.pow(normalized, 2.0) * 10.0)));

                        case "step":
                                if (currentTotalTraceDistance < 2.0) {
                                        numChangesToMake = 1;
                                } else if (currentTotalTraceDistance < 5.0) {
                                        numChangesToMake = 2;
                                } else if (currentTotalTraceDistance < 15.0) {
                                        numChangesToMake = 5;
                                } else {
                                        numChangesToMake = 10;
                                }

                        default:
                                numChangesToMake = 1;
                }

                List<String> mutated = new ArrayList<>(trace);
                int changesRemaining = numChangesToMake;

                if (mutated.isEmpty()) {
                        for (int i = 0; i < numChangesToMake; i++) {
                                mutated.add(symbols[r.nextInt(symbols.length)]);
                        }
                        return mutated;
                }

                while (changesRemaining > 0) {
                        int operator = r.nextInt(3);

                        switch (operator) {
                                case 0:
                                        mutated = mutateChangeSymbol(mutated, symbols);
                                        changesRemaining--;
                                        break;

                                case 1:
                                        mutated = mutateAddSymbol(mutated, symbols);
                                        changesRemaining--;
                                        break;

                                case 2:
                                        if (mutated.size() > 1) {
                                                mutated = mutateDeleteSymbol(mutated);
                                                changesRemaining--;
                                        }
                                        break;
                        }
                }

                return mutated;
        }

        /**
         * Mutate by changing a random symbol to another symbol
         * Example: ["A", "B", "C"] -> ["D", "B", "C"]
         */
        static List<String> mutateChangeSymbol(List<String> trace, String[] symbols) {
                if (trace.isEmpty()) return new ArrayList<>(trace);
                
                List<String> mutated = new ArrayList<>(trace);
                int indexToChange = r.nextInt(mutated.size());
                
                String currentSymbol = mutated.get(indexToChange);
                String newSymbol;
                do {
                        newSymbol = symbols[r.nextInt(symbols.length)];
                } while (newSymbol.equals(currentSymbol) && symbols.length > 1);
                
                mutated.set(indexToChange, newSymbol);
                return mutated;
        }

        /**
         * Mutate by adding a random symbol at a random position
         */
        static List<String> mutateAddSymbol(List<String> trace, String[] symbols) {
                List<String> mutated = new ArrayList<>(trace);
                
                int insertionPoint = r.nextInt(mutated.size() + 1);
                String newSymbol = symbols[r.nextInt(symbols.length)];
                
                mutated.add(insertionPoint, newSymbol);
                return mutated;
        }

        /**
         * Mutate by deleting a random symbol
         */
        static List<String> mutateDeleteSymbol(List<String> trace) {
                if (trace.isEmpty()) return new ArrayList<>(trace);
                
                List<String> mutated = new ArrayList<>(trace);
                int indexToDelete = r.nextInt(mutated.size());
                mutated.remove(indexToDelete);
                
                return mutated;
        }

        /**
         * Generate a completely random trace
         */
        static List<String> generateCompletelyRandomTrace(String[] symbols) {
                ArrayList<String> trace = new ArrayList<>();
                int randomLength = 5 + r.nextInt(20);
                for (int i = 0; i < randomLength; i++) {
                        trace.add(symbols[r.nextInt(symbols.length)]);
                }
                return trace;
        }

        /**
         * Generate a random trace from an array of symbols.
         */
        static List<String> generateRandomTrace(String[] symbols) {
                ArrayList<String> trace = new ArrayList<>();
                for (int i = 0; i < traceLength; i++) {
                        trace.add(symbols[r.nextInt(symbols.length)]);
                }
                return trace;
        }

        static List<String> mutateTraceEven(List<String> trace, String[] symbols) {
                List<String> mutation;
                String type;
                
                int operatorChoice = r.nextInt(3);
                switch (operatorChoice) {
                        case 0:
                                mutation = mutateChangeSymbol(trace, symbols);
                                type = "CHANGE";
                                break;
                        case 1:
                                mutation = mutateAddSymbol(trace, symbols);
                                type = "ADD";
                                break;
                        case 2:
                                mutation = mutateDeleteSymbol(trace);
                                type = "DELETE";
                                break;
                        default:
                                mutation = mutateChangeSymbol(trace, symbols);
                                type = "CHANGE";
                }
                return mutation;
        }

        static List<String> mutateTraceOnThreshold(List<String> trace, String[] symbols) {
                List<String> mutation = new ArrayList<>(trace);
                if (currentTotalTraceDistance < 2.0) {
                        double rand = r.nextDouble();
                        if (rand < 0.8) mutation = mutateChangeSymbol(trace, symbols);
                        else if (rand < 0.9) mutation = mutateAddSymbol(trace, symbols);
                        else mutation = mutateDeleteSymbol(trace);
                }
                else if (currentTotalTraceDistance < 10.0) {
                        double rand = r.nextDouble();
                        if (rand < 0.4) mutation = mutateChangeSymbol(trace, symbols);
                        else if (rand < 0.7) mutation = mutateAddSymbol(trace, symbols);
                        else mutation = mutateDeleteSymbol(trace);
                }
                else {
                        double rand = r.nextDouble();
                        if (rand < 0.2) mutation = mutateChangeSymbol(trace, symbols);
                        else if (rand < 0.6) mutation = mutateAddSymbol(trace, symbols);
                        else mutation = mutateDeleteSymbol(trace);
                }
                return mutation;
        }

        static void printUniqueBranches() {
                output("========== UNIQUE BRANCHES SUMMARY ==========");
                output("Total unique branches encountered: " + bestBranchDistances.size());

                int reachedBranches = 0;
                int unreachedBranches = 0;
                
                for (Map.Entry<String, Double> entry : bestBranchDistances.entrySet()) {
                        if (entry.getValue() == 0.0) {
                                reachedBranches++;
                        } else {
                                unreachedBranches++;
                        }
                }
                
                output("Branches reached (distance = 0): " + reachedBranches);
                output("Branches unreached (distance > 0): " + unreachedBranches);

                // RANDOM FUZZER REPORTING ONLY
                output("Total actual unique branches visited during run: " + totalVisitedBranches.size());
                output("Best single-trace branch count: " + bestSingleTraceBranchCount);
                output("Input trace with highest number of unique branches: " + bestSingleTrace);

                if (uniqueErrorIds.isEmpty()) {
                        output("Unique Errors: 0 — IDs: None");
                } else {
                        List<Integer> sortedErrors = new ArrayList<>(uniqueErrorIds);
                        Collections.sort(sortedErrors);
                        StringBuilder errorIds = new StringBuilder();

                        for (int i = 0; i < sortedErrors.size(); i++) {
                                if (i > 0) errorIds.append(", ");
                                errorIds.append(sortedErrors.get(i));
                        }

                        output("Unique Errors: " + sortedErrors.size() + " — IDs: " + errorIds.toString());
                }
                
                output("============================================");
        }

        /**
         * Parses error messages from stdout and extracts error IDs.
         */
        static void parseAndTrackErrors(String message) {
                if (message == null) return;

                java.util.regex.Pattern pattern = java.util.regex.Pattern.compile("error_(\\d+)");
                java.util.regex.Matcher matcher = pattern.matcher(message);

                while (matcher.find()) {
                        try {
                                int errorId = Integer.parseInt(matcher.group(1));
                                uniqueErrorIds.add(errorId);
                        } catch (NumberFormatException e) {
                                // Ignore parsing errors
                        }
                }
        }

        static List<String> getUnreachedBranchesSorted() {
                List<String> unreachedBranches = new ArrayList<>();
                for (Map.Entry<String, Double> entry : bestBranchDistances.entrySet()) {
                        if (entry.getValue() != 0.0) {
                                unreachedBranches.add(entry.getKey());
                        }
                }

                unreachedBranches.sort((b1, b2) -> {
                        Double d1 = bestBranchDistances.get(b1);
                        Double d2 = bestBranchDistances.get(b2);
                        return d1.compareTo(d2);
                });

                return unreachedBranches;
        }

        static String getNextTarget(List<String> unreachedBranches, String selectionType){
                if (unreachedBranches.isEmpty()) {
                        return null;
                }
                
                switch (selectionType) {
                        case "shortest":
                                double bestDistance = Double.MAX_VALUE;
                                String bestBranch = unreachedBranches.get(0);

                                for (String branch : unreachedBranches) {
                                        double d = bestBranchDistances.get(branch);
                                        if (d < bestDistance) {
                                                bestDistance = d;
                                                bestBranch = branch;
                                        }
                                }

                                return bestBranch;
                        
                        case "mixed":
                                int x = r.nextInt(100);
                                int delta = r.nextInt(Math.max(1, unreachedBranches.size() / 3));
                                
                                if (x > 60) {
                                        return unreachedBranches.get(delta);
                                } else if (x < 30) {
                                        return unreachedBranches.get(Math.max(0, unreachedBranches.size() - 1 - delta));
                                } else {
                                        return unreachedBranches.get(unreachedBranches.size() / 2);
                                }
                                
                        default:
                                return unreachedBranches.get(r.nextInt(unreachedBranches.size()));
                }
        }

        /**
         * RANDOM FUZZER RUN ONLY.
         * This runs pure random traces for 5 minutes.
         * It does not call the smart fuzzer.
         */
        static void run() {
                output("Starting RANDOM fuzzing lab...");

                initialize(DistanceTracker.inputSymbols);

                long startTime = System.currentTimeMillis();
                long runtimeMillis = 5 * 60 * 1000;
                long endTime = startTime + runtimeMillis;

                int executedTraces = 0;

                while (!isFinished && System.currentTimeMillis() < endTime) {
                        try {
                                currentTrace = generateRandomTrace(DistanceTracker.inputSymbols);
                                currentTotalTraceDistance = 0.0;

                                currentTraceBranches.clear();

                                DistanceTracker.runNextFuzzedSequence(currentTrace.toArray(new String[0]));

                                updateBestRandomTrace();

                                executedTraces++;

                                if (executedTraces % 1000 == 0) {
                                        output("[Progress] Executed traces: " + executedTraces
                                                + ", total actual unique branches visited: " + totalVisitedBranches.size()
                                                + ", best single-trace branch count: " + bestSingleTraceBranchCount
                                                + ", unique errors: " + uniqueErrorIds.size());
                                }

                        } catch (Exception e) {
                                output("Error during random fuzzing: " + e.getMessage());
                                parseAndTrackErrors(e.getMessage());
                        }
                }

                long actualRuntimeSeconds = (System.currentTimeMillis() - startTime) / 1000;

                output("End RANDOM fuzzing lab.");
                output("Actual runtime seconds: " + actualRuntimeSeconds);
                output("Executed traces: " + executedTraces);

                isFinished = true;
                printUniqueBranches();
        }

        /**
         * Method that is used for catching the output from standard out.
         * Parses error messages from the output to track unique errors.
         * @param out the string that has been outputted in the standard out.
         */
        public static void output(String out){
                System.out.println(out);
                parseAndTrackErrors(out);
        }
}