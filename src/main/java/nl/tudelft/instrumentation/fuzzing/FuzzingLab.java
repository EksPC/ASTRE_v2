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

        static long currentSeed = 0L;
        static List<long[]> currentRunSnapshots = new ArrayList<>();
        static long lastSnapshotTime = 0L;
        static final int SNAPSHOT_INTERVAL_MS = 1000;
        static final long[] SEEDS = {42L, 123L, 456L, 789L, 1337L};
        static String outDir = "results/";
        static String resultsRoot = "results";
        static long runtimeMillis = 5 * 60 * 1000L;
        static String[] activeModes = {"hill_base", "hill_improved"};

        // Improvement-specific state for the coverage-aware hill climber.
        static List<List<String>> coverageCorpus = new ArrayList<>();
        static int maxCorpusSize = 200;
        static int lastCorpusCoverage = 0;
        static int lastCorpusErrorCount = 0;
        static Map<String, Integer> targetAttempts = new HashMap<>();
        static Map<String, Integer> targetSuccesses = new HashMap<>();

        // Needed to keep track of the branches not reached yet.
        static Map<String, Double> bestBranchDistances = new HashMap<>();

        // Stores the best trace observed so far for each branch target. Linked to bestBranchDistance
        static Map<String, List<String>> bestTrace = new HashMap<>();
        
        // Theoretically we could've saved both trace and distance in a single map

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

                coverageCorpus.clear();
                lastCorpusCoverage = 0;
                lastCorpusErrorCount = 0;
                targetAttempts.clear();
                targetSuccesses.clear();
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
                
                // Track Distance to each branch (0 for the branch we took)
                double distanceToTakenBranch = branchDistance(condition, value);
                double distanceToOppositeBranch = branchDistance(condition, oppositeValue);
                
                // Current total distance accumulatd by this branch, used to guide the fuzzing strategy
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

                // If the current best distance doesn't contain this key or
                //  the current trace's distance is less than the currently saved one, update the best distance and best trace
                if (!bestBranchDistances.containsKey(key) || distance < bestBranchDistances.get(key)) {
                        bestBranchDistances.put(key, distance);
                        bestTrace.put(key, currentTrace);

                        // This is used in the hill climbing strategy
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
                                break;

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
                                break;

                        case "quadratic":
                                double normalized = Math.min(1.0, currentTotalTraceDistance / 100.0);
                                numChangesToMake = Math.max(1, Math.min(10, (int) (Math.pow(normalized, 2.0) * 10.0)));
                                break;

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
                                break;

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

                        case "coverageAware":
                                return getCoverageAwareTarget(unreachedBranches);

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
         * Improved target choice for Task 3.
         *
         * The base hill climber always follows the closest currently known unreached branch.
         * That is greedy and can repeatedly spend the budget on targets that do not lead to
         * new coverage. The improved version still favours small branch distances, but adds
         * a penalty for targets that have already consumed many attempts. With 20% probability
         * it explores a random known target to avoid repeatedly attacking the same local basin.
         */
        static String getCoverageAwareTarget(List<String> unreachedBranches) {
                if (unreachedBranches.size() == 1) {
                        return unreachedBranches.get(0);
                }

                if (r.nextDouble() < 0.20) {
                        return unreachedBranches.get(r.nextInt(unreachedBranches.size()));
                }

                String bestBranch = unreachedBranches.get(0);
                double bestScore = Double.MAX_VALUE;

                int candidateLimit = Math.min(25, unreachedBranches.size());
                for (int i = 0; i < candidateLimit; i++) {
                        String branch = unreachedBranches.get(i);
                        double distance = normalize(bestBranchDistances.getOrDefault(branch, Double.MAX_VALUE));
                        int attempts = targetAttempts.getOrDefault(branch, 0);
                        int successes = targetSuccesses.getOrDefault(branch, 0);

                        double stagnationPenalty = 0.03 * attempts;
                        double successBonus = successes > 0 ? -0.10 : 0.0;
                        double score = distance + stagnationPenalty + successBonus;

                        if (score < bestScore) {
                                bestScore = score;
                                bestBranch = branch;
                        }
                }

                return bestBranch;
        }

        static boolean isHillMode(String mode) {
                return mode.equals("hill_base") || mode.equals("hill_improved") || mode.equals("hillclimb");
        }

        static boolean isImprovedMode(String mode) {
                return mode.equals("hill_improved");
        }

        static void configureFromSystemProperties() {
                runtimeMillis = Long.parseLong(System.getProperty("fuzzing.timeoutSeconds", "300")) * 1000L;
                traceLength = Integer.parseInt(System.getProperty("fuzzing.traceLength", "10"));
                maxIterationWithoutImprovement = Integer.parseInt(System.getProperty("fuzzing.maxNoImprove", "50"));
                maxCorpusSize = Integer.parseInt(System.getProperty("fuzzing.maxCorpusSize", "200"));
                resultsRoot = System.getProperty("fuzzing.resultsDir", "results");

                String modesProperty = System.getProperty("fuzzing.modes", "hill_base,hill_improved");
                String[] rawModes = modesProperty.split(",");
                List<String> parsedModes = new ArrayList<>();
                for (String rawMode : rawModes) {
                        String mode = rawMode.trim();
                        if (!mode.isEmpty()) {
                                parsedModes.add(mode);
                        }
                }
                if (!parsedModes.isEmpty()) {
                        activeModes = parsedModes.toArray(new String[0]);
                }
        }

        static List<String> fuzzImproved(String[] inputSymbols, int noImproveCount) {
                if (r.nextDouble() < 0.05) {
                        return generateCompletelyRandomTrace(inputSymbols);
                }

                List<String> seedTrace;
                if (currentTarget != null && bestTrace.get(currentTarget) != null && r.nextDouble() < 0.70) {
                        seedTrace = bestTrace.get(currentTarget);
                } else if (!coverageCorpus.isEmpty()) {
                        seedTrace = coverageCorpus.get(r.nextInt(coverageCorpus.size()));
                } else if (currentTarget != null && bestTrace.get(currentTarget) != null) {
                        seedTrace = bestTrace.get(currentTarget);
                } else {
                        seedTrace = generateRandomTrace(inputSymbols);
                }

                double targetDistance = currentTarget == null
                                ? Double.MAX_VALUE
                                : bestBranchDistances.getOrDefault(currentTarget, Double.MAX_VALUE);
                int strength = adaptiveMutationStrength(targetDistance, noImproveCount, seedTrace.size());
                List<String> mutated = mutateTraceWithStrength(seedTrace, inputSymbols, strength);

                if (noImproveCount > maxIterationWithoutImprovement / 2 && !coverageCorpus.isEmpty() && r.nextDouble() < 0.30) {
                        mutated = spliceWithCorpusTrace(mutated, inputSymbols);
                }

                return mutated;
        }

        static int adaptiveMutationStrength(double targetDistance, int noImproveCount, int traceSize) {
                int strength;
                double normalizedDistance = normalize(targetDistance);

                if (targetDistance == 0.0 || normalizedDistance < 0.10) {
                        strength = 1;
                } else if (normalizedDistance < 0.50) {
                        strength = 2;
                } else {
                        strength = 3;
                }

                strength += noImproveCount / 15;

                int maxStrength = Math.max(1, Math.min(12, traceSize + 2));
                return Math.max(1, Math.min(maxStrength, strength));
        }

        static List<String> mutateTraceWithStrength(List<String> trace, String[] symbols, int strength) {
                List<String> mutated = new ArrayList<>(trace);
                if (mutated.isEmpty()) {
                        mutated.add(symbols[r.nextInt(symbols.length)]);
                }

                for (int i = 0; i < strength; i++) {
                        double choice = r.nextDouble();
                        if (choice < 0.60) {
                                mutated = mutateChangeSymbol(mutated, symbols);
                        } else if (choice < 0.82) {
                                mutated = mutateAddSymbol(mutated, symbols);
                        } else if (mutated.size() > 1) {
                                mutated = mutateDeleteSymbol(mutated);
                        } else {
                                mutated = mutateChangeSymbol(mutated, symbols);
                        }
                }

                return mutated;
        }

        static List<String> spliceWithCorpusTrace(List<String> trace, String[] symbols) {
                if (coverageCorpus.isEmpty()) {
                        return mutateTraceWithStrength(trace, symbols, 1);
                }

                List<String> other = coverageCorpus.get(r.nextInt(coverageCorpus.size()));
                if (trace.isEmpty() || other.isEmpty()) {
                        return mutateTraceWithStrength(trace, symbols, 1);
                }

                int splitA = r.nextInt(trace.size());
                int splitB = r.nextInt(other.size());
                List<String> spliced = new ArrayList<>();
                spliced.addAll(trace.subList(0, splitA));
                spliced.addAll(other.subList(splitB, other.size()));

                if (spliced.isEmpty()) {
                        spliced.add(symbols[r.nextInt(symbols.length)]);
                }

                return spliced;
        }

        static void recordInterestingTrace(List<String> trace) {
                int coverage = totalVisitedBranches.size();
                int errorCount = uniqueErrorIds.size();

                if (coverageCorpus.isEmpty() || coverage > lastCorpusCoverage || errorCount > lastCorpusErrorCount) {
                        coverageCorpus.add(new ArrayList<>(trace));
                        lastCorpusCoverage = coverage;
                        lastCorpusErrorCount = errorCount;

                        while (coverageCorpus.size() > maxCorpusSize) {
                                coverageCorpus.remove(0);
                        }
                }
        }

        static void executeTraceAndUpdateCorpus(List<String> trace, boolean useCorpus) {
                currentTrace = trace;
                currentTotalTraceDistance = 0.0;
                currentTraceBranches.clear();

                try {
                        DistanceTracker.runNextFuzzedSequence(currentTrace.toArray(new String[0]));
                } catch (Exception e) {
                        output("Error: " + e.getMessage());
                        parseAndTrackErrors(e.getMessage());
                }

                updateBestRandomTrace();
                if (useCorpus) {
                        recordInterestingTrace(currentTrace);
                }
        }

        static void run() {
                configureFromSystemProperties();

                String problemName = DistanceTracker.problem.getClass().getSimpleName();
                outDir = resultsRoot + "/" + problemName + "/";
                new java.io.File(outDir).mkdirs();

                output("Starting fuzzing lab for Task 3.");
                output("Modes: " + String.join(", ", activeModes));
                output("Seeds per mode: " + SEEDS.length);
                output("Timeout per run: " + (runtimeMillis / 1000) + " seconds");
                output("Output directory: " + outDir);

                List<String[]> allSummaries = new ArrayList<>();

                for (String mode : activeModes) {
                        output("========== " + mode.toUpperCase() + " PHASE ==========");
                        for (int runIdx = 0; runIdx < SEEDS.length; runIdx++) {
                                long seed = SEEDS[runIdx];
                                output("=== " + mode + " run " + (runIdx + 1) + "/" + SEEDS.length + " (seed=" + seed + ") ===");
                                allSummaries.add(runSingleSeed(seed, runIdx + 1, mode));
                        }
                }

                saveSummaryCSV(allSummaries);
                saveStatsCSV(allSummaries);
                output("All runs complete. Results saved in " + outDir);
                isFinished = true;
        }

        static String[] runSingleSeed(long seed, int runIndex, String mode) {
                if (!mode.equals("random") && !isHillMode(mode)) {
                        throw new IllegalArgumentException("Unknown fuzzing mode: " + mode);
                }

                r = new Random(seed);
                currentSeed = seed;
                bestTraceAndDistance = null;
                currentTarget = null;
                targetReached = false;
                iterationWithoutImprovement = 0;
                discoveredBranches = 0;
                totalErrors = 0;
                bestBranchDistances = new HashMap<>();
                bestTrace = new HashMap<>();
                currentRunSnapshots = new ArrayList<>();

                initialize(DistanceTracker.inputSymbols);

                long startTime = System.currentTimeMillis();
                long endTime = startTime + runtimeMillis;
                lastSnapshotTime = startTime;
                int executedTraces = 0;
                boolean improved = isImprovedMode(mode);

                currentRunSnapshots.add(new long[]{0, 0, 0, 0, 0});

                if (mode.equals("random")) {
                        while (System.currentTimeMillis() < endTime) {
                                executeTraceAndUpdateCorpus(generateRandomTrace(DistanceTracker.inputSymbols), false);
                                executedTraces++;
                                maybeSnapshot(runIndex, mode, startTime, executedTraces, null, Double.NaN);
                        }
                } else {
                        while (System.currentTimeMillis() < endTime) {
                                List<String> unreached = getUnreachedBranchesSorted();
                                currentTarget = getNextTarget(unreached, improved ? "coverageAware" : "shortest");

                                if (currentTarget == null) {
                                        List<String> discoveryTrace = improved
                                                        ? fuzzImproved(DistanceTracker.inputSymbols, 0)
                                                        : generateRandomTrace(DistanceTracker.inputSymbols);
                                        executeTraceAndUpdateCorpus(discoveryTrace, improved);
                                        executedTraces++;
                                        maybeSnapshot(runIndex, mode, startTime, executedTraces, null, Double.NaN);
                                        continue;
                                }

                                targetAttempts.put(currentTarget, targetAttempts.getOrDefault(currentTarget, 0) + 1);
                                int noImproveCount = 0;

                                while (noImproveCount < maxIterationWithoutImprovement
                                       && System.currentTimeMillis() < endTime) {
                                        double prevBestDist = bestBranchDistances.getOrDefault(currentTarget, Double.MAX_VALUE);

                                        List<String> candidate = improved
                                                        ? fuzzImproved(DistanceTracker.inputSymbols, noImproveCount)
                                                        : fuzz(DistanceTracker.inputSymbols, 2);
                                        executeTraceAndUpdateCorpus(candidate, improved);
                                        executedTraces++;

                                        double newBestDist = bestBranchDistances.getOrDefault(currentTarget, Double.MAX_VALUE);
                                        if (newBestDist < prevBestDist) {
                                                noImproveCount = 0;
                                                if (newBestDist == 0.0) {
                                                        targetSuccesses.put(currentTarget, targetSuccesses.getOrDefault(currentTarget, 0) + 1);
                                                        break;
                                                }
                                        } else {
                                                noImproveCount++;
                                        }

                                        maybeSnapshot(runIndex, mode, startTime, executedTraces, currentTarget, newBestDist);
                                }

                                if (bestBranchDistances.getOrDefault(currentTarget, Double.MAX_VALUE) > 0.0) {
                                        List<String> restartTrace = improved
                                                        ? fuzzImproved(DistanceTracker.inputSymbols, maxIterationWithoutImprovement)
                                                        : generateRandomTrace(DistanceTracker.inputSymbols);
                                        executeTraceAndUpdateCorpus(restartTrace, improved);
                                        executedTraces++;
                                }
                        }
                }

                long actualRuntime = System.currentTimeMillis() - startTime;

                currentRunSnapshots.add(new long[]{
                        actualRuntime,
                        executedTraces,
                        totalVisitedBranches.size(),
                        countReachedBranches(),
                        uniqueErrorIds.size()
                });

                saveTimeSeriesCSV(runIndex, seed, mode, currentRunSnapshots);
                printUniqueBranches();

                return new String[]{
                        String.valueOf(runIndex),
                        mode,
                        String.valueOf(seed),
                        String.valueOf(executedTraces),
                        String.valueOf(totalVisitedBranches.size()),
                        String.valueOf(countReachedBranches()),
                        String.valueOf(uniqueErrorIds.size()),
                        String.valueOf(actualRuntime / 1000)
                };
        }

        static void maybeSnapshot(int runIndex, String mode, long startTime, int executedTraces, String target, double targetDistance) {
                long now = System.currentTimeMillis();
                if (now - lastSnapshotTime >= SNAPSHOT_INTERVAL_MS) {
                        currentRunSnapshots.add(new long[]{
                                now - startTime,
                                executedTraces,
                                totalVisitedBranches.size(),
                                countReachedBranches(),
                                uniqueErrorIds.size()
                        });
                        lastSnapshotTime = now;

                        String targetInfo = target == null
                                        ? ""
                                        : ", target: " + target + ", dist: " + String.format("%.3f", targetDistance);
                        output("[Run " + runIndex + " " + mode + "] Traces: " + executedTraces
                                + ", visited: " + totalVisitedBranches.size()
                                + ", reached: " + countReachedBranches() + "/" + bestBranchDistances.size()
                                + ", errors: " + uniqueErrorIds.size()
                                + targetInfo);
                }
        }

        static int countReachedBranches() {
                int count = 0;
                for (double d : bestBranchDistances.values()) {
                        if (d == 0.0) count++;
                }
                return count;
        }

        static void saveTimeSeriesCSV(int runIndex, long seed, String mode, List<long[]> snapshots) {
                String filename = outDir + "run" + runIndex + "_seed" + seed + "_" + mode + "_timeseries.csv";
                try (java.io.PrintWriter pw = new java.io.PrintWriter(new java.io.FileWriter(filename))) {
                        pw.println("elapsed_ms,executed_traces,visited_branches,reached_branches,unique_errors");
                        for (long[] s : snapshots) {
                                pw.println(s[0] + "," + s[1] + "," + s[2] + "," + s[3] + "," + s[4]);
                        }
                        output("Time series saved: " + filename);
                } catch (java.io.IOException e) {
                        output("Error saving time series: " + e.getMessage());
                }
        }

        static void saveSummaryCSV(List<String[]> summaries) {
                String filename = outDir + "summary.csv";
                try (java.io.PrintWriter pw = new java.io.PrintWriter(new java.io.FileWriter(filename))) {
                        pw.println("run_index,mode,seed,executed_traces,visited_branches,reached_branches,unique_errors,runtime_seconds");
                        for (String[] s : summaries) {
                                pw.println(String.join(",", s));
                        }
                        output("Summary saved: " + filename);
                } catch (java.io.IOException e) {
                        output("Error saving summary: " + e.getMessage());
                }
        }

        static void saveStatsCSV(List<String[]> summaries) {
                // summary row layout: run_index(0), mode(1), seed(2), executed_traces(3),
                //   visited_branches(4), reached_branches(5), unique_errors(6), runtime_seconds(7)
                String[] colNames = {"executed_traces", "visited_branches", "reached_branches", "unique_errors", "runtime_seconds"};
                int[]    colIdx   = {3, 4, 5, 6, 7};

                Map<String, List<String[]>> byMode = new java.util.LinkedHashMap<>();
                for (String[] row : summaries) {
                        byMode.computeIfAbsent(row[1], k -> new ArrayList<>()).add(row);
                }

                String filename = outDir + "stats.csv";
                try (java.io.PrintWriter pw = new java.io.PrintWriter(new java.io.FileWriter(filename))) {
                        StringBuilder header = new StringBuilder("mode");
                        for (String col : colNames) {
                                header.append(",").append(col).append("_mean")
                                      .append(",").append(col).append("_std");
                        }
                        pw.println(header);

                        for (Map.Entry<String, List<String[]>> entry : byMode.entrySet()) {
                                StringBuilder line = new StringBuilder(entry.getKey());
                                for (int ci : colIdx) {
                                        double[] vals = new double[entry.getValue().size()];
                                        for (int i = 0; i < vals.length; i++) {
                                                vals[i] = Double.parseDouble(entry.getValue().get(i)[ci]);
                                        }
                                        double m = computeMean(vals);
                                        double s = computeStd(vals, m);
                                        line.append(",").append(String.format("%.2f", m))
                                            .append(",").append(String.format("%.2f", s));
                                }
                                pw.println(line);
                        }
                        output("Stats saved: " + filename);
                } catch (java.io.IOException e) {
                        output("Error saving stats: " + e.getMessage());
                }
        }

        static double computeMean(double[] vals) {
                double sum = 0;
                for (double v : vals) sum += v;
                return sum / vals.length;
        }

        static double computeStd(double[] vals, double mean) {
                if (vals.length < 2) return 0.0;
                double sumSq = 0;
                for (double v : vals) sumSq += (v - mean) * (v - mean);
                return Math.sqrt(sumSq / (vals.length - 1));
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