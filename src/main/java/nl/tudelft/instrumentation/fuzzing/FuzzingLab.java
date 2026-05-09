package nl.tudelft.instrumentation.fuzzing;
import java.util.*;

import com.github.javaparser.utils.Pair;


// public enum Strategy {
//         RANDOM,
//         THRESHOLD,
//         EVEN
// }

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
        
        static final double K = 1.0;

        
        // Needed to keep track of the branches not reached yet.      
        static Map<String, Double> bestBranchDistances = new HashMap<>();

        // Stores the best trace observed so far for each branch target. Linked to bestBranchDistance
        static Map<String, List<String>> bestTrace = new HashMap<>();
        
        static void setErrorCount(int count){
                totalErrors = count;
        }

        
        static void initialize(String[] inputSymbols){
                // Initialise a random trace from the input symbols of the problem.
                currentTrace = generateRandomTrace(inputSymbols);
                currentTotalTraceDistance = 0.0;
                failedIterationMap = new HashMap<>();
        }


        // static double getTraceSum(String branchKey){
                
        // }
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
        
                updateBestDistance(takenKey, distanceToTakenBranch);
                updateBestDistance(oppositeKey, distanceToOppositeBranch);
                
                updateBestTrace();
                
                // System.out.println("Line " + line_nr);
                // System.out.println("Condition: " + condition.toString());
                // System.out.println("Taken branch: " + value);
                // System.out.println("Normalizing when covering a condition");
                // System.out.println("Distance to taken branch: " + distanceToTakenBranch);
                // System.out.println("Distance to opposite branch: " + distanceToOppositeBranch);
                // System.out.println();
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
                        // If we got a distance to the <key> branch lass than the current one, update both the distance and the trace  
                        bestBranchDistances.put(key, distance);
                        bestTrace.put(key, currentTrace);
                        

                        if(key.equals(currentTarget)){
                                targetReached = true;
                        }
                }

        }

        static void updateBestTrace(){
                // Update the best trace if the total distance decreases, even if the target distance increases
                if (bestTraceAndDistance == null || currentTotalTraceDistance < bestTraceAndDistance.b) {
                        bestTraceAndDistance = new Pair<>(currentTrace, currentTotalTraceDistance);
                        iterationWithoutImprovement = 0;
                        
                }
        }

        /**
         * Method for fuzzing new inputs for a program.
         * @param inputSymbols the inputSymbols to fuzz from.
         * @param mutationNumber the number to decide which mutation operator to use, can be used for tuning the fuzzing strategy. 0 for even mutation, 1 for distance-based mutation, etc.
         * @return a fuzzed sequence
         */
        static List<String> fuzz(String[] inputSymbols, int mutationNumber) {
                /*
                 * Add here your code for fuzzing a new sequence for the RERS problem.
                 * You can guide your fuzzer to fuzz "smart" input sequences to cover
                 * more branches. Right now we just generate a complete random sequence
                 * using the given input symbols. Please change it to your own code.
                 */

                if (currentTarget == null || bestTrace.get(currentTarget) == null){
                        return generateRandomTrace(inputSymbols);
                }

                switch (mutationNumber) {
                        case 0:
                                return mutateTraceEven(bestTrace.get(currentTarget), inputSymbols);
                        case 1:
                                return mutateTraceOnThreshold(bestTrace.get(currentTarget), inputSymbols);
                        default:
                                return generateRandomTrace(inputSymbols);
                }
        }

        /**
        * Mutate by changing a random symbol to another symbol
        * Example: ["A", "B", "C"] -> ["D", "B", "C"]
        */
        static List<String> mutateChangeSymbol(List<String> trace, String[] symbols) {
                if (trace.isEmpty()) return new ArrayList<>(trace);
                
                List<String> mutated = new ArrayList<>(trace);
                int indexToChange = r.nextInt(mutated.size());
                
                // Pick a different symbol
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
        * Example: ["A", "B", "C"] -> ["A", "B", "C", "D"]
        * Or: ["A", "B", "C"] -> ["A", "D", "B", "C"]
        */
        static List<String> mutateAddSymbol(List<String> trace, String[] symbols) {
                List<String> mutated = new ArrayList<>(trace);
                
                // Add at random position (including end)
                int insertionPoint = r.nextInt(mutated.size() + 1);
                String newSymbol = symbols[r.nextInt(symbols.length)];
                
                mutated.add(insertionPoint, newSymbol);
                return mutated;
        }

        /**
         * Mutate by deleting a random symbol
         * Example: ["A", "B", "C"] -> ["A", "C"]
         */
        static List<String> mutateDeleteSymbol(List<String> trace) {
                if (trace.isEmpty()) return new ArrayList<>(trace);
                
                List<String> mutated = new ArrayList<>(trace);
                int indexToDelete = r.nextInt(mutated.size());
                mutated.remove(indexToDelete);
                
                return mutated;
        }

        /**
         * Generate a completely random trace (for escaping local minima)
         */
        static List<String> generateCompletelyRandomTrace(String[] symbols) {
                ArrayList<String> trace = new ArrayList<>();
                int randomLength = 5 + r.nextInt(20); // Length between 5 and 24
                for (int i = 0; i < randomLength; i++) {
                trace.add(symbols[r.nextInt(symbols.length)]);
                }
                return trace;
        }

        /**
         * Generate a random trace from an array of symbols.
         * @param symbols the symbols from which a trace should be generated from.
         * @return a random trace that is generated from the given symbols.
         */
        static List<String> generateRandomTrace(String[] symbols) {
                ArrayList<String> trace = new ArrayList<>();
                for (int i = 0; i < traceLength; i++) {
                        trace.add(symbols[r.nextInt(symbols.length)]);
                }
                return trace;
        }
        
        /**
         * Mutates a trace by changing one random position to a new symbol.
         * This is the core "neighbor" generation for Hill Climbing.
         * @param originalTrace The trace to mutate.
         * @param alphabet The possible input symbols.
         * @return A new mutated trace.
         */
        static List<String> mutateTraceEven(List<String> trace, String[] symbols) {
                
                List<String> mutation;
                String type;
                
                int operatorChoice = r.nextInt(3);
                switch (operatorChoice) {
                case 0:
                        // Change symbol
                        mutation = mutateChangeSymbol(trace, symbols);
                        type = "CHANGE";
                        break;
                case 1:
                        // Add symbol
                        mutation = mutateAddSymbol(trace, symbols);
                        type = "ADD";
                        break;
                case 2:
                        // Delete symbol
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
                        // Close: 80% CHANGE, 10% ADD, 10% DELETE
                        double rand = r.nextDouble();
                        if (rand < 0.8) mutation = mutateChangeSymbol(trace, symbols);
                        else if (rand < 0.9) mutation = mutateAddSymbol(trace, symbols);
                        else mutation = mutateDeleteSymbol(trace);
                }
                else if (currentTotalTraceDistance < 10.0) {
                        // Medium: 40% CHANGE, 30% ADD, 30% DELETE
                        double rand = r.nextDouble();
                        if (rand < 0.4) mutation = mutateChangeSymbol(trace, symbols);
                        else if (rand < 0.7) mutation = mutateAddSymbol(trace, symbols);
                        else mutation = mutateDeleteSymbol(trace);
                }
                else {
                        // Far: 20% CHANGE, 40% ADD, 40% DELETE
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
                output("Total errors encountered: " + totalErrors);                
                
                output("============================================");
        }
                


        static List<String> getUnreachedBranchesSorted() {
                List<String> unreachedBranches = new ArrayList<>();
                for (Map.Entry<String, Double> entry : bestBranchDistances.entrySet()) {
                        // A distance of 0.0 means the branch has been covered [cite: 830]
                        if (entry.getValue() != 0.0) {
                        unreachedBranches.add(entry.getKey());
                        }
                }

                // Sort the list based on the values in the bestBranchDistances map
                // This uses the "Hill Climbing" principle of selecting the best neighbor [cite: 841, 852]
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
                                String bestBranch = unreachedBranches.get(0);  // Default to first
                                for (String branch : unreachedBranches) {
                                        double d = bestBranchDistances.get(branch);
                                        if (d < bestDistance) {
                                        bestDistance = d;
                                        bestBranch = branch;
                                        }
                                }
                                return bestBranch;  // Always returns
                        
                        case "mixed":
                                // Mix of close, far, and middle branches
                                int x = r.nextInt(100);
                                int delta = r.nextInt(Math.max(1, unreachedBranches.size() / 3));
                                
                                if (x > 60) {
                                        // 60% chance: pick close branch (index 0 is closest)
                                        return unreachedBranches.get(delta);
                                } else if (x < 30) {
                                        // 30% chance: pick far branch
                                        return unreachedBranches.get(Math.max(0, unreachedBranches.size() - 1 - delta));
                                } else {
                                        // 10% chance: pick middle branch
                                        return unreachedBranches.get(unreachedBranches.size() / 2);
                                }
                                
                                default:
                                        // Random selection
                                        return unreachedBranches.get(r.nextInt(unreachedBranches.size()));
                }
        }


        

        static void run() {
                output("Starting fuzzing lab...");   

                initialize(DistanceTracker.inputSymbols);
                DistanceTracker.runNextFuzzedSequence(currentTrace.toArray(new String[0]));
                
                int searchBudget = 200;
                int totalBudget = 20000;
                Set<String> uniqueErrors = new HashSet<>();

                while(!isFinished && totalBudget > 0){ 
                        try {
                                List<String> unreachedBranches = getUnreachedBranchesSorted();
                                
                                if (unreachedBranches.isEmpty()) {
                                        output("All branches reached! Fuzzing complete.");
                                        isFinished = true;
                                        break;
                                }
                                
                                currentTarget = getNextTarget(unreachedBranches, "random");
                                
                                if (currentTarget == null) {
                                        output("Error: Failed to select target branch");
                                        isFinished = true;
                                        break;
                                }
                                
                                targetReached = false;
                                int iterations = 0;
                                
                                output("\n[Target] Branch: " + currentTarget);

                                while (iterations < searchBudget && !targetReached) {
                                        
                                        while (iterationWithoutImprovement < maxIterationWithoutImprovement && !targetReached) {
                                        currentTrace = fuzz(DistanceTracker.inputSymbols, 1);  
                                        currentTotalTraceDistance = 0.0;
                                        
                                        DistanceTracker.runNextFuzzedSequence(currentTrace.toArray(new String[0]));

                                        totalBudget--;
                                        iterations++;
                                        iterationWithoutImprovement++;
                                        
                                        if (currentTarget != null) {
                                                failedIterationMap.put(currentTarget, iterationWithoutImprovement);
                                        }
                                        }

                                        if (targetReached) {
                                                output("Target branch " + currentTarget + " reached!");
                                                break; 
                                        }

                                        
                                        iterationWithoutImprovement = 0;
                                        currentTotalTraceDistance = 0.0;
                                        currentTrace = generateRandomTrace(DistanceTracker.inputSymbols);
                                }

                        } catch (Exception e) {
                        output("Error during fuzzing: " + e.getMessage());
                        uniqueErrors.add(e.getMessage());
                        e.printStackTrace();
                        }
                }

                output("End fuzzing lab.");                      
                isFinished = true;
                printUniqueBranches();
                }

       

        /**
         * Method that is used for catching the output from standard out.
         * You should write your own logic here.
         * @param out the string that has been outputted in the standard out.
         */
        public static void output(String out){
                System.out.println(out);
        }
}
