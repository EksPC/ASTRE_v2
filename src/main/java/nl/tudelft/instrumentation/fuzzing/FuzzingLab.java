package nl.tudelft.instrumentation.fuzzing;

import java.util.*;

/**
 * You should write your own solution using this class.
 */
public class FuzzingLab {
        static Random r = new Random();
        static List<String> currentTrace;
        static int traceLength = 10;
        static boolean isFinished = false;

        static final double K = 1.0;

        //
        // Stores the best normalized distance observed so far for each branch target.
        // 
        static Map<String, Double> bestBranchDistances = new HashMap<>();

        static void initialize(String[] inputSymbols){
                // Initialise a random trace from the input symbols of the problem.
                currentTrace = generateRandomTrace(inputSymbols);
        }

        /**
         * Write your solution that specifies what should happen when a new branch has been found.
         */
        static void encounteredNewBranch(MyVar condition, boolean value, int line_nr) {
                boolean oppositeValue = !value;
        
                double distanceToTakenBranch = branchDistance(condition, value);
                double distanceToOppositeBranch = branchDistance(condition, oppositeValue);
        
                String takenKey = line_nr + ":" + value;
                String oppositeKey = line_nr + ":" + oppositeValue;
        
                updateBestDistance(takenKey, distanceToTakenBranch);
                updateBestDistance(oppositeKey, distanceToOppositeBranch);
        
                System.out.println("Line " + line_nr);
                System.out.println("Condition: " + condition.toString());
                System.out.println("Taken branch: " + value);
                System.out.println("Normalizing when covering a condition");
                System.out.println("Distance to taken branch: " + distanceToTakenBranch);
                System.out.println("Distance to opposite branch: " + distanceToOppositeBranch);
                System.out.println();
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
                }
        }

        /**
         * Method for fuzzing new inputs for a program.
         * @param inputSymbols the inputSymbols to fuzz from.
         * @return a fuzzed sequence
         */
        static List<String> fuzz(String[] inputSymbols){
                /*
                 * Add here your code for fuzzing a new sequence for the RERS problem.
                 * You can guide your fuzzer to fuzz "smart" input sequences to cover
                 * more branches. Right now we just generate a complete random sequence
                 * using the given input symbols. Please change it to your own code.
                 */

                // Branch distance is implemented above.
                // TODO: Hill climbing is not implemented yet.
                return generateRandomTrace(inputSymbols);
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

        static void run() {
                initialize(DistanceTracker.inputSymbols);
                DistanceTracker.runNextFuzzedSequence(currentTrace.toArray(new String[0]));

                //  // Place here your code to guide your fuzzer with its search.
                // while(!isFinished) {
                //         // Do things!
                //         try {
                //                 System.out.println("Woohoo, looping!");
                //                 Thread.sleep(1000);
                //         } catch (InterruptedException e) {
                //                 e.printStackTrace();
                //         }
                // }
                
                // No hill climbing implemented yet.
                isFinished = true;
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
