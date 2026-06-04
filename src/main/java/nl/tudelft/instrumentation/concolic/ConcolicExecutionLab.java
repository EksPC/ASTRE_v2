package nl.tudelft.instrumentation.concolic;

import java.util.*;
import java.util.stream.Collectors;

import com.microsoft.z3.*;

class ErrorTracker {
    int errorsNumber = 0;
    Set<String> errorsList = new HashSet<>();
}


class ExpressionsTracker{
    int unaryIntExpr = 0;
    int binaryIntExpr = 0;
    int unaryBoolExpr = 0;
    int binaryBoolExpr = 0;
    int stringExpr = 0;
    HashMap<String, Integer> map = new HashMap<>();
}


/**
 * Lab 2, Task 1, subtask 2.
 *
 * This implementation uses concolic execution to guide fuzzing.
 *
 * Strategy:
 * 1. Execute a concrete trace.
 * 2. Whenever an instrumented branch is reached, construct the symbolic branch constraint.
 * 3. Ask Z3 whether the opposite branch is satisfiable under the current path constraint.
 * 4. If SAT, store the solver trace and queue it for execution.
 * 5. If UNSAT, store the branch target so it is not solved repeatedly.
 * 6. Prefer solver traces in fuzzing, but use mutation or random restart when the queue is empty.
 */
public class ConcolicExecutionLab {

    static final int MAX_TRACE_LENGTH = 100;

    static Random r = new Random();
    static Boolean isFinished = false;
    static List<String> currentTrace;
    static int traceLength = 10;
    static ErrorTracker tracker = new ErrorTracker();

    // Five minute experiment budget, matching the previous assignment setup.
    static final long RUN_TIME_MS = 5L * 60L * 1000L;

    // Queue of traces returned by the SMT solver.
    static final Queue<List<String>> solverTraceQueue = new ArrayDeque<>();

    // Avoid executing the exact same solver trace repeatedly.
    static final Set<String> queuedTraceKeys = new HashSet<>();

    // Branch bookkeeping.
    static final Set<String> coveredBranches = new HashSet<>();
    static final Set<String> satisfiableBranches = new HashSet<>();
    static final Set<String> unsatisfiableBranches = new HashSet<>();

    // Branch target to trace mappings.
    static final Map<String, List<String>> satisfiableBranchToTrace = new LinkedHashMap<>();
    static final Map<String, List<String>> unsatisfiableBranchToTrace = new LinkedHashMap<>();

    // These fields are used to classify the result of the last solver call.
    static boolean lastSolveWasSatisfiable = false;
    static String pendingTargetBranchKey = null;
    static List<String> pendingCurrentTrace = null;

    // Convergence graph data.
    static long startTimeMs = 0L;
    static final List<String> convergenceCsv = new ArrayList<>();

    static void initialize(String[] inputSymbols){
        isFinished = false;
        currentTrace = generateRandomTrace(inputSymbols);
        
        System.out.println("VALID INPUT SYMBOLS: " + Arrays.toString(PathTracker.inputSymbols));
        
        solverTraceQueue.clear();
        queuedTraceKeys.clear();
        

        coveredBranches.clear();
        satisfiableBranches.clear();
        unsatisfiableBranches.clear();

        satisfiableBranchToTrace.clear();
        unsatisfiableBranchToTrace.clear();

        tracker.errorsList.clear();

        convergenceCsv.clear();
        convergenceCsv.add("time_ms,unique_error_count,error_code");

        startTimeMs = System.currentTimeMillis();
    }

    /**
     * Create a symbolic variable, assign it a value, and add the assignment
     * to the path constraint.
     */
    static MyVar createVar(String name, Expr value, Sort s){
        Context c = PathTracker.ctx;

        Expr z3var = c.mkConst(
            c.mkSymbol(name + "_" + PathTracker.z3counter++),
            s
        );

        PathTracker.addToModel(c.mkEq(z3var, value));

        return new MyVar(z3var, name);
    }

    /**
     * Create a symbolic input variable.
     *
     * Input variables remain free, except that we constrain them to one of the
     * valid input symbols of the currently running RERS problem.
     */
    static MyVar createInput(String name, Expr value, Sort s){
        Context c = PathTracker.ctx;

        Expr z3var = c.mkConst(
            c.mkSymbol(name + "_" + PathTracker.z3counter++),
            s
        );

        BoolExpr validInputConstraint = c.mkFalse();

        for (String input: PathTracker.inputSymbols) {
            validInputConstraint = c.mkOr(
                c.mkEq(z3var, c.mkString(input)),
                validInputConstraint
            );
        }

        PathTracker.addToModel(validInputConstraint);

        MyVar inputVar = new MyVar(z3var, name);

        // Required so PathTracker.solve can reconstruct the input trace.
        PathTracker.inputs.add(inputVar);

        return inputVar;
    }

    static MyVar createBoolExpr(BoolExpr var, String operator){
        Context c = PathTracker.ctx;

        if (operator.equals("!")) {
            return new MyVar(c.mkNot(var));
        }

        throw new RuntimeException("Unsupported unary boolean operator: " + operator);
    }

    static MyVar createBoolExpr(BoolExpr left_var, BoolExpr right_var, String operator){
        Context c = PathTracker.ctx;

        if(operator.equals("&") || operator.equals("&&")){
            return new MyVar(c.mkAnd(left_var, right_var));
        }

        if (operator.equals("|") || operator.equals("||")) {
            return new MyVar(c.mkOr(left_var, right_var));
        }

        if (operator.equals("==")) {
            return new MyVar(c.mkEq(left_var, right_var));
        }

        if (operator.equals("!=")) {
            return new MyVar(c.mkNot(c.mkEq(left_var, right_var)));
        }

        throw new RuntimeException("Unsupported binary boolean operator: " + operator);
    }

    static MyVar createIntExpr(IntExpr var, String operator){
        Context c = PathTracker.ctx;

        if(operator.equals("+")){
            return new MyVar(var);
        }

        if (operator.equals("-")) {
            return new MyVar(c.mkUnaryMinus(var));
        }

        throw new RuntimeException("Unsupported unary integer operator: " + operator);
    }

    static MyVar createIntExpr(IntExpr left_var, IntExpr right_var, String operator){
        Context c = PathTracker.ctx;

        if (operator.equals("+")) {
            return new MyVar(c.mkAdd(left_var, right_var));
        }

        if (operator.equals("-")) {
            return new MyVar(c.mkSub(left_var, right_var));
        }

        if (operator.equals("*")) {
            return new MyVar(c.mkMul(left_var, right_var));
        }

        if (operator.equals("/")) {
            return new MyVar(c.mkDiv(left_var, right_var));
        }

        if (operator.equals("%")) {
            return new MyVar(c.mkMod(left_var, right_var));
        }

        if (operator.equals("^")) {
            return new MyVar(c.mkPower(left_var, right_var));
        }

        if (operator.equals("==")) {
            return new MyVar(c.mkEq(left_var, right_var));
        }

        if (operator.equals("!=")) {
            return new MyVar(c.mkNot(c.mkEq(left_var, right_var)));
        }

        if (operator.equals("<=")) {
            return new MyVar(c.mkLe(left_var, right_var));
        }

        if (operator.equals("<")) {
            return new MyVar(c.mkLt(left_var, right_var));
        }

        if (operator.equals(">=")) {
            return new MyVar(c.mkGe(left_var, right_var));
        }

        if (operator.equals(">")) {
            return new MyVar(c.mkGt(left_var, right_var));
        }

        throw new RuntimeException("Unsupported binary integer operator: " + operator);
    }

    static MyVar createStringExpr(SeqExpr left_var, SeqExpr right_var, String operator){
        Context c = PathTracker.ctx;

        if(operator.equals("==")){
            return new MyVar(c.mkEq(left_var, right_var));
        }

        if(operator.equals("!=")){
            return new MyVar(c.mkNot(c.mkEq(left_var, right_var)));
        }

        throw new RuntimeException("Unsupported string operator: " + operator);
    }

    /**
     * Single static assignment.
     *
     * Every assignment creates a fresh symbolic variable version.
     */
    static void assign(MyVar var, String name, Expr value, Sort s){
        Context c = PathTracker.ctx;

        Expr new_z3var = c.mkConst(
            c.mkSymbol(name + "_" + PathTracker.z3counter++),
            s
        );

        PathTracker.addToModel(c.mkEq(new_z3var, value));

        var.z3var = new_z3var;
    }

    /**
     * Called whenever the instrumented program reaches an if statement.
     *
     * The important point is that we solve the opposite branch first, then add
     * the actually taken branch to z3branches. If we add the taken branch first,
     * the solver may receive contradictory constraints when trying to flip it.
     */
static void encounteredNewBranch(MyVar condition, boolean value, int line_nr){
    Context c = PathTracker.ctx;

    BoolExpr conditionExpr = (BoolExpr) condition.z3var;

    BoolExpr oppositeBranch = c.mkEq(
        conditionExpr,
        value ? c.mkFalse() : c.mkTrue()
    );

    String takenKey = branchKey(line_nr, value);
    String targetKey = branchKey(line_nr, !value);

    coveredBranches.add(takenKey);

    boolean targetAlreadyKnown =
        coveredBranches.contains(targetKey)
        || satisfiableBranches.contains(targetKey)
        || unsatisfiableBranches.contains(targetKey);

    if (!targetAlreadyKnown) {
        pendingTargetBranchKey = targetKey;
        pendingCurrentTrace = copyTrace(currentTrace);
        lastSolveWasSatisfiable = false;

        PathTracker.solve(oppositeBranch, false);

        if (lastSolveWasSatisfiable) {
            satisfiableBranches.add(targetKey);
        } else {
            unsatisfiableBranches.add(targetKey);
            unsatisfiableBranchToTrace.put(
                targetKey,
                copyTrace(pendingCurrentTrace)
            );
        }

        pendingTargetBranchKey = null;
        pendingCurrentTrace = null;
    }
}

    /**
     * Called by PathTracker.solve when Z3 finds a satisfiable input trace.
     */
    static void newSatisfiableInput(LinkedList<String> new_inputs) {
        lastSolveWasSatisfiable = true;

        List<String> solverTrace = sanitizeSolverTrace(new_inputs);

        // The solver trace reaches the target branch. A short random suffix helps
        // continue exploration after that branch.
        addExplorationSuffix(solverTrace, PathTracker.inputSymbols);

        addCandidateTrace(solverTrace);

        if (pendingTargetBranchKey != null) {
            satisfiableBranchToTrace.put(
                pendingTargetBranchKey,
                copyTrace(solverTrace)
            );
        }

        System.out.println(
            "SAT branch " + pendingTargetBranchKey
            + " -> queued trace of length "
            + solverTrace.size()
        );
    }

    /**
     * Pick the next input trace.
     *
     * Solver traces have priority. If the solver queue is empty, use mutation
     * or random restart to discover fresh paths and create new path constraints.
     */
    static List<String> fuzz(String[] inputSymbols){
        if (!solverTraceQueue.isEmpty()) {
            currentTrace = copyTrace(solverTraceQueue.poll());
            return currentTrace;
        }

        if (currentTrace == null || r.nextDouble() < 0.35) {
            currentTrace = generateRandomTrace(inputSymbols);
        } else {
            currentTrace = mutateTrace(currentTrace, inputSymbols);
        }

        return currentTrace;
    }

    static List<String> generateRandomTrace(String[] symbols) {
        ArrayList<String> trace = new ArrayList<>();

        int length = 1 + r.nextInt(Math.max(1, traceLength));

        for (int i = 0; i < length; i++) {
            trace.add(symbols[r.nextInt(symbols.length)]);
        }

        return trace;
    }

    static List<String> generateTrace(){
        return fuzz(PathTracker.inputSymbols);
    }

    static void run() {
        initialize(PathTracker.inputSymbols);

        while(!isFinished) {
            try {
                List<String> nextTrace = generateTrace();

                PathTracker.runNextFuzzedSequence(
                    nextTrace.toArray(new String[0])
                );

                if (System.currentTimeMillis() - startTimeMs >= RUN_TIME_MS) {
                    isFinished = true;
                }
            } catch (Throwable t) {
                System.err.println(
                    "Trace failed: " + currentTrace + " -> " + t.getMessage()
                );
            }
        }

        printErrorReport();
        printBranchReport();
        printConvergenceCsv();
    }

    static String branchKey(int line, boolean branchValue) {
        return line + ":" + (branchValue ? "T" : "F");
    }

    static List<String> sanitizeSolverTrace(LinkedList<String> rawInputs) {
        ArrayList<String> cleaned = new ArrayList<>();
        
        Set<String> validInputs = new HashSet<>(
            Arrays.asList(PathTracker.inputSymbols)
        );
    
        for (String raw : rawInputs) {
            if (raw == null) {
                continue;
            }
        
            String symbol = raw
                .replace("\"", "")
                .replace("[", "")
                .replace("]", "")
                .replace(",", "")
                .trim();
        
            if (validInputs.contains(symbol)) {
                cleaned.add(symbol);
            }
        
            if (cleaned.size() >= MAX_TRACE_LENGTH) {
                break;
            }
        }
    
        if (cleaned.isEmpty()) {
            cleaned.add(
                PathTracker.inputSymbols[
                    r.nextInt(PathTracker.inputSymbols.length)
                ]
            );
        }
    
        return cleaned;
    }

    static void addExplorationSuffix(List<String> trace, String[] inputSymbols) {
        int suffixLength = r.nextInt(3);
    
        for (int i = 0; i < suffixLength; i++) {
            if (trace.size() >= MAX_TRACE_LENGTH) {
                return;
            }
        
            trace.add(inputSymbols[r.nextInt(inputSymbols.length)]);
        }
    }

    static void addCandidateTrace(List<String> trace) {
        List<String> copy = copyTrace(trace);
        String key = traceKey(copy);

        if (queuedTraceKeys.add(key)) {
            solverTraceQueue.offer(copy);
        }
    }

    static List<String> mutateTrace(List<String> trace, String[] inputSymbols) {
        ArrayList<String> mutated = new ArrayList<>(trace);

        if (mutated.isEmpty()) {
            mutated.add(inputSymbols[r.nextInt(inputSymbols.length)]);
            return mutated;
        }

        int operation = r.nextInt(3);

        if (operation == 0) {
            int index = r.nextInt(mutated.size());
            mutated.set(index, inputSymbols[r.nextInt(inputSymbols.length)]);
        } else if (operation == 1 && mutated.size() < 3 * traceLength) {
            int index = r.nextInt(mutated.size() + 1);
            mutated.add(index, inputSymbols[r.nextInt(inputSymbols.length)]);
        } else if (mutated.size() > 1) {
            int index = r.nextInt(mutated.size());
            mutated.remove(index);
        }

        return mutated;
    }

    static String traceKey(List<String> trace) {
        return String.join(",", trace);
    }

    static List<String> copyTrace(List<String> trace) {
        if (trace == null) {
            return new ArrayList<>();
        }

        return new ArrayList<>(trace);
    }

    public static void printErrorReport(){
        System.out.println("========== ERROR REPORT ==========");
    
        if (tracker.errorsList.isEmpty()) {
            System.out.println("No errors found.");
        } else {
            ArrayList<String> sortedErrors = new ArrayList<>(tracker.errorsList);
        
            sortedErrors.sort((a, b) -> {
                try {
                    return Integer.compare(Integer.parseInt(a), Integer.parseInt(b));
                } catch (NumberFormatException e) {
                    return a.compareTo(b);
                }
            });
        
            for (String error : sortedErrors) {
                System.out.println("error_" + error);
            }
        }
    
        System.out.println("Total unique errors: " + tracker.errorsList.size());
        System.out.println("==================================");
    }

    public static void printBranchReport(){
        System.out.println("========== CONCOLIC BRANCH REPORT ==========");
        System.out.println("Covered branches: " + coveredBranches.size());
        System.out.println("SAT branch targets: " + satisfiableBranches.size());
        System.out.println("UNSAT branch targets: " + unsatisfiableBranches.size());
        System.out.println("Queued solver traces not yet executed: " + solverTraceQueue.size());
        System.out.println("===========================================");
    }

    public static void printConvergenceCsv(){
        System.out.println("========== CONVERGENCE CSV ==========");

        for (String row : convergenceCsv) {
            System.out.println(row);
        }

        System.out.println("=====================================");
    }

    public static void output(String out){
        if(out.contains("error_")){
            java.util.regex.Matcher matcher =
                java.util.regex.Pattern.compile("error_(\\d+)").matcher(out);

            if (matcher.find()) {
                String errorCode = matcher.group(1);

                boolean isNew = tracker.errorsList.add(errorCode);

                if (isNew) {
                    long elapsed = System.currentTimeMillis() - startTimeMs;

                    convergenceCsv.add(
                        elapsed + "," + tracker.errorsList.size() + "," + errorCode
                    );

                    System.out.println(
                        "CONVERGENCE,"
                        + elapsed + ","
                        + tracker.errorsList.size()
                        + ",error_"
                        + errorCode
                    );
                }
            }
        }

        System.out.println(out);
    }
}