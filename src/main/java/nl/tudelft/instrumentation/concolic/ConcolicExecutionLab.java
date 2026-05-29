package nl.tudelft.instrumentation.concolic;

import java.lang.reflect.Array;
import java.util.*;
import java.util.stream.Collectors;

import com.microsoft.z3.*;
class ErrorTracker {
    int errorsNumber = 0;
    Set<String> errorsList = new HashSet<>();
}


class ExpressionsTracker{
    // Keep track of the amount of expressions per operator type that I meet in the integer expression
    int unaryIntExpr = 0;
    int binaryIntExpr = 0;
    int unaryBoolExpr = 0;
    int binaryBoolExpr = 0;
    int stringExpr = 0;
    
    HashMap<String, Integer> map = new HashMap<>(); 

}
/**
 * You should write your solution using this class.
 * 
 * Z3 API: https://z3prover.github.io/api/html/classcom_1_1microsoft_1_1z3_1_1_context.html
 */
public class ConcolicExecutionLab {

    static Random r = new Random();
    static Boolean isFinished = false;
    static List<String> currentTrace;
    static int traceLength = 10;
    static ErrorTracker tracker = new ErrorTracker();


    static void initialize(String[] inputSymbols){
        // Initialise a random trace from the input symbols of the problem.
        currentTrace = generateRandomTrace(inputSymbols);
    }

    /**
     * Create var, assign value and add to path constraint.
     * @param name
     * @param value
     * @param s
     * @return
     */
    static MyVar createVar(String name, Expr value, Sort s){
        Context c = PathTracker.ctx;
        /**
         * Create var, assign value and add to path constraint.
         * We show how to do it for creating new symbols, please
         * add similar steps to the functions below in order to
         * obtain a path constraint.
        */
        
        // This causes the format like m_0, unique identifier for the static assignment (see slide 48)
        Expr z3var = c.mkConst(c.mkSymbol(name + "_" + PathTracker.z3counter++), s);

        // Create a mathematical constraint as an expression that assigns the value (input) to the newly
        //  created variable. Add it to the pathtracker.
        PathTracker.addToModel(c.mkEq(z3var, value));

        return new MyVar(z3var, name);
    }

    static MyVar createInput(String name, Expr value, Sort s){

        // Create an input var, these should be free variables!
        Context c = PathTracker.ctx;

        
        Expr z3var = c.mkConst(c.mkSymbol(name + "_" + PathTracker.z3counter++), s); // change this line to the correct code for creating a z3var.
        System.out.println("z3var string created: " + z3var.toString());
        // The following code is to add an additional constraint on the input variable.
        // The input variable must have a value that is equal to one of the input symbols.
        BoolExpr constraint = c.mkFalse(); //Since we need to continue with OR, we start with the neutral FALSE  

        for (String input: PathTracker.inputSymbols) {
            constraint = c.mkOr(c.mkEq(z3var, c.mkString(input)), constraint);
        }

        PathTracker.addToModel(constraint);
        MyVar inputVar = new MyVar(z3var, name);

        // We add the input variable to the list of inputs in the PathTracker, 
        //  this is useful for keeping track of the current inputs for the solver.
        PathTracker.inputs.add(inputVar);
        return inputVar;
    }

    static MyVar createBoolExpr(BoolExpr var, String operator){
        // Handle the following unary operators: !
        
        return new MyVar(PathTracker.ctx.mkNot(var));
    }

    static MyVar createBoolExpr(BoolExpr left_var, BoolExpr right_var, String operator){
        // Handle the following binary operators: &, &&, |, ||
        if(operator.equals("&") || operator.equals("&&")){
            return new MyVar(PathTracker.ctx.mkAnd(left_var, right_var));
        } else if (operator.equals("|") || operator.equals("||")) {
            return new MyVar(PathTracker.ctx.mkOr(left_var, right_var));
        }
        
        return new MyVar(PathTracker.ctx.mkFalse());
    }

    static MyVar createIntExpr(IntExpr var, String operator){
        // Handle the following unary operators for numerical operations: +, -
        

        if(operator.equals("+")){
            return new MyVar(var);
        } else if (operator.equals("-")) {
            return new MyVar(PathTracker.ctx.mkUnaryMinus(var));
        }
        return new MyVar(PathTracker.ctx.mkFalse());
    }

    static MyVar createIntExpr(IntExpr left_var, IntExpr right_var, String operator){
        // Handle the following binary operators for numerical operations: +, -, /, *, %, ^, ==, <=, <, >= and >
        if (operator.equals("+")) {
            return new MyVar(PathTracker.ctx.mkAdd(left_var, right_var));
        } else if (operator.equals("-")) {
            return new MyVar(PathTracker.ctx.mkSub(left_var, right_var));
        } else if (operator.equals("*")) {
            return new MyVar(PathTracker.ctx.mkMul(left_var, right_var));
        } else if (operator.equals("/")) {
            return new MyVar(PathTracker.ctx.mkDiv(left_var, right_var));
        } else if (operator.equals("%")) {
            return new MyVar(PathTracker.ctx.mkMod(left_var, right_var));
        } else if (operator.equals("^")) {
            return new MyVar(PathTracker.ctx.mkPower(left_var, right_var));
        } else if (operator.equals("==")) {
            return new MyVar(PathTracker.ctx.mkEq(left_var, right_var));
        } else if (operator.equals("<=")) {
            return new MyVar(PathTracker.ctx.mkLe(left_var, right_var));
        } else if (operator.equals("<")) {
            return new MyVar(PathTracker.ctx.mkLt(left_var, right_var));
        } else if (operator.equals(">=")) {
            return new MyVar(PathTracker.ctx.mkGe(left_var, right_var));
        } else if (operator.equals(">")) {
            return new MyVar(PathTracker.ctx.mkGt(left_var, right_var));
        }

        return new MyVar(PathTracker.ctx.mkFalse());
    }

    static MyVar createStringExpr(SeqExpr left_var, SeqExpr right_var, String operator){
        
        // We only support String.equals
        if(operator.equals("==")){
            return new MyVar(PathTracker.ctx.mkEq(left_var, right_var));
        }
        
        return new MyVar(PathTracker.ctx.mkFalse());

    }

    static void assign(MyVar var, String name, Expr value, Sort s){
        // All variable assignments, use single static assignment
        // Create a new version of the already present variable.
        Context c = PathTracker.ctx;
        Expr new_z3var = c.mkConst(c.mkSymbol(name + "_" + PathTracker.z3counter++), s);
        PathTracker.addToModel(c.mkEq(new_z3var, value));
        var.z3var = new_z3var; // Update the z3var of the MyVar to the new version.

    }

    static void encounteredNewBranch(MyVar condition, boolean value, int line_nr){
        // We need to extract the new branch as a boolean expression
        BoolExpr new_branch;
        if(value){
            new_branch = (BoolExpr) condition.z3var;
        } else {
            new_branch = PathTracker.ctx.mkNot((BoolExpr) condition.z3var);
        }
        // Call the solver
        PathTracker.solve(new_branch, false);
        
    }

    static void newSatisfiableInput(LinkedList<String> new_inputs) {
        
        List<String> trimmed_new_inputs = new_inputs.stream()
            .map(s -> s.replaceAll("^\"|\"$", ""))
            .collect(Collectors.toList());
        
        currentTrace = new ArrayList<>(trimmed_new_inputs);
        System.out.println("New satisfiable input found! - "+ currentTrace.size());

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
         * more branches using concolic execution. Right now we just generate
         * a complete random sequence using the given input symbols. Please
         * change it to your own code.
         */
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

    static List<String> generateTrace(){
        // Generate a trace using the current path constraint in the PathTracker.
        // You can use the solver to generate new inputs that satisfy the path constraint, and then generate a new trace using these inputs.
        // For now, we just return the current trace, but you should change it to your own code.
        return currentTrace;
    }

    static void run() {
        initialize(PathTracker.inputSymbols);
        PathTracker.runNextFuzzedSequence(currentTrace.toArray(new String[0]));
        // Place here your code to guide your fuzzer with its search using Concolic Execution.
        
        printErrorReport();

        // while(!isFinished) {
        //     // Do things!
        //     try {
                
        //         System.out.println("Woohoo, looping!");
        //         Thread.sleep(1000);
        //     } catch (InterruptedException e) {
        //         e.printStackTrace();
        //     }
        // }
    }


    public static void printErrorReport(){

        System.out.println("========== ERROR REPORT ==========");
        if (tracker.errorsList.isEmpty()) {
            System.out.println("No errors found.");
        } else {
            int index = 1;
            for (String error : tracker.errorsList) {
                System.out.println("[" + index + "] " + error);
                index++;
            }
        }
        System.out.println("==================================");
    }

    public static void output(String out){
        if(out.contains("error_")){
            String errorCode = out.substring(out.lastIndexOf("_") + 1).trim();
            tracker.errorsList.add(errorCode);
        }
        System.out.println(out);
    }

}