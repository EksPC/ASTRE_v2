import java.util.HashSet;
import java.util.Set;

public class Errors {

    static Set<Integer> triggeredErrors = new HashSet<>();

    public static void __VERIFIER_error(int i) {
        triggeredErrors.add(i);
        throw new IllegalStateException( "error_" + i + " - triggered errors: " + triggeredErrors.size() );
    }
}