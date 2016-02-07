package at.sanzinger.graal.verify.test;

import com.oracle.graal.code.CompilationResult;
import com.oracle.graal.compiler.test.GraalCompilerTest;

public class VerificationTest extends GraalCompilerTest {

    protected CompilationResult compile(String methodName) {
        return super.compile(getResolvedJavaMethod(methodName), null);
    }
}
