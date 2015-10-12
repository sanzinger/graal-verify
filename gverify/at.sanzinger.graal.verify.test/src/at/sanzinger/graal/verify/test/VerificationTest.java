package at.sanzinger.graal.verify.test;

import com.oracle.graal.compiler.test.GraalCompilerTest;

public class VerificationTest extends GraalCompilerTest {

    protected jdk.vm.ci.code.CompilationResult compile(String methodName) {
        return super.compile(getResolvedJavaMethod(methodName), null);
    }
}
