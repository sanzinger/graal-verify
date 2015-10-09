package at.sanzinger.graal.verify.test;

import jdk.internal.jvmci.code.CompilationResult;
import jdk.internal.jvmci.meta.ResolvedJavaMethod;

import com.oracle.graal.compiler.test.GraalCompilerTest;

public class VerificationTest extends GraalCompilerTest {

    protected CompilationResult compile(String methodName) {
        return super.compile(getResolvedJavaMethod(methodName), null);
    }
}
