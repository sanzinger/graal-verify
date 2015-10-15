package at.sanzinger.graal.verify.test;

import at.sanzinger.graal.verify.SMTLibGeneratorPhase;

import com.oracle.graal.compiler.test.GraalCompilerTest;
import com.oracle.graal.phases.PhaseSuite;
import com.oracle.graal.phases.tiers.LowTierContext;
import com.oracle.graal.phases.tiers.Suites;

public class VerificationTest extends GraalCompilerTest {

    protected jdk.vm.ci.code.CompilationResult compile(String methodName) {
        return super.compile(getResolvedJavaMethod(methodName), null);
    }

    @Override
    protected Suites createSuites() {
        Suites s = super.createSuites();
        PhaseSuite<LowTierContext> lt = s.getLowTier();
        lt.appendPhase(new SMTLibGeneratorPhase());
        return s;
    }
}
