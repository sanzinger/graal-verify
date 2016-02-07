package at.sanzinger.graal.verify;

import com.oracle.graal.compiler.phases.BasicCompilerConfiguration;
import com.oracle.graal.hotspot.DefaultHotSpotGraalCompilerFactory;
import com.oracle.graal.phases.PhaseSuite;
import com.oracle.graal.phases.tiers.CompilerConfiguration;
import com.oracle.graal.phases.tiers.LowTierContext;
import com.oracle.graal.serviceprovider.ServiceProvider;

import jdk.vm.ci.runtime.JVMCICompilerFactory;

@ServiceProvider(JVMCICompilerFactory.class)
public class VerifyingCompilerConfiguration extends DefaultHotSpotGraalCompilerFactory {
    @Override
    public String getCompilerName() {
        return "graal-verify";
    }

    @Override
    protected CompilerConfiguration createCompilerConfiguration() {
        return new VerificationCompilerConfiguration();
    }

    public static class VerificationCompilerConfiguration extends BasicCompilerConfiguration {
        @Override
        public PhaseSuite<LowTierContext> createLowTier() {
            PhaseSuite<LowTierContext> lowTier = super.createLowTier();
            lowTier.appendPhase(new SMTLibGeneratorPhase());
            return lowTier;
        }
    }
}
