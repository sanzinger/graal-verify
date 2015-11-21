package at.sanzinger.graal.verify;

import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.CharBuffer;

import org.junit.Assert;
import org.junit.Test;

import at.sanzinger.boolector.Boolector;
import at.sanzinger.boolector.BoolectorInstance;
import at.sanzinger.boolector.SMT;
import at.sanzinger.graal.verify.EquivalenceCheck;
import at.sanzinger.graal.verify.SMTLibGeneratorPhase;

public class EquivalenceCheckTest {
    @Test
    public void testForEquivalence() throws Exception {
        checkEquivalence("model.smt2");
    }

    @Test
    public void testForEquivalence2() throws Exception {
        checkEquivalence("model2.smt2");
    }

    private static void checkEquivalence(String filename) throws IOException {
        String model = rr(filename);
        try (BoolectorInstance bi = getBoolector().newInstance()) {
            SMT smt = new SMT(model);
            smt.addCheck(new EquivalenceCheck());
            bi.execute(smt);
        }
    }

    private static Boolector getBoolector() {
        Boolector btor = SMTLibGeneratorPhase.getBoolector();
        Assert.assertNotNull("No Boolector found", btor);
        return btor;
    }

    /**
     * Read Resource
     *
     * @param name Resource name relative tho {@link EquivalenceCheckTest}
     * @return String representation of the resource file
     * @throws IOException Exception which may occur during resource read
     */
    private static String rr(String name) throws IOException {
        try (InputStreamReader isr = new InputStreamReader(EquivalenceCheckTest.class.getResource(name).openStream())) {
            CharBuffer buff = CharBuffer.allocate(1024);
            int read = isr.read(buff);
            buff.position(0);
            return buff.subSequence(0, read).toString();
        }
    }
}
