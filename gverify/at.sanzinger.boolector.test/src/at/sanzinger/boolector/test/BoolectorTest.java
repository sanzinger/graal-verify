package at.sanzinger.boolector.test;

import static java.lang.System.currentTimeMillis;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.CharBuffer;

import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import at.sanzinger.boolector.Boolector;
import at.sanzinger.boolector.BoolectorInstance;
import at.sanzinger.boolector.SMT;
import at.sanzinger.boolector.SMT.Check;
import at.sanzinger.boolector.SMTResult;

public class BoolectorTest {
    private static String BTOR_HOME;
    private Boolector btor;

    @BeforeClass
    public static void setUpClass() {
        BTOR_HOME = System.getenv("BTOR_HOME");
        if (BTOR_HOME == null || BTOR_HOME.length() == 0) {
            fail("BTOR_HOME must be set");
        }
    }

    @Before
    public void setUp() {
        btor = new Boolector(BTOR_HOME + File.separator + "boolector");
    }

    @Test
    public void boolectorVerifyTest() throws Exception {
        btor.verify();
    }

    @Test
    public void startBtorTest() throws Exception {
        BoolectorInstance i = btor.newInstance();
        i.close();
        assertFalse(i.isRunning());
    }

    @Test
    public void executeBtor() throws Exception {
        SMT s = new SMT(rr("sample1.smt2"));
        s.addCheck(new Check(rr("sample1_q1.smt2")));
        s.addCheck(new Check(rr("sample1_q2.smt2")));
        try (BoolectorInstance i = btor.newInstance()) {
            SMTResult[] r = i.execute(s);
            assertEquals(2, r.length);
            assertEquals("unsat", r[0].status());
            assertEquals("sat", r[1].status());
        }
    }

    @Test
    public void testAutoclose() throws Exception {
        BoolectorInstance escape;
        long start = currentTimeMillis();
        try (BoolectorInstance i = btor.newInstance()) {
            SMT s = new SMT("");
            s.addCheck(new Check(""));
            assertFalse(i.isRunning());
            SMTResult[] r = i.execute(s);
            assertEquals("sat", r[0].status());
            assertTrue(i.isRunning());
            escape = i;
        }
        assertTrue("Must be executed in less than 50 ms", currentTimeMillis() - start < 50);

        assertFalse(escape.isRunning());
    }

    /**
     * Read Resource
     *
     * @param name Resource name relative tho {@link BoolectorTest}
     * @return String representation of the resource file
     * @throws IOException Exception which may occur during resource read
     */
    private static String rr(String name) throws IOException {
        try (InputStreamReader isr = new InputStreamReader(BoolectorTest.class.getResource(name).openStream())) {
            CharBuffer buff = CharBuffer.allocate(1024);
            int read = isr.read(buff);
            buff.position(0);
            return buff.subSequence(0, read).toString();
        }
    }
}
