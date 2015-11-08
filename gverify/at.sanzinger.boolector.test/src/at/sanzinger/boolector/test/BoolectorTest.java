package at.sanzinger.boolector.test;

import static java.lang.System.currentTimeMillis;
import static java.lang.System.lineSeparator;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
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
import at.sanzinger.boolector.BoolectorInstance.FrameHandle;
import at.sanzinger.boolector.SMT;
import at.sanzinger.boolector.SMT.Check;
import at.sanzinger.boolector.SMTModel;
import at.sanzinger.boolector.SMTModel.Definition;
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
        s.addCheck(new Check("sample1_q1", rr("sample1_q1.smt2")));
        s.addCheck(new Check("sample1_q1", rr("sample1_q2.smt2")));
        try (BoolectorInstance i = btor.newInstance()) {
            SMTResult[] r = i.execute(s);
            assertEquals(2, r.length);
            assertEquals("unsat", r[0].status());
            assertNull(r[0].getError());
            assertEquals("sat", r[1].status());
            assertNull(r[1].getError());
        }
    }

    @Test
    public void testAutoclose() throws Exception {
        BoolectorInstance escape;
        long start = currentTimeMillis();
        try (BoolectorInstance i = btor.newInstance()) {
            SMT s = new SMT("");
            s.addCheck(new Check("test", ""));
            assertFalse(i.isRunning());
            SMTResult[] r = i.execute(s);
            assertEquals("sat", r[0].status());
            assertNull(r[0].getError());
            assertTrue(i.isRunning());
            escape = i;
        }
        assertTrue("Must be executed in less than 50 ms", currentTimeMillis() - start < 50);

        assertFalse(escape.isRunning());
    }

    @Test
    public void testSinlgelineError() throws Exception {
        try (BoolectorInstance i = btor.newInstance()) {
            SMT s = new SMT("(set-logic UNKNOWN)");
            s.addCheck(new Check("test", ""));
            try {
                i.execute(s);
            } catch (Exception e) {
                assertEquals("boolector: <stdin>:1:12: expected logic at 'UNKNOWN'" + lineSeparator(), e.getMessage());
            }
        }
    }

    @Test
    public void testNestedPush() {
        try (BoolectorInstance i = btor.newInstance()) {
            try (FrameHandle h = i.push()) {
                SMT s = new SMT("(set-logic QF_BV)\n(declare-fun n () Bool)");
                s.addCheck(new Check("satisfyable", "(assert (= n #b1))\n(assert (= n #b0))"));
                SMTResult r = i.execute(s)[0];
                assertEquals("unsat", r.status());
            }
            try (FrameHandle h = i.push()) {
                SMT s = new SMT("(set-logic QF_BV)\n(declare-fun n () Bool)");
                s.addCheck(new Check("satisfyable", "(assert (= n #b1))"));
                SMTResult r = i.execute(s)[0];
                assertEquals("sat", r.status());
            }
        }
    }

    @Test
    public void testModel() {
        try (BoolectorInstance i = btor.newInstance()) {
            i.define("(set-logic QF_BV)\n(declare-fun n1 () Bool)\n(assert (= n1 #b1))");
            SMTModel m = i.getModel();
            Definition[] d = m.getDefinitions();
            assertEquals(1, d.length);
            assertEquals("n1", d[0].getName());
            assertEquals("#b1", d[0].getValue());
        }
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
