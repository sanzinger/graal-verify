package at.sanzinger.boolector.test;

import static java.lang.System.currentTimeMillis;
import static java.lang.System.lineSeparator;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.CharBuffer;

import org.junit.Before;
import org.junit.Test;

import at.sanzinger.boolector.Boolector;
import at.sanzinger.boolector.BoolectorInstance;
import at.sanzinger.boolector.BoolectorInstance.FrameHandle;
import at.sanzinger.boolector.SMTModel;
import at.sanzinger.boolector.SMTModel.Definition;
import at.sanzinger.boolector.SMTResult;

public class BoolectorTest {
    private Boolector btor;

    @Before
    public void setUp() {
        btor = new Boolector();
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
        try (BoolectorInstance i = btor.newInstance()) {
            i.define(rr("sample1.smt2"));
            try (FrameHandle fh = i.push()) {
                i.define(rr("sample1_q1.smt2"));
                SMTResult r = i.checkSat();
                assertEquals("unsat", r.status());
                assertNull(r.getError());
            }
            try (FrameHandle fh = i.push()) {
                i.define(rr("sample1_q2.smt2"));
                SMTResult r = i.checkSat();
                assertEquals("sat", r.status());
                assertNull(r.getError());
            }
        }
    }

    @Test
    public void testAutoclose() throws Exception {
        BoolectorInstance escape;
        long start = currentTimeMillis();
        try (BoolectorInstance i = btor.newInstance()) {
            assertFalse(i.isRunning());
            SMTResult r = i.checkSat();
            assertEquals("sat", r.status());
            assertNull(r.getError());
            assertTrue(i.isRunning());
            escape = i;
        }
        assertTrue("Must be executed in less than 300 ms", currentTimeMillis() - start < 300);

        assertFalse(escape.isRunning());
    }

    @Test
    public void testSinlgelineError() throws Exception {
        try (BoolectorInstance i = btor.newInstance()) {
            try {
                i.define("(set-logic UNKNOWN)");
                i.checkSat();
            } catch (Exception e) {
                assertEquals("boolector: <stdin>:1:12: expected logic at 'UNKNOWN'" + lineSeparator(), e.getMessage());
            }
        }
    }

    @Test
    public void testNestedPush() {
        try (BoolectorInstance i = btor.newInstance()) {
            try (FrameHandle h = i.push()) {
                i.define("(set-logic QF_BV)\n(declare-fun n () Bool)");
                i.define("(assert (= n #b1))\n(assert (= n #b0))");
                SMTResult r = i.checkSat();
                assertEquals("unsat", r.status());
            }
            try (FrameHandle h = i.push()) {
                i.define("(set-logic QF_BV)\n(declare-fun n () Bool)");
                i.define("(assert (= n #b1))");
                SMTResult r = i.checkSat();
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
