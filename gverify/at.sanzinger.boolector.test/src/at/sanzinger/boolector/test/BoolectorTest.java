package at.sanzinger.boolector.test;

import static org.junit.Assert.*;

import java.io.File;

import org.junit.BeforeClass;
import org.junit.Test;

import at.sanzinger.boolector.Boolector;

public class BoolectorTest {
    private static String BTOR_HOME;

    @BeforeClass
    public static void setUpClass() {
        BTOR_HOME = System.getenv("BTOR_HOME");
        if (BTOR_HOME == null || BTOR_HOME.length() == 0) {
            fail("BTOR_HOME must be set");
        }
    }

    @Test
    public void boolectorVerifyTest() throws Exception {
        Boolector btor = new Boolector(BTOR_HOME + File.separator + "boolector");
        btor.verify();
    }
}
