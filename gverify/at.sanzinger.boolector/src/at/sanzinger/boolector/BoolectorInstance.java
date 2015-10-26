package at.sanzinger.boolector;

import static java.util.concurrent.TimeUnit.SECONDS;

import java.io.IOException;
import java.io.InputStream;
import java.io.PrintWriter;

import at.sanzinger.boolector.SMT.Check;

public class BoolectorInstance implements AutoCloseable {
    private final Boolector boolector;
    private boolean opened = false;
    private Process p;
    private InputStream is;
    private PrintWriter out;

    public BoolectorInstance(Boolector binary) {
        this.boolector = binary;
    }

    private void ensureOpen() {
        if (opened) {
            return;
        }
        boolector.verify();
        String[] args = {boolector.getBtorBinary().getAbsolutePath(), "-m"};
        try {
            p = Runtime.getRuntime().exec(args);
            is = p.getInputStream();
            out = new PrintWriter(p.getOutputStream());
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public void execute(SMT smt) {
        ensureOpen();
        out.write(smt.getModel());
        for (Check c : smt.getChecks()) {
            out.println("(push 1)");
            out.println(c.getCheck());
            out.println("(pop 1)");
        }
    }

    public void close() throws Exception {
        if (!opened) {
            return;
        }
        out.println();
        out.println("(exit)");
        p.waitFor(1, SECONDS);
        is.close();
        out.close();
        p.destroyForcibly();
    }
}
