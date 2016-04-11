package at.sanzinger.boolector;

import static java.util.concurrent.TimeUnit.SECONDS;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

public class BoolectorInstance implements AutoCloseable {
    private final Boolector boolector;
    private boolean opened = false;
    private Process p;
    private BufferedReader ir;
    private BufferedReader errIr;
    private PrintWriter out;
    @SuppressWarnings("unused") private int level = 0;
    private boolean satDone = false;

    public BoolectorInstance(Boolector binary) {
        this.boolector = binary;
    }

    private void ensureOpen() {
        if (opened) {
            if (!p.isAlive()) {
                String stderrLines = readRemainingLines(errIr);
                String stdoutLines = readRemainingLines(ir);
                throw new RuntimeException("Process died, stdout: " + stdoutLines + " stderr: " + stderrLines);
            }
            return;
        }
        String[] args = {boolector.getBtorCmd(), "-m", "-i", "-smt2"};
        try {
            p = Runtime.getRuntime().exec(args);
            // is = new BufferedInputStream(.getInputStream();
            ir = new BufferedReader(new InputStreamReader(p.getInputStream()));
            errIr = new BufferedReader(new InputStreamReader(p.getErrorStream()));
            out = new PrintWriter(p.getOutputStream());
            opened = true;
        } catch (IOException e) { // Cleanup partially created resources
            if (p != null) {
                p.destroyForcibly();
            }
            closeSilent(out, ir, errIr);
            ir = null;
            errIr = null;
            out = null;
        }
    }

    private static String readRemainingLines(BufferedReader r) {
        String line;
        StringBuilder lines = new StringBuilder();
        try {
            while (r.ready() && (line = r.readLine()) != null) {
                lines.append('\n');
                lines.append(line);
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        return lines.substring(Math.min(lines.length(), 1));
    }

    private static void closeSilent(AutoCloseable... closeables) {
        for (AutoCloseable c : closeables) {
            if (c == null) {
                continue;
            }
            try {
                c.close();
            } catch (Exception e) {
                e.printStackTrace();
            }
        }
    }

    public CheckResult[] execute(SMT smt) {
        ensureOpen();
        satDone = false;
        printOut(smt.getModel());
        CheckResult[] results = new CheckResult[smt.getChecks().size()];
        int i = 0;
        for (Function<BoolectorInstance, CheckResult> c : smt.getChecks()) {
            results[i++] = c.apply(this);
        }
        return results;
    }

    public void define(String check) {
        satDone = false;
        ensureOpen();
        printOut(check);
    }

    public SMTModel getModel() {
        if (!satDone) {
            checkSat();
        }
        try {
            List<String> lines = new ArrayList<>(10);
            printOut("(get-model)");
            while (true) {
                String line = ir.readLine();
                if (line == null) {
                    String err = readRemainingLines(errIr);
                    throw new RuntimeException(String.format("Boolector printed error: %s", err));
                }
                lines.add(line);
                if (")".equals(line)) {
                    break;
                }
            }
            return new SMTModel(lines);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public SMTResult checkSat() {
        ensureOpen();
        printOut("(check-sat)");
        satDone = true;
        try {
            String sat = ir.readLine();
            StringBuffer error = null;
            while (errIr.ready()) {
                if (error == null) {
                    error = new StringBuffer();
                }
                error.append(errIr.readLine());
            }
            SMTResult result = new SMTResult(sat, error == null ? null : error.toString());
            return result;
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    static String getPendingLines(InputStream is) {
        return getPendingLines(new BufferedReader(new InputStreamReader(is)));
    }

    static String getPendingLines(BufferedReader ir) {
        try {
            StringBuilder err = new StringBuilder();
            while (ir.ready()) {
                err.append(ir.readLine());
            }
            return err.length() > 0 ? err.toString() : null;
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private void printOut(String line) {
        printIdent(line, ">> ");
        out.println(line);
        out.flush();
    }

    @SuppressWarnings("unused")
    private void printIdent(String line, String prefixString) {
// StringBuilder prefix = new StringBuilder();
// for (int i = 0; i < level; i++) {
// prefix.append(" ");
// }
// prefix.append(prefixString);
// System.out.println(prefix + line.replace(System.lineSeparator(), System.lineSeparator() +
// prefix));
    }

    public void pop() {
        satDone = false;
        level--;
        printOut("(pop 1)");
    }

    public FrameHandle push() {
        satDone = false;
        ensureOpen();
        printOut("(push 1)");
        String error = getPendingLines(errIr);
        if (error != null) {
            throw new RuntimeException(error);
        }
        level++;
        return new FrameHandle();
    }

    public void close() {
        if (!opened) {
            return;
        }
        printOut("\n(exit)");
        try {
            p.waitFor(1, SECONDS);
        } catch (InterruptedException ie) {
            ie.printStackTrace();
        }
        closeSilent(out, ir, errIr);
        p.destroyForcibly();
        p = null;
        ir = null;
        out = null;
        opened = false;
    }

    public boolean isRunning() {
        return p != null && p.isAlive();
    }

    public class FrameHandle implements AutoCloseable {
        private boolean closed = false;

        public void close() {
            if (closed) {
                throw new RuntimeException("Handle is already closed");
            }
            pop();
            closed = true;
        }
    }
}
