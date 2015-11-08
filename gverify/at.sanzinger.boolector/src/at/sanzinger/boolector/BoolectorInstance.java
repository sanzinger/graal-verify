package at.sanzinger.boolector;

import static java.lang.System.lineSeparator;
import static java.util.concurrent.TimeUnit.SECONDS;

import java.io.IOException;
import java.io.InputStream;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

public class BoolectorInstance implements AutoCloseable {
    private final Boolector boolector;
    private boolean opened = false;
    private Process p;
    private InputStream is;
    private InputStream errIs;
    private PrintWriter out;

    public BoolectorInstance(Boolector binary) {
        this.boolector = binary;
    }

    private void ensureOpen() {
        if (opened) {
            return;
        }
        boolector.verify();
        String[] args = {boolector.getBtorBinary().getAbsolutePath(), "-m", "-i", "-smt2"};
        try {
            p = Runtime.getRuntime().exec(args);
            is = p.getInputStream();
            errIs = p.getErrorStream();
            out = new PrintWriter(p.getOutputStream());
            opened = true;
        } catch (IOException e) { // Cleanup partially created resources
            if (p != null) {
                p.destroyForcibly();
            }
            closeSilent(out, is, errIs);
            is = null;
            out = null;
        }
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

    public SMTResult[] execute(SMT smt) {
        ensureOpen();
        out.write(smt.getModel());
        out.flush();
        SMTResult[] results = new SMTResult[smt.getChecks().size()];
        int i = 0;
        for (Function<BoolectorInstance, SMTResult> c : smt.getChecks()) {
            results[i++] = c.apply(this);
        }
        return results;
    }

    public void define(String check) {
        ensureOpen();
        out.println(check);
        out.flush();
    }

    public SMTModel getModel() {
        out.println("(check-sat)\n(get-model)");
        out.flush();
        try {
            List<String> lines = waitForOutputLine(1000, ")", "unsat");
            if (lines.get(0).equals("unsat")) {
                return null;
            } else {
                return new SMTModel(lines.subList(1, lines.size()));
            }
        } catch (InterruptedException e) {
            return null;
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public SMTResult checkSat(String check) {
        define(check);
        out.println("(check-sat)");
        out.flush();
        List<String> lines;
        long waitUntil = System.currentTimeMillis() + 5000;
        try {
            do {
                lines = waitForOutputLine(200, "sat", "unsat");
            } while (lines == null && waitUntil < System.currentTimeMillis() && errIs.available() == 0);
            String error = getPendingLines(errIs);
            SMTResult result = new SMTResult(lines, error);
            return result;
        } catch (InterruptedException e) {
            return null;
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private static String getPendingLines(InputStream is) {
        try {
            StringBuilder err = new StringBuilder();
            while (is.available() > 0) {
                err.append(readLineWithTimeout(is, 1));
            }
            return err.length() > 0 ? err.toString() : null;
        } catch (InterruptedException e) {
            return null;
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public void pop() {
        out.println("(pop 1)");
        out.flush();
    }

    public FrameHandle push() {
        ensureOpen();
        out.println("(push 1)");
        out.flush();
        String error = getPendingLines(errIs);
        if (error != null) {
            throw new RuntimeException(error);
        }
        return new FrameHandle();
    }

    private static String readLineWithTimeout(InputStream is, int timeout) throws IOException, InterruptedException {
        int maxLineLength = 4096;
        long start = System.currentTimeMillis();
        if (!is.markSupported()) {
            throw new IllegalArgumentException("This InputStreamReader does not support marking");
        }
        is.mark(maxLineLength);
        byte[] cbuff = new byte[maxLineLength];
        int offset = 0;
        while (start + timeout > System.currentTimeMillis() && offset < maxLineLength) {
            int avail = Math.min(is.available(), maxLineLength - offset);
            int read = is.read(cbuff, offset, avail);
            String line = new String(cbuff, 0, offset + read);
            int lineend = line.indexOf(System.lineSeparator());
            if (lineend != -1) {
                is.reset();
                is.skip(lineend + 1);
                return line.substring(0, lineend + lineSeparator().length());
            }
            offset += read;
            if (avail == 0) {
                Thread.sleep(1);
            }
        }
        is.reset();
        return null;
    }

    /**
     * Waits one of lines appear on the output stream and returns the matching string
     */
    private List<String> waitForOutputLine(int timeout, String... lines) throws IOException, InterruptedException {
        List<String> result = new ArrayList<>(10);
        long start = System.currentTimeMillis();
        while (start + timeout > System.currentTimeMillis()) {
            String line = readLineWithTimeout(is, 2);
            if (line != null) {
                line = line.trim();
                result.add(line);
                for (String searchedLine : lines) {
                    if (line.equals(searchedLine)) {
                        return result;
                    }
                }
            }
        }
        return null;
    }

    public void close() {
        if (!opened) {
            return;
        }
        out.println();
        out.println("(exit)");
        out.flush();
        try {
            p.waitFor(1, SECONDS);
        } catch (InterruptedException ie) {
            ie.printStackTrace();
        }
        closeSilent(out, is, errIs);
        p.destroyForcibly();
        p = null;
        is = null;
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
