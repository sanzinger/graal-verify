package at.sanzinger.boolector;

import static java.lang.System.lineSeparator;
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
    private InputStream is;
    private InputStream errIs;
    private PrintWriter out;

    public BoolectorInstance(Boolector binary) {
        this.boolector = binary;
    }

    private void ensureOpen() {
        if (opened) {
            if (!p.isAlive()) {
                String stderrLines = readRemainingLines(errIs);
                String stdoutLines = readRemainingLines(is);
                throw new RuntimeException("Process died, stdout: " + stdoutLines + " stderr: " + stderrLines);
            }
            return;
        }
        String[] args = {boolector.getBtorCmd(), "-m", "-i", "-smt2"};
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

    private static String readRemainingLines(InputStream is) {
        BufferedReader r = new BufferedReader(new InputStreamReader(is));
        String line;
        StringBuilder lines = new StringBuilder();
        try {
            while ((line = r.readLine()) != null) {
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

    public SMTResult[] execute(SMT smt) {
        ensureOpen();
        printOut(smt.getModel());
        SMTResult[] results = new SMTResult[smt.getChecks().size()];
        int i = 0;
        for (Function<BoolectorInstance, SMTResult> c : smt.getChecks()) {
            results[i++] = c.apply(this);
        }
        return results;
    }

    public void define(String check) {
        ensureOpen();
        printOut(check);
    }

    public SMTModel getModel() {
        printOut("(check-sat)\n(get-model)");
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
        printOut("(check-sat)");
        List<String> lines;
        long waitUntil = System.currentTimeMillis() + 5000;
        try {
            do {
                lines = waitForOutputLine(200, "sat", "unsat");
            } while (lines == null && waitUntil > System.currentTimeMillis() && errIs.available() == 0);
            String error = getPendingLines(errIs);
            SMTResult result = new SMTResult(lines, error);
            return result;
        } catch (InterruptedException e) {
            return null;
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    static String getPendingLines(InputStream is) {
        try {
            StringBuilder err = new StringBuilder();
            while (is.available() > 0) {
                err.append(readLineWithTimeout(is, 2));
            }
            return err.length() > 0 ? err.toString() : null;
        } catch (InterruptedException e) {
            return null;
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private void printOut(String line) {
        System.out.println(line);
        out.println(line);
        out.flush();
    }

    public void pop() {
        printOut("(pop 1)");
    }

    public FrameHandle push() {
        ensureOpen();
        printOut("(push 1)");
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
        printOut("\n(exit)");
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
