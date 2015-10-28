package at.sanzinger.boolector;

import static java.util.concurrent.TimeUnit.SECONDS;

import java.io.IOException;
import java.io.InputStream;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;

import at.sanzinger.boolector.SMT.Check;

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
        String[] args = {boolector.getBtorBinary().getAbsolutePath(), "-m", "-i"};
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
        SMTResult[] results = new SMTResult[smt.getChecks().size()];
        int i = 0;
        try {
            for (Check c : smt.getChecks()) {
                out.println("(push 1)");
                out.println(c.getCheck());
                out.println("(check-sat)");
                out.flush();
                List<String> lines = waitForOutputLine(1000, "sat", "unsat");
                String err = readLineWithTimeout(p.getErrorStream(), 1);
                if (err != null) {
                    System.err.println(err);
                }
                out.println("(pop 1)");
                out.flush();
                if (lines != null) {
                    results[i] = new SMTResult(c, lines);
                }
                i++;
            }
        } catch (IOException | InterruptedException e) {
            e.printStackTrace();
            close();
            return null;
        }
        return results;
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
                is.skip(lineend);
                return line;
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
}
