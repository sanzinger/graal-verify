package at.sanzinger.boolector;

import java.io.IOException;
import java.util.Arrays;

public class Boolector {
    private final String btorCmd;

    public Boolector(String cmd) {
        btorCmd = cmd;
    }

    public Boolector() {
        this("boolector");
    }

    public boolean verify() {
        String version = getVersion();
        if (version == null) {
            return false;
        } else {
            return true;
        }
    }

    private static String getBtorVersion(String cmd) {
        try {
            String[] cmdArr = {cmd, "--version"};
            Process p = Runtime.getRuntime().exec(cmdArr);
            try {
                p.waitFor();
            } catch (InterruptedException e) {
                return null;
            }
            String stdout = BoolectorInstance.getPendingLines(p.getInputStream());
            String stderr = BoolectorInstance.getPendingLines(p.getErrorStream());
            if (stderr != null && stderr.length() > 0) {
                throw new RuntimeException("Command " + Arrays.toString(cmdArr) + " gave unexpected output: stderr: " + stderr + " stdout: " + stdout);
            }
            return stdout.trim();
        } catch (IOException e) {
            return null;
        }
    }

    public String getBtorCmd() {
        return btorCmd;
    }

    public BoolectorInstance newInstance() {
        return new BoolectorInstance(this);
    }

    public String getVersion() {
        return getBtorVersion(getBtorCmd());
    }
}
