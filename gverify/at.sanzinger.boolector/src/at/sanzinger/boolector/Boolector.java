package at.sanzinger.boolector;

import java.io.File;

public class Boolector {
    private final File btorBinary;

    public Boolector(String file) {
        btorBinary = new File(file);
    }

    public void verify() throws IllegalArgumentException {
        String msg = null;
        if (!btorBinary.exists()) {
            msg = "does not exist";
        } else if (!btorBinary.isFile()) {
            msg = "is not a file";
        } else if (!btorBinary.canExecute()) {
            msg = "is not an executable";
        }
        if (msg != null) {
            throw new IllegalArgumentException(String.format("Boolector binary %s.", btorBinary));
        }
    }

    public File getBtorBinary() {
        return btorBinary;
    }
}
