package at.sanzinger.boolector;

import java.util.List;

import at.sanzinger.boolector.SMT.Check;

public class SMTResult {
    private final Check check;
    private final List<String> lines;
    private final String error;

    public SMTResult(Check check, List<String> lines, String error) {
        super();
        this.check = check;
        this.lines = lines;
        this.error = error;
    }

    public String status() {
        return lines.get(lines.size() - 1);
    }

    public String getError() {
        return error;
    }

    @Override
    public String toString() {
        return String.format("SMTResult: %s: %s", check.toString(), status());
    }
}
