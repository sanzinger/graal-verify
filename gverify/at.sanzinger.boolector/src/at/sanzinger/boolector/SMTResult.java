package at.sanzinger.boolector;

import java.util.List;

import at.sanzinger.boolector.SMT.Check;

public class SMTResult {
    private final Check check;
    private final List<String> lines;

    public SMTResult(Check check, List<String> lines) {
        super();
        this.check = check;
        this.lines = lines;
    }

    public String status() {
        return lines.get(lines.size() - 1);
    }

    @Override
    public String toString() {
        return String.format("SMTResult: %s: %s", check.toString(), status());
    }
}
