package at.sanzinger.boolector;

import java.util.List;

public class SMTResult {
    private final List<String> lines;
    private final String error;

    public SMTResult(List<String> lines, String error) {
        super();
        this.lines = lines;
        this.error = error;
    }

    public String status() {
        return lines == null ? null : lines.get(lines.size() - 1);
    }

    public String getError() {
        return error;
    }

    public boolean isSat() {
        return "sat".equals(status());
    }

    public boolean isError() {
        return error != null;
    }

    @Override
    public String toString() {
        return String.format("SMTResult: %s %s", status(), getError());
    }
}
