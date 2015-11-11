package at.sanzinger.boolector;

import java.util.List;

public class SMTResult {
    private final List<String> lines;
    private final String error;
    private String name;

    public SMTResult(List<String> lines, String error) {
        this(lines, error, null);
    }

    public SMTResult(List<String> lines, String error, String name) {
        super();
        this.lines = lines;
        this.error = error;
        this.name = name;
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

    public void setName(String name) {
        this.name = name;
    }

    public String getName() {
        return name;
    }

    @Override
    public String toString() {
        return String.format("SMTResult[%s]: %s %s", name, status(), getError());
    }
}
