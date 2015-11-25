package at.sanzinger.boolector;

import static java.util.Collections.unmodifiableList;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

public class SMT {
    private final String model;
    private final List<Function<BoolectorInstance, CheckResult>> checks = new ArrayList<>();

    public SMT(String model) {
        super();
        this.model = model;
    }

    public String getModel() {
        return model;
    }

    public void addCheck(Function<BoolectorInstance, CheckResult> c) {
        checks.add(c);
    }

    public List<Function<BoolectorInstance, CheckResult>> getChecks() {
        return unmodifiableList(checks);
    }
}
