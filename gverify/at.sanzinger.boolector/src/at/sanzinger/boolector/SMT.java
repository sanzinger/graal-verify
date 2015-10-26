package at.sanzinger.boolector;

import static java.util.Collections.unmodifiableList;

import java.util.ArrayList;
import java.util.List;

public class SMT {
    private final String model;
    private final List<Check> checks = new ArrayList<>();

    public SMT(String model) {
        super();
        this.model = model;
    }

    public String getModel() {
        return model;
    }

    public void addCheck(Check c) {
        checks.add(c);
    }

    public List<Check> getChecks() {
        return unmodifiableList(checks);
    }

    public static class Check {
        private final String check;

        public Check(String check) {
            super();
            this.check = check;
        }

        public String getCheck() {
            return check;
        }
    }
}
