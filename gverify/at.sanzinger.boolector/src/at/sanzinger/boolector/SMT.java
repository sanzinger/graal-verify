package at.sanzinger.boolector;

import static java.util.Collections.unmodifiableList;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

import at.sanzinger.boolector.BoolectorInstance.FrameHandle;

public class SMT {
    private final String model;
    private final List<Function<BoolectorInstance, SMTResult>> checks = new ArrayList<>();

    public SMT(String model) {
        super();
        this.model = model;
    }

    public String getModel() {
        return model;
    }

    public void addCheck(Function<BoolectorInstance, SMTResult> c) {
        checks.add(c);
    }

    public List<Function<BoolectorInstance, SMTResult>> getChecks() {
        return unmodifiableList(checks);
    }

    public static class Check implements Function<BoolectorInstance, SMTResult> {
        private final String check;
        private final String name;

        public Check(String name, String check) {
            super();
            this.check = check;
            this.name = name;
        }

        public String getCheck() {
            return check;
        }

        public String getName() {
            return name;
        }

        public SMTResult apply(BoolectorInstance t) {
            try (FrameHandle h = t.push()) {
                SMTResult r = t.checkSat(getCheck());
                r.setName(getName());
                return r;
            }
        }

        @Override
        public String toString() {
            return name + " " + check.trim();
        }
    }
}
