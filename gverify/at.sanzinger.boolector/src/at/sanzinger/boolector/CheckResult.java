package at.sanzinger.boolector;

import java.util.function.Function;

public class CheckResult {
    private final String name;
    private final Function<BoolectorInstance, CheckResult> check;
    private final State state;
    private final String message;

    public CheckResult(String name, Function<BoolectorInstance, CheckResult> check, State state) {
        this(name, check, state, null);
    }

    public CheckResult(String name, Function<BoolectorInstance, CheckResult> check, State state, String message) {
        super();
        this.name = name;
        this.check = check;
        this.state = state;
        this.message = message;
    }

    public String getName() {
        return name;
    }

    public State getState() {
        return state;
    }

    public String getMessage() {
        return message;
    }

    @Override
    public String toString() {
        return String.format("CheckResult check %s: %s state [%s]: '%s'", name, check, state, message);
    }

    public enum State {
        OK,
        SUSPICIOUS,
        ERROR
    }
}
