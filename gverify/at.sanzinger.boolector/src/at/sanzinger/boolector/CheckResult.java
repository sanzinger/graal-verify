package at.sanzinger.boolector;

import java.util.function.Function;

public class CheckResult {
    private final Function<BoolectorInstance, CheckResult> check;
    private final State state;
    private final String message;

    public CheckResult(Function<BoolectorInstance, CheckResult> check, State state) {
        this(check, state, null);
    }

    public CheckResult(Function<BoolectorInstance, CheckResult> check, State state, String message) {
        super();
        this.check = check;
        this.state = state;
        this.message = message;
    }

    public State getState() {
        return state;
    }

    public String getMessage() {
        return message;
    }

    @Override
    public String toString() {
        return String.format("CheckResult check: %s state [%s]: '%s'", check, state, message);
    }

    public enum State {
        OK,
        SUSPICIOUS,
        ERROR
    }
}
