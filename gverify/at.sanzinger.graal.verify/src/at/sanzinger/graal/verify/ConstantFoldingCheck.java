package at.sanzinger.graal.verify;

import java.util.ArrayList;
import java.util.function.Function;

import at.sanzinger.boolector.BoolectorInstance;
import at.sanzinger.boolector.BoolectorInstance.FrameHandle;
import at.sanzinger.boolector.CheckResult;
import at.sanzinger.boolector.SMTModel;
import at.sanzinger.boolector.SMTModel.Definition;
import at.sanzinger.boolector.SMTResult;

import com.oracle.graal.debug.Debug;
import com.oracle.graal.debug.DebugCloseable;
import com.oracle.graal.debug.DebugTimer;
import com.oracle.graal.graph.Node;

public class ConstantFoldingCheck implements Function<BoolectorInstance, CheckResult> {
    private static final String NAME = "Constant folding check";
    private static final DebugTimer DT = Debug.timer("ConstantfoldingCheck");
    private final Function<String, Node> nodeTranslator;
    private final Function<Node, Boolean> isConstant;

    public ConstantFoldingCheck(Function<String, Node> nodeTranslator, Function<Node, Boolean> isConstant) {
        super();
        this.nodeTranslator = nodeTranslator;
        this.isConstant = isConstant;
    }

    public CheckResult apply(BoolectorInstance t) {
        ArrayList<SMTResult> constantFoldable = new ArrayList<>();
        try (FrameHandle h = t.push(); DebugCloseable dt = DT.start()) {
            SMTModel m = t.getModel();
            for (Definition d : m.getDefinitions()) {
                Node n = nodeTranslator.apply(d.getName());
                if (isConstant.apply(n)) {
                    continue;
                }
                try (FrameHandle h2 = t.push()) {
                    String check = String.format("(assert (not (= %s %s)))", d.getName(), d.getValue());
                    t.define(check);
                    SMTResult result = t.checkSat();
                    result.setName(String.format("Node %s is constant with value %s", n, d.getValue()));
                    if (!result.isSat()) {
                        constantFoldable.add(result);
                    }
                }
            }
        }
        if (constantFoldable.size() == 0) {
            return new CheckResult(NAME, this, CheckResult.State.OK);
        } else {
            return new CheckResult(NAME, this, CheckResult.State.SUSPICIOUS, constantFoldable.toString());
        }
    }

    @Override
    public String toString() {
        return String.format("Constant folding check");
    }
}
