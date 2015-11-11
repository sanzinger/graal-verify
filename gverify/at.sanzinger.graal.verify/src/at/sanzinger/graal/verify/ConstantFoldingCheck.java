package at.sanzinger.graal.verify;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.function.Function;

import com.oracle.graal.graph.Node;

import at.sanzinger.boolector.BoolectorInstance;
import at.sanzinger.boolector.BoolectorInstance.FrameHandle;
import at.sanzinger.boolector.SMTModel;
import at.sanzinger.boolector.SMTModel.Definition;
import at.sanzinger.boolector.SMTResult;

public class ConstantFoldingCheck implements Function<BoolectorInstance, SMTResult> {
    private final Function<String, Node> nodeTranslator;
    private final Function<Node, Boolean> isConstant;

    public ConstantFoldingCheck(Function<String, Node> nodeTranslator, Function<Node, Boolean> isConstant) {
        super();
        this.nodeTranslator = nodeTranslator;
        this.isConstant = isConstant;
    }

    public SMTResult apply(BoolectorInstance t) {
        ArrayList<SMTResult> constantFoldable = new ArrayList<>();
        try (FrameHandle h = t.push()) {
            SMTModel m = t.getModel();
            for (Definition d : m.getDefinitions()) {
                Node n = nodeTranslator.apply(d.getName());
                if (isConstant.apply(n)) {
                    continue;
                }
                try (FrameHandle h2 = t.push()) {
                    String check = String.format("(assert (not (= %s %s)))", d.getName(), d.getValue());
                    SMTResult result = t.checkSat(check);
                    result.setName(String.format("Node %s is constant with value %s", n, d.getValue()));
                    if (!result.isSat()) {
                        constantFoldable.add(result);
                    }
                }
            }
        }
        return new SMTResult(Arrays.asList("Constant fold check revealed following: " + constantFoldable, constantFoldable.size() > 0 ? "unsat" : "sat"), null, constantFoldable.toString());
    }
}
