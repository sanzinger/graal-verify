package at.sanzinger.graal.verify;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.function.Function;

import at.sanzinger.boolector.BoolectorInstance;
import at.sanzinger.boolector.BoolectorInstance.FrameHandle;
import at.sanzinger.boolector.SMTModel;
import at.sanzinger.boolector.SMTModel.Definition;
import at.sanzinger.boolector.SMTResult;

public class ConstantFoldingCheck implements Function<BoolectorInstance, SMTResult> {

    public SMTResult apply(BoolectorInstance t) {
        ArrayList<SMTResult> constantFoldable = new ArrayList<>();
        try (FrameHandle h = t.push()) {
            SMTModel m = t.getModel();
            for (Definition d : m.getDefinitions()) {
                try (FrameHandle h2 = t.push()) {
                    String check = String.format("(assert (not (= %s %s)))", d.getName(), d.getValue());
                    SMTResult result = t.checkSat(check);
                    if (!result.isSat()) {
                        constantFoldable.add(result);
                    }
                }
            }
        }
        return new SMTResult(Arrays.asList("Constant fold check revealed following: " + constantFoldable, constantFoldable.size() > 0 ? "sat" : "unsat"), null);
    }
}
