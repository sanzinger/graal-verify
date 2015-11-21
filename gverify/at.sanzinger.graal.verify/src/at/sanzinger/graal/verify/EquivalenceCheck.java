package at.sanzinger.graal.verify;

import static java.lang.String.format;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.Set;
import java.util.function.Function;

import at.sanzinger.boolector.BoolectorInstance;
import at.sanzinger.boolector.BoolectorInstance.FrameHandle;
import at.sanzinger.boolector.SMTModel;
import at.sanzinger.boolector.SMTModel.Definition;
import at.sanzinger.boolector.SMTResult;

public class EquivalenceCheck implements Function<BoolectorInstance, SMTResult> {
    public EquivalenceCheck() {

    }

    @Override
    public SMTResult apply(BoolectorInstance t) {
        try (FrameHandle fh = t.push()) {
            equivalenceExtraction(t);
            return new SMTResult(Arrays.asList("sat"), null);
        }
    }

    private static void equivalenceExtraction(BoolectorInstance btor) {
        SMTModel rootModel = getModel(btor);
        Set<Set<Definition>> p = buildP(rootModel);
        HashMap<Definition, Definition> e = new HashMap<>();
        Pair pair = new Pair();
        while (getNextPair(pair, p)) {
            SMTModel model;
            if ((model = sat(btor, pair.k, pair.l)) != null) {
                refineP(p, pair, model);
            } else {
                e.put(pair.l, pair.k);
                pair.d.remove(pair.k);
            }
        }
        System.out.println(e);
    }

    private static SMTModel sat(BoolectorInstance btor, Definition k, Definition l) {
        try (FrameHandle fh = btor.push()) {
            String assertion = format("(assert (not (= %s %s)))", k.getName(), l.getName());
            if (btor.checkSat(assertion).isSat()) {
                return getModel(btor);
            } else {
                return null;
            }
        }
    }

    private static SMTModel getModel(BoolectorInstance btor) {
        try (FrameHandle fh = btor.push()) {
            return btor.getModel();
        }
    }

    private static void refineP(Set<Set<Definition>> p, Pair pair, SMTModel model) {
        HashMap<String, Set<Definition>> res = new HashMap<>();
        for (Definition d : pair.d) {
            Definition newDefinition = model.getDefinition(d.getName());
            if (newDefinition == null) {
                model.getDefinition(d.getName());
                throw new IllegalStateException("Definition of " + d.getName() + " not found");
            }
            String modelValue = newDefinition.getValue();
            Set<Definition> s = res.get(modelValue);
            if (s == null) {
                res.put(modelValue, s = Collections.newSetFromMap(new IdentityHashMap<Definition, Boolean>()));
            }
            s.add(d);
        }
        boolean removed = p.remove(pair.d);
        assert removed : "Must be in set";
        p.addAll(res.values());
    }

    private static boolean getNextPair(Pair pair, Set<Set<Definition>> p) {
        for (Set<Definition> def : p) {
            if (!p.contains(def)) {
                throw new RuntimeException("p is not stable");
            }
            int size = def.size();
            if (size >= 2) {
                Iterator<Definition> it = def.iterator();
                pair.k = it.next();
                pair.l = it.next();
                pair.d = def;
                return true;
            }
        }
        return false;
    }

    private static Set<Set<Definition>> buildP(SMTModel rootModel) {
        HashMap<String, Set<Definition>> p = new HashMap<>();
        for (Definition d : rootModel.getDefinitions()) {
            String value = d.getValue();
            Set<Definition> e = p.get(value);
            if (e == null) {
                e = Collections.newSetFromMap(new IdentityHashMap<Definition, Boolean>());
                p.put(value, e);
            }
            e.add(d);
        }
        Set<Set<Definition>> pSet = Collections.newSetFromMap(new IdentityHashMap<Set<Definition>, Boolean>());
        pSet.addAll(p.values());
        return pSet;
    }

    private static final class Pair {
        Definition l;
        Definition k;
        Set<Definition> d;

        @Override
        public String toString() {
            return String.format("l: %s k: %d");
        }
    }
}
