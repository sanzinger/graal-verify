package at.sanzinger.graal.verify;

import static java.lang.String.format;

import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Function;

import at.sanzinger.boolector.BoolectorInstance;
import at.sanzinger.boolector.BoolectorInstance.FrameHandle;
import at.sanzinger.boolector.CheckResult;
import at.sanzinger.boolector.CheckResult.State;
import at.sanzinger.boolector.SMTModel;
import at.sanzinger.boolector.SMTModel.Definition;

public class EquivalenceCheck implements Function<BoolectorInstance, CheckResult> {
    private static final String NAME = "Equivalence check";

    private final Function<String, String> nodeNameTranslator;
    private final BiFunction<String, String, Boolean> isKnownEquivalence;

    public EquivalenceCheck(BiFunction<String, String, Boolean> isKnownEquivalence, Function<String, String> nodeNameTranslator) {
        this.nodeNameTranslator = nodeNameTranslator;
        this.isKnownEquivalence = isKnownEquivalence;
    }

    public EquivalenceCheck() {
        this((x, y) -> false, n -> n.toString());
    }

    @Override
    public CheckResult apply(BoolectorInstance t) {
        try (FrameHandle fh = t.push()) {
            Map<Definition, Definition> equivalences = equivalenceExtraction(t);
            String resultString = null;
            CheckResult.State resultState = State.OK;
            if (equivalences.size() > 0) {
                StringBuilder sb = new StringBuilder();
                sb.append("Equivalences found: ");
                boolean newFound = false;
                for (Entry<Definition, Definition> d : equivalences.entrySet()) {
                    String a = nodeNameTranslator.apply(d.getKey().getName());
                    String b = nodeNameTranslator.apply(d.getValue().getName());
                    if (!isKnownEquivalence.apply(d.getKey().getName(), d.getValue().getName())) {
                        sb.append(format("%s==%s, ", a, b));
                        newFound = true;
                    }
                }
                if (newFound) {
                    resultString = sb.substring(0, sb.length() - 2);
                    resultState = CheckResult.State.ERROR;
                }
            }
            return new CheckResult(NAME, this, resultState, resultString);
        }
    }

    private static HashMap<Definition, Definition> equivalenceExtraction(BoolectorInstance btor) {
        SMTModel rootModel = getModel(btor);
        Set<Set<Definition>> p = buildP(rootModel);
        HashMap<Definition, Definition> e = new HashMap<>();
        Pair pair = new Pair();
        while (getNextPair(pair, p)) {
            SMTModel model;
            if ((model = sat(btor, pair.k, pair.l)) != null) {
                refineP(p, pair.d, model);
            } else {
                e.put(pair.l, pair.k);
                pair.d.remove(pair.k);
            }
        }
        return e;
    }

    private static SMTModel sat(BoolectorInstance btor, Definition k, Definition l) {
        try (FrameHandle fh = btor.push()) {
            String assertion = format("(assert (not (= %s %s)))", k.getName(), l.getName());
            btor.define(assertion);
            if (btor.checkSat().isSat()) {
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

    private static void refineP(Set<Set<Definition>> p, Set<Definition> definitions, SMTModel model) {
        HashMap<String, Set<Definition>> res = new HashMap<>();
        for (Definition d : definitions) {
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
        boolean removed = p.remove(definitions);
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

    @Override
    public String toString() {
        return "EquivalenceCheck";
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
