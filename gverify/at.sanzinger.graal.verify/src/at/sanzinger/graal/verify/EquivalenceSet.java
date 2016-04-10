package at.sanzinger.graal.verify;

import java.util.BitSet;

import com.oracle.graal.graph.Graph;
import com.oracle.graal.graph.Node;

public class EquivalenceSet {
    private final int nodeCount;
    private final BitSet bitSet;

    public EquivalenceSet(Graph g) {
        this.nodeCount = g.getNodeCount();
        this.bitSet = new BitSet((nodeCount * (nodeCount - 1)) / 2);
    }

    public boolean isEquivalent(Node a, Node b) {
        return bitSet.get(getIndex(a, b));
    }

    public void setEquivalent(Node a, Node b) {
        int idx = getIndex(a, b);
        if (!bitSet.get(idx)) {
            bitSet.set(idx);
            setTransitive(a, b);
            setTransitive(b, a);
        }
    }

    private void setTransitive(Node a, Node b) {
        for (Node c : a.inputs()) {
            if (isEquivalent(a, c)) {
                setEquivalent(b, c);
            }
        }
        for (Node c : a.usages()) {
            if (isEquivalent(a, c)) {
                setEquivalent(b, c);
            }
        }
    }

    @SuppressWarnings("deprecation")
    private int getIndex(Node ai, Node bi) {
        Node a;
        Node b;
        if (ai.getId() > bi.getId()) {
            a = bi;
            b = ai;
        } else {
            a = ai;
            b = bi;
        }
        return a.getId() * nodeCount + b.getId();
    }
}
