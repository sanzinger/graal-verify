package at.sanzinger.graal.verify;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;

import jdk.vm.ci.common.JVMCIError;

import com.oracle.graal.graph.Node;
import com.oracle.graal.nodes.AbstractMergeNode;
import com.oracle.graal.nodes.IfNode;
import com.oracle.graal.nodes.MergeNode;
import com.oracle.graal.nodes.ValuePhiNode;
import com.oracle.graal.nodes.extended.SwitchNode;

/**
 * This class walks up from a phi node and finds all relevant if nodes, and generates a SMT ite
 * statement with the correct values.
 */
public class PhiConditionResolver {
    private final ValuePhiNode phi;
    private static final If UNSUPPORTED = new If(false, null);

    public PhiConditionResolver(ValuePhiNode phi) {
        super();
        this.phi = phi;
    }

    public String resolve() {
        Graph g = new Graph();
        AbstractMergeNode merge = phi.merge();
        if (!(merge instanceof MergeNode)) {
            return null;
        }
        int ct = merge.phiPredecessorCount();
        IfNode[] pathHeads = new IfNode[ct];
        int j = 1;
        for (int i = 0; i < ct; i++) {
            If parent = ifPredecessor(merge.phiPredecessorAt(i));
            if (parent == UNSUPPORTED) {
                return null;
            }
            if (g.addExit(new TreeExitNode(i), parent.pred, parent.trueSuccessor)) {
                pathHeads[i] = parent.pred;
            } else {
                j++;
                pathHeads[i] = null;
            }
        }
        while (j < ct) {
            j = 0;
            for (int i = 0; i < ct; i++) {
                IfNode current = pathHeads[i];
                if (current == null) {
                    j++;
                    continue;
                }
                If parent = ifPredecessor(current);
                if (parent == UNSUPPORTED) {
                    return null;
                }
                if (parent != null) {
                    if (g.addEdge(current, parent.pred, parent.trueSuccessor)) {
                        pathHeads[i] = parent.pred;
                    } else {
                        pathHeads[i] = null;
                    }
                } else {
                    pathHeads[i] = null;
                }
            }
        }
        TreeIfNode root = g.getRoot();
        return toString(root);
    }

    @SuppressWarnings("deprecation")
    private String toString(TreeNode node) {
        if (node instanceof TreeIfNode) {
            return String.format("(ite n%s %s %s)", ((TreeIfNode) node).node.condition().getId(), toString(((TreeIfNode) node).trueSuccessor), toString(((TreeIfNode) node).falseSuccessor));
        } else if (node instanceof TreeExitNode) {
            return "n" + phi.valueAt(((TreeExitNode) node).index).getId();
        } else {
            throw JVMCIError.shouldNotReachHere(String.format("%s", node));
        }
    }

    private static If ifPredecessor(Node node) {
        Node tmp = node;
        Node prev;
        do {
            prev = tmp;
            tmp = getPredecessor(tmp);
            if (tmp instanceof SwitchNode) {
                return UNSUPPORTED;
            }
        } while (tmp != null && !(tmp instanceof IfNode));
        IfNode ifNode = (IfNode) tmp;
        if (ifNode != null) {
            return new If(ifNode.trueSuccessor().equals(prev), ifNode);
        } else {
            return null;
        }
    }

    public static class If {
        public final boolean trueSuccessor;
        public final IfNode pred;

        public If(boolean trueSuccessor, IfNode pred) {
            super();
            this.trueSuccessor = trueSuccessor;
            this.pred = pred;
        }

        @Override
        public int hashCode() {
            return pred.hashCode();
        }

        @Override
        public boolean equals(Object obj) {
            if (obj instanceof If) {
                return pred.equals(((If) obj).pred);
            } else {
                return false;
            }
        }

        @Override
        public String toString() {
            return String.format("%s(%s)", pred, trueSuccessor);
        }
    }

    private static Node getPredecessor(Node n) {
        if (n == null) {
            return null;
        }
        Iterator<? extends Node> it = n.cfgPredecessors().iterator();
        if (it.hasNext()) {
            return it.next();
        } else {
            return null;
        }
    }

    public static class Graph {
        private Map<IfNode, TreeIfNode> edges = new LinkedHashMap<>();
        private List<TreeExitNode> exits = new ArrayList<>();
        private List<TreeNode> nonTrivial = new ArrayList<>();

        public boolean addEdge(IfNode child, IfNode parent, boolean trueSuccessor) {
            TreeIfNode existing = edges.get(child);
            assert existing != null;
            return addEdge(existing, parent, trueSuccessor);
        }

        public boolean addExit(TreeExitNode child, IfNode parentIfNode, boolean trueSuccessor) {
            exits.add(child);
            return addEdge(child, parentIfNode, trueSuccessor);
        }

        private boolean addEdge(TreeNode child, IfNode parentIfNode, boolean trueSuccessor) {
            // assert child.getParent() == null : child;
            TreeIfNode parent = edges.get(parentIfNode);
            boolean added = parent == null;
            if (parent == null) {
                parent = new TreeIfNode(parentIfNode);
                edges.put(parentIfNode, parent);
            }
            child.setParent(parent);
            if (trueSuccessor) {
                // assert parent.trueSuccessor == null : parent + " " + parent.trueSuccessor;
                parent.trueSuccessor = child;
            } else {
                // assert parent.falseSuccessor == null : parent.falseSuccessor;
                parent.falseSuccessor = child;
            }
            return added;
        }

        public TreeIfNode getRoot() {
            cleanup();
            for (TreeNode n : nonTrivial) {
                if (n.getParent() == null) {
                    return (TreeIfNode) n;
                }
            }
            return null;
        }

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder();
            for (TreeIfNode n : edges.values()) {
                sb.append(String.format("%s ? %s : %s\n", n.node, n.trueSuccessor, n.falseSuccessor));
            }
            return sb.toString();
        }

        private void cleanup() {
            Queue<TreeNode> worklist = new LinkedList<>(exits);
            while (!worklist.isEmpty()) {
                TreeNode n = worklist.remove();
                TreeNode parent = n.getParent();
                if (parent != null) {
                    if (n.isTrivial()) {
                        parent.replaceChild(n, n.getSimplification());
                    } else {
                        nonTrivial.add(n);
                    }
                    if (!worklist.contains(parent)) {
                        worklist.add(parent);
                    }
                } else if (n.isTrivial()) {
                    for (TreeNode child : n.getChildren()) {
                        if (child != null) {
                            child.setParent(null);
                        }
                    }
                } else /* if (!n.isTrivial()) */{
                    nonTrivial.add(n);
                }
            }
            for (TreeNode i : nonTrivial) {
                assert !i.isTrivial() : i;
            }
        }
    }

    public abstract static class TreeNode {
        private TreeIfNode parent;

        public void setParent(TreeIfNode parent) {
            this.parent = parent;
        }

        public TreeIfNode getParent() {
            return parent;
        }

        public abstract boolean isTrivial();

        public abstract TreeNode getSimplification();

        public abstract void replaceChild(TreeNode child, TreeNode replace);

        public abstract TreeNode[] getChildren();
    }

    public static class TreeIfNode extends TreeNode {
        private final IfNode node;
        private TreeNode trueSuccessor;
        private TreeNode falseSuccessor;

        public TreeIfNode(IfNode node) {
            super();
            this.node = node;
        }

        @Override
        public int hashCode() {
            return this.node.hashCode();
        }

        @Override
        public boolean equals(Object obj) {
            if (obj instanceof TreeIfNode) {
                return ((TreeIfNode) obj).node.equals(node);
            } else {
                return false;
            }
        }

        @Override
        public String toString() {
            return String.format("%s", node);
        }

        @Override
        public boolean isTrivial() {
            return trueSuccessor == null || falseSuccessor == null;
        }

        @Override
        public void replaceChild(TreeNode child, TreeNode replace) {
            if (trueSuccessor != null && trueSuccessor.equals(child)) {
                trueSuccessor = replace;
            } else if (falseSuccessor != null && falseSuccessor.equals(child)) {
                falseSuccessor = replace;
            } else {
                throw JVMCIError.shouldNotReachHere(this.toString() + " " + trueSuccessor + " " + falseSuccessor);
            }
            replace.setParent(this);
        }

        @Override
        public TreeNode getSimplification() {
            assert isTrivial();
            return trueSuccessor == null ? falseSuccessor : trueSuccessor;
        }

        @Override
        public TreeNode[] getChildren() {
            return new TreeNode[]{trueSuccessor, falseSuccessor};
        }
    }

    public static class TreeExitNode extends TreeNode {
        private final int index;

        public TreeExitNode(int index) {
            super();
            this.index = index;
        }

        @Override
        public int hashCode() {
            return index;
        }

        @Override
        public boolean equals(Object obj) {
            if (obj instanceof TreeExitNode) {
                return ((TreeExitNode) obj).index == index;
            } else {
                return false;
            }
        }

        @Override
        public String toString() {
            return "ex " + index;
        }

        @Override
        public boolean isTrivial() {
            return false;
        }

        @Override
        public void replaceChild(TreeNode child, TreeNode replace) {
            throw JVMCIError.shouldNotReachHere();
        }

        @Override
        public TreeNode getSimplification() {
            throw JVMCIError.shouldNotReachHere();
        }

        @Override
        public TreeNode[] getChildren() {
            return new TreeNode[0];
        }
    }
}
