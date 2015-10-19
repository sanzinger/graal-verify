package at.sanzinger.graal.verify;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.IdentityHashMap;

import jdk.vm.ci.meta.PrimitiveConstant;
import jdk.vm.ci.options.Option;
import jdk.vm.ci.options.OptionType;
import jdk.vm.ci.options.OptionValue;
import at.sanzinger.graal.verify.gen.OperatorDescription;

import com.oracle.graal.compiler.common.type.PrimitiveStamp;
import com.oracle.graal.debug.TTY;
import com.oracle.graal.graph.Node;
import com.oracle.graal.graph.NodeClass;
import com.oracle.graal.graph.iterators.NodeIterable;
import com.oracle.graal.nodes.ConstantNode;
import com.oracle.graal.nodes.EndNode;
import com.oracle.graal.nodes.IfNode;
import com.oracle.graal.nodes.LogicNode;
import com.oracle.graal.nodes.ParameterNode;
import com.oracle.graal.nodes.PhiNode;
import com.oracle.graal.nodes.StructuredGraph;
import com.oracle.graal.nodes.ValueNode;
import com.oracle.graal.nodes.ValuePhiNode;
import com.oracle.graal.nodes.calc.AddNode;
import com.oracle.graal.nodes.calc.AndNode;
import com.oracle.graal.nodes.calc.DivNode;
import com.oracle.graal.nodes.calc.IntegerEqualsNode;
import com.oracle.graal.nodes.calc.IntegerLessThanNode;
import com.oracle.graal.nodes.calc.MulNode;
import com.oracle.graal.nodes.calc.NegateNode;
import com.oracle.graal.nodes.calc.NotNode;
import com.oracle.graal.nodes.calc.OrNode;
import com.oracle.graal.nodes.calc.RemNode;
import com.oracle.graal.nodes.calc.SubNode;
import com.oracle.graal.phases.BasePhase;
import com.oracle.graal.phases.tiers.LowTierContext;

public class SMTLibGeneratorPhase extends BasePhase<LowTierContext> {
    private static final IdentityHashMap<NodeClass<? extends ValueNode>, OperatorDescription<?>> n2o = new IdentityHashMap<>();

    // @formatter:off
    @Option(help = "Dump SMT-V2 representation of the graphs into this directory", type=OptionType.User)
    private static final OptionValue<String> DumpSMTDir = new OptionValue<>(null);
    // @formatter:on

    private static <T extends ValueNode> void n2o(NodeClass<T> nodeClass, String opName) {
        n2o.put(nodeClass, new OperatorDescription<>(nodeClass, (n) -> defaultDeclaration(n), (n) -> defaultDefinition(opName, n)));
    }

    private static <T extends ValueNode> void n2o(OperatorDescription<T> d) {
        n2o.put(d.getNodeClass(), d);
    }

    static {
        n2o(NotNode.TYPE, "bvnot");
        n2o(AndNode.TYPE, "bvand");
        n2o(OrNode.TYPE, "bvor");
        n2o(NegateNode.TYPE, "bvneg");
        n2o(AddNode.TYPE, "bvadd");
        n2o(SubNode.TYPE, "bvsub");
        n2o(MulNode.TYPE, "bvmul");
        n2o(DivNode.TYPE, "bvsdiv");
        n2o(RemNode.TYPE, "bvsrem");
        n2o(ParameterNode.TYPE, null);
        n2o(IntegerLessThanNode.TYPE, "bvslt");
        n2o(IntegerEqualsNode.TYPE, "=");
        n2o(new OperatorDescription<>(IfNode.TYPE, SMTLibGeneratorPhase::booleanDeclaration, SMTLibGeneratorPhase::ifDefinition));
        n2o(new OperatorDescription<>(PhiNode.TYPE, SMTLibGeneratorPhase::defaultDeclaration, SMTLibGeneratorPhase::phiDefinition));
        n2o(new OperatorDescription<>(ValuePhiNode.TYPE, SMTLibGeneratorPhase::defaultDeclaration, SMTLibGeneratorPhase::phiDefinition));
        n2o(new OperatorDescription<>(ConstantNode.TYPE, SMTLibGeneratorPhase::defaultDeclaration, SMTLibGeneratorPhase::defineConstant));
    }

    private static String defaultDefinition(String opName, ValueNode n) {
        if (opName == null) {
            return null;
        }
        StringBuilder sb = new StringBuilder();
        if (n.inputs().count() > 0) {
            sb.append("(assert (= ");
            sb.append(getNodeString(n));
            sb.append(" (");
            sb.append(opName);
            for (Node i : n.inputs()) {
                sb.append(' ');
                sb.append(getNodeString(i));
            }
            sb.append(")))");
        }
        return sb.toString();
    }

    private static String ifDefinition(IfNode n) {
        IfSuccessorPair ifSucc = findDominatingIfNode(n.predecessor());
        String nodeString = getNodeString(n);
        StringBuilder sb = new StringBuilder();
        sb.append("(assert (= ");
        sb.append(nodeString);
        sb.append(' ');
        sb.append(getNodeString(n.condition()));
        sb.append("))");

        if (ifSucc != null) {
            sb.append(String.format("\n(assert (= %s (%s %s)))", nodeString, ifSucc.trueSuccessor ? "" : "not", getNodeString(ifSucc.ifNode)));
        }
        return sb.toString();
    }

    private static String phiDefinition(PhiNode n) {
        StringBuilder sb = new StringBuilder();
        StringBuilder closing = new StringBuilder();
        sb.append("(assert ");
        int i = 0;
        NodeIterable<EndNode> pred = n.merge().cfgPredecessors();
        for (Node en : pred) {
            IfSuccessorPair ifNodeSucc = findDominatingIfNode(en);
            IfNode ifNode = ifNodeSucc.ifNode;
            sb.append("(");
            if (i + 1 < pred.count()) {
                sb.append("xor ");
            }
            sb.append("(and (");
            if (!ifNodeSucc.trueSuccessor) {
                sb.append("not ");
            }
            sb.append(getNodeString(ifNode));
            sb.append(") (= ");
            sb.append(getNodeString(n));
            sb.append(' ');
            sb.append(getNodeString(n.valueAt(i)));
            sb.append(")) ");
            closing.append(")");
            i++;
        }
        sb.append(closing);
        sb.append(")");
        return sb.toString();
    }

    private static IfSuccessorPair findDominatingIfNode(Node fn) {
        Node n = fn;
        Node prev = null;
        while (!(n instanceof IfNode)) {
            prev = n;
            n = n.predecessor();
            if (n == null) {
                return null;
            }
        }
        IfNode ifNode = (IfNode) n;
        return new IfSuccessorPair(ifNode, ifNode.trueSuccessor().equals(prev));
    }

    private static class IfSuccessorPair {
        public final IfNode ifNode;
        public final boolean trueSuccessor;

        public IfSuccessorPair(IfNode ifNode, boolean trueSuccessor) {
            super();
            this.ifNode = ifNode;
            this.trueSuccessor = trueSuccessor;
        }

    }

    private static String booleanDeclaration(ValueNode n) {
        return String.format("(declare-fun %s () Bool)", getNodeString(n));
    }

    private static String defaultDeclaration(ValueNode n) {
        String type;
        if (n instanceof LogicNode) {
            type = "Bool";
        } else {
            PrimitiveStamp ps = (PrimitiveStamp) n.stamp();
            type = String.format("(_ BitVec %d)", ps.getBits());
        }
        return String.format("(declare-fun %s () %s)", getNodeString(n), type);
    }

    private static String defineConstant(ConstantNode n) {
        PrimitiveConstant c = (PrimitiveConstant) n.asConstant();
        int bits = c.getJavaKind().getBitCount();
        return String.format("(assert (= %s #x%0" + (bits / 4) + "x))", getNodeString(n), c.asBoxedPrimitive());
    }

    @Override
    protected void run(StructuredGraph graph, LowTierContext context) {
        String prologue = "(set-logic QF_BV)";
        StringBuilder declarations = new StringBuilder();
        StringBuilder definitions = new StringBuilder();
        for (Node n : graph.getNodes()) {
            if (n instanceof ValueNode) {
                @SuppressWarnings("unchecked")
                OperatorDescription<ValueNode> d = (OperatorDescription<ValueNode>) n2o.get(n.getNodeClass());
                if (d != null) {
                    appendCrNonNull(declarations, d.getDeclaration().apply((ValueNode) n));
                    appendCrNonNull(definitions, d.getDefinition().apply((ValueNode) n));
                }
            }
        }
        String filename = graph.method().format("%h_%n_(%p).smt2").replace(' ', '_');
        File outfile = new File(DumpSMTDir.getValue(), filename);
        try {
            TTY.println("Write SMT model of %s to file %s", graph.method(), outfile);
            writeToFile(outfile, prologue, declarations, definitions);
        } catch (IOException e) {
            TTY.println("Cannot write file to %s %s", outfile, e);
        }
    }

    private static void appendCrNonNull(StringBuilder sb, String v) {
        if (v != null) {
            sb.append(v);
            sb.append('\n');
        }
    }

    public static void writeToFile(File f, CharSequence... s) throws IOException {
        try (FileWriter fw = new FileWriter(f)) {
            for (CharSequence cs : s) {
                fw.write(cs.toString());
                fw.write('\n');
            }
        }
    }

    /**
     * Translates the given node into a symbolic name for n used in the SMT file.
     */
    @SuppressWarnings("deprecation")
    private static String getNodeString(Node n) {
        return "n" + n.getId();
    }
}
