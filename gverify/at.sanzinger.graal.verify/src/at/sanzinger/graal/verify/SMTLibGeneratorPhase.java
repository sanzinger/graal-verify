package at.sanzinger.graal.verify;

import static com.oracle.graal.debug.TTY.println;
import static java.lang.String.format;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Function;

import jdk.vm.ci.common.JVMCIError;
import jdk.vm.ci.meta.Constant;
import jdk.vm.ci.meta.PrimitiveConstant;
import jdk.vm.ci.options.Option;
import jdk.vm.ci.options.OptionType;
import jdk.vm.ci.options.OptionValue;
import at.sanzinger.boolector.Boolector;
import at.sanzinger.boolector.BoolectorInstance;
import at.sanzinger.boolector.SMT;
import at.sanzinger.boolector.SMT.Check;
import at.sanzinger.boolector.SMTResult;
import at.sanzinger.graal.verify.gen.OperatorDescription;

import com.oracle.graal.compiler.common.type.AbstractPointerStamp;
import com.oracle.graal.compiler.common.type.ObjectStamp;
import com.oracle.graal.compiler.common.type.PrimitiveStamp;
import com.oracle.graal.compiler.common.type.Stamp;
import com.oracle.graal.debug.TTY;
import com.oracle.graal.graph.Node;
import com.oracle.graal.graph.NodeClass;
import com.oracle.graal.graph.iterators.NodeIterable;
import com.oracle.graal.nodes.AbstractMergeNode;
import com.oracle.graal.nodes.ConstantNode;
import com.oracle.graal.nodes.IfNode;
import com.oracle.graal.nodes.InvokeNode;
import com.oracle.graal.nodes.LogicNode;
import com.oracle.graal.nodes.LoopBeginNode;
import com.oracle.graal.nodes.MergeNode;
import com.oracle.graal.nodes.ParameterNode;
import com.oracle.graal.nodes.PhiNode;
import com.oracle.graal.nodes.StructuredGraph;
import com.oracle.graal.nodes.ValueNode;
import com.oracle.graal.nodes.ValuePhiNode;
import com.oracle.graal.nodes.calc.AddNode;
import com.oracle.graal.nodes.calc.AndNode;
import com.oracle.graal.nodes.calc.DivNode;
import com.oracle.graal.nodes.calc.IntegerBelowNode;
import com.oracle.graal.nodes.calc.IntegerDivNode;
import com.oracle.graal.nodes.calc.IntegerEqualsNode;
import com.oracle.graal.nodes.calc.IntegerLessThanNode;
import com.oracle.graal.nodes.calc.IntegerRemNode;
import com.oracle.graal.nodes.calc.IntegerTestNode;
import com.oracle.graal.nodes.calc.LeftShiftNode;
import com.oracle.graal.nodes.calc.MulNode;
import com.oracle.graal.nodes.calc.NegateNode;
import com.oracle.graal.nodes.calc.NotNode;
import com.oracle.graal.nodes.calc.OrNode;
import com.oracle.graal.nodes.calc.RemNode;
import com.oracle.graal.nodes.calc.RightShiftNode;
import com.oracle.graal.nodes.calc.SubNode;
import com.oracle.graal.nodes.calc.UnsignedRightShiftNode;
import com.oracle.graal.phases.BasePhase;
import com.oracle.graal.phases.tiers.LowTierContext;

public class SMTLibGeneratorPhase extends BasePhase<LowTierContext> {
    private static final IdentityHashMap<NodeClass<? extends ValueNode>, OperatorDescription<?>> n2o = new IdentityHashMap<>();

    // @formatter:off
    @Option(help = "Dump SMT-V2 representation of the graphs into this directory", type=OptionType.User)
    private static final OptionValue<String> DumpSMTDir = new OptionValue<>(null);

    @Option(help = "Boolector binary", type=OptionType.User)
    private static final OptionValue<String> Btor = new OptionValue<>(null);
    // @formatter:on

    private static Boolector boolector;
    private static final AtomicInteger unknownCounter = new AtomicInteger();

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
        n2o(InvokeNode.TYPE, null);
        n2o(IntegerLessThanNode.TYPE, "bvslt");
        n2o(IntegerBelowNode.TYPE, "bvult");
        n2o(IntegerEqualsNode.TYPE, "=");
        n2o(IntegerTestNode.TYPE, "=");
        n2o(IntegerRemNode.TYPE, "bvurem");
        n2o(IntegerDivNode.TYPE, "bvsdiv");
        n2o(UnsignedRightShiftNode.TYPE, "bvlshr");
        n2o(LeftShiftNode.TYPE, "bvshl");
        n2o(RightShiftNode.TYPE, "bvashr");
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
            if (!allCaptured(n.inputs())) {
                return null;
            }
            int bits = getBits(n);
            sb.append("(assert (= ");
            sb.append(getNodeString(n));
            sb.append(" (");
            sb.append(opName);
            for (Node i : n.inputs()) {
                int iBits = getBits((ValueNode) i);
                sb.append(' ');
                if (iBits < bits) {
                    sb.append(String.format("((_ sign_extend %d) %s)", bits - iBits, getNodeString(i)));
                } else {
                    sb.append(getNodeString(i));
                }
            }
            sb.append(")))");
        }
        return sb.toString();
    }

    private static String phiDefinition(PhiNode n) {
        StringBuilder sb = new StringBuilder();
        StringBuilder closing = new StringBuilder();
        sb.append("(assert (= ");
        sb.append(getNodeString(n));
        sb.append(" ");
        int i = 0;
        AbstractMergeNode merge = n.merge();
        Iterable<? extends Node> pred = null;
        int count = 0;
        if (merge instanceof MergeNode) {
            NodeIterable<? extends Node> predNodeIter = n.merge().cfgPredecessors();
            pred = predNodeIter;
            count = predNodeIter.count();

        } else if (merge instanceof LoopBeginNode) {
            return null;
        }
        assert count >= 2 : "Count: " + count + " n: " + n;
        if (allCaptured(pred)) {
            for (Node en : pred) {
                IfSuccessorPair ifNodeSucc = findDominatingIfNode(en);
                ValueNode ifNode = ifNodeSucc.ifNode.condition();
                sb.append("(");
                if (i + 1 < count) {
                    sb.append("ite ");
                    sb.append("(");
                    if (!ifNodeSucc.trueSuccessor) {
                        sb.append("not ");
                    }
                    sb.append(getNodeString(ifNode));
                    sb.append(") ");
                }
                sb.append(' ');
                sb.append(getNodeString(n.valueAt(i)));
                sb.append(' ');
                closing.append(")");
                i++;
            }
            sb.append(closing);
            sb.append("))");
            return sb.toString();
        } else {
            return null;
        }
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

    private static String defaultDeclaration(ValueNode n) {
        return declaration(n, getBits(n));
    }

    private static int getBits(ValueNode n) {
        Stamp stamp = n.stamp();
        if (n instanceof LogicNode) {
            return 1;
        } else if (stamp instanceof PrimitiveStamp) {
            PrimitiveStamp ps = (PrimitiveStamp) n.stamp();
            return ps.getBits();
        } else if (stamp instanceof ObjectStamp || stamp instanceof AbstractPointerStamp) {
            return 64;
        } else {
            throw JVMCIError.unimplemented(n.toString() + " " + n.stamp());
        }
    }

    private static String declaration(ValueNode n, int bits) {
        String type;
        if (bits == 1) {
            type = "Bool";
        } else {
            type = String.format("(_ BitVec %d)", bits);
        }
        return String.format("(declare-fun %s () %s)", getNodeString(n), type);
    }

    private static String defineConstant(ConstantNode n) {
        Constant c = n.asConstant();
        int bitLength = 0;
        long bits = 0;
        if (c instanceof PrimitiveConstant) {
            bitLength = ((PrimitiveConstant) c).getJavaKind().getBitCount();
            PrimitiveConstant pc = (PrimitiveConstant) c;
            switch (pc.getJavaKind()) {
                case Long:
                    bits = pc.asLong();
                    break;
                case Int:
                case Short:
                case Byte:
                    bits = pc.asInt();
                    break;
                case Char:
                    bits = pc.asInt() & 0xFFFF;
                    break;
                case Boolean:
                    bits = pc.asBoolean() ? 1 : 0;
                    break;
                case Float:
                    bits = Float.floatToRawIntBits(pc.asFloat());
                    break;
                case Double:
                    bits = Double.doubleToRawLongBits(pc.asDouble());
                    break;
                default:
                    throw JVMCIError.shouldNotReachHere("Unknown PrimitiveConstant " + pc);
            }
        }
        if (bitLength > 0) {
            long value = bitLength < 64 ? bits & ((1l << bitLength) - 1) : bits;
            return String.format("(assert (= %s #x%0" + (bitLength / 4) + "x))", getNodeString(n), value);
        } else {
            return null;
        }
    }

    @Override
    protected void run(StructuredGraph graph, LowTierContext context) {
        String prologue = "(set-logic QF_BV)";
        StringBuilder declarations = new StringBuilder();
        StringBuilder definitions = new StringBuilder();
        List<ValueNode> definedNodes = new ArrayList<>();
        for (Node n : graph.getNodes()) {
            if (n instanceof ValueNode) {
                @SuppressWarnings("unchecked")
                OperatorDescription<ValueNode> d = (OperatorDescription<ValueNode>) n2o.get(n.getNodeClass());
                if (d != null) {
                    appendCrNonNull(declarations, d.getDeclaration().apply((ValueNode) n));
                    appendCrNonNull(definitions, d.getDefinition().apply((ValueNode) n));
                    definedNodes.add((ValueNode) n);
                }
            }
        }
        SMT smt = new SMT(prologue + declarations + definitions);
        smt.addCheck(new ConstantFoldingCheck(s -> graph.getNode(Integer.parseInt(s.substring(1))), n -> n instanceof ConstantNode));
        smt.addCheck(new EquivalenceCheck());
        if (!DumpSMTDir.hasDefaultValue()) {
            dumpSMT(graph, prologue, declarations, definitions);
        }
        check(smt, definedNodes);
    }

    private static boolean allCaptured(Iterable<? extends Node> nodes) {
        for (Node n : nodes) {
            if (!isCaptured(n)) {
                return false;
            }
        }
        return true;
    }

    private static boolean isCaptured(Node n) {
        return n2o.containsKey(n.getNodeClass());
    }

    private static void dumpSMT(StructuredGraph graph, String prologue, StringBuilder declarations, StringBuilder definitions) {
        String filename;
        if (graph.method() == null) {
            filename = String.format("%s_%d.smt2", graph.toString(), unknownCounter.incrementAndGet());
        } else {
            filename = graph.method().format("%h_%n_(%p).smt2").replace(' ', '_').replace('/', '_');
        }
        File outfile = new File(DumpSMTDir.getValue(), filename);
        try {
            println("Write SMT model of %s to file %s", graph.method(), outfile);
            writeToFile(outfile, prologue, declarations, definitions);
        } catch (IOException e) {
            println("Cannot write file to %s %s", outfile, e);
        }
    }

    private static void check(SMT smt, List<ValueNode> definedNodes) {
// addEqualityChecks(smt, definedNodes);
        Boolector btor = getBoolector();
        if (btor != null) {
            try (BoolectorInstance bi = btor.newInstance()) {
                SMTResult[] results = bi.execute(smt);
                for (int i = 0; i < results.length; i++) {
                    SMTResult result = results[i];
                    Function<BoolectorInstance, SMTResult> check = smt.getChecks().get(i);
                    if (result.isError()) {
                        println("Error on checking %s: %s", check, result.getError());
                    }
                    if (!result.isSat()) {
                        println("unsat: %s", result.getName());
                    }
                }
            }
        }
    }

// private static void addEqualityChecks(SMT smt, List<ValueNode> definedNodes) {
// int sz = definedNodes.size();
// for (int i = 0; i < sz; i++) {
// ValueNode ni = definedNodes.get(i);
// String nni = getNodeString(ni);
// for (int j = i + 1; j < sz; j++) {
// if (i == j) {
// continue;
// }
// ValueNode nj = definedNodes.get(j);
// String nnj = getNodeString(nj);
// if (ni.stamp().equals(nj.stamp())) {
// String name = format("%s == %s", ni, nj);
// smt.addCheck(new Check(name, "(assert (not (= " + nni + " " + nnj + ")))"));
// }
// }
// }
// }

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
    static String getNodeString(Node n) {
        return "n" + n.getId();
    }

    static Boolector getBoolector() {
        if (boolector == null) {
            String btorPath;
            if (!Btor.hasDefaultValue()) {
                btorPath = Btor.getValue();
            } else {
                btorPath = "boolector";
            }
            boolector = new Boolector(btorPath); // write race ok
            if (!boolector.verify()) {
                boolector = null;
                TTY.println("Could not find boolector with command: " + btorPath);
                return null;
            }
        }
        return boolector;
    }
}
