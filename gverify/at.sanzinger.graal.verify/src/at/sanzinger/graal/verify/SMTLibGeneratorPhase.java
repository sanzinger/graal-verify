package at.sanzinger.graal.verify;

import static com.oracle.graal.debug.TTY.println;

import java.io.File;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.channels.FileChannel;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Function;

import com.oracle.graal.compiler.amd64.AMD64AddressNode;
import com.oracle.graal.compiler.common.type.AbstractPointerStamp;
import com.oracle.graal.compiler.common.type.FloatStamp;
import com.oracle.graal.compiler.common.type.IllegalStamp;
import com.oracle.graal.compiler.common.type.IntegerStamp;
import com.oracle.graal.compiler.common.type.ObjectStamp;
import com.oracle.graal.compiler.common.type.PrimitiveStamp;
import com.oracle.graal.compiler.common.type.Stamp;
import com.oracle.graal.compiler.common.type.VoidStamp;
import com.oracle.graal.debug.TTY;
import com.oracle.graal.graph.Node;
import com.oracle.graal.graph.NodeClass;
import com.oracle.graal.graph.NodeClassIterable;
import com.oracle.graal.hotspot.nodes.CompressionNode;
import com.oracle.graal.hotspot.word.PointerCastNode;
import com.oracle.graal.nodes.ConstantNode;
import com.oracle.graal.nodes.InvokeNode;
import com.oracle.graal.nodes.LogicNode;
import com.oracle.graal.nodes.ParameterNode;
import com.oracle.graal.nodes.PiArrayNode;
import com.oracle.graal.nodes.PiNode;
import com.oracle.graal.nodes.StructuredGraph;
import com.oracle.graal.nodes.ValueNode;
import com.oracle.graal.nodes.ValuePhiNode;
import com.oracle.graal.nodes.calc.AddNode;
import com.oracle.graal.nodes.calc.AndNode;
import com.oracle.graal.nodes.calc.DivNode;
import com.oracle.graal.nodes.calc.FloatConvertNode;
import com.oracle.graal.nodes.calc.FloatEqualsNode;
import com.oracle.graal.nodes.calc.FloatLessThanNode;
import com.oracle.graal.nodes.calc.IntegerBelowNode;
import com.oracle.graal.nodes.calc.IntegerDivNode;
import com.oracle.graal.nodes.calc.IntegerEqualsNode;
import com.oracle.graal.nodes.calc.IntegerLessThanNode;
import com.oracle.graal.nodes.calc.IntegerRemNode;
import com.oracle.graal.nodes.calc.IntegerTestNode;
import com.oracle.graal.nodes.calc.IsNullNode;
import com.oracle.graal.nodes.calc.LeftShiftNode;
import com.oracle.graal.nodes.calc.MulNode;
import com.oracle.graal.nodes.calc.NarrowNode;
import com.oracle.graal.nodes.calc.NegateNode;
import com.oracle.graal.nodes.calc.NotNode;
import com.oracle.graal.nodes.calc.ObjectEqualsNode;
import com.oracle.graal.nodes.calc.OrNode;
import com.oracle.graal.nodes.calc.PointerEqualsNode;
import com.oracle.graal.nodes.calc.ReinterpretNode;
import com.oracle.graal.nodes.calc.RemNode;
import com.oracle.graal.nodes.calc.RightShiftNode;
import com.oracle.graal.nodes.calc.SubNode;
import com.oracle.graal.nodes.calc.UnsignedRightShiftNode;
import com.oracle.graal.nodes.extended.FixedValueAnchorNode;
import com.oracle.graal.nodes.extended.ForeignCallNode;
import com.oracle.graal.nodes.memory.FloatingReadNode;
import com.oracle.graal.nodes.memory.ReadNode;
import com.oracle.graal.options.Option;
import com.oracle.graal.options.OptionType;
import com.oracle.graal.options.OptionValue;
import com.oracle.graal.phases.BasePhase;
import com.oracle.graal.phases.tiers.LowTierContext;
import com.oracle.graal.printer.BinaryGraphPrinter;
import com.oracle.graal.word.nodes.WordCastNode;

import at.sanzinger.boolector.Boolector;
import at.sanzinger.boolector.BoolectorInstance;
import at.sanzinger.boolector.CheckResult;
import at.sanzinger.boolector.SMT;
import at.sanzinger.boolector.dump.JSONDumper;
import at.sanzinger.graal.verify.gen.OperatorDescription;
import jdk.vm.ci.common.JVMCIError;
import jdk.vm.ci.meta.Constant;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.PrimitiveConstant;

public class SMTLibGeneratorPhase extends BasePhase<LowTierContext> {
    private static final IdentityHashMap<NodeClass<? extends ValueNode>, OperatorDescription<?>> n2o = new IdentityHashMap<>();
    private static final SimpleDateFormat logfileDateFormat = new SimpleDateFormat("yyyy-MM-dd-hhmmss");
    private static final String logfileNamePattern = "smt-log-%s.json";
    private static JSONDumper dumper;

    // @formatter:off
    @Option(help = "Dump SMT-V2 representation of the graphs into this directory", type=OptionType.User)
    static final OptionValue<String> DumpSMTDir = new OptionValue<>(null);

    @Option(help = "Boolector binary", type=OptionType.User)
    static final OptionValue<String> Btor = new OptionValue<>(null);
    // @formatter:on

    private static Boolector boolector;
    private static final AtomicInteger unknownCounter = new AtomicInteger();
    private static final OperatorDescription<ValueNode> defaultDescription = new OperatorDescription<>(ValueNode.TYPE, SMTLibGeneratorPhase::defaultDeclaration, n -> null);
    private static final String DECLARE = declare();

    private static <T extends ValueNode> void n2o(NodeClass<T> nodeClass, String opName) {
        n2o.put(nodeClass, new OperatorDescription<>(nodeClass, (n) -> defaultDeclaration(n), (n) -> defaultDefinition(opName, n)));
    }

    private static <T extends ValueNode> void arithmetic(NodeClass<T> nodeClass, String opName) {
        n2o.put(nodeClass, new OperatorDescription<>(nodeClass, (n) -> defaultDeclaration(n), (n) -> defaultArithmeticDefinition(n, opName)));
    }

    private static String declare() {
        StringBuilder sb = new StringBuilder();
        for (String i : new String[]{"add", "sub", "mul", "sdiv"}) {
            sb.append(String.format("(declare-fun f%s ( (_ BitVec 32) (_ BitVec 32) ) (_ BitVec 32) )\n", i));
            sb.append(String.format("(declare-fun d%s ( (_ BitVec 64) (_ BitVec 64) ) (_ BitVec 64) )\n", i));
        }
        for (String i : new String[]{"eq", "lt"}) {
            sb.append(String.format("(declare-fun f%s ( (_ BitVec 32) (_ BitVec 32) ) Bool )\n", i));
            sb.append(String.format("(declare-fun d%s ( (_ BitVec 64) (_ BitVec 64) ) Bool )\n", i));
        }
        sb.append("(declare-fun uncompress ( (_ BitVec 64) ) (_ BitVec 64) )\n");
        return sb.toString();
    }

    private static <T extends ValueNode> void n2o(OperatorDescription<T> d) {
        n2o.put(d.getNodeClass(), d);
    }

    static {
        n2o(NotNode.TYPE, "bvnot");
        n2o(AndNode.TYPE, "bvand");
        n2o(OrNode.TYPE, "bvor");
        n2o(NegateNode.TYPE, "bvneg");
        arithmetic(AddNode.TYPE, "add");
        arithmetic(SubNode.TYPE, "sub");
        arithmetic(MulNode.TYPE, "mul");
        arithmetic(DivNode.TYPE, "sdiv");
        n2o(RemNode.TYPE, "bvsrem");
        n2o(ParameterNode.TYPE, null);
        n2o(InvokeNode.TYPE, null);
        n2o(ForeignCallNode.TYPE, null);
        n2o(FloatConvertNode.TYPE, null);
        n2o(ReinterpretNode.TYPE, null);
        n2o(NarrowNode.TYPE, null);
        n2o(IntegerLessThanNode.TYPE, "bvslt");
        arithmetic(FloatLessThanNode.TYPE, "lt");
        n2o(IntegerBelowNode.TYPE, "bvult");
        n2o(IntegerEqualsNode.TYPE, "=");
        arithmetic(FloatEqualsNode.TYPE, "eq");
        n2o(IntegerTestNode.TYPE, "=");
        n2o(ObjectEqualsNode.TYPE, "=");
        n2o(PointerEqualsNode.TYPE, "=");
        n2o(IntegerRemNode.TYPE, "bvurem");
        n2o(IntegerDivNode.TYPE, "bvsdiv");
        n2o(UnsignedRightShiftNode.TYPE, "bvlshr");
        n2o(LeftShiftNode.TYPE, "bvshl");
        n2o(RightShiftNode.TYPE, "bvashr");

        n2o(CompressionNode.TYPE, "uncompress");

        n2o(new OperatorDescription<>(IsNullNode.TYPE, SMTLibGeneratorPhase::defaultDeclaration, SMTLibGeneratorPhase::isNullDefinition));
        n2o(new OperatorDescription<>(AMD64AddressNode.TYPE, SMTLibGeneratorPhase::defaultDeclaration, (n) -> null));
        n2o(new OperatorDescription<>(PiArrayNode.TYPE, SMTLibGeneratorPhase::defaultDeclaration, (n) -> null));
        n2o(new OperatorDescription<>(PointerCastNode.TYPE, SMTLibGeneratorPhase::defaultDeclaration, (n) -> String.format("(assert (= %s %s))", getNodeString(n), getNodeString(n.getInput()))));
        n2o(new OperatorDescription<>(PiNode.TYPE, SMTLibGeneratorPhase::defaultDeclaration, (n) -> String.format("(assert (= %s %s))", getNodeString(n), getNodeString(n.object()))));
        n2o(new OperatorDescription<>(FixedValueAnchorNode.TYPE, SMTLibGeneratorPhase::defaultDeclaration, (n) -> String.format("(assert (= %s %s))", getNodeString(n), getNodeString(n.object()))));
        n2o(new OperatorDescription<>(ReadNode.TYPE, SMTLibGeneratorPhase::defaultDeclaration, (n) -> null));
        n2o(new OperatorDescription<>(FloatingReadNode.TYPE, SMTLibGeneratorPhase::defaultDeclaration, (n) -> null));
        n2o(new OperatorDescription<>(WordCastNode.TYPE, SMTLibGeneratorPhase::defaultDeclaration, (n) -> String.format("(assert (= %s %s))", getNodeString(n), getNodeString(n.getInput()))));
        n2o(new OperatorDescription<>(ValuePhiNode.TYPE, SMTLibGeneratorPhase::defaultDeclaration, SMTLibGeneratorPhase::phiDefinition));
        n2o(new OperatorDescription<>(ConstantNode.TYPE, SMTLibGeneratorPhase::defaultDeclaration, SMTLibGeneratorPhase::defineConstant));
    }

    private static String defaultArithmeticDefinition(ValueNode n, String op) {
        String prefix;
        Stamp stamp;
        if (n instanceof LogicNode) {
            NodeClassIterable inputs = n.inputs();
            stamp = ((ValueNode) inputs.first()).stamp();
        } else {
            stamp = n.stamp();
        }
        if (stamp instanceof IntegerStamp) {
            prefix = "bv";
        } else if (stamp instanceof FloatStamp) {
            FloatStamp fs = (FloatStamp) stamp;
            if (fs.getBits() == JavaKind.Float.getBitCount()) {
                prefix = "f";
            } else if (fs.getBits() == JavaKind.Double.getBitCount()) {
                prefix = "d";
            } else {
                throw JVMCIError.shouldNotReachHere();
            }
        } else {
            throw JVMCIError.shouldNotReachHere(n + " " + n.stamp().toString());
        }
        return defaultDefinition(prefix + op, n);
    }

    private static String defaultDefinition(String opName, ValueNode n) {
        if (opName == null) {
            return null;
        }
        StringBuilder sb = new StringBuilder();
        if (n.inputs().count() > 0) {
            int bits = getBits(n);
            sb.append("(assert (= ");
            sb.append(getNodeString(n));
            sb.append(" (");
            sb.append(opName);
            for (Node i : n.inputs()) {
                if (i instanceof ValueNode) {
                    int iBits = getBits((ValueNode) i);
                    sb.append(' ');
                    if (iBits < bits) {
                        sb.append(String.format("((_ sign_extend %d) %s)", bits - iBits, getNodeString(i)));
                    } else {
                        sb.append(getNodeString(i));
                    }
                }
            }
            sb.append(")))");
        }
        return sb.toString();
    }

    private static String isNullDefinition(IsNullNode node) {
        ValueNode value = node.getValue();
        return String.format("(assert (= %s (= %s %s)))", getNodeString(node), makeSMTConstant(0, getBits(value)), getNodeString(value));
    }

    private static String phiDefinition(ValuePhiNode n) {
        PhiConditionResolver r = new PhiConditionResolver(n);
        String res = r.resolve();
        if (res != null) {
            return String.format("(assert (= %s %s))", getNodeString(n), r.resolve());
        } else {
            return null;
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
        } else if (stamp instanceof ObjectStamp || stamp instanceof AbstractPointerStamp || stamp instanceof IllegalStamp) {
            return 64;
        } else if (stamp instanceof VoidStamp) {
            return 0;
        } else {
            throw JVMCIError.unimplemented(n.toString() + " " + n.stamp());
        }
    }

    private static String declaration(ValueNode n, int bits) {
        String type;
        if (bits == 0) {
            return null;
        } else if (bits == 1) {
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
            bitLength = getBits(n); // ((PrimitiveConstant) c).getJavaKind().getBitCount();
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
                case Illegal:
                    return null;
                default:
                    throw JVMCIError.shouldNotReachHere("Unknown PrimitiveConstant " + pc);
            }
        }
        if (bitLength > 0) {
            long value = bitLength < 64 ? bits & ((1l << bitLength) - 1) : bits;
            return String.format("(assert (= %s %s))", getNodeString(n), makeSMTConstant(value, bitLength));
        } else {
            return null;
        }
    }

    private static String makeSMTConstant(long constant, int bits) {
        return String.format("#x%0" + (bits / 4) + "x", constant);
    }

    private static JSONDumper getDumper() {
        if (dumper == null) {
            synchronized (SMTLibGeneratorPhase.class) {
                if (dumper == null) {
                    try {
                        String filename = String.format(logfileNamePattern, logfileDateFormat.format(new java.util.Date()));
                        FileOutputStream fos = new FileOutputStream(filename);
                        dumper = new JSONDumper(fos);
                        Runtime.getRuntime().addShutdownHook(new Thread() {
                            @Override
                            public void run() {
                                dumper.close();
                            }
                        });
                    } catch (IOException e) {
                        throw new RuntimeException(e);
                    }
                }
            }
        }
        return dumper;
    }

    @Override
    protected void run(StructuredGraph graph, LowTierContext context) {
        try {
            String prologue = "(set-logic QF_BV)\n" + DECLARE;
            StringBuilder declarations = new StringBuilder();
            StringBuilder definitions = new StringBuilder();
            List<ValueNode> definedNodes = new ArrayList<>();
            for (Node n : graph.getNodes()) {
                @SuppressWarnings("unchecked")
                OperatorDescription<ValueNode> d = (OperatorDescription<ValueNode>) n2o.get(n.getNodeClass());
                if (d == null && isCaptured(n)) {
                    d = defaultDescription;
                }
                if (d != null) {
                    appendCrNonNull(declarations, d.getDeclaration().apply((ValueNode) n));
                    appendCrNonNull(definitions, d.getDefinition().apply((ValueNode) n));
                    definedNodes.add((ValueNode) n);
                }
            }
            SMT smt = new SMT(prologue + declarations + definitions);
            Function<String, Node> s2n = s -> graph.getNode(Integer.parseInt(s.substring(1)));
            smt.addCheck(new ConstantFoldingCheck(s2n, n -> n instanceof ConstantNode));
            smt.addCheck(new EquivalenceCheck(n -> s2n.apply(n).toString()));
            if (!DumpSMTDir.hasDefaultValue()) {
                dumpSMT(graph, prologue, declarations, definitions);
            }
            CheckResult[] results = check(smt);
            report(graph, results);
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    private static void report(StructuredGraph graph, CheckResult[] results) {
        getDumper().dump(graph.toString(), results);
        ArrayList<CheckResult> errors = new ArrayList<>();
        for (int i = 0; i < results.length; i++) {
            CheckResult result = results[i];
            if (result.getState().equals(CheckResult.State.ERROR) || result.getState().equals(CheckResult.State.SUSPICIOUS)) {
                println("\n" + result.toString() + "\n");
                errors.add(result);
            }
        }
        if (errors.size() > 0) {
            String fileName = getFileNameForGraph(graph) + ".bgv";
            Path dumpPath = Paths.get(DumpSMTDir.hasDefaultValue() ? "." : DumpSMTDir.getValue(), fileName);
            try {

                try (BinaryGraphPrinter printer = new BinaryGraphPrinter(
                                FileChannel.open(dumpPath, StandardOpenOption.WRITE, Files.exists(dumpPath) ? StandardOpenOption.TRUNCATE_EXISTING : StandardOpenOption.CREATE_NEW))) {
                    printer.beginGroup(getFileNameForGraph(graph), "", null, -1);
                    printer.print(graph, errors.toString());
                    printer.endGroup();
                }
            } catch (IOException e) {
                throw new JVMCIError(e);
            }
        }
    }

    private static boolean isCaptured(Node n) {
        if (n instanceof ValueNode && (((ValueNode) n).stamp() instanceof IntegerStamp || ((ValueNode) n).stamp() instanceof FloatStamp)) {
            return true;
        }
        return n2o.containsKey(n.getNodeClass());
    }

    private static void dumpSMT(StructuredGraph graph, String prologue, StringBuilder declarations, StringBuilder definitions) {
        String filename = getFileNameForGraph(graph) + ".smt2";
        File outfile = new File(DumpSMTDir.getValue(), filename);
        try {
            println("Write SMT model of %s to file %s", graph.method(), outfile);
            writeToFile(outfile, prologue, declarations, definitions);
        } catch (IOException e) {
            println("Cannot write file to %s %s", outfile, e);
        }
    }

    private static String getFileNameForGraph(StructuredGraph graph) {
        if (graph.method() == null) {
            return String.format("%s_%d", graph.toString(), unknownCounter.incrementAndGet());
        } else {
            return graph.method().format("%h_%n_(%p)").replace(' ', '_').replace('/', '_');
        }
    }

    private static CheckResult[] check(SMT smt) {
        Boolector btor = getBoolector();
        if (btor != null) {
            try (BoolectorInstance bi = btor.newInstance()) {
                return bi.execute(smt);
            }
        } else {
            return new CheckResult[0];
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
    static String getNodeString(Node n) {
        return "n" + n.getId();
    }

    public static Boolector getBoolector() {
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
