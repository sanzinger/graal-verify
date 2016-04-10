package at.sanzinger.graal.verify.gen;

import java.util.function.Function;

import com.oracle.graal.graph.Node;
import com.oracle.graal.graph.NodeClass;

public final class OperatorDescription<T extends Node> {
    public static final int UNBOUNDED_INPUTS = -1;
    public static final long FLAG_EQUIVALENT = 0x1; // The node is an identity function (PiNode for
                                                    // example)
    private final NodeClass<T> nodeClass;
    private final long flags;
    private final Function<T, String> declaration;
    private final Function<T, String> definition;

    public OperatorDescription(NodeClass<T> nodeClass, Function<T, String> declaration, Function<T, String> definition) {
        this(nodeClass, declaration, definition, 0);
    }

    public OperatorDescription(NodeClass<T> nodeClass, Function<T, String> declaration, Function<T, String> definition, long flags) {
        super();
        this.nodeClass = nodeClass;
        this.declaration = declaration;
        this.definition = definition;
        this.flags = flags;
    }

    public NodeClass<T> getNodeClass() {
        return nodeClass;
    }

    public Function<T, String> getDeclaration() {
        return declaration;
    }

    public Function<T, String> getDefinition() {
        return definition;
    }

    public long getFlags() {
        return flags;
    }

    @Override
    public String toString() {
        return String.format("OperatorDescription for %s ", nodeClass);
    }
}