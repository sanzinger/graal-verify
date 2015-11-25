package at.sanzinger.graal.verify.gen;

import java.util.function.Function;

import com.oracle.graal.graph.Node;
import com.oracle.graal.graph.NodeClass;

public final class OperatorDescription<T extends Node> {
    public static final int UNBOUNDED_INPUTS = -1;
    private final NodeClass<T> nodeClass;
    private final Function<T, String> declaration;
    private final Function<T, String> definition;

    public OperatorDescription(NodeClass<T> nodeClass, Function<T, String> declaration, Function<T, String> definition) {
        super();
        this.nodeClass = nodeClass;
        this.declaration = declaration;
        this.definition = definition;
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

    @Override
    public String toString() {
        return String.format("OperatorDescription for %s ", nodeClass);
    }
}