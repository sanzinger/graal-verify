package at.sanzinger.graal.verify.gen;

import java.util.function.Function;

import com.oracle.graal.graph.Node;

public final class OperatorDescription<T extends Node> {
    public static final int UNBOUNDED_INPUTS = -1;
    private final int inputs;
    private final Function<T, String> declaration;
    private final Function<T, String> definition;

    public OperatorDescription(int inputs, Function<T, String> declaration, Function<T, String> definition) {
        super();
        assert inputs == UNBOUNDED_INPUTS || inputs >= 0;
        this.inputs = inputs;
        this.declaration = declaration;
        this.definition = definition;
    }

    public boolean isUnary() {
        return inputs == 1;
    }

    public boolean isBinary() {
        return inputs == 2;
    }

    public int getInputs() {
        return inputs;
    }

    public Function<T, String> getDeclaration() {
        return declaration;
    }

    public Function<T, String> getDefinition() {
        return definition;
    }
}