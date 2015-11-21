package at.sanzinger.boolector;

import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class SMTModel {
    private final List<String> lines;
    private static final Pattern defPattern = Pattern.compile("\\(define-fun (\\w+) \\(\\) \\([^)]*\\) ([a-zA-Z_0-9#]+)\\)");

    public SMTModel(List<String> lines) {
        this.lines = lines;
    }

    @Override
    public String toString() {
        return lines.toString();
    }

    public Definition[] getDefinitions() {
        Definition[] defs = new Definition[lines.size() - 2];
        for (int i = 1; i < lines.size() - 1; i++) {
            String defLine = lines.get(i);
            defs[i - 1] = definitionFromLine(defLine);
        }
        return defs;
    }

    private static Definition definitionFromLine(String line) {
        Matcher m = defPattern.matcher(line);
        if (m.matches()) {
            String name = m.group(1);
            String value = m.group(2);
            return new Definition(name, value);
        } else {
            return null;
        }
    }

    public Definition getDefinition(String name) {
        for (Definition d : getDefinitions()) {
            if (d.getName().equals(name)) {
                return d;
            }
        }
        return null;
    }

    public static class Definition {
        private final String name;
        private final String value;

        public Definition(String name, String value) {
            super();
            this.name = name;
            this.value = value;
        }

        public String getName() {
            return name;
        }

        public String getValue() {
            return value;
        }

        @Override
        public String toString() {
            return String.format("(= %s %s)", name, value);
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((name == null) ? 0 : name.hashCode());
            result = prime * result + ((value == null) ? 0 : value.hashCode());
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            Definition other = (Definition) obj;
            if (name == null) {
                if (other.name != null)
                    return false;
            } else if (!name.equals(other.name))
                return false;
            if (value == null) {
                if (other.value != null)
                    return false;
            } else if (!value.equals(other.value))
                return false;
            return true;
        }

    }
}
