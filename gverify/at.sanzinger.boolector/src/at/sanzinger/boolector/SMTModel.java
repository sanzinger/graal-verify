package at.sanzinger.boolector;

import java.util.ArrayList;
import java.util.List;

public class SMTModel {
    private final List<String> lines;

    public SMTModel(List<String> lines) {
        this.lines = lines;
    }

    @Override
    public String toString() {
        return lines.toString();
    }

    public Definition[] getDefinitions() {
        List<Definition> defs = new ArrayList<>(lines.size());
        for (String defLine : lines) {
            Definition def = definitionFromLine(defLine);
            if (def != null) {
                defs.add(def);
            }
        }
        return defs.toArray(new Definition[0]);
    }

    private static Definition definitionFromLine(String line) {
        // we're looking for (define-fun n87 () (_ BitVec 8) #b00000000)
        int idx = 0;
        int len = line.length();
        while (idx < len && line.charAt(idx++) == ' ') {
            // ignore leading whitespace
        }
        idx--;
        final String defineFun = "(define-fun ";
        if (line.startsWith(defineFun, idx) && line.endsWith(")")) {
            int nameStart = idx + defineFun.length();
            int nameEnd = line.indexOf(' ', nameStart + 1);
            String name = line.substring(nameStart, nameEnd);
            int valueStart = line.lastIndexOf(' ') + 1;
            String value = line.substring(valueStart, line.length() - 1);
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
