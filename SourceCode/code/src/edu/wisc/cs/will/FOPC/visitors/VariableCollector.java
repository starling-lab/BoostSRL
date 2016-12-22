package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Variable;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class VariableCollector {

    private static final VariableCollectorVisitor VARIABLE_COOLLECTOR_VISITOR = new VariableCollectorVisitor();

    public static Set<Variable> collectVariables(Sentence sentence, Set<Variable> set) {
        if (set == null) {
            set = new HashSet<Variable>();
        }
        sentence.accept(VARIABLE_COOLLECTOR_VISITOR, set);
        return set;
    }

    public static Set<Variable> collectVariables(Term term, Set<Variable> set) {
        if (set == null) {
            set = new HashSet<Variable>();
        }
        term.accept(VARIABLE_COOLLECTOR_VISITOR, set);
        return set;
    }

    private static class VariableCollectorVisitor extends DefaultFOPCVisitor<Set<Variable>> {

        public VariableCollectorVisitor() {
            super(false);
        }

        @Override
        public Term visitVariable(Variable variable, Set<Variable> counters) {
            counters.add(variable);
            return null;
        }
    }

    private VariableCollector() {
    }
}
