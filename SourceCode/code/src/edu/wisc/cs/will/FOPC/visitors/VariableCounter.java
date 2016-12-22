package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Variable;
import java.util.HashMap;
import java.util.Map;

public class VariableCounter  {

    private static final VariableCounterVisitor VARIABLE_COUNTER_VISITOR = new VariableCounterVisitor();

    public static Map<Variable, Integer> countVariables(Sentence sentence) {
        Map<Variable, Integer> map = new HashMap<Variable, Integer>();
        sentence.accept(VARIABLE_COUNTER_VISITOR, map);
        return map;
    }

    public static Map<Variable, Integer> countVariables(Term term) {
        Map<Variable, Integer> map = new HashMap<Variable, Integer>();
        term.accept(VARIABLE_COUNTER_VISITOR, map);
        return map;
    }

    private static class VariableCounterVisitor extends DefaultFOPCVisitor<Map<Variable, Integer>> {

        public VariableCounterVisitor() {
            super(false);
        }


        @Override
        public Term visitVariable(Variable variable, Map<Variable, Integer> counters) {
        Integer count = counters.get(variable);
        if (count == null) {
            count = 1;
        }
        else {
            count++;
        }
        counters.put(variable, count);
        return null;
    }
    }

    private VariableCounter() {
    }
}
