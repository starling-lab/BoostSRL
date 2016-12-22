/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.visitors.DefaultFOPCVisitor;
import java.util.ArrayList;
import java.util.List;

/**
 *
 * @author twalker
 */
public class DefiniteClauseCostAggregator {

    private static final PredicateCollectorVisitor PREDICATE_COLLECTOR_VISITOR = new PredicateCollectorVisitor();

    public static final DefiniteClauseCostAggregator PREDICATE_COST_AGGREGATOR = new DefiniteClauseCostAggregator();

    public enum AggregationMode {

        MINIMUM,
        MEAN,
        MAXIMUM

    }

    private DefiniteClauseCostAggregator() {
    }

    public double getAggregateCost(AggregationMode mode, Clause clause) {

        if (clause.isDefiniteClause() == false) {
            throw new IllegalArgumentException("Clause must be definite clause.  Got: " + clause + ".");
        }

        List<PredicateNameAndArity> predicates = new ArrayList<PredicateNameAndArity>();

        for (Literal literal : clause.getDefiniteClauseBody()) {
            literal.accept(PREDICATE_COLLECTOR_VISITOR, predicates);
        }

        double value = 0;

        switch (mode) {
            case MAXIMUM:
                value = Double.MIN_VALUE;
                break;
            case MINIMUM:
                value = Double.MAX_VALUE;
                break;
            case MEAN:
                value = 0;
                break;
        }

        if (!predicates.isEmpty()) {
            for (PredicateNameAndArity pnaa : predicates) {

                double cost = pnaa.getPredicateName().getCost( pnaa.getArity() );
                switch (mode) {
                    case MAXIMUM:
                        value = Math.max(value, cost);
                        break;
                    case MINIMUM:
                        value = Math.min(value, cost);
                        break;
                    case MEAN:
                        value += cost / predicates.size();
                        break;
                }
            }
        }

        return value;
    }

    private static class PredicateCollectorVisitor extends DefaultFOPCVisitor<List<PredicateNameAndArity>> {

        @Override
        public Term visitFunction(Function function, List<PredicateNameAndArity> data) {
            data.add(function.getPredicateNameAndArity());
            return null;
        }

        @Override
        public Sentence visitLiteral(Literal literal, List<PredicateNameAndArity> data) {
            data.add(literal.getPredicateNameAndArity());
            return null;
        }
    }
}
