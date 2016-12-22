/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.visitors.DefaultFOPCVisitor;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 *
 * @author twalker
 */
public class PredicateCollector {

    private static final PredicateCollectorVisitor PREDICATE_COLLECTOR_VISITOR = new PredicateCollectorVisitor();

    public static Set<PredicateNameAndArity> collectPredicates(Sentence sentence, HornClauseContext context) {

        PredicateCollectorData data = new PredicateCollectorData(context);
        
        sentence.accept(PREDICATE_COLLECTOR_VISITOR, data);

        return data.predicates;
    }

    private static class PredicateCollectorVisitor extends DefaultFOPCVisitor<PredicateCollectorData> {

        public PredicateCollectorVisitor() {
            super(false);
        }



        @Override
        public Term visitFunction(Function function, PredicateCollectorData data) {

            PredicateNameAndArity pnaa = function.getPredicateNameAndArity();

            data.predicates.add(pnaa);

            processBackgroundRules(pnaa, data);

            if ( pnaa.getContainsCallable() ) {
                super.visitFunction(function, data);
            }

            return null;
        }

        @Override
        public Sentence visitLiteral(Literal literal, PredicateCollectorData data) {

            PredicateNameAndArity pnaa = literal.getPredicateNameAndArity();

            data.predicates.add(pnaa);

            processBackgroundRules(pnaa, data);

            if ( pnaa.getContainsCallable() ) {
                super.visitLiteral(literal, data);
            }

            return null;
        }

        private void processBackgroundRules(PredicateNameAndArity pnaa, PredicateCollectorData data) {

            if ( data.context != null && data.closedList.contains(pnaa) == false) {
                data.closedList.add(pnaa);

                List<DefiniteClause> clauses = data.context.getClausebase().getAssertions(pnaa);

                if ( clauses != null ) {
                    for (DefiniteClause clause : clauses) {
                        List<Literal> literals = clause.getDefiniteClauseBody();
                        if ( literals != null ) {
                            for (Literal literal : literals) {
                                literal.accept(this, data);
                            }
                        }
                    }
                }
            }
        }
    }

    private static class PredicateCollectorData {
        Set<PredicateNameAndArity> predicates = new HashSet<PredicateNameAndArity>();
        HornClauseContext context;
        
        // Set of background knowledge predicates that have already been expanded.
        Set<PredicateNameAndArity> closedList = new HashSet<PredicateNameAndArity>();

        public PredicateCollectorData(HornClauseContext context) {
            this.context = context;
        }


    }

    private PredicateCollector() {
    }
}
