/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.FOPC.visitors.ElementAndPath;
import edu.wisc.cs.will.FOPC.visitors.ElementFinder;
import edu.wisc.cs.will.FOPC.visitors.ElementPath;
import edu.wisc.cs.will.FOPC.visitors.ElementRemover;
import edu.wisc.cs.will.ResThmProver.DefaultProof;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.ResThmProver.Proof;
import edu.wisc.cs.will.Utils.Filter;
import java.util.Collection;
import java.util.List;

/**
 *
 * @author twalker
 */
public class PruneIfTrueRule implements PruningRule {

    PredicateNameAndArity prunedPredicate;

    DefiniteClause condition;

    public PruneIfTrueRule(PredicateNameAndArity prunedPredicate, Clause condition) {
        this.prunedPredicate = prunedPredicate;
        this.condition = condition;

        if (this.condition.getDefiniteClauseHead().getArity() != 1) {
            throw new IllegalArgumentException("Pruning rule for duplicates requires form:  prune(AddedLiteral) :- body.");
        }
    }

    public Sentence pruneElement(HornClauseContext context, Sentence sentence, ElementPath pathToPrune, SentenceOrTerm element) {

        if (element instanceof LiteralOrFunction && ((LiteralOrFunction) element).getPredicateNameAndArity().equals(prunedPredicate)) {

            BindingList bl = new BindingList();

            Term t0 = condition.getDefiniteClauseHead().getArgument(0);

            bl = Unifier.UNIFIER.unify(t0, element.asTerm(), bl);

            if (bl != null) {

                Clause c = context.getStringHandler().getClause(condition.getDefiniteClauseBody(), null);
                c = c.applyTheta(bl);

                Proof p = new DefaultProof(context, c);
                //p.getProver().setTraceLevel(2);
                BindingList newBindings = p.prove();

                if (newBindings != null) {
                    // The condition is true, so apply the bindings to the sentence remove this literal.
                    sentence = sentence.applyTheta(newBindings);
                    sentence = ElementRemover.removeElement(sentence, pathToPrune);

                }
            }
        }

        return sentence;
    }


}
