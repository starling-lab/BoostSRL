/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;

/**
 *
 * @author twalker
 */
public class DoubleNegationByFailureRemover {

    private static final int debugLevel = 0;

    private static final RemoveNegationByFailureVisitor REMOVE_NEGATION_BY_FAILURE_VISITOR = new RemoveNegationByFailureVisitor();

    public static Sentence removeDoubleNegationByFailure(Sentence sentence) {

        Sentence result = sentence.accept(REMOVE_NEGATION_BY_FAILURE_VISITOR, null);

        return result;
    }


    public static class RemoveNegationByFailureVisitor extends DefaultFOPCVisitor<Void> {

        private RemoveNegationByFailureVisitor() {
        }

        @Override
        public Term visitFunction(Function function, Void data) {
            Term result = super.visitFunction(function, data);
            if (result instanceof Function) {
                Function f = (Function) result;
                if ( f.getStringHandler().isNegationByFailure(f) ) {
                    Clause contents = f.getStringHandler().getNegationByFailureContents(f);
                    if ( function.getStringHandler().isNegationByFailure(contents)) {
                        result = function.getStringHandler().getNegationByFailureContents(contents).asTerm();
                    }
                }
            }

            return result;
        }

        @Override
        public Sentence visitLiteral(Literal literal, Void data) {
            Sentence result = super.visitLiteral(literal, data);
            if (result instanceof Literal) {
                Literal f = (Literal) result;
                if ( f.getStringHandler().isNegationByFailure(f) ) {
                    Clause contents = f.getStringHandler().getNegationByFailureContents(f);
                    if ( literal.getStringHandler().isNegationByFailure(contents)) {
                        result = literal.getStringHandler().getNegationByFailureContents(contents);
                    }
                }
            }

            return result;
        }
    }

    private DoubleNegationByFailureRemover() {
    }
}
