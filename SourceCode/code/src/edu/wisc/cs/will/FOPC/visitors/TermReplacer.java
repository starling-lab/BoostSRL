/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.Constant;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.SentenceAsTerm;
import edu.wisc.cs.will.FOPC.StringConstant;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.FOPC.visitors.DefaultFOPCVisitor;
import java.util.Map;

/** Visitor that replaces Terms in a Sentence with other Terms.
 *
 * @author twalker
 */
public class TermReplacer extends DefaultFOPCVisitor<Map<? extends Term, ? extends Term>> {

    private static final ReplaceTermsVisitor REPLACE_TERMS_VISITOR = new ReplaceTermsVisitor();

    public TermReplacer() {
    }

    public static <T extends Sentence> T replaceTerms(T sentence, Map<? extends Term, ? extends Term> oldToNewMap) {
        return (T)sentence.accept(REPLACE_TERMS_VISITOR, oldToNewMap);
    }

    public static Term replaceTerms(Term term, Map<? extends Term, ? extends Term> oldToNewMap) {
        return term.accept(REPLACE_TERMS_VISITOR, oldToNewMap);
    }

    private static class ReplaceTermsVisitor extends DefaultFOPCVisitor<Map<? extends Term, ? extends Term>> {

        @Override
        public Term visitFunction(Function term, Map<? extends Term, ? extends Term> data) {

            Term result = data.get(term);

            if (result == null) {
                result = super.visitFunction(term,data);
            }

            return result;
        }

        @Override
        public Term visitNumericConstant(NumericConstant term, Map<? extends Term, ? extends Term> data) {
            Term result = data.get(term);

            if (result == null) {
                result = super.visitNumericConstant(term,data);
            }

            return result;
        }

        @Override
        public Term visitStringConstant(StringConstant term, Map<? extends Term, ? extends Term> data) {
            Term result = data.get(term);

            if (result == null) {
                result = super.visitStringConstant(term,data);
            }

            return result;
        }

        @Override
        public Term visitOtherConstant(Constant term, Map<? extends Term, ? extends Term> data) {
            Term result = data.get(term);

            if (result == null) {
                result = super.visitOtherConstant(term,data);
            }

            return result;
        }

        @Override
        public Term visitOtherTerm(Term term, Map<? extends Term, ? extends Term> data) {
            Term result = data.get(term);

            if (result == null) {
                result = super.visitOtherTerm(term,data);
            }

            return result;
        }

        @Override
        public Term visitSentenceAsTerm(SentenceAsTerm term, Map<? extends Term, ? extends Term> data) {
            Term result = data.get(term);

            if (result == null) {
                result = super.visitSentenceAsTerm(term,data);
            }

            return result;
        }

        @Override
        public Term visitVariable(Variable term, Map<? extends Term, ? extends Term> data) {
            Term result = data.get(term);

            if (result == null) {
                result = super.visitVariable(term,data);
            }

            return result;
        }


    }
}
