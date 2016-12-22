/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.ConnectedSentence;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.ListAsTerm;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.QuantifiedSentence;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.SentenceAsTerm;
import edu.wisc.cs.will.FOPC.StringConstant;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Variable;

/**
 *
 * @author twalker
 */
public class ElementRemover {

    private static final ElementRemoverVisitor ELEMENT_REMOVER_VISITOR = new ElementRemoverVisitor();

    public static Sentence removeElement(Sentence sentence, ElementPath path) {
        ElementRemoverData data = new ElementRemoverData(path);

        return sentence.accept(ELEMENT_REMOVER_VISITOR, data);
    }

    public static Term removeElement(Term term, ElementPath path) {
        ElementRemoverData data = new ElementRemoverData(path);

        return term.accept(ELEMENT_REMOVER_VISITOR, data);
    }

    private static class ElementRemoverData extends ElementPositionVisitor.ElementPositionData {
        ElementPath pathToRemove;

        public ElementRemoverData(ElementPath pathToRemove) {
            this.pathToRemove = pathToRemove;
        }
    }

    private static class ElementRemoverVisitor extends ElementPositionVisitor<ElementRemoverData>{

        @Override
        public Clause visitClause(Clause clause, ElementRemoverData data) {

            if ( data.pathToRemove != null && data.pathToRemove.equals(data.getCurrentPosition()) ) {
                return null;
            }

            return super.visitClause(clause, data);
        }

        @Override
        public ConnectedSentence visitConnectedSentence(ConnectedSentence sentence, ElementRemoverData data) {
            if ( data.pathToRemove != null && data.pathToRemove.equals(data.getCurrentPosition()) ) {
                return null;
            }

            return super.visitConnectedSentence(sentence, data);
        }

        @Override
        public Term visitFunction(Function function, ElementRemoverData data) {

            if ( data.pathToRemove != null && data.pathToRemove.equals(data.getCurrentPosition()) ) {
                return null;
            }

            return super.visitFunction(function, data);
        }

        @Override
        public Term visitListAsTerm(ListAsTerm listAsTerm, ElementRemoverData data) {

            if ( data.pathToRemove != null && data.pathToRemove.equals(data.getCurrentPosition()) ) {
                return null;
            }

            return super.visitListAsTerm(listAsTerm, data);
        }

        @Override
        public Literal visitLiteral(Literal literal, ElementRemoverData data) {

            if ( data.pathToRemove != null && data.pathToRemove.equals(data.getCurrentPosition()) ) {
                return null;
            }

            return super.visitLiteral(literal, data);
        }

        @Override
        public Term visitNumericConstant(NumericConstant numericConstant, ElementRemoverData data) {

            if ( data.pathToRemove != null && data.pathToRemove.equals(data.getCurrentPosition()) ) {
                return null;
            }

            return super.visitNumericConstant(numericConstant, data);
        }

        @Override
        public QuantifiedSentence visitQuantifiedSentence(QuantifiedSentence sentence, ElementRemoverData data) {

            if ( data.pathToRemove != null && data.pathToRemove.equals(data.getCurrentPosition()) ) {
                return null;
            }

            return super.visitQuantifiedSentence(sentence, data);
        }

        @Override
        public Term visitSentenceAsTerm(SentenceAsTerm sentenceAsTerm, ElementRemoverData data) {

            if ( data.pathToRemove != null && data.pathToRemove.equals(data.getCurrentPosition()) ) {
                return null;
            }

            return super.visitSentenceAsTerm(sentenceAsTerm, data);
        }

        @Override
        public Term visitStringConstant(StringConstant stringConstant, ElementRemoverData data) {

            if ( data.pathToRemove != null && data.pathToRemove.equals(data.getCurrentPosition()) ) {
                return null;
            }

            return super.visitStringConstant(stringConstant, data);
        }

        @Override
        public Term visitVariable(Variable variable, ElementRemoverData data) {

            if ( data.pathToRemove != null && data.pathToRemove.equals(data.getCurrentPosition()) ) {
                return null;
            }
            
            return super.visitVariable(variable, data);
        }

    }

    private ElementRemover() {
    }
}
