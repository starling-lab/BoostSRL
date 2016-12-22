/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.ConsCell;
import edu.wisc.cs.will.FOPC.Constant;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.ListAsTerm;
import edu.wisc.cs.will.FOPC.LiteralAsTerm;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.SentenceAsTerm;
import edu.wisc.cs.will.FOPC.StringConstant;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.FOPC.visitors.SentenceVisitor;
import edu.wisc.cs.will.FOPC.visitors.TermVisitor;
import java.util.ArrayList;
import java.util.List;

/**
 *
 * @author twalker
 */
public class DefaultTermVisitor<Data> implements TermVisitor<Term, Data> {

    SentenceVisitor<Sentence, Data> sentenceVisitor;

    public DefaultTermVisitor() {
    }

    public DefaultTermVisitor(SentenceVisitor<Sentence, Data> sentenceVisitor) {
        this.sentenceVisitor = sentenceVisitor;
    }

    

    public SentenceVisitor<Sentence, Data> getSentenceVisitor() {
        return sentenceVisitor;
    }

    public void setSentenceVisitor(SentenceVisitor<Sentence, Data> sentenceVisitor) {
        this.sentenceVisitor = sentenceVisitor;
    }
    
    public Term visitFunction(Function function, Data data) {

        List<Term> newTerms = null;

        if ( function.getArity() != 0 ) {
            newTerms = new ArrayList<Term>();
            for (Term term : function.getArguments()) {
                Term newTerm = term.accept(this, data);
                newTerms.add(newTerm);
            }
        }

        return function.getStringHandler().getFunction(function, newTerms);

    }

    public Term visitConsCell(ConsCell consCell, Data data) {
        return visitFunction(consCell,data);
    }

    public Term visitVariable(Variable variable, Data data) {
        return variable;
    }

    public Term visitSentenceAsTerm(SentenceAsTerm sentenceAsTerm, Data data) {
        Term result = sentenceAsTerm;
        
        if ( sentenceVisitor != null ) {
            Sentence s = sentenceAsTerm.sentence.accept(sentenceVisitor, data);
            result = s.asTerm();
        }

        return result;
    }

    public Term visitLiteralAsTerm(LiteralAsTerm literalAsTerm, Data data) {
        Term result = literalAsTerm;

        if ( sentenceVisitor != null ) {
            Sentence s = literalAsTerm.itemBeingWrapped.accept(sentenceVisitor, data);
            result = s.asTerm();
        }

        return result;
    }

    public Term visitListAsTerm(ListAsTerm listAsTerm, Data data) {
        Term result = listAsTerm;

        if ( sentenceVisitor != null && listAsTerm.getObjects() != null) {
            List<Term> objects = new ArrayList<Term>();
            for (Term term : listAsTerm.getObjects()) {
                objects.add(term.accept(this, data));
            }
            result = listAsTerm.getStringHandler().getListAsTerm(objects);
        }

        return result;
    }

    public Term visitNumericConstant(NumericConstant numericConstant, Data data) {
        return numericConstant;
    }

    public Term visitStringConstant(StringConstant stringConstant, Data data) {
        return stringConstant;
    }

    public Term visitOtherConstant(Constant constant, Data data) {
        return constant;
    }

    public Term visitOtherTerm(Term term, Data data) {
        return term;
    }

}
