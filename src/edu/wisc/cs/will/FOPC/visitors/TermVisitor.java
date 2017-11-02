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
import edu.wisc.cs.will.FOPC.SentenceAsTerm;
import edu.wisc.cs.will.FOPC.StringConstant;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Variable;

/**
 *
 * @author twalker
 */
public interface TermVisitor<Return, Data> {
    public Return visitFunction(Function function, Data data);
    public Return visitConsCell(ConsCell consCell, Data data);
    public Return visitVariable(Variable variable, Data data);
    public Return visitSentenceAsTerm(SentenceAsTerm sentenceAsTerm, Data data);
    public Return visitLiteralAsTerm(LiteralAsTerm literalAsTerm, Data data);
    public Return visitListAsTerm(ListAsTerm listAsTerm, Data data);
    public Return visitNumericConstant(NumericConstant numericConstant, Data data);
    public Return visitStringConstant(StringConstant stringConstant, Data data);
    public Return visitOtherConstant(Constant constant, Data data);
    public Return visitOtherTerm(Term term, Data data);
}
