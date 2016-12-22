/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.ConnectedSentence;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.QuantifiedSentence;
import edu.wisc.cs.will.FOPC.Sentence;

/**
 *
 * @author twalker
 */
public interface SentenceVisitor<Return, Data> {
    public Return visitOtherSentence(Sentence otherSentence, Data data);
    public Return visitConnectedSentence(ConnectedSentence sentence, Data data);
    public Return visitQuantifiedSentence(QuantifiedSentence sentence, Data data);
    public Return visitClause(Clause clause, Data data);
    public Return visitLiteral(Literal literal, Data data);
}
