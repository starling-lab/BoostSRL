/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.ConnectedSentence;
import edu.wisc.cs.will.FOPC.ConnectiveName;
import edu.wisc.cs.will.FOPC.ConsCell;
import edu.wisc.cs.will.FOPC.Constant;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.ListAsTerm;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.LiteralAsTerm;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.QuantifiedSentence;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.SentenceAsTerm;
import edu.wisc.cs.will.FOPC.StringConstant;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Variable;
import java.util.ArrayList;
import java.util.List;
 
/**
 *
 * @author twalker
 */
public class DefaultFOPCVisitor<Data> implements SentenceVisitor<Sentence, Data>, TermVisitor<Term, Data> {

    /** Indicates that a sentence should be constructed as we visit the Sentence/Terms.
     *
     * If false, all default visitor methods will return null and no Sentence/Terms will be constructed.
     *
     * Note: Even if this is true, an overriden method can return null to indicate that the caller should
     * not construct a Sentence/Term from that result.
     */
    private boolean buildSentence = true;

    public DefaultFOPCVisitor() {
    }

    public DefaultFOPCVisitor(boolean buildSentence) {
        this.buildSentence = buildSentence;
    }

    public Sentence visitOtherSentence(Sentence otherSentence, Data data) {
        return buildSentence == false ? null : otherSentence;
    } 

    public Sentence visitConnectedSentence(ConnectedSentence sentence, Data data) {
        Sentence a = sentence.getSentenceA() == null ? null : sentence.getSentenceA().accept(this, data);
        Sentence b = sentence.getSentenceB() == null ? null : sentence.getSentenceB().accept(this, data);

        return buildSentence == false ? null : getCombinedConnectedSentence(sentence, a, b);
    }

    /** Performs some "smart" recombining of connected sentences.
     *
     * This method attempts to handle cases where the subsentence visits return null.  In many
     * cases, specially handling will be required to maintain the semantics of the returned
     * sentence, but this provided a simple why to handle null values.
     *
     * @param originalSentence
     * @param newA
     * @param newB
     * @return
     */
    public static Sentence getCombinedConnectedSentence(ConnectedSentence originalSentence, Sentence newA, Sentence newB) {

        Sentence result = null;

        if (ConnectiveName.isaNOT(originalSentence.getConnective().name)) {
            if (newB == null) {
                newB = originalSentence.getStringHandler().trueLiteral;
            }
            result = originalSentence.getStringHandler().getConnectedSentence(originalSentence.getConnective(), newB);
        }
        else {
            if (newA == null && newB == null) {
                result = null;
            }
            else if (newB == null) {
                result = newA;
            }
            else if (newA == null) {
                result = newB;
            }
            else {
                result = originalSentence.getStringHandler().getConnectedSentence(newA, originalSentence.getConnective(), newB);
            }
        }

        return result;

    }

    public Sentence visitQuantifiedSentence(QuantifiedSentence sentence, Data data) {
        Sentence newBody = sentence.body.accept(this, data);

        Sentence result = null;

        if (newBody != null) {
            result = sentence.replaceVariablesAndBody(sentence.variables, newBody);
        }

        return result;
    }

    public Sentence visitClause(Clause clause, Data data) {
        List<Literal> positiveLits = null;
        List<Literal> negativeLits = null;

        if (clause.getPosLiteralCount() > 0) {
            if (buildSentence) {
                positiveLits = new ArrayList<Literal>();
            }
            for (Literal literal : clause.getPositiveLiterals()) {
                Sentence newStuff = literal.accept(this, data);
                if (buildSentence && newStuff != null) {
                    positiveLits.addAll(newStuff.asClause().getPositiveLiterals());
                }
            }
        }

        if (clause.getNegLiteralCount() > 0) {
            if (buildSentence) {
                negativeLits = new ArrayList<Literal>();
            }
            for (Literal literal : clause.getNegativeLiterals()) {
                Sentence newStuff = literal.accept(this, data);
                if (buildSentence && newStuff != null) {
                    negativeLits.addAll(newStuff.asClause().getPositiveLiterals());
                }
            }
        }

        return buildSentence == false ? null : clause.getStringHandler().getClause(positiveLits, negativeLits);
    }

    /** Visit the literal.
     *
     * The DefaultFOPCVisitor assumes that the return value of visitLiteral
     * is either a Literal, a Clause with all positive literals, or null.
     *
     * Children can return other sentence forms, but should be aware that
     * unexpected behavior will result.
     *
     * @param literal
     * @param data
     * @return
     */
    public Sentence visitLiteral(Literal literal, Data data) {

        Literal result = literal;

        List<Term> newTerms = null;

        if (literal.getArity() != 0) {
            if (buildSentence) {
                newTerms = new ArrayList<Term>();
            }
            
            for (Term term : literal.getArguments()) {
                Term newTerm = term.accept(this, data);
                if (buildSentence) {
                    newTerms.add(newTerm);
                }
            }

            if (buildSentence) {
                result = literal.getStringHandler().getLiteral(literal, newTerms);
            }
        }

        return buildSentence == false ? null : result;
    }

    public Term visitFunction(Function function, Data data) {

        Function result = function;

        List<Term> newTerms = null;

        if (function.getArity() != 0) {
            if (buildSentence) {
                newTerms = new ArrayList<Term>();
            }
            for (Term term : function.getArguments()) {
                Term newTerm = term.accept(this, data);
                if (buildSentence) {
                    newTerms.add(newTerm);
                }
            }

            if (buildSentence) {
                result = function.getStringHandler().getFunction(function, newTerms);
            }
        }

        return buildSentence == false ? null : result;

    }

    public Term visitConsCell(ConsCell consCell, Data data) {
        Term result = null; // Don't build a new consCell if all of the accepts return null.

        if (consCell.isNil()) {
            result = consCell;
        }
        else {
            Term currentPosition = consCell;
            ConsCell tail = null;

            while (currentPosition != null) {
                if (currentPosition instanceof ConsCell) {
                    ConsCell cellPosition = (ConsCell) currentPosition;

                    if (cellPosition.isNil()) {
                        currentPosition = null; // We will fall out of the loop when we see a nil.
                    }
                    else {
                        // Call accept on the car() of the cellPosition cell.
                        Term newCar = cellPosition.car().accept(this, data);

                        if (buildSentence && newCar != null) {

                            ConsCell newCell = consCell.getStringHandler().getConsCell(newCar, consCell.getStringHandler().getNil(), null);
                            if (tail == null) {
                                // If we haven't starting constructing the cell chain, so record this first cell as the result.
                                result = newCell;
                            }
                            else {
                                // We are extending the tail, so set the cdr of tail and update tail to this.
                                tail.setCdr(newCell);
                            }
                            tail = newCell;
                        }

                        currentPosition = cellPosition.cdr();
                    }
                }
                else {
                    // The currentPosition is not a consCell.
                    // It is probably a variable since that is the only thing that
                    // should occur in a cdr position.
                    Term newTerm = currentPosition.accept(this, data);
                    if (buildSentence && newTerm != null && tail != null) {
                        // We are extending the tail, so set the cdr of tail.

                        // If tail is null here...hmm...that shouldn't happen
                        // since we had a consCell coming in so the first iteration
                        // of the while loop had to create a tail.
                        tail.setCdr(newTerm);
                    }

                    // Now just drop out of the loop by setting currentPosition to null;
                    currentPosition = null;
                }
            }
        }

        return buildSentence == false ? null : result;
    }

    public Term visitVariable(Variable variable, Data data) {
        return buildSentence == false ? null : variable;
    }

    public Term visitSentenceAsTerm(SentenceAsTerm sentenceAsTerm, Data data) {
        Term result = sentenceAsTerm;


        Sentence s = sentenceAsTerm.sentence.accept(this, data);

        if (buildSentence && s != null) {
            result = s.asTerm();
        }


        return buildSentence == false ? null : result;
    }

    public Term visitLiteralAsTerm(LiteralAsTerm literalAsTerm, Data data) {
        Term result = literalAsTerm;

        Sentence s = literalAsTerm.itemBeingWrapped.accept(this, data);

        if (buildSentence && s != null) {
            result = s.asTerm();
        }

        return buildSentence == false ? null : result;
    }

    public Term visitListAsTerm(ListAsTerm listAsTerm, Data data) {
        Term result = listAsTerm;

        if (listAsTerm.getObjects() != null) {
            List<Term> objects = null;

            if (buildSentence) {
                objects = new ArrayList<Term>();
            }
            for (Term term : listAsTerm.getObjects()) {
                Term newTerm = term.accept(this, data);
                if (buildSentence && newTerm != null) {
                    objects.add(newTerm);
                }
            }
            if (buildSentence) {
                result = listAsTerm.getStringHandler().getListAsTerm(objects);
            }
        }

        return buildSentence == false ? null : result;
    }

    public Term visitNumericConstant(NumericConstant numericConstant, Data data) {
        return buildSentence == false ? null : numericConstant;
    }

    public Term visitStringConstant(StringConstant stringConstant, Data data) {
        return buildSentence == false ? null : stringConstant;
    }

    public Term visitOtherConstant(Constant constant, Data data) {
        return buildSentence == false ? null : constant;
    }

    public Term visitOtherTerm(Term term, Data data) {
        return buildSentence == false ? null : term;
    }
}
