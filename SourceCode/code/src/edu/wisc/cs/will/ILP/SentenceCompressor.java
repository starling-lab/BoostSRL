package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.ConnectedSentence;
import edu.wisc.cs.will.FOPC.ConnectiveName;
import edu.wisc.cs.will.FOPC.visitors.DefaultFOPCVisitor;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.Sentence;
import java.util.ArrayList;
import java.util.List;

/** Sentence Visitor that compresses Clause joined via AND connectives into a single clause.
 * 
 * @author twalker
 */
public class SentenceCompressor extends DefaultFOPCVisitor<Void> {

    private static final SentenceCompressorVisitor SENTENCE_COMPRESSOR_VISITOR = new SentenceCompressorVisitor();

    private SentenceCompressor() {
    }

    public static Sentence getCompressedSentence(Sentence sentence) {
        return sentence.accept(SENTENCE_COMPRESSOR_VISITOR, null);
    }

    private static class SentenceCompressorVisitor extends DefaultFOPCVisitor<Void> {

        private SentenceCompressorVisitor() {
        }

        
        @Override
        public Sentence visitConnectedSentence(ConnectedSentence sentence, Void data) {
            Sentence result = sentence;
            if (ConnectiveName.isaAND(sentence.getConnective().name)) {

                Sentence newA = sentence.getSentenceA().accept(this, data);
                Sentence newB = sentence.getSentenceB().accept(this, data);

                if ((newA instanceof Clause || newA instanceof Literal) && (newB instanceof Clause || newB instanceof Literal)) {

                    List<Literal> posLits = new ArrayList<Literal>();
                    List<Literal> negLits = new ArrayList<Literal>();

                    if (newA instanceof Clause) {
                        Clause clause = (Clause) newA;
                        if (clause.getNegLiteralCount() > 0) {
                            negLits.addAll(clause.getNegativeLiterals());
                        }
                        if (clause.getPosLiteralCount() > 0) {
                            posLits.addAll(clause.getPositiveLiterals());
                        }
                    }
                    else if (newA instanceof Literal) {
                        Literal literal = (Literal) newA;
                        posLits.add(literal);
                    }

                    if (newB instanceof Clause) {
                        Clause clause = (Clause) newB;
                        if (clause.getNegLiteralCount() > 0) {
                            negLits.addAll(clause.getNegativeLiterals());
                        }
                        if (clause.getPosLiteralCount() > 0) {
                            posLits.addAll(clause.getPositiveLiterals());
                        }
                    }
                    else if (newB instanceof Literal) {
                        Literal literal = (Literal) newB;
                        posLits.add(literal);
                    }

                    result = sentence.getStringHandler().getClause(posLits, negLits);

                }
                else {
                    result = sentence.getStringHandler().getConnectedSentence(newA, sentence.getConnective(), newB);
                }
            }
            else {
                result = super.visitConnectedSentence(sentence, data);
            }
            return result;
        }
    }
}
