/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.PruningRule;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import java.util.List;

/**
 *
 * @author twalker
 */
public class SentencePruner {

    private static final SentencePrunerListener SENTENCE_PRUNER_LISTENER = new SentencePrunerListener();

    public static Sentence pruneSentence(HornClauseContext context, Sentence sentence, List<? extends PruningRule> rules) {

        ElementPositionVisitor<SentencePrunerData> v = new ElementPositionVisitor<SentencePrunerData>(SENTENCE_PRUNER_LISTENER);

        Sentence newSentence = null;

        while (true) {

            SentencePrunerData data = new SentencePrunerData(context, rules, sentence);

            try {
                sentence.accept(v, data);
            }
            catch (StopVisitingException e) {
                
            }

            newSentence = data.sentence;


            if (newSentence == null || sentence == newSentence) {
                break;
            }
            else {
                sentence = newSentence;
            }
        }

        return sentence;

    }

    private static class SentencePrunerData extends ElementPositionVisitor.ElementPositionData {

        HornClauseContext context;

        List<? extends PruningRule> rules;

        Sentence sentence;

        public SentencePrunerData(HornClauseContext context, List<? extends PruningRule> rules, Sentence sentence) {
            this.context = context;
            this.rules = rules;
            this.sentence = sentence;
        }

        public HornClauseContext getContext() {
            return context;
        }

        public void setContext(HornClauseContext context) {
            this.context = context;
        }

        public List<? extends PruningRule> getRules() {
            return rules;
        }

        public void setRules(List<PruningRule> rules) {
            this.rules = rules;
        }
    }

    private static class SentencePrunerListener implements ElementPositionListener<SentencePrunerData> {

        public boolean visiting(Sentence s, SentencePrunerData data) {

            for (PruningRule pruningRule : data.rules) {
                Sentence newSentence = pruningRule.pruneElement(data.context, data.sentence, data.getCurrentPosition(), s);
                if (newSentence != data.sentence) {
                    data.sentence = newSentence;
                    throw new StopVisitingException();
                }
            }

            return true;
        }

        public boolean visiting(Term t, SentencePrunerData data) {
            for (PruningRule pruningRule : data.rules) {
                Sentence newSentence = pruningRule.pruneElement(data.context, data.sentence, data.getCurrentPosition(), t);
                if (newSentence != data.sentence) {
                    data.sentence = newSentence;
                    throw new StopVisitingException();
                }
            }

            return true;
        }
    }

    private SentencePruner() {
    }
}
