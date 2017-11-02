/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.FOPC.visitors.ElementPath;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;

/**
 *
 * @author twalker
 */
public interface PruningRule {

    /** Prunes the inputSentence for a given internal element.
     *
     *    This is used during advice processing to rewrite existing
     *    advice sentences.  In this context, the whole piece of advice
     *    will be provided at once and element might refer to an element
     *    somewhere inside of the implication.
     *
     * @param sentence The input sentence.
     * @param pathToPrune The path being pruned.
     * @param element The actual element to be pruned (located at pathToPrune).
     * @return The rewritten sentence, null if the branch should be pruned completely.
     */
    public Sentence pruneElement(HornClauseContext context, Sentence sentence, ElementPath pathToPrune, SentenceOrTerm element);
}
