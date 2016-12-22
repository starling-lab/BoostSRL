package edu.wisc.cs.will.stdAIsearch;

import java.util.List;

import edu.wisc.cs.will.Utils.Utils;

/**
 * Implements a best-first search where the next node that is examined is the
 * one with the best score.
 * 
 * @author shavlik
 */
public class BestFirstSearch extends SearchStrategy {
    /**
     * Default constructor. Does nothing.
     */
    public BestFirstSearch() {
    }

    /**
     * @see edu.wisc.cs.will.stdAIsearch.SearchStrategy#addChildrenToOpenList(edu.wisc.cs.will.stdAIsearch.OpenList, java.util.List)
     */
    @Override
    public <T extends SearchNode> void addChildrenToOpenList(OpenList<T> open, List<T> children) throws SearchInterrupted {
        int counter = 0;
        int number  = 0;
        
        if (children != null) {
            if (task.verbosity > 2) {
            	number = children.size();
                Utils.println("  Adding " + number + " children to OPEN.");
            }
            for (T node : children) {
                if (task.verbosity > 2) {
                    Utils.println("    |OPEN|= " + open.size() + "  Score and insert (" + (counter++) + " of " + number + "): '" + node + "'.");
                }
                // For best-first search, insert according to score.  (HIGHER scores are better, and ties go to the "older" node, ie the one already in OPEN.)
                open.insertByScoreIntoOpenList(node);
            }
        }
    }
}
