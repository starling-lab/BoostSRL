package edu.wisc.cs.will.stdAIsearch;

import java.util.List;

/**
 * <p>
 * Implements a hill climbing search.
 * </p>
 * <p>
 * Hill climbing is not the same as best-first search with beamWidth=1 (ie, no
 * downhill moves allowed), so need to handle it explicitly.
 * </p>
 * 
 * @author shavlik
 */
public class HillClimbing extends SearchStrategy {
    /**
     * Whether this search allows flat moves. The default is false, which does
     * not accept the best child if it scores the SAME as the parent.
     */
    public boolean allowFlatMoves = false;

    /**
     * Empty constructor.
     */
    public HillClimbing() {
    }

    /**
     * Sets up the given search task with a beam of width 1.
     * 
     * @see edu.wisc.cs.will.stdAIsearch.SearchStrategy#setSearchTask(edu.wisc.cs.will.stdAIsearch.StateBasedSearchTask)
     */
    public void setSearchTask(StateBasedSearchTask task) {
        super.setSearchTask(task);
        task.beamWidth = 1;
    }

    /**
     * Effectively adds the best child to the open list unless all the children
     * are worse than the parent.
     * 
     * @see edu.wisc.cs.will.stdAIsearch.SearchStrategy#addChildrenToOpenList(edu.wisc.cs.will.stdAIsearch.OpenList,
     *      java.util.List)
     */
    public <T extends SearchNode> void addChildrenToOpenList(OpenList<T> open, List<T> children) throws SearchInterrupted {
        double scoreOfParent = task.lastNodeVisited.score;

        // This is inefficient in that it will insert ALL nodes that exceed (or,
        // possibly, tie) scoreOfParent, then prune to size 1,
        // but this design avoids repeated code, and hill climbing is usually
        // quite fast so not a big deal.
        // However, it might make sense to repeat the code for scoring nodes here.        
        for (T node : children) {
            open.insertByScoreIntoOpenList(node, scoreOfParent, allowFlatMoves);
        }
    }

    /**
     * Returns "hill climbing".
     * 
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return "hill climbing";
    }
}
