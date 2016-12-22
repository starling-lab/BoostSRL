package edu.wisc.cs.will.stdAIsearch;

import java.util.List;

/**
 * A place-holder superclass for different types of searches.
 * 
 * @author shavlik
 */
public abstract class SearchStrategy {
    /**
     * The specification for a state-based search task.
     */
    protected StateBasedSearchTask task;

    /**
     * Default constructor. Does nothing.
     */
    public SearchStrategy() {
    }

    /**
     * Constructs a search strategy that will carry out the given search task.
     * 
     * @param task
     *                The specification of the search task.
     */
    public SearchStrategy(StateBasedSearchTask task) {
        this.task = task;
    }

    /**
     * Sets the search task that this search works on.
     * 
     * @param task
     *                The new specification of the search task.
     */
    public void setSearchTask(StateBasedSearchTask task) {
        this.task = task;
    }

    /**
     * Adds more states to the open list of states.
     * 
     * @param open
     *                The open list of states waiting to be examined.
     * @param children
     *                The states to add to the open list.
     * @throws SearchInterrupted
     *                 If the search is interrupted.
     */
    public abstract <T extends SearchNode> void addChildrenToOpenList(OpenList<T> open, List<T> children) throws SearchInterrupted;

    /**
     * Clears any information this search has saved while conducting its task.
     * 
     * @param insideIterativeDeepening
     *                Whether the search is currently doing iterative deepening.
     */
    public void clearAnySavedInformation(boolean insideIterativeDeepening) {
        return; // Don't make this abstract since it is unlikely that a search strategy will have something that needs resetting.
    }
}
