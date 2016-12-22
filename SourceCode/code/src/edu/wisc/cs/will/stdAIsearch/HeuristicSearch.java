package edu.wisc.cs.will.stdAIsearch;

/**
 * The abstract superclass of searches using heuristics.
 * 
 * @author shavlik
 */
public abstract class HeuristicSearch extends SearchStrategy {
    /**
     * Empty constructor.
     */
    public HeuristicSearch() {
    }

    /**
     * Returns "heuristic search".
     * 
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return "heuristic search";
    }
}
