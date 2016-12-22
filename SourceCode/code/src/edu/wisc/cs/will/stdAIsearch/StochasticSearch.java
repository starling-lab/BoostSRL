package edu.wisc.cs.will.stdAIsearch;

/**
 * <p>
 * Implements a stochastic search.
 * </p>
 * <p>
 * Possibly one might want a stochastic, non-heuristic search (and hence should
 * use Java's interfaces), but that should be rare (and the score can always be
 * depth or -depth, to get depth-first or breadth-first search).
 * </p>
 * 
 * @author shavlik
 */
public abstract class StochasticSearch extends HeuristicSearch {
    /**
     * Empty constructor.
     */
    public StochasticSearch() {
    }

    /**
     * Returns "stochastic search".
     * 
     * @see edu.wisc.cs.will.stdAIsearch.HeuristicSearch#toString()
     */
    public String toString() {
        return "stochastic search";
    }
}
