/**
 * The job of this class is to keep track of a search and return the desired result at the end. 
 */
package edu.wisc.cs.will.stdAIsearch;

import edu.wisc.cs.will.Utils.Utils;
import java.io.IOException;
import java.io.Serializable;

/**
 * @author shavlik
 *
 */
public class SearchMonitor implements Serializable { // Don't make this abstract since a generic monitor may well suffice.
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	private transient StateBasedSearchTask taskBeingMonitored;
	protected SearchResult         searchResult;
	protected SearchNode           terminatingNode;
	public static final   SearchResult         goalFound                 = new SearchResult(true,  "Goal was found."); // Only need to create these ONCE (some search instances are called multiple times).
	public static final   SearchResult         maxNodesConsideredReached = new SearchResult(false, "Reached maxNodesConsidered.");
	public static final   SearchResult         maxNodesCreatedReached    = new SearchResult(false, "Reached maxNodesCreated.");
	public static final   SearchResult         openBecameEmpty           = new SearchResult(false, "OPEN became empty before a goal was found.");
	public static final   SearchResult         maxNodesConsideredThisIterationReached = new SearchResult(false, "Reached maxNodesConsideredThisIteration.");
	public static final   SearchResult         maxNodesCreatedThisIterationReached    = new SearchResult(false, "Reached maxNodesCreatedThisIteration.");
    public static final   SearchResult         maxTimeUsedPerIteration    = new SearchResult(false, "Reached maximum clock time limit.");
	/**
	 * 
	 */
	public SearchMonitor() {		
	}
	public SearchMonitor(StateBasedSearchTask task) {
		setTaskBeingMonitored(task);
	}
	
	public void setSearchTask(StateBasedSearchTask task) {
		setTaskBeingMonitored(task);
	}
	
	public void reportSolutionPath() {
		if (terminatingNode == null) { return; }
		else { 
			Utils.println("Soln path:");
			terminatingNode.reportSolutionPath(1);
		}
	}
	
	public void recordNodeExpansion(SearchNode nodeBeingExpanded) {
		return;
	}

	public void recordNodeCreation(SearchNode nodeBeingCreated) {
		return;
	}

	// Return TRUE only if this node is acceptable as one that sets "best score seen so far."
	public boolean recordNodeBeingScored(SearchNode nodeBeingCreated, double score) throws SearchInterrupted {
		return true;
	}
	
	public void searchEndedByTerminator(SearchNode currentNode) {
		terminatingNode = currentNode;
		if (getTaskBeingMonitored().verbosity > 0) { Utils.println("Search ended because goal found."); }
		searchResult = goalFound;
	}
	
	public void searchEndedByMaxNodesConsidered(int numberOfNodesConsidered) {
		if (getTaskBeingMonitored().verbosity > 0) { Utils.println("Search ended because " + numberOfNodesConsidered      + " exceeds the max number of nodes considered."); }
		searchResult = maxNodesConsideredReached;
	}
	
	public boolean searchReachedMaxNodesCreated(int searchEndedByMaxNodesCreated) {
		if (getTaskBeingMonitored().verbosity > 0) { Utils.println("Search created " + searchEndedByMaxNodesCreated + "nodes, which exceeds the max number of nodes created."); }
		// Should override this if there is a reason to continue until OPEN is empty.
		searchResult = maxNodesCreatedReached;
		return getTaskBeingMonitored().stopWhenMaxNodesCreatedReached;
	}
	
	public void searchEndedByMaxNodesConsideredThisIteration(int numberOfNodesConsideredThisIteration) {
		if (getTaskBeingMonitored().verbosity > 0) { Utils.println("Search ended because " + numberOfNodesConsideredThisIteration      + " exceeds the max number of nodes considered for this iteration."); }
		searchResult = maxNodesConsideredThisIterationReached;
	}
	               
	public boolean searchReachedMaxNodesCreatedThisIteration(int searchEndedByMaxNodesCreatedThisIteration) {
		if (getTaskBeingMonitored().verbosity > 0) { Utils.println("Search ended because " + searchEndedByMaxNodesCreatedThisIteration + " exceeds the max number of nodes created for this iteration."); }
		searchResult = maxNodesCreatedThisIterationReached;
		// Should override this if there is a reason to continue until OPEN is empty.
		return getTaskBeingMonitored().stopWhenMaxNodesCreatedThisIterationReached;
	}

    public void searchEndedByMaxTimeUsed() {
        if (getTaskBeingMonitored().verbosity > 0) { Utils.println("Search ended because maximum clock time reached."); }
		searchResult = maxTimeUsedPerIteration;
    }

	public void searchEndedBecauseOPENbecameEmpty() {
		if (getTaskBeingMonitored().verbosity > 0) { Utils.println("Search ended because OPEN became empty."); }
		searchResult = openBecameEmpty;
	}
	
	public SearchResult getSearchResult() {
		// Determine what should be returned when the search has completed.
		return searchResult;
	}
	
	public SearchNode getGoalNode() {
		return terminatingNode;
	}

	public void setTaskBeingMonitored(StateBasedSearchTask taskBeingMonitored) {
		this.taskBeingMonitored = taskBeingMonitored;
	}
	public StateBasedSearchTask getTaskBeingMonitored() {
		return taskBeingMonitored;
	}
	
	public void clearAnySavedInformation(boolean insideIterativeDeepening) {
		return;
	}

   /** Methods for reading a Object cached to disk.
    *
    * @param in
    * @throws java.io.IOException
    * @throws java.lang.ClassNotFoundException
    */
    private void readObject(java.io.ObjectInputStream in) throws IOException, ClassNotFoundException {
        if ( in instanceof StateBasedSearchInputStream == false ) {
            throw new IllegalArgumentException(getClass().getCanonicalName() + ".readObject() input stream must support StateBasedSearchInputStream interface");
        }

        in.defaultReadObject();

        StateBasedSearchInputStream stateBasedSearchInputStream = (StateBasedSearchInputStream) in;

        this.setTaskBeingMonitored(stateBasedSearchInputStream.getStateBasedSearchTask());
    }

}
