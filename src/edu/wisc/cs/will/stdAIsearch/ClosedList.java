/**
 * Keep track of nodes already visited.  Order doesn't matter (fast access does) so use a hash table.
 */
package edu.wisc.cs.will.stdAIsearch;

/**
 * @author shavlik
 *
 */
public abstract class ClosedList {
	protected StateBasedSearchTask task;
	
	/**
	 * TODO have a max size on this (and then randomly discard some percent if full? see linkedHashMap)
	 */

	/**
	 * 
	 */
	public ClosedList() {
		
	}
	public ClosedList(StateBasedSearchTask task) {
		this.task = task;
	}
	
	public void setSearchTask(StateBasedSearchTask task) {
		this.task = task;
	}	
	
	public void clearAnySavedInformation(boolean insideInterativeDeepening) {
		return;
	}

	public abstract void    addNodeToClosed(    SearchNode node);
	public abstract boolean alreadyInClosedList(SearchNode node);
	public abstract void    emptyClosedList();
	public abstract void    reportClosedSize();

}
