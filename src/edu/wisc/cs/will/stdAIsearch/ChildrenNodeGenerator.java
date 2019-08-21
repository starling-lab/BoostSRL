/**
 * 
 */
package edu.wisc.cs.will.stdAIsearch;

import java.util.List;

/** Generate
 * 
 * Given a node in a search space, generates the children of that node.
 * Implementations of this class should lookup the StateBasedSearchTask 
 * to which this parent belongs and remove items in the CLOSED list.
 *
 * @param <T> Type of Search Node.
 * @author shavlik
 *
 */
public abstract class ChildrenNodeGenerator<T extends SearchNode> {
	
    protected StateBasedSearchTask<T> task;
    //protected List<T> newChildren; // This is only used to return a list of children.  It could be put on the stack (if Java allowed that), but by making it an instance variable, at least there is no need to garbage collect in the middle of a search.

	/**
	 * 
	 */		
	public ChildrenNodeGenerator() {
	}

    public ChildrenNodeGenerator(StateBasedSearchTask<T> task) {
		this.task = task;
	}

    public void setSearchTask(StateBasedSearchTask<T> task) {
		this.task = task;
	}
	
    public abstract List<T> collectChildren(T nodeBeingExplored) throws SearchInterrupted;

	public abstract void             clearAnySavedInformation(boolean insideIterativeDeepening);
}
