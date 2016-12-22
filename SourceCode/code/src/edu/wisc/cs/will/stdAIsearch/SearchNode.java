/**
 * 
 */
package edu.wisc.cs.will.stdAIsearch;

import edu.wisc.cs.will.Utils.Utils;
import java.io.IOException;
import java.io.Serializable;

/**
 * @author shavlik
 *
 */
@SuppressWarnings("serial")
public abstract class SearchNode implements Serializable {

	/**
	 * 
	 */
	private SearchNode           parentNode;
	transient public StateBasedSearchTask task;      // Provide a back pointer.
	public int                  depth = 0; // Depth in the search tree (root is 0).
	public double               score = 0; // Used for heuristic searches.
	public double               bonusScore = 0; // Used if we want to 'tweak' the score of a node to manipulate the ordering of the OPEN list.
	protected boolean           dontAddMeToOPEN = false;
	
	public SearchNode(StateBasedSearchTask task) { // Use this to create the ROOT nodes, since it connects nodes to the search task.
		this.task       = task;
		if (task == null) { Utils.error("Creating a search node but have task=null."); }
		this.parentNode = null;		
	}
	public SearchNode(SearchNode parentNode) {
		task = parentNode.task;
		this.parentNode = parentNode;
		if (parentNode == null) { Utils.error("Do not call SearchNode(null)."); }
		else { depth  = parentNode.depth + 1; task = parentNode.task; }		
	}
	
	public boolean dontActuallyAddToOpen() {
		return dontAddMeToOPEN;
	}
	
	public void reportSolutionPath(int depth) {
		for (int i=0; i < depth; i++) {
			Utils.print(" ");  // No way to do this with one command?
		}
		Utils.println(toString());
		if (getParentNode() == null) { return; }
		else { getParentNode().reportSolutionPath(depth + 1); }
	}
	
	// The next two are only needed when dealing with CLOSED lists.
	// Remember that if two search nodes are equal, then their hash codes also need to be equal.
	public int hashCode() {
		return super.hashCode(); // Use the built-in hash code, but leave this here as a reminder to override if needed (if two different nodes are equal, then they will need to have the same hash code [I think]).
	}	
	
	public boolean equals(Object otherNode) { // Leave this here as a reminder to override if needed.
		return super.equals(otherNode); 
	}

   /** Methods for reading a Object cached to disk.
    *
    * @param in
    * @throws java.io.IOException
    * @throws java.lang.ClassNotFoundException
    */
    private void readObject(java.io.ObjectInputStream in) throws IOException, ClassNotFoundException {
        if ( in instanceof StateBasedSearchInputStream == false ) {
            throw new IllegalArgumentException(getClass().getCanonicalName() + ".readObject() input stream must support FOPCObjectInputStream interface");
        }

        in.defaultReadObject();

        StateBasedSearchInputStream stateBasedSearchInputStream = (StateBasedSearchInputStream) in;

        this.task = stateBasedSearchInputStream.getStateBasedSearchTask();
    }

    /**
     * @return the parentNode
     */
    public SearchNode getParentNode() {
        return parentNode;
    }

    /**
     * @param parentNode the parentNode to set
     */
    public void setParentNode(SearchNode parentNode) {
        this.parentNode = parentNode;
    }
	public boolean getDontAddMeToOPEN() {
		return dontAddMeToOPEN;
	}
	public void setDontAddMeToOPEN(boolean dontAddMeToOPEN) {
		this.dontAddMeToOPEN = dontAddMeToOPEN;
	}
}
