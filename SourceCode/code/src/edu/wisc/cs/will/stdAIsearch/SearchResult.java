/**
 * The job of this class is to collect the information of interest from a search (e.g., best node found). 
 */
package edu.wisc.cs.will.stdAIsearch;

import java.io.Serializable;

/**
 * @author shavlik
 *
 */
public class SearchResult implements Serializable {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	public  boolean goalFound = false;
	private String  reason;
	/**
	 * 
	 */
	public SearchResult(boolean goalFound) {
		this(goalFound, "Reason not given.");
	}
	public SearchResult(boolean goalFound, String reason) {
		this.goalFound = goalFound;
		this.reason    = reason;
	}
	
	public boolean goalFound() {
		return goalFound;
	}
	
	public String toString() {
		if (goalFound) {
			return "Search ended successfully.  "   + reason;
		}
		else {
			return "Search ended unsuccessfully.  " + reason;
		}
	}

}
