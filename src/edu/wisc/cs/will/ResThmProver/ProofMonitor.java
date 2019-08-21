/**
 * 
 */
package edu.wisc.cs.will.ResThmProver;


import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchMonitor;
import edu.wisc.cs.will.stdAIsearch.SearchNode;
import edu.wisc.cs.will.stdAIsearch.StateBasedSearchTask;

/**
 * @author shavlik
 *
 */

@SuppressWarnings("serial")
public class ProofMonitor extends SearchMonitor {

	/**
	 * Allow the watching of Prolog proofs, presumably for debugging purposes.
	 */
	public ProofMonitor(StateBasedSearchTask owner) {
	      this.setTaskBeingMonitored(owner);
	}

	
	public void recordNodeExpansion(SearchNode nodeBeingExpanded) {
		HornSearchNode horn = (HornSearchNode) nodeBeingExpanded;
		
		Utils.println("\n% Prolog-node expansion: ");
		horn.reportNodePredicates();
	}

	public void recordNodeCreation(SearchNode nodeBeingCreated) {
		HornSearchNode horn = (HornSearchNode) nodeBeingCreated;
		
		Utils.println("\n% Prolog-node creation: ");
		horn.reportNodePredicates();
	}

}
