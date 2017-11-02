/**
 * 
 */
package edu.wisc.cs.will.ResThmProver;

import java.util.List;

import edu.wisc.cs.will.stdAIsearch.EndTest;
import edu.wisc.cs.will.stdAIsearch.SearchNode;
import edu.wisc.cs.will.FOPC.Binding;

/**
 * @author shavlik
 *
 */
public class ProofDone extends EndTest {
	HornSearchNode goalNodeFound;
	/**
	 * 
	 */
	public ProofDone(HornClauseProver task) {
		super(task);
	}
	
	public boolean endSearch(SearchNode currentNode) {
		HornSearchNode thisNode = (HornSearchNode)currentNode;
		boolean result = thisNode.isSolution();
		if (result) { goalNodeFound = thisNode; }
		return result;
	}
	
	public void clearAnySavedInformation(boolean insideIterativeDeepening) {
		goalNodeFound = null;
	}
	
	public List<Binding> collectBindingsUsedInProof() {
		if (goalNodeFound == null) { return null; }
		return goalNodeFound.collectBindingsToRoot();
	}

    public List<Binding> collectQueryBindings() {
        if (goalNodeFound == null) { return null; }
		return goalNodeFound.collectQueryBindings().collectBindingsInList();
    }

	public String toString() {
		if (goalNodeFound == null) { return "Search ended without finding a proof-by-negation."; }
		return "Search ended successfully.";
	}
}
