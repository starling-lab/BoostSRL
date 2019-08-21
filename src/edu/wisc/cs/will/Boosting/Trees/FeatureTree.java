/**
 * 
 */
package edu.wisc.cs.will.Boosting.Trees;

import edu.wisc.cs.will.Boosting.OneClass.FeatureVector;
import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Theory;
import edu.wisc.cs.will.Utils.RegressionValueOrVector;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author tkhot
 *
 */
public class FeatureTree extends ClauseBasedTree {

		
	public FeatureTree(WILLSetup setup) {
		super(setup);			
	}



	public void parseTheory(Theory th) {
		if (th.getClauses() == null) {
			Utils.error("No regular clauses!!!");
		}
		for (Clause cl : th.getClauses()) {
			if (cl == null)
				continue;
			addClause(cl);
		}
		// Add supporting clauses to bk
		if(th.getSupportClauses() != null) {
			for (Clause cl : th.getSupportClauses()) {
				if (cl == null)
					continue;
				addSupportingClause(cl);
				setup.getInnerLooper().getContext().getClausebase().assertBackgroundKnowledge(cl);
			}
		}
	}
	
	
	public FeatureVector getFeatureVector(RegressionRDNExample ex) {
		FeatureVector result = new FeatureVector();
		for (Clause clause : regressionClauses) {
			RegressionValueOrVector wt = getRegressionClauseWt(clause, ex);
			if (wt != null) {
				if (wt.isHasVector()) {
					// Not implemented
					Utils.error("Can not handle multi class examples: " + ex);
					return result;
				}
				result.append(1); // FIX(TVK): wt.getSingleRegressionValue());
				if (result.usepath) {
					result.pathFeatures.add("" + (int)wt.getSingleRegressionValue());
					return result;
				}
			} else {
				result.append(0);
			}
		}
		return result;
	}

	public RegressionValueOrVector getRegressionValue(Example ex) {
		Utils.error("Can not get regression value for feature tree");
		return null;
	}
	public void reparseFeatureTree() {
		reparseRegressionTrees();
	}
	
	
	
	
}
