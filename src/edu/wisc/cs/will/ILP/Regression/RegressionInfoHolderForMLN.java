/**
 * 
 */
package edu.wisc.cs.will.ILP.Regression;

import edu.wisc.cs.will.Boosting.EM.HiddenLiteralState;
import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.DataSetUtils.RegressionExample;
import edu.wisc.cs.will.ILP.LearnOneClause;
import edu.wisc.cs.will.ILP.SingleClauseNode;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

/**
 * @author tkhot
 *
 */
public class RegressionInfoHolderForMLN extends RegressionInfoHolderForRDN {

	
	public RegressionInfoHolderForMLN() {
		super();
	}

//	
//	
//	/* (non-Javadoc)
//	 * @see edu.wisc.cs.will.ILP.Regression.RegressionInfoHolder#weightedVarianceAtSuccess()
//	 */
//	@Override
//	public double weightedVarianceAtSuccess() {
//		// TODO Auto-generated method stub
//		return 0;
//	}
//
//	/* (non-Javadoc)
//	 * @see edu.wisc.cs.will.ILP.Regression.RegressionInfoHolder#weightedVarianceAtFailure()
//	 */
//	@Override
//	public double weightedVarianceAtFailure() {
//		// TODO Auto-generated method stub
//		return 0;
//	}
//
//	/* (non-Javadoc)
//	 * @see edu.wisc.cs.will.ILP.Regression.RegressionInfoHolder#totalExampleWeightAtSuccess()
//	 */
//	@Override
//	public double totalExampleWeightAtSuccess() {
//		// TODO Auto-generated method stub
//		return 0;
//	}
//
//	/* (non-Javadoc)
//	 * @see edu.wisc.cs.will.ILP.Regression.RegressionInfoHolder#totalExampleWeightAtFailure()
//	 */
//	@Override
//	public double totalExampleWeightAtFailure() {
//		// TODO Auto-generated method stub
//		return 0;
//	}
//
//	/* (non-Javadoc)
//	 * @see edu.wisc.cs.will.ILP.Regression.RegressionInfoHolder#meanAtSuccess()
//	 */
//	@Override
//	public double meanAtSuccess() {
//		// TODO Auto-generated method stub
//		return 0;
//	}
//
//	/* (non-Javadoc)
//	 * @see edu.wisc.cs.will.ILP.Regression.RegressionInfoHolder#meanAtFailure()
//	 */
//	@Override
//	public double meanAtFailure() {
//		// TODO Auto-generated method stub
//		return 0;
//	}
//
//	/* (non-Javadoc)
//	 * @see edu.wisc.cs.will.ILP.Regression.RegressionInfoHolder#addFailureStats(edu.wisc.cs.will.ILP.Regression.RegressionInfoHolder)
//	 */
//	@Override
//	public RegressionInfoHolder addFailureStats(RegressionInfoHolder addThis) {
//		// TODO Auto-generated method stub
//		return null;
//	}
//
//
//	@Override
//	public void addFailureExample(Example eg, long numGrndg, double weight) {
//		// TODO Auto-generated method stub
//		
//	}
//
//	@Override
//	public double variance() {
//		// TODO Auto-generated method stub
//		return 0;
//	}

	@Override
	public void populateExamples(LearnOneClause task, SingleClauseNode caller) throws SearchInterrupted {
		if (!task.regressionTask) { Utils.error("Should call this when NOT doing regression."); }
		if (caller.getPosCoverage() < 0.0) { caller.computeCoverage(); }
		HiddenLiteralState lastState = null;
		for (Example posEx : task.getPosExamples()) {
			double weight = posEx.getWeightOnExample();
			double output = ((RegressionExample) posEx).getOutputValue();
			ProbDistribution prob   = ((RegressionRDNExample)posEx).getProbOfExample();
			if (prob.isHasDistribution()) {
				Utils.error("Expected single probability value but contains distribution");
			}
			if (!caller.posExampleAlreadyExcluded(posEx)) {
				long num = 1;
				if (caller != caller.getRootNode()) {
					if (posEx instanceof RegressionRDNExample) {
						RegressionRDNExample rex = (RegressionRDNExample)posEx;
						HiddenLiteralState  newState = rex.getStateAssociatedWithOutput();
						if (newState != null &&
							!newState.equals(lastState)) {
							String predName =  posEx.predicateName.name;
							if (predName.startsWith(WILLSetup.multiclassPredPrefix)) {
								predName = predName.substring(WILLSetup.multiclassPredPrefix.length());
							}
							task.updateFacts(lastState, newState, predName);
							lastState = newState;
						}
					}
					num  = caller.getNumberOfGroundingsForRegressionEx(posEx);
				}
				if (num == 0) {
					Utils.waitHere("Number of groundings = 0 for " + posEx + " with " + caller.getClause());
					num = 1;
				}
				//Utils.println("adding "  + num + ":" + output + ":" + fraction);
				
				trueStats.addNumOutput(num, output, weight, prob.getProbOfBeingTrue());		
			}
		}
		RegressionInfoHolder totalFalseStats = caller.getTotalFalseBranchHolder() ;
		if (totalFalseStats != null) {
			falseStats = falseStats.add(((RegressionInfoHolderForRDN)totalFalseStats).falseStats);
		}
	}
}
