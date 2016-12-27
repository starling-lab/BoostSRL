/**
 * 
 */
package edu.wisc.cs.will.ILP.Regression;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.ILP.LearnOneClause;
import edu.wisc.cs.will.ILP.SingleClauseNode;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

/**
 * @author tkhot
 *
 */
public abstract class RegressionInfoHolder {

	
	protected BranchStats trueStats;
	protected BranchStats falseStats;
	
	
	public abstract double weightedVarianceAtSuccess();
	public abstract double weightedVarianceAtFailure();
	
	public abstract double totalExampleWeightAtSuccess();
	public abstract double totalExampleWeightAtFailure();
	
	public abstract double meanAtSuccess();
	public abstract double meanAtFailure();
	
	public double[] meanVectorAtSuccess() {
		return null;
	}
	public double[] meanVectorAtFailure() {
		return null;
	}
	
	
	
	public abstract RegressionInfoHolder addFailureStats(RegressionInfoHolder addThis);
	
	public double varianceAtSuccess() {
		return weightedVarianceAtSuccess() / totalExampleWeightAtSuccess();
	}
	
	public double varianceAtFailure() {
		return weightedVarianceAtFailure() / totalExampleWeightAtFailure();
	}
	public abstract void addFailureExample(Example eg, long numGrndg, double weight);
	public abstract double variance();
	public abstract void populateExamples(LearnOneClause task, SingleClauseNode singleClauseNode) throws SearchInterrupted;
	/**
	 * @return the trueStats
	 */
	public BranchStats getTrueStats() {
		return trueStats;
	}
	/**
	 * @param trueStats the trueStats to set
	 */
	public void setTrueStats(BranchStats trueStats) {
		this.trueStats = trueStats;
	}
	/**
	 * @return the falseStats
	 */
	public BranchStats getFalseStats() {
		return falseStats;
	}
	/**
	 * @param falseStats the falseStats to set
	 */
	public void setFalseStats(BranchStats falseStats) {
		this.falseStats = falseStats;
	}
}
