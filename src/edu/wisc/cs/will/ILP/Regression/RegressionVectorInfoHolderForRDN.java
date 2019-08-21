/**
 * 
 */
package edu.wisc.cs.will.ILP.Regression;

import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.ILP.LearnOneClause;
import edu.wisc.cs.will.ILP.SingleClauseNode;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

/**
 * @author tkhot
 *
 */
public class RegressionVectorInfoHolderForRDN extends RegressionInfoHolderForRDN {
	
	
	public RegressionVectorInfoHolderForRDN() {
		trueStats = new BranchVectorStats();
		falseStats = new BranchVectorStats();
	}

	/* (non-Javadoc)
	 * @see edu.wisc.cs.will.ILP.Regression.RegressionInfoHolder#weightedVarianceAtSuccess()
	 */
	@Override
	public double weightedVarianceAtSuccess() {		
		return trueStats.getWeightedVariance();
	}

	/* (non-Javadoc)
	 * @see edu.wisc.cs.will.ILP.Regression.RegressionInfoHolder#weightedVarianceAtFailure()
	 */
	@Override
	public double weightedVarianceAtFailure() {
		return falseStats.getWeightedVariance();
	}

	/* (non-Javadoc)
	 * @see edu.wisc.cs.will.ILP.Regression.RegressionInfoHolder#totalExampleWeightAtSuccess()
	 */
	@Override
	public double totalExampleWeightAtSuccess() {
		return trueStats.getNumExamples();
	}

	/* (non-Javadoc)
	 * @see edu.wisc.cs.will.ILP.Regression.RegressionInfoHolder#totalExampleWeightAtFailure()
	 */
	@Override
	public double totalExampleWeightAtFailure() {
		return falseStats.getNumExamples();
	}

	/* (non-Javadoc)
	 * @see edu.wisc.cs.will.ILP.Regression.RegressionInfoHolder#meanAtSuccess()
	 */
	@Override
	public double meanAtSuccess() {
		return Double.NaN;
	}

	/* (non-Javadoc)
	 * @see edu.wisc.cs.will.ILP.Regression.RegressionInfoHolder#meanAtFailure()
	 */
	@Override
	public double meanAtFailure() {
		return Double.NaN;
	}

	/* (non-Javadoc)
	 * @see edu.wisc.cs.will.ILP.Regression.RegressionInfoHolder#addFailureStats(edu.wisc.cs.will.ILP.Regression.RegressionInfoHolder)
	 */
	@Override
	public RegressionInfoHolder addFailureStats(RegressionInfoHolder addThis) {
		RegressionVectorInfoHolderForRDN regHolder = new RegressionVectorInfoHolderForRDN();
		if (addThis == null) {
			regHolder.falseStats = this.falseStats.add(new BranchVectorStats());
		} else {
			regHolder.falseStats = this.falseStats.add(((RegressionVectorInfoHolderForRDN)addThis).falseStats);
		}
		return regHolder;
	}


	@Override
	public void addFailureExample(Example eg, long numGrndg, double weight) {
		double output[] =  ((RegressionRDNExample) eg).getOutputVector();
		//double prob   = ((RegressionRDNExample)eg).getProbOfExample();
		// TODO (TVK) : use vectors for probability weighting
		((BranchVectorStats)falseStats).addNumVectorOutput(numGrndg, output, weight, 1);
	}

	@Override
	public double variance() {
		return (weightedVarianceAtSuccess() + weightedVarianceAtFailure()) / (totalExampleWeightAtSuccess() + totalExampleWeightAtFailure());
		//return trueStats.getWeightedVariance() + falseStats.getWeightedVariance();
	}

	@Override
	public void populateExamples(LearnOneClause task, SingleClauseNode caller) throws SearchInterrupted {
		  if (!task.regressionTask) { Utils.error("Should call this when NOT doing regression."); }
          if (caller.getPosCoverage() < 0.0) { caller.computeCoverage(); }
          for (Example posEx : task.getPosExamples()) {
              double weight = posEx.getWeightOnExample();
              double output[] =  ((RegressionRDNExample) posEx).getOutputVector();
            	//double prob   = ((RegressionRDNExample)posEx).getProbOfExample();
              
              if (!caller.posExampleAlreadyExcluded(posEx)) {
          		// TODO (TVK) : use vectors for probability weighting
            	  ((BranchVectorStats)trueStats).addNumVectorOutput(1, output, weight, 1);		
              }
          }
          RegressionInfoHolder totalFalseStats = caller.getTotalFalseBranchHolder() ;
          if (totalFalseStats != null) {
        	  falseStats = falseStats.add(((RegressionVectorInfoHolderForRDN)totalFalseStats).falseStats);
          }
	}
	
	
	public double[] meanVectorAtSuccess() {
		return ((BranchVectorStats)trueStats).getLambdaVector(false);
	}
	public double[] meanVectorAtFailure() {
		return ((BranchVectorStats)falseStats).getLambdaVector(false);
	}
	
	
	

}
