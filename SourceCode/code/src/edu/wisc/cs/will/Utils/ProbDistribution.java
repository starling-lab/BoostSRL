/**
 * 
 */
package edu.wisc.cs.will.Utils;

import java.util.Arrays;

import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;

/**
 * @author tkhot
 *
 */
public class ProbDistribution {

	
	/** Used if we don't have a distribution over multiple values but a single probability */
	private double probOfBeingTrue;
	
	private double[] probDistribution = null;
	
	private boolean hasDistribution;
	
	public ProbDistribution(double prob) {
		setProbOfBeingTrue(prob);
	}

	
	// Added by Navdeep, Srijita to Handle Regression
		public ProbDistribution(double prob,boolean regression) {
			setProbOfBeingTrue(prob,regression);
		}
		
		// Added by Navdeep, Srijita to Handle Regression
		public void setProbOfBeingTrue(double probOfBeingTrue,boolean regression) {
			if(regression)
			{
				setHasDistribution(false);		
				this.probOfBeingTrue = probOfBeingTrue;
			}
		}
	
	
	
	public ProbDistribution(double[] dist) {
		setProbDistribution(dist);
	}
	
	public ProbDistribution(ProbDistribution copy) {
		this.hasDistribution  = copy.hasDistribution;
		if (hasDistribution) {
			this.probDistribution = copy.probDistribution.clone();
		} else {
			this.probOfBeingTrue = copy.probOfBeingTrue;
		}
	}
	
	/** 
	 * Construct distribution using sigmoid
	 * @param reg
	 */
	public ProbDistribution(RegressionValueOrVector reg) {
		this(reg, true);
	}
	
	public ProbDistribution(RegressionValueOrVector reg, boolean useSigmoid) {
		if (useSigmoid) {
			initUsingSigmoid(reg);
		} else {
			initAfterNormalizing(reg); 
		}
	}
	
	private void initAfterNormalizing(RegressionValueOrVector reg) {
		if (reg.isHasVector()) {
			double deno = VectorStatistics.sum(reg.getRegressionVector());
			double[] probDist = VectorStatistics.scalarProduct(reg.getRegressionVector(), 1/deno);
			setProbDistribution(probDist);
		} else {
			setProbOfBeingTrue(reg.getSingleRegressionValue());
		}
	}

	private void initUsingSigmoid(RegressionValueOrVector reg) {
		if (reg.isHasVector()) {
			double[] exp = VectorStatistics.exponentiate(reg.getRegressionVector());
			double deno = VectorStatistics.sum(exp);
			double[] probDist = VectorStatistics.scalarProduct(exp, 1/deno);
			for (int i = 0; i < probDist.length; i++) {
				if (Double.isNaN(probDist[i])) {
					probDist[i] = 1;
				}
			}
			setProbDistribution(probDist);
		} else {
			setProbOfBeingTrue(BoostingUtils.sigmoid(reg.getSingleRegressionValue(), 0));
		}
	}
	public void scaleDistribution(double scalar) {
		if (isHasDistribution()) {
			probDistribution = VectorStatistics.scalarProduct(probDistribution, scalar); 
		} else {
			probOfBeingTrue *= scalar;
		}
	}
	
	public void addDistribution(ProbDistribution add){
		// If null, then add 0
		if (add == null) {
			return;
		}
		
		if (isHasDistribution()) {
			probDistribution = VectorStatistics.addVectors(this.probDistribution, add.probDistribution);
		} else {
			probOfBeingTrue += add.probOfBeingTrue;
		}
	}
	
	
	@Override
	public String toString() {
		if (isHasDistribution()) {
			return Arrays.toString(probDistribution);
		} else{
			return probOfBeingTrue+"";
		}
	}
	
	/**
	 * @return the probOfBeingTrue
	 */
	public double getProbOfBeingTrue() {
		if (isHasDistribution()) {
			Utils.error("Expected single probability value but contains distribution");
		}
		return probOfBeingTrue;
	}

	/**
	 * @param probOfBeingTrue the probOfBeingTrue to set
	 */
	public void setProbOfBeingTrue(double probOfBeingTrue) {
		if (probOfBeingTrue > 1) {
			Utils.error("Probability greater than 1!!: " +  probOfBeingTrue);
		}
		setHasDistribution(false);		
		this.probOfBeingTrue = probOfBeingTrue;
	}

	/**
	 * @return the probDistribution
	 */
	public double[] getProbDistribution() {
		if (!isHasDistribution()) {
			Utils.error("Expected distribution but contains single probability value");
		}
		return probDistribution;
	}

	/**
	 * @param probDistribution the probDistribution to set
	 */
	public void setProbDistribution(double[] probDistribution) {
		setHasDistribution(true);
		this.probDistribution = probDistribution;
	}

	/**
	 * @return the hasDistribution
	 */
	public boolean isHasDistribution() {
		return hasDistribution;
	}

	/**
	 * @param hasDistribution the hasDistribution to set
	 */
	public void setHasDistribution(boolean hasDistribution) {
		this.hasDistribution = hasDistribution;
	}

	public double norm() {
		if (isHasDistribution()) {
			return Math.sqrt(VectorStatistics.dotProduct(probDistribution, probDistribution));
		} 
		
		
		return probOfBeingTrue;
	}

	/** 
	 * Return a randomly selected value from the distribution
	 * @return
	 */
	public int randomlySelect() {
		if (!isHasDistribution()) {
			return (Utils.random() < probOfBeingTrue) ? 1 : 0;
		}
		double cumulative = 0;
		double rand = Utils.random();
		for (int i = 0; i < probDistribution.length; i++) {
			// System.out.println(probDistribution[i]);
			cumulative += probDistribution[i];
			if (rand < cumulative) {
				return i;
			}
		}
		Utils.error("Cumulative distribution doesn't sum to 1. Sum:" + cumulative);
		return 0;
	}
	
	public double probOfTakingValue(int value) {
		if (isHasDistribution()) {
			if (value >= probDistribution.length) {
				Utils.error("Cannot return probability of taking value = " + value + ". Has to be less than " + probDistribution.length);
			}
			return probDistribution[value];
		}
		if (value == 1) { return getProbOfBeingTrue(); }
		if (value == 0) { return 1 - getProbOfBeingTrue();}
		Utils.error("Cannot return probability of taking value = " + value + ". Has to be 0/1.");
		return -1;
	}
	
}
