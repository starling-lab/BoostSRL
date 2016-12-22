/**
 * 
 */
package edu.wisc.cs.will.Utils;

import java.util.Arrays;

/**
 * @author tkhot
 *
 */
public class RegressionValueOrVector {

	/** Used if we don't have a distribution over multiple values but a single probability */
	private double singleRegressionValue;
	
	private double[] regressionVector;
	
	private boolean hasVector;
	
	public RegressionValueOrVector(double prob) {
		setSingleRegressionValue(prob);
	}

	public RegressionValueOrVector(double[] dist) {
		setRegressionVector(dist);
	}
	
	public RegressionValueOrVector(RegressionValueOrVector copy) {
		this.hasVector  = copy.hasVector;
		this.regressionVector = copy.regressionVector.clone();
		this.singleRegressionValue = copy.singleRegressionValue;
	}
	
	public void multiply(double scalar) {
		if (isHasVector()) {
			regressionVector = VectorStatistics.scalarProduct(regressionVector, scalar); 
		} else {
			singleRegressionValue *= scalar;
		}
	}
	
	public void addValueOrVector(RegressionValueOrVector add){
		// If null, then add 0
		if (add == null) {
			return;
		}
		
		if (isHasVector()) {
			regressionVector = VectorStatistics.addVectors(this.regressionVector, add.regressionVector);
		} else {
			singleRegressionValue += add.singleRegressionValue;
		}
	}
	
	public void addScalar(double scalar) {
		if (isHasVector()) {
			regressionVector = VectorStatistics.addScalar(regressionVector, scalar);
		} else {
			singleRegressionValue += scalar;
		}
	}
	
	@Override
	public String toString() {
		if (isHasVector()) {
			return Arrays.toString(regressionVector);
		} else{
			return singleRegressionValue+"";
		}
	}

	/**
	 * @return the singleRegressionValue
	 */
	public double getSingleRegressionValue() {
		return singleRegressionValue;
	}

	/**
	 * @param singleRegressionValue the singleRegressionValue to set
	 */
	public void setSingleRegressionValue(double singleRegressionValue) {
		this.singleRegressionValue = singleRegressionValue;
	}

	/**
	 * @return the regressionVector
	 */
	public double[] getRegressionVector() {
		return regressionVector;
	}

	/**
	 * @param regressionVector the regressionVector to set
	 */
	public void setRegressionVector(double[] regressionVector) {
		setHasVector(true);
		this.regressionVector = regressionVector;
	}

	/**
	 * @return the hasVector
	 */
	public boolean isHasVector() {
		return hasVector;
	}

	/**
	 * @param hasVector the hasVector to set
	 */
	public void setHasVector(boolean hasVector) {
		this.hasVector = hasVector;
	}
	
	
}
