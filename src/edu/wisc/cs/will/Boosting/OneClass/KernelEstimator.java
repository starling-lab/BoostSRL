/**
 * 
 */
package edu.wisc.cs.will.Boosting.OneClass;

import java.util.ArrayList;
import java.util.List;

/**
 * @author tkhot
 *
 */
public class KernelEstimator {

	private double bandwidth;
	
	private enum KernelFunction {
		EPAN,
		GAUSSIAN
	}
	
	private KernelFunction kernelType;
	
	public KernelEstimator() {
		bandwidth = 0.5;
		kernelType = KernelFunction.GAUSSIAN;
	}
	
	public double getDistance(int commonEdges) {
		if (commonEdges == -1) {
			return 0; 
		}
		return Math.exp(-(double)commonEdges);
	}
	
	public double getKernelValue(double distance) {
		switch (kernelType) {
		case EPAN:
			return (3.0/4.0) * (1 - Math.pow(distance/bandwidth, 2));
			
		case GAUSSIAN:
			return (1.0 / Math.sqrt(2.0 * Math.PI)) * Math.exp(- Math.pow(distance/bandwidth, 2.0) / 2);
			
		default:
			return distance;
		}
	}
	
	public double getKernelFromEdges(int commonEdges) {
		return getKernelValue(getDistance(commonEdges));
	}
	
	public double getProbabilityFromDistance(List<Double> distances) {
		List<Double> kernelVals = new ArrayList<Double>();
		for (Double dist : distances) {
			kernelVals.add(getKernelValue(dist));
		}
		return getProbabilityFromKernel(kernelVals);
	}

	public double getProbabilityFromKernel(List<Double> kernelVals) {
		double sum = 0;
		for (Double kval : kernelVals) {
			sum += kval;
		}
		return (1/((double)kernelVals.size() * bandwidth)) * sum;
	}

	/**
	 * @return the bandwidth
	 */
	public double getBandwidth() {
		return bandwidth;
	}

	/**
	 * @param bandwidth the bandwidth to set
	 */
	public void setBandwidth(double bandwidth) {
		this.bandwidth = bandwidth;
	}
	
}
