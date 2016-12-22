/**
 * 
 */
package edu.wisc.cs.will.Utils;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;

/**
 * @author tkhot
 *
 */
public class VectorStatistics {

	
	private List<double[]> datapoints;
	
	private int size;
	
	public VectorStatistics() {
		datapoints = new ArrayList<double[]>();
		size = 0;
	}
	
	
	public void addVector(double[] vec) {
		datapoints.add(vec);
		if (size != 0) {
			if (size != vec.length) {
				Utils.error("vector not of expected size: " + size);
			}
		} else {
			size = vec.length;
		}
	}
	
	public double[] getMean() {
		if (datapoints.size() == 0) {
			Utils.error("No data points");
			return null;
		}
		double[] sum = new double[size];
		int count = 0;
		// For each data point
		for (double[] data : datapoints) {
			// For each index
			for (int i = 0; i < size; i++) {
				if (count == 0) {
					sum[i] = 0;
				}
				sum[i] += data[i];
			}
			count++;
		}
		for (int i = 0; i < size; i++) {
			sum[i] = sum[i] / count;
		}
		return sum;
	}
	
	public double getVariance() {
		if (datapoints.size() == 0) {
			Utils.error("No data points");
			return 0;
		}
		double[] mean = getMean();
		double sum = 0;
		// For each data point
		for (double[] data : datapoints) {
			double l2norm = 0;
			// For each index
			for (int i = 0; i < size; i++) {
				l2norm += Math.pow(data[i] - mean[i], 2);
			}
			sum += l2norm;
		}
		return sum/datapoints.size();
	}
	
	public static double[] scalarProduct(double[] vec, double scalar) {
		double[] result = new double[vec.length];
		
		for (int i = 0; i < vec.length; i++) {
			result[i] = vec[i] * scalar;
		}
		return result;
	}
	
	public static double[] addScalar(double[] vec, double scalar) {
		double[] result = new double[vec.length];
		
		for (int i = 0; i < vec.length; i++) {
			result[i] = vec[i] + scalar;
		}
		return result;
	}
	
	public static double dotProduct(double[] a, double[] b) {
		if (a.length != b.length) {
			Utils.error("Vector lengths don't match for dot product!!:" + a.length + " Vs " + b.length);
		}
		double result = 0;
		for (int i = 0; i < a.length; i++) {
			result = result + a[i]*b[i];
		}
		return result;
	}
	
	public static double[] addVectors(double[] a, double[] b) {
		if (a.length != b.length) {
			Utils.error("Vector lengths don't match for addition!!:" + a.length + " Vs " + b.length);
		}
		double[] result = new double[a.length];
		
		for (int i = 0; i < a.length; i++) {
			result[i] = a[i]+b[i];
		}
		return result;
	}


	public static double[] exponentiate(double[] vec) {
		double[] result = new double[vec.length];
		
		for (int i = 0; i < vec.length; i++) {
			result[i] = Math.exp(vec[i]);
		}
		return result;
	}
	
	public static double sum(double[] vec) {
		double sum=0;
		for (double val : vec) {
			sum += val;
		}
		return sum;
	}


	public static double[] createIndicator(int length, int index) {
		double[] result = new double[length];
		Arrays.fill(result, 0);
		result[index] = 1;
		return result;
	}


	public static double[] subtractVectors(double[] a, double[] b) {
		if (a.length != b.length) {
			Utils.error("Vector lengths don't match for addition!!:" + a.length + " Vs " + b.length);
		}
		double[] result = new double[a.length];
		
		for (int i = 0; i < a.length; i++) {
			result[i] = a[i]-b[i];
		}
		return result;
	}
}
