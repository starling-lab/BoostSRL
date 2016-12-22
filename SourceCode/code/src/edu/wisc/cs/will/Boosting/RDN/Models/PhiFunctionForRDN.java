/**
 * 
 */
package edu.wisc.cs.will.Boosting.RDN.Models;

import java.util.List;

import edu.wisc.cs.will.Boosting.RDN.ConditionalModelPerPredicate;
import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.Trees.ClauseBasedTree;
import edu.wisc.cs.will.Boosting.Utils.PhiFunction;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.Utils.Utils;

/**
 * For RDNs
 * f : sum of log probabilities of the examples
 * x : psi_{m-1} for every example
 * p : Gradient of every example fit by the tree
 * @author Tushar Khot
 *
 */
public class PhiFunctionForRDN implements PhiFunction {

	
	private double[] x;
	private double[] p;
	private boolean[] positiveEg;
	
	public PhiFunctionForRDN(ConditionalModelPerPredicate model,
							 ClauseBasedTree tree,
							 List<RegressionRDNExample> examples) {
		x = new double[examples.size()];
		p = new double[examples.size()];
		positiveEg = new boolean[examples.size()];
		for (int i = 0; i < examples.size(); i++) {
			if (examples.get(i).isHasRegressionVector()) {
				Utils.waitHere("Can't find phi function for multi-class examples");
			}
			x[i] = model.returnModelRegression(examples.get(i)).getSingleRegressionValue();
			p[i] = tree.getRegressionValue(examples.get(i)).getSingleRegressionValue();
			positiveEg[i] = examples.get(i).isOriginalTruthValue();
		}
	}
	
	/* (non-Javadoc)
	 * @see edu.wisc.cs.will.Boosting.Utils.PhiFunction#phiAt(double)
	 */
	@Override
	public double phiAt(double alpha) {
		double sum=0;
		// 
		for (int i = 0; i < x.length; i++) {
			double psi = x[i] + alpha*p[i];
			if (positiveEg[i]) {
				sum = sum + psi;
			}
			sum = sum - Math.log(1 + Math.exp(psi));
		}
		Utils.println("phi(" + alpha +") = " + -sum);
		return -sum;
	}

	/* (non-Javadoc)
	 * @see edu.wisc.cs.will.Boosting.Utils.PhiFunction#phiDashAt(double)
	 */
	@Override
	public double phiDashAt(double alpha) {
		double sum = 0;
		for (int i = 0; i < x.length; i++) {
			double fdash = 0;
			if (positiveEg[i]) {
				fdash = 1;
			}
			fdash = fdash - probOfExample(x[i] + alpha*p[i]);
			sum = sum + p[i] * fdash;
		}
		Utils.println("phi_dash(" + alpha +") = " + -sum);
		return -sum;
	}

	private double probOfExample(double psi) {
		return (Math.exp(psi) / (1 + Math.exp(psi)));
	}

}
