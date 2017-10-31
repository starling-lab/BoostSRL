package edu.wisc.cs.will.Boosting.Utils;

import edu.wisc.cs.will.Utils.Utils;

/**
 * Class performs line search to compute step length give a PhiFunction
 * that computes phi value at a given step length
 * @author Tushar Khot
 *
 */
public class LineSearch {

	private double initialAlpha=0.001;
	private double c1=0.0001;
	private double c2=0.9;
	private double alphaMax=100;
	private int maxIterations = 100;
	private double multiplierConstant=2;
	
	public LineSearch() {
		
	}
	
	public double getStepLength(PhiFunction phi) {
		double alpha=initialAlpha;
		double phi_d_0 = phi.phiDashAt(0);
		double phi_0 = phi.phiAt(0);
		double prev_phi_alpha = 1;
		double prev_alpha=0;
		int i=0;
		for (; i < maxIterations; i++) {
			double phi_alpha = phi.phiAt(alpha);
			if (phi_alpha > phi_0 + (c1*alpha*phi_d_0)||
				(i > 0 && phi_alpha >= prev_phi_alpha)	) {
				alpha = zoom(prev_alpha, alpha);
				break;
			}
			
			double phi_d_alpha = phi.phiDashAt(alpha);
			if (Math.abs(phi_d_alpha) <= -c2*phi_d_0) {
				// this alpha is selected
				break;
			}
			if (phi_d_alpha >= 0) {
				alpha = zoom(alpha, prev_alpha);
				break;
			}
			prev_phi_alpha = phi_alpha;
			prev_alpha = alpha;
			
			// Take new alpha
			alpha = Math.min(multiplierConstant*alpha, alphaMax);
		}
		if (i == maxIterations) {
			Utils.println("%% Didn't find any step size in " + maxIterations + " steps.\n");
			return 0;
		}
		return alpha;
	}



	private double zoom(double alpha, double prevAlpha) {
		// TODO use interpolation
		if(alpha < prevAlpha) {
			return alpha + (prevAlpha - alpha)/multiplierConstant;
		} else {
			return prevAlpha - (prevAlpha - alpha)/multiplierConstant;
		}
	}
}
