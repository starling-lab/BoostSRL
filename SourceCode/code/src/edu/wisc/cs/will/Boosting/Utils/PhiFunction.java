package edu.wisc.cs.will.Boosting.Utils;

/**
 * Class that computes the value of phi to be used in LineSearch
 * phi(alpha) = f(x + alpha*p).
 * phi'(alpha) = p*f'(x+alpha*p) 
 * where 
 * alpha is the step length
 * f is the function
 * x is the current position
 * p is the descent direction
 * @author Tushar Khot
 *
 */
public interface PhiFunction {

	/**
	 * 
	 * @param alpha Step length
	 * @return the value of phi at alpha
	 */
	public double phiAt(double alpha);
	
	/**
	 * 
	 * @param alpha Step length
	 * @return the derivative of phi at alpha
	 */
	public double phiDashAt(double alpha);
}
