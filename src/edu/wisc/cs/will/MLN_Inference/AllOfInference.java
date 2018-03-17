/**
 * 
 */
package edu.wisc.cs.will.MLN_Inference;

import edu.wisc.cs.will.Utils.Utils;

/**
 * This is a catch-all class that holds common data structures for the various inference classes.
 * 
 * @author shavlik
 *
 */
public abstract class AllOfInference {

	protected final static int maxWarnings  = 100;
	protected              int warningCount =   0;  // Count how many warnings provided to user; stop when some maximum number reached. 

	public    final static double prior_for_being_true_default = 0.1;  // When literals are randomly flipped, this is the probability they will be set to TRUE.
	private   final static double samplingRatioForReports      = 0.01; // Use this to reduce the reporting rate.
	
	public    boolean useGreedyInitialStates = true; // When creating initial states, greedily set all literals to what is best for them.  If false, set randomly using prior_for_being_true_default.
	public    double m_for_m_estimates       =  10.0; // Used when estimating probabilities.
	public    double prior_for_being_true    =  prior_for_being_true_default; // Used for estimating probabilities, and also for setting initial values of literals.
	
	protected boolean reportFlagOn = true;
	protected boolean setReportFlag() {
		reportFlagOn = (Utils.random() < samplingRatioForReports);
		return reportFlagOn;
	}
	
	// Provide some timers.  Could write using arrays, but simply brute-force it.
	protected long   start1 = System.currentTimeMillis();
	protected long   end1;
	protected double timeTaken1; // Units are milliseconds.
	protected long   start2 = System.currentTimeMillis();
	protected long   end2;
	protected double timeTaken2;
	protected long   start3 = System.currentTimeMillis();
	protected long   end3;
	protected double timeTaken3;

	protected void endTimer1() {
		end1       = System.currentTimeMillis();
		timeTaken1 = (end1 - start1) / 1000.0;
		start1     = end1;
	}	
	protected void endTimer2() {
		end2       = System.currentTimeMillis();
		timeTaken2 = (end2 - start2) / 1000.0;
		start2     = end2;
	}	
	protected void endTimer3() {
		end3       = System.currentTimeMillis();
		timeTaken3 = (end3 - start3) / 1000.0;
		start3     = end3;
	}
	
	

}
