package edu.wisc.cs.will.MLN_Inference;

import edu.wisc.cs.will.MLN_Task.GroundedMarkovNetwork;
import edu.wisc.cs.will.Utils.Utils;

/**
 * This class implements MCSAT Sampling.
 * 
 * @author pavan and shavlik
 */
public class MCSATInference extends MCMCInference {
	private MCSAT theMCSAT;
	private Gibbs theGibbs;
	// Use Gibbs Sampling with this probability during MC-SAT runs to explore the modes.
	private double probOfGibbsSample = 0.0;
	
	public MCSATInference(GroundedMarkovNetwork groundedMarkovNetwork, double priorProbOfBeingTrue) {
		super(groundedMarkovNetwork, priorProbOfBeingTrue);
		theMCSAT = new MCSAT(groundedMarkovNetwork, priorProbOfBeingTrue);
		theGibbs = new Gibbs(groundedMarkovNetwork, priorProbOfBeingTrue);
	}
	public MCSATInference(GroundedMarkovNetwork groundedMarkovNetwork, double priorProbOfBeingTrue, 
						  int maxNumBurninginSteps,        int maxNumSteps, int numberOfMCMCtrials) {
		super(groundedMarkovNetwork, priorProbOfBeingTrue, maxNumBurninginSteps, maxNumSteps, numberOfMCMCtrials);
		theMCSAT = new MCSAT(groundedMarkovNetwork, priorProbOfBeingTrue);
	}	
	public MCSATInference(GroundedMarkovNetwork groundedMarkovNetwork, double priorProbOfBeingTrue, 
						  int maxNumBurninginSteps,        int maxNumSteps, int numberOfMCMCtrials, 
						  int maxNumberOfStarts_SampleSAT, int maxNumberOfFlips_SampleSAT) {
		super(groundedMarkovNetwork, priorProbOfBeingTrue, maxNumBurninginSteps, maxNumSteps, numberOfMCMCtrials);
		theMCSAT = new MCSAT(groundedMarkovNetwork, priorProbOfBeingTrue, maxNumberOfStarts_SampleSAT, maxNumberOfFlips_SampleSAT);
	}	
	public MCSATInference(GroundedMarkovNetwork groundedMarkovNetwork, double priorProbOfBeingTrue, 
			  			  int maxNumBurninginSteps,        int maxNumSteps, int numberOfMCMCtrials, 
			  			  int maxNumberOfStarts_SampleSAT, int maxNumberOfFlips_SampleSAT,
			  			  double probOfWalkSAT, double temperatureSA, int maxNumStepsAfterSoln_sampleSAT) {
		super(groundedMarkovNetwork, priorProbOfBeingTrue, maxNumBurninginSteps, maxNumSteps, numberOfMCMCtrials);
		theMCSAT = new MCSAT(groundedMarkovNetwork, priorProbOfBeingTrue, maxNumberOfStarts_SampleSAT, maxNumberOfFlips_SampleSAT, probOfWalkSAT, temperatureSA, maxNumStepsAfterSoln_sampleSAT);
	}
	
	/**
	 * Generate the next sample.
	 */
	public void getNextSample() {
		if (groundedMarkovNetwork.doingLazyInference) { Utils.error("Should not call this when doingLazyInference=true!"); }
		if (Utils.random() < probOfGibbsSample) {
			theGibbs.getNextSample();
		} else {
			theMCSAT.getNextSample();
		}
	}	
	public int getStepsPerSample() {
		return theMCSAT.getStepsPerSample();
	}
	public void cleanUpSampleGenerator() {
		theMCSAT.cleanUpSampleGenerator();
	}
	
}