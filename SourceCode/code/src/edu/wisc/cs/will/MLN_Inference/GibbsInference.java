package edu.wisc.cs.will.MLN_Inference;

import java.util.Set;

import edu.wisc.cs.will.MLN_Task.GroundLiteral;
import edu.wisc.cs.will.MLN_Task.GroundedMarkovNetwork;
import edu.wisc.cs.will.Utils.Utils;

/**
 * This class implements Gibbs Sampling.
 * 
 * @author pavan and shavlik
 */
public class GibbsInference extends MCMCInference {
	private static final int debugLevel = 0;
	
	private Gibbs gibbsSampler;

	public GibbsInference(GroundedMarkovNetwork groundedMarkovNetwork, double priorProbOfBeingTrue) {
		super(groundedMarkovNetwork, priorProbOfBeingTrue);
		gibbsSampler = new Gibbs(groundedMarkovNetwork, priorProbOfBeingTrue);
	}	
	public GibbsInference(GroundedMarkovNetwork groundedMarkovNetwork, double priorProbOfBeingTrue, int maxNumBurninginSteps, int maxNumSteps) {
		super(groundedMarkovNetwork, priorProbOfBeingTrue, maxNumBurninginSteps, maxNumSteps);
		gibbsSampler = new Gibbs(groundedMarkovNetwork, priorProbOfBeingTrue);
	}	
	public GibbsInference(GroundedMarkovNetwork groundedMarkovNetwork, double priorProbOfBeingTrue, int maxNumBurninginSteps, int maxNumSteps, int numberOfMCMCtrials) {
		super(groundedMarkovNetwork, priorProbOfBeingTrue, maxNumBurninginSteps, maxNumSteps, numberOfMCMCtrials);
		gibbsSampler = new Gibbs(groundedMarkovNetwork, priorProbOfBeingTrue);
	}
	
	/**
	 * Generate the next Gibbs sample. Sample each literal based on its conditional probability.
	 */
	public void getNextSample() {
		if (debugLevel > 0) { Utils.println("% GIBBS: get sample."); }
		gibbsSampler.getNextSample();
	}
	public int getStepsPerSample() {
		return gibbsSampler.getStepsPerSample();
	}
	public void cleanUpSampleGenerator() {
		
	}
	
	public void setFixedLiterals(Set<GroundLiteral> fixedLiterals) {
		// Utils.println("%GI: Set fixed literals");
		super.setFixedLiterals(fixedLiterals);
		gibbsSampler.setFixedLiterals(fixedLiterals);
	}

}