package edu.wisc.cs.will.MLN_Inference;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.MLN_Task.GroundLiteral;
import edu.wisc.cs.will.MLN_Task.GroundedMarkovNetwork;
import edu.wisc.cs.will.MLN_Task.MLNreductionProblemTooLargeException;
import edu.wisc.cs.will.Utils.Utils;

/**
 * An abstract MCMC-inference class.
 * 
 *   http://en.wikipedia.org/wiki/Markov_chain_Monte_Carlo
 * 
 * Note: this class calls MaxWalkSAT to create the initial state.
 *       No need to use a lot of starts and flips for this, since only the initial state,
 *       though can override by passing in variables to specify these.
 * 
 * @author pavan and shavlik 
 *  
 */
public abstract class MCMCInference extends Inference {	
	private   final static int debugLevel        =    1;
	protected final static int reportingInterval = 1000;
	
	public  final static int numberOfMCMCtrials_default =     5; //0; // The product of this and maxSteps is the number of samples produced.
	public  final static int burnInSteps_default        =   100; // (So current total is ?K, ?K of which are 'burn in' samples.  But note that one sample might also involve 1000 'moves.')
	public  final static int maxMCMCsteps_default       =   900 + burnInSteps_default; // Includes the burn-in, but this is PER trial.
	
	public  int      maxNumberOfStartsForInitialState   =      5; // These are used to find good starting states for MCSAT, where most clauses are satisfied.
	public  int      maxNumberOfFlipsForInitialState    =  20000; // The product of these two numbers should be 100K, at least if this code is to make the defaults (as of March 2009) in Alchemy.  
	
	protected int      numberOfMCMCtrials   = numberOfMCMCtrials_default;
	protected int      maxNumbBurnInSteps   = burnInSteps_default;   // Maximum number of steps during the burning-in phase.
	protected int      maxNumSteps          = maxMCMCsteps_default;  // Maximum number of steps including the burning-in phase.
	protected int      totalNumSteps        = 0;                     // A variable to keep track of number of steps WHEN CALCULATING probability(lit=true).
	protected int[]    numTrue;                                      // Number of times the query literal is true.
	
	protected MaxWalkSAT theMaxWalkSATsolver;
	
	public MCMCInference(GroundedMarkovNetwork groundedMarkovNetwork, double priorProbOfBeingTrue) {		
		super(groundedMarkovNetwork);
		prior_for_being_true = priorProbOfBeingTrue;
	}
	public MCMCInference(GroundedMarkovNetwork groundedMarkovNetwork, double priorProbOfBeingTrue, int maxNumbBurnInSteps, int maxNumSteps) {		
		this(groundedMarkovNetwork, priorProbOfBeingTrue);
		this.maxNumbBurnInSteps = maxNumbBurnInSteps;
		this.maxNumSteps        = maxNumSteps;
	}
	public MCMCInference(GroundedMarkovNetwork groundedMarkovNetwork, double priorProbOfBeingTrue, int maxNumbBurnInSteps, int maxNumSteps, int numberOfMCMCtrials) {		
		this(groundedMarkovNetwork, priorProbOfBeingTrue);
		this.maxNumbBurnInSteps = maxNumbBurnInSteps;
		this.maxNumSteps        = maxNumSteps;
		this.numberOfMCMCtrials = numberOfMCMCtrials;
	}
	public MCMCInference(GroundedMarkovNetwork groundedMarkovNetwork, double priorProbOfBeingTrue, int maxNumbBurnInSteps, int maxNumSteps, int numberOfMCMCtrials,
				         int maxNumberOfStartsForInitialState, int maxNumberOfFlipsForInitialState) {		
		this(groundedMarkovNetwork, priorProbOfBeingTrue);
		this.maxNumbBurnInSteps = maxNumbBurnInSteps;
		this.maxNumSteps        = maxNumSteps;
		this.numberOfMCMCtrials = numberOfMCMCtrials;
		this.maxNumberOfStartsForInitialState  = maxNumberOfStartsForInitialState;
		this.maxNumberOfFlipsForInitialState   = maxNumberOfFlipsForInitialState;
	}
	
	protected abstract void cleanUpSampleGenerator(); // Clean up after each MCM run (actually, before the next).
	
	protected void initForTheseFlexibleLiterals(Collection<GroundLiteral> lits) {
		groundedMarkovNetwork.initializeForTheseQueries(lits);
		if (lits != null) {
			numTrue = new int[Utils.getSizeSafely(lits)]; // Note: even with lazy inference, we need to keep counts on all query literals (TODO could wait until TRUE the first time).
			for (int i = 0; i < numTrue.length; i++) { numTrue[i] = 0; } // Probably Java will set these to 0 anyway, but only a small, one-time cost.
		}
	}
	
	private void startPosition() { // Do a (presumably short) MaxWalkSAT to initialize before the MCMC begins.
		cleanUpSampleGenerator();
		reportFlagOn = true;
		groundedMarkovNetwork.setAllMarkers(this); // Play it safe and mark all the items in case some code checks for markers.
		int stepsUsed = theMaxWalkSATsolver.solve(null, null, reportFlagOn);
		if (debugLevel > -10) { Utils.println("%   Used " + Utils.comma(stepsUsed) + " steps to do the MaxWalkSAT initialization for MCMC.  Final number of active clauses is " + Utils.comma(theMaxWalkSATsolver.last_countOfActiveClauses) + " and best cost is " + Utils.truncate(theMaxWalkSATsolver.bestCost, 2) + "."); }
		groundedMarkovNetwork.clearAllMarkers();
	}
	
	public List<InferenceResult> findQueryState(Collection<GroundLiteral> queryLiterals, Map<GroundLiteral,String> documentationForQueries) throws MLNreductionProblemTooLargeException {
		this.documentationForQueries = documentationForQueries;
		initForTheseFlexibleLiterals(queryLiterals);
		if (queryLiterals == null) { return createInferenceResult(queryLiterals, documentationForQueries); } // Might be some queries in the evidence.
		if (theMaxWalkSATsolver == null) { theMaxWalkSATsolver = new MaxWalkSAT(groundedMarkovNetwork, prior_for_being_true, maxNumberOfStartsForInitialState, maxNumberOfFlipsForInitialState); }		
		int totalWork = numberOfMCMCtrials * theMaxWalkSATsolver.getStepsPerSample() + numberOfMCMCtrials * maxNumSteps * getStepsPerSample();
		if (debugLevel > -10) { Utils.println("\n%  MCMC will be performed " + Utils.comma(numberOfMCMCtrials) + 
												  " times for " + Utils.comma(maxNumSteps) + " steps (of which " + Utils.comma(maxNumbBurnInSteps) + " will be 'burn-in' steps each trial).\n% " +
												  " Hence " + Utils.comma(numberOfMCMCtrials * (maxNumSteps - maxNumbBurnInSteps)) + " samples will be used to estimate probabilities of the query literals given the KB and the evidence.\n% " +
												  " In each trial a relatively short MaxWalkSAT run (" + Utils.comma(theMaxWalkSATsolver.getStepsPerSample()) + " steps) will find a starting point.\n% " +
												  " After that, each sample will take up to " + Utils.comma(getStepsPerSample()) + " steps, for a total of as many as " + 
												  Utils.comma(totalWork) + " steps."); }
		Utils.println("%  At 1 sample per second, inference will take around " + Utils.truncate((numberOfMCMCtrials * maxNumSteps) / (1 * 3600.0), 2) + " hours.");
		//Utils.waitHere("findQueryState");
		endTimer1();  // This also restarts the timer.
		for (int trial = 1; trial <= numberOfMCMCtrials; trial++) { // Perform the burn-in phase multiple times.
			endTimer2(); // This also restarts the timer.
			if (debugLevel > -10) { Utils.println("%  Starting MCMC burn-in phase for trial #" + trial + " ..."); }
			startPosition(); //Utils.waitHere();
			// groundedMarkovNetwork.printLiteralsAndClauses();
			boolean continueSampling = true;
			boolean inBurnInPhase    = true;
			int     numSteps         = 0;
			while (continueSampling) { // Get next MCMC sample.			
				getNextSample();
				numSteps++;
				if (debugLevel > 1 && numSteps % reportingInterval == 0) { Utils.println("%    Number of MCMC steps done this trial = " + Utils.comma(numSteps)); }
				if (inBurnInPhase) {// Variables totalNumSteps and numTrue[] are not updated during the burn-in phase.
					if (checkForBurnInConvergence() || numSteps >= maxNumbBurnInSteps) { // End of burn-in phase.
						inBurnInPhase = false;
						endTimer2();
						if (debugLevel > -10) { Utils.println("%   Done burning in for MCMC trial #" +  Utils.comma(trial) + ".  Took " + Utils.truncate(timeTaken2, 3) + " seconds for the burn-in."); }
					}
				} else { // Start keeping statistics on how often each literal is true.			
					totalNumSteps++;
					updateCountsOnQueryLiterals(groundedMarkovNetwork, queryLiterals, trial, numSteps);
					if (checkForConvergence() || numSteps >= maxNumSteps) { continueSampling = false; }
				}			
			}
			if (debugLevel > -10) { 
				endTimer2();
				Utils.println("\n% Took " + Utils.truncate(timeTaken2, 3) + " seconds for MCMC-inference trial #" + Utils.comma(trial) + " (including burn-in time).");
			}
		}
		cleanUpSampleGenerator();
		if (debugLevel > -10) { 
			endTimer1();
			Utils.println("\n% Took " + Utils.truncate(timeTaken1, 3) + " seconds for the " + Utils.comma(numberOfMCMCtrials) + " MCMC trials.");
		}
		return createInferenceResult(queryLiterals, documentationForQueries);
	}	
	
	protected void updateCountsOnQueryLiterals(GroundedMarkovNetwork groundedMarkovNetwork, Collection <GroundLiteral> queryGndLits, int trial, int numSteps) {
		if (queryGndLits == null) { Utils.error("Should not reach here if there are query literals."); }
		if (queryGndLits.size() != numTrue.length) { Utils.error("Size of query literals (" + Utils.comma(queryGndLits.size()) + ") does not equal size of numTrue vector (" + Utils.comma(numTrue.length) + ")."); }
		int index         = 0;
		int numberQueries = Utils.getSizeSafely(queryGndLits);
		int reportFreq    = 250;
		int numbSamples   =  10;
		int samplingRate  = Math.max(1, numberQueries / numbSamples);
		int offset = (numberQueries <= numbSamples ? 0 : Utils.random0toNminus1(samplingRate));
		boolean report = (numSteps % reportFreq == 0); // Only report every N steps.
		if (queryGndLits != null) for (GroundLiteral gLit : queryGndLits) {	// Note: we assume Java always sequences through this collection in the same order.
			if (groundedMarkovNetwork.isaQueryLiteralNotInReducedNetwork(gLit)) {
				gLit.setValue(Utils.random() < 0.5, null, null); // We know these have prob=0.5, but sample for convenience.
			}
			if (gLit.getValue()) { numTrue[index]++; }
			if (debugLevel > -10 && report && (index + offset) % samplingRate == 0) { Utils.println("% Trial #" + Utils.comma(trial) + "." + Utils.comma(numSteps) + ": CURRENT PROB for query literal #" + Utils.comma(index) + " '" + gLit + "' = " + numTrue[index] + " / " + totalNumSteps + 
							                                      " = " + Utils.truncate((numTrue[index] + prior_for_being_true * m_for_m_estimates) / (totalNumSteps + m_for_m_estimates), 3) + " [using m=" + m_for_m_estimates + "]"); }
			//if (debugLevel > -10 && report && index == 25) { Utils.println("% ... [only first 25 values shown here]."); }
			index++;
		}
	}
	
	protected List<InferenceResult> createInferenceResult(Collection<GroundLiteral> queryGndLits, Map<GroundLiteral,String> documentationForQueries) {
		result = new ArrayList<InferenceResult>();
		int index = 0;
		if (queryGndLits != null) for (GroundLiteral literal : queryGndLits) {
			double probability = (numTrue[index] + prior_for_being_true * m_for_m_estimates) / (totalNumSteps + m_for_m_estimates);
			result.add(new InferenceResult(literal, probability, (documentationForQueries == null ? "" : documentationForQueries.get(literal))));
			index++;
		}
		addAnyQueriesInEvidence(result);
		Collections.sort(result, inferenceResultComparator); // LEAST probable will be in front.
		return result;
	}
	
	public abstract void getNextSample();
	public abstract int  getStepsPerSample();
	
	// Currently we do not use the convergence tests.
	protected boolean checkForConvergence() {
		return false;
	}
	
	protected boolean checkForBurnInConvergence() {
		return false;
	}
}