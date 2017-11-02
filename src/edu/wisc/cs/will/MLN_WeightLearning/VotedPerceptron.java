package edu.wisc.cs.will.MLN_WeightLearning;

import java.util.Collection;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.MLN_Inference.AllOfInference;
import edu.wisc.cs.will.MLN_Inference.Gibbs;
import edu.wisc.cs.will.MLN_Inference.MCSAT;
import edu.wisc.cs.will.MLN_Inference.SAT;
import edu.wisc.cs.will.MLN_Inference.SampleSAT;
import edu.wisc.cs.will.MLN_Task.Block;
import edu.wisc.cs.will.MLN_Task.GroundClause;
import edu.wisc.cs.will.MLN_Task.GroundLiteral;
import edu.wisc.cs.will.MLN_Task.GroundedMarkovNetwork;
import edu.wisc.cs.will.MLN_Task.TimeStamp;
import edu.wisc.cs.will.Utils.Utils;

/**
 * This class implements the Voted Perceptron algorithm and extensions like
 * Contrastive Divergence (using MCMC samples to estimate expectation counts)
 * and a heuristic for adapting the learning rate, eta).
 * 
 * @author pavan and shavlik
 */
public class VotedPerceptron extends DiscriminativeWeightLearning {
	private final static int debugLevel = -10;
	
	// How to get expected number of clauses satisfied.
	public  final static int     SATinfer          = 0; // Use SATinfer to avoid name conflict with class SAT.
	public  final static int     MCMC              = 1;
	public  final static int     SPECIALIZED_SAT   = 2;
	public  final static int     PSEUDO_LIKELIHOOD = 3;
	
	public  final static boolean useDifferentEtas_default         = false; // Eta is scaled for each clause proportional to its size.  NEEDS MORE THOUGHT BEFORE IT US USED.
	public  final static int     numStarts_default                =     1;
	public  final static int     numStepsPerStart_default         =   100;
	public  final static int     numMCMCstepsPerIteration_default =   100;
	public  final static int     typeOfEstimation_default         =  MCMC; 	
	public  final static double  eta_default                      =     0.01;	
	public  final static int     numLearningSteps_default         =   500;
		
	private boolean  useDifferentEtas         = useDifferentEtas_default;
	private double   eta                      = eta_default;
	private int      typeOfEstimation         = typeOfEstimation_default;	
	private int      numMCMCstepsPerIteration = numMCMCstepsPerIteration_default;	
	private int      numStarts                = numStarts_default;
	private int      numStepsPerStart         = numStepsPerStart_default;
	private int      numLearningSteps         = numLearningSteps_default;
    private int      maxNumberOfStarts_SampleSAT = SAT.maxNumberOfStarts_default;
    private int      maxNumberOfFlips_SampleSAT  = SAT.maxNumberOfFlips_default;
	
	private double  oneNormDistance = -1.0;
	private boolean inited          = false;
	
	private Gibbs   gibbsSampler;
	private MCSAT   mcsatSampler;
	
	public VotedPerceptron(GroundedMarkovNetwork groundedMarkovNetwork) {		
		super(groundedMarkovNetwork);
		setupVP();
	}	
	public VotedPerceptron(GroundedMarkovNetwork groundedMarkovNetwork, int numLearningSteps) {
		super(groundedMarkovNetwork);
		this.numLearningSteps = numLearningSteps;
		setupVP();
	}	
	public VotedPerceptron(GroundedMarkovNetwork groundedMarkovNetwork,
            			   int numLearningSteps,
            			   int numStarts,
            			   int numStepsPerStart) {
		super(groundedMarkovNetwork);
		this.numLearningSteps = numLearningSteps;
		this.numStarts        = numStarts;
		this.numStepsPerStart = numStepsPerStart;
		setupVP();
	}
	public VotedPerceptron(GroundedMarkovNetwork groundedMarkovNetwork,
            			   int     numLearningSteps,
            			   int     numStarts,
            			   int     numStepsPerStart,
            			   int     numMCMCstepsPerIteration,
            			   int     typeOfEstimation,
            			   double  eta,
            			   boolean useDifferentEtas) {
		super(groundedMarkovNetwork);
		this.numLearningSteps = numLearningSteps;
		this.numStarts        = numStarts;
		this.numStepsPerStart = numStepsPerStart;
		this.numMCMCstepsPerIteration = numMCMCstepsPerIteration;
		this.typeOfEstimation = typeOfEstimation;
		this.eta              = eta;
		this.useDifferentEtas = useDifferentEtas;
		setupVP();
	}	
	public VotedPerceptron(GroundedMarkovNetwork groundedMarkovNetwork,
			               int     numLearningSteps,
			               int     numStarts,
			               int     numStepsPerStart,
			               int     numMCMCstepsPerIteration,
			               int     typeOfEstimation,
			               double  eta,
			               boolean useDifferentEtas,
			               int     maxNumberOfStarts_SampleSAT, 
			               int     maxNumberOfFlips_SampleSAT) {
		super(groundedMarkovNetwork);
		this.numLearningSteps = numLearningSteps;
		this.numStarts        = numStarts;
		this.numStepsPerStart = numStepsPerStart;
		this.numMCMCstepsPerIteration = numMCMCstepsPerIteration;
		this.typeOfEstimation = typeOfEstimation;
		this.eta              = eta;
		this.useDifferentEtas = useDifferentEtas;
    	this.maxNumberOfStarts_SampleSAT = maxNumberOfStarts_SampleSAT;
    	this.maxNumberOfFlips_SampleSAT  = maxNumberOfFlips_SampleSAT;
		setupVP();
	}

	
	private void setupVP() {
		gibbsSampler = new Gibbs(groundedMarkovNetwork, AllOfInference.prior_for_being_true_default);
		mcsatSampler = new MCSAT(groundedMarkovNetwork, AllOfInference.prior_for_being_true_default, maxNumberOfStarts_SampleSAT, maxNumberOfFlips_SampleSAT);		
	}
	
	/**
	 * Do gradient descent for some number of steps.
	 */
	public Collection<Clause> learn(TimeStamp timeStamp) {
		double startTime = -1;
		for (int i = 0; i < numLearningSteps; i++) {
			if (debugLevel > 0 && i % 100 == 0) { 
				Utils.print("% VP gradient-descent step #" + i);
    			long   endTime   = System.currentTimeMillis();
    			double timeTaken = (endTime - startTime) / 1000.0;
    			if (startTime  > 0) { Utils.println(".   Took " + Utils.truncate(timeTaken, 2) + " seconds."); }
    			else                { Utils.println("."); }
        		startTime = endTime;
			}
			updateWeights(timeStamp);
			// Use EM to set the values on the hidden/unknown literals.
		  //  updateMissingLiterals();
		}
		assignWeights();
		assignActualValuesToGroundLiterals(timeStamp);
		return groundedMarkovNetwork.getAllClausesThatWereGrounded();
	}	

	/**
	 * One step of gradient descent.
	 */
	public void updateWeights(TimeStamp timeStamp) {
		computeCurrEstNumSatisfiedClauses(timeStamp);
		
		adjustEta();
		double sumAbsPartialDerivatives =  0.0;
    	double max                      = -0.1;
    	int    worstClauseIndex         = -1;
		for (int i = 0; i < numberOfClausesUsed; i++) {			
			double partialDerivative = numSatisfiedGroundClausesInDatabase[i] - currEstNumSatisfiedGroundClauses[i];
			sumAbsPartialDerivatives += Math.abs(partialDerivative);
			if (print1normGradient && sumAbsPartialDerivatives > max) { max = sumAbsPartialDerivatives; worstClauseIndex = i; }
    		if (useDifferentEtas && numSatisfiedGroundClausesInDatabase[i] != 0) { // Use a different local eta for each clause.
				currentWeights[i] += eta * partialDerivative / numSatisfiedGroundClausesInDatabase[i];
			} else {
				currentWeights[i] += eta * partialDerivative;
			}
			Clause clause = indexToClause[i];
			if (debugLevel > -11) { Utils.println("% VP:   Clause #" + i + ":  deriv = " + Utils.truncate(partialDerivative, 2) + ", #satisfiedInTrainSet = " + Utils.truncate(numSatisfiedGroundClausesInDatabase[i], 0) + ", estimated number satisified = " + Utils.truncate(currEstNumSatisfiedGroundClauses[i], 2) + ", wgt = " + Utils.truncate(currentWeights[i], 3) + " '" + clause + "'"); }
			Collection<GroundClause> gndClauses = groundedMarkovNetwork.getAllGroundClauses(clause);
			if (gndClauses != null)	for (GroundClause gndClause : gndClauses) {	gndClause.setWeightOnSentence(currentWeights[i]); }
			sumWeights[i] += currentWeights[i];  // This is the 'running total' of weights, since we combine the perceptrons resulting from each state as a means of overfitting reduction. 
		}
		// Since so many print outs if done every time, randomly print one on a hundred.
		if (print1normGradient && Utils.random() < 0.01) { Utils.println("% VP: 1-norm of gradient (avg over the " + Utils.comma(numberOfClausesUsed) + " clauses): " + Utils.truncate(sumAbsPartialDerivatives / numberOfClausesUsed, 3) + ".  The infinity norm = " + Utils.truncate(max, 0) + " from clause '" + indexToClause[worstClauseIndex] + "'.\n"); }
	}
	
	/**
	 * Computes an estimation of the expected number of times each clause is satisfied in
	 * the database.  We can use various techniques like using the MAP state of the atoms, MCMC sampling,
	 * or pseudo-likelihood assumption (the assumption that each ground predicate is dependent
	 * only on its neighbors) to estimate the expected counts.
	 *
	 */
	private void computeCurrEstNumSatisfiedClauses(TimeStamp timeStamp) {
		//long before = System.currentTimeMillis();
		if (typeOfEstimation == SATinfer) {
			SAT solver = new SampleSAT(groundedMarkovNetwork, AllOfInference.prior_for_being_true_default, numStarts, numStepsPerStart);	
			solver.solve(groundedMarkovNetwork.getAllGroundLiterals_ExpensiveVersion(), null, true);
			for (int i = 0; i < numberOfClausesUsed; i++) {
				Clause clause = indexToClause[i];
				currEstNumSatisfiedGroundClauses[i] = groundedMarkovNetwork.numberOfSatisfiedGroundClauses(clause);
				if (debugLevel > 3) { Utils.println("% Number of satisfied training-set clauses at MAP state = " + Utils.truncate(currEstNumSatisfiedGroundClauses[i], 0) + " for '" + clause + "'."); }
			}
		} else if (typeOfEstimation == MCMC) {
			if (!inited) {
				SAT solver = new SampleSAT(groundedMarkovNetwork, AllOfInference.prior_for_being_true_default, numStarts, numStepsPerStart);	
				solver.solve(groundedMarkovNetwork.getAllGroundLiterals_ExpensiveVersion(), null, true);
				inited = true;
			}
			double[] sumNumSatisfiedClauses = new double[numberOfClausesUsed];
			
			for (int i = 0; i < numMCMCstepsPerIteration; i++) {
				if (MCMCsamplingType == GIBBS_SAMPLING) gibbsSampler.getNextSample();
	            else mcsatSampler.getNextSample();
				for (int j = 0; j < numberOfClausesUsed; j++) {
					Clause clause = indexToClause[j];
					double currEst = groundedMarkovNetwork.numberOfSatisfiedGroundClauses(clause);
					sumNumSatisfiedClauses[j] += currEst;
					// Utils.println("% Number of satisfied training-set clauses at MAP state = " + Utils.truncate(currEst, 0) + " for '" + clause + "'.");
				}
			}
			// For MCMC sampler, we need to reset the sampler every rounds as the weights have changed
			// and new negative clauses may have been created.
		       if (MCMCsamplingType != GIBBS_SAMPLING) {
		        	mcsatSampler.cleanUpSampleGenerator();
		        }
			for (int i = 0; i < numberOfClausesUsed; i++) {
				currEstNumSatisfiedGroundClauses[i] = sumNumSatisfiedClauses[i] / numMCMCstepsPerIteration;
			}
		} else if (typeOfEstimation == SPECIALIZED_SAT) {			
			specialized_SAT(timeStamp);	
			for (int i = 0; i < numberOfClausesUsed; i++) {
				Clause clause = indexToClause[i];
				currEstNumSatisfiedGroundClauses[i] = groundedMarkovNetwork.numberOfSatisfiedGroundClauses(clause);
			}
		} else if (typeOfEstimation == PSEUDO_LIKELIHOOD) {
			expectationCountsUsingPseudoLikelihoodAssumption(null);
			Utils.waitHere("setupTimeStamp");
		}
		//long after = System.currentTimeMillis();		
		//Utils.println("time taken for estimating num satisfied clauses: " + (after - before));
	}
	
	/**
	 * This is a very specialized kind-of SAT. Currently in place only for some comparison purposes for some specific MLN structures.
	 */
	private void specialized_SAT(TimeStamp timeStamp) {
		Map<GroundLiteral,Block> allBlocks = groundedMarkovNetwork.getAllBlocks();
		if (allBlocks != null) {
			Set<Entry<GroundLiteral,Block>> blockSet = allBlocks.entrySet();
			for (Entry<GroundLiteral,Block> entry : blockSet) {
				Block block = entry.getValue();	
				block.initValues(timeStamp);			
				if (block.valuesFixed()) continue;
				int index = 0;
				int bestIndex = 0;
				double bestValue = Integer.MIN_VALUE;
				boolean newState = true;
				do {
					double numSatisfiedGroundClauses = block.sumSatisfiedClauses();
					if (numSatisfiedGroundClauses > bestValue) {
						bestValue = numSatisfiedGroundClauses;
						bestIndex = index;
					}
					newState = block.moveToNextState(timeStamp);
					index++;
				} while (newState);
				block.setState(bestIndex, timeStamp);
			}
		}
		for (GroundLiteral gndLiteral : groundedMarkovNetwork.getAllGroundLiterals_ExpensiveVersion()) { // TODO - remove _Expensive*
			if (gndLiteral.getBlock() != null) continue;
			gndLiteral.setValueOnly(true,  timeStamp);
			double weightsWhenTrue = gndLiteral.getWeightSatisfiedClauses();
			gndLiteral.setValueOnly(false, timeStamp);
			double weightsWhenFalse = gndLiteral.getWeightSatisfiedClauses();
			if (weightsWhenTrue > weightsWhenFalse) gndLiteral.setValueOnly(true,  timeStamp);
			if (weightsWhenTrue < weightsWhenFalse) gndLiteral.setValueOnly(false, timeStamp);
			if (weightsWhenTrue == weightsWhenFalse) {
				if (Utils.random() > 0.5) { gndLiteral.setValueOnly(true,  timeStamp);  }
				else                      { gndLiteral.setValueOnly(false, timeStamp); }
			}
		}
	}
	
	/**
	 * Here we estimate the expected counts of the clauses using the pseudo-likelihood assumption - that a node is dependent only on its neighbors.
	 */
	private void expectationCountsUsingPseudoLikelihoodAssumption(TimeStamp timeStamp) {		
		for (int i = 0; i < numberOfClausesUsed; i++) {
			currEstNumSatisfiedGroundClauses[i] = 0.0;
		}
		Map<GroundLiteral,Block> allBlocks = groundedMarkovNetwork.getAllBlocks();
		if (allBlocks != null) {
			Set<Entry<GroundLiteral,Block>> blockSet = groundedMarkovNetwork.getAllBlocks().entrySet();
			for (Entry<GroundLiteral,Block> entry : blockSet) {
				Block block = entry.getValue();	
				block.initValues(timeStamp);			
				if (block.valuesFixed()) {
					for (GroundClause gndClause : block.getGndClauses()) {
						if (gndClause.isSatisfiedCached()) {
							Utils.waitHere("fix code below");
							int index = 0; //clauseToIndex.get(gndClause.getParentClause());
							currEstNumSatisfiedGroundClauses[index]++; 
						}
					}				
				} else {
					double[] tempWgtSatisfiedClauses = new double[numberOfClausesUsed];
					double expWeightSatisfiedClauses = 0;
					double denominator = 0;
					boolean newState = true;
					
					do {
						expWeightSatisfiedClauses = Math.exp(block.sumSatisfiedClauses());
						for (GroundClause gndClause : block.getGndClauses()) {
							if (!gndClause.isSatisfiedCached()) continue;
							Utils.waitHere("fix code below");
							int index = 0; //clauseToIndex.get(gndClause.getParentClause());
							tempWgtSatisfiedClauses[index] += expWeightSatisfiedClauses; 
						}
						denominator += expWeightSatisfiedClauses;
						newState = block.moveToNextState(timeStamp);				
					} while (newState);
					for (int i = 0; i < numberOfClausesUsed; i++) {
						currEstNumSatisfiedGroundClauses[i] += tempWgtSatisfiedClauses[i] / denominator;
					}
				}			
			}
		}
		for (GroundLiteral gndLiteral : groundedMarkovNetwork.getAllGroundLiterals_ExpensiveVersion()) { // TODO - remove _Expensive*
			if (gndLiteral.getBlock() != null) { continue; }
			boolean actualValue = holdInitialLiteralValues.get(gndLiteral);
			gndLiteral.setValueOnly(true,  timeStamp);
			double weightsWhenTrue = gndLiteral.getWeightSatisfiedClauses();
			gndLiteral.setValueOnly(false, timeStamp);
			double weightsWhenFalse = gndLiteral.getWeightSatisfiedClauses();
			double probTrue = 1.0 / (1.0 + Math.exp(weightsWhenFalse - weightsWhenTrue));
			for (GroundClause gndClause : gndLiteral.getGndClauseSet()) {				
				gndLiteral.setValueOnly(true,  timeStamp); // JWSJWSJWS do we want to just do 'local' setValue()?
				double valueWhenTrue  = gndClause.checkIfSatisfied(timeStamp) ? 1 : 0; // These are used to pull out the probability assigned to the correct class.
				gndLiteral.setValueOnly(false, timeStamp);
				double valueWhenFalse = gndClause.checkIfSatisfied(timeStamp) ? 0 : 1;
				double expectedWeight = (probTrue * valueWhenTrue + (1 - probTrue) * valueWhenFalse);
				Utils.waitHere("fix code below");
				int index = 0; // clauseToIndex.get( gndClause.getParentClause());
				currEstNumSatisfiedGroundClauses[index] += expectedWeight;
			}
			gndLiteral.setValueOnly(actualValue, timeStamp);
		}
	}
	
	/**
	 * Average the weights over all steps of the gradient descent and assign these as the weights
	 * of the clauses.
	 */
	private void assignWeights() {
		for (int i = 0; i < numberOfClausesUsed; i++) {
			double averageWeight = sumWeights[i] / (numLearningSteps + 1); // Add the one due to the initial weights.
			Clause clause = indexToClause[i];
			clause.setWeightOnSentence(averageWeight);
			Utils.println(i + " " + averageWeight);
		}
	}	
	
	/**
	 * To adjust eta on the fly.  TODO - should this be generalized on a per-clause basis?
	 */
	private void adjustEta() {
		double newOneNormDistance = 0.0;
		for (int i = 0; i < numberOfClausesUsed; i++) {			
			newOneNormDistance += Math.abs(numSatisfiedGroundClausesInDatabase[i] - currEstNumSatisfiedGroundClauses[i]);
		}
		if (debugLevel > 1) { Utils.println("%  VP: OneNorm distance  =" + Utils.truncate(newOneNormDistance, 4) + " [was " + Utils.truncate(oneNormDistance, 4) + "]"); }
		if (oneNormDistance == -1) {
			oneNormDistance = newOneNormDistance;
			return;
		}
		if (oneNormDistance > newOneNormDistance) eta *= 1.01; // Can take a larger step size.
		if (oneNormDistance < newOneNormDistance) eta *= 0.99; // Seem to have overshot the local minimum, so reduce the step size.
		
		oneNormDistance = newOneNormDistance;		
	}
}