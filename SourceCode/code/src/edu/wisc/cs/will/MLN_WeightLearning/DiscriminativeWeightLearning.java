package edu.wisc.cs.will.MLN_WeightLearning;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
 * This is the discriminative learning base class. Currently, we assume a closed world
 * assumption - there are no missing values.
 * 
 * TODO - create a TUNE set and look for overfitting (early stopping)
 *        do this by pulling out some constants (10% of each type?)
 *        then creating two groundings (but tune set will have much sparse connectivity, so not representative)
 * 
 * @author pavan and shavlik
 */
public abstract class DiscriminativeWeightLearning {	
	private static final int debugLevel = 0;
		
	protected int      numberOfClausesUsed = -1;
	protected double[] numSatisfiedGroundClausesInDatabase; // Use arrays to speed up code (i.e., instead of maps).
	protected double[] currEstNumSatisfiedGroundClauses;
	protected double[] sumWeights;
	protected double[] currentWeights;
	protected Clause[] indexToClause;
	protected Map<Clause,Integer> clauseToIndex;
	
	protected GroundedMarkovNetwork         groundedMarkovNetwork;
	protected Map<GroundLiteral,Boolean>      holdInitialLiteralValues;
	
	// How to assign initial weights.
	public static final int ALL_ZERO          = 0;
	public static final int RANDOM            = 1; 
	public static final int LOG_COUNTS_RATIO  = 2;
	public static final int typeOfInitialWeights_default = ALL_ZERO;
	public              int typeOfInitialWeights         = typeOfInitialWeights_default;
	
	// Type of MCMC sampling.	
	public static final int GIBBS_SAMPLING           = 0;
	public static final int MCSAT_SAMPLING           = 1;
	public static final int MCMCsamplingType_default = GIBBS_SAMPLING;
	public              int MCMCsamplingType         = MCMCsamplingType_default;

	
	// For EM  on hidden literals
	public int numMCMCIterationsForEM   = 100;
	public int MCMCsamplingTypeForEM    = GIBBS_SAMPLING;
	// Probability of applying EM on the missing literals in each round
	public double missingValueUpdateRate = 1.00;
	
	public static final boolean print1normGradient_default = (debugLevel > 1);
	public              boolean print1normGradient         = print1normGradient_default;
	
	
	public DiscriminativeWeightLearning(GroundedMarkovNetwork groundedMarkovNetwork) {
		this.groundedMarkovNetwork = groundedMarkovNetwork;	
		Collection<Clause> allClauses = groundedMarkovNetwork.getAllClausesThatWereGrounded();
		numberOfClausesUsed           = Utils.getSizeSafely(groundedMarkovNetwork.getAllClausesThatWereGrounded());
		Collection<GroundLiteral> gndLiterals = groundedMarkovNetwork.getAllGroundLiterals_ExpensiveVersion(); // TODO - remove _Expensive*
		if (numberOfClausesUsed > 0) {
			sumWeights                          = new double[numberOfClausesUsed];
			currentWeights                      = new double[numberOfClausesUsed];
			numSatisfiedGroundClausesInDatabase = new double[numberOfClausesUsed];
			currEstNumSatisfiedGroundClauses    = new double[numberOfClausesUsed];
			indexToClause                       = new Clause[numberOfClausesUsed];  // Provide a fast way to get back to clauses when needed.
			clauseToIndex                       = new HashMap<Clause,Integer>(4);   // And a quick way to get the index of a clause.
			groundedMarkovNetwork.task.setAllQueryVariablesToTheirTrainingValues(); // Set the values of the ground literals to that in the training set.
			for (int i = 0; i < numberOfClausesUsed; i++) { // This FOR LOOP collects the number of true groundings given the training set.
				Clause clause = Utils.getIthItemInCollectionUnsafe(allClauses, i);
				indexToClause[i] = clause;
				clauseToIndex.put(clause, i);
				// Use training data to get this count
				numSatisfiedGroundClausesInDatabase[i] = groundedMarkovNetwork.numberOfSatisfiedGroundClauses(clause);
				if (debugLevel > 1) { Utils.println("% Number of satisfied clauses in database = " + Utils.truncate(numSatisfiedGroundClausesInDatabase[i], 0) + " for '" + clause + "'"); }
			}
			initWeights(); // Be sure to compute AFTER setting all the queries and setting numSatisfiedGroundClausesInDatabase[].
			holdInitialLiteralValues = new HashMap<GroundLiteral,Boolean>(4); // Probably no longer need this, but keep around for now.
			Map<GroundLiteral,Block> allBlocks = groundedMarkovNetwork.getAllBlocks();
			if (gndLiterals != null && allBlocks != null) for (GroundLiteral gndLiteral : gndLiterals) {
				holdInitialLiteralValues.put(gndLiteral, gndLiteral.getValue());
				Block block = allBlocks.get(gndLiteral);
				if (block != null) { block.init(); }
			}		
		}			
	}

	
	/**
	 * Initialize the weights of the MLN clauses. The various types of initializations are setting
	 *      all weights to 0, 
	 *      small random weights in [-0.1, 0.1) 
	 *      weights from a Gaussian distribution [NOT YET IMPLEMENTED], or 
	 *      the weights equal to the log ratio of the number of times the clause is satisfied and violated in the data (slightly 'smoothed' by adding 1 to both counts).
	 */
	private void initWeights() {
		if (numberOfClausesUsed < 1) { return ; }
		for (int i = 0; i < numberOfClausesUsed; i++) {
			Clause clause = indexToClause[i];
			double numberOfGroundings = groundedMarkovNetwork.numberOfGroundings(clause);
			if (numberOfGroundings < 1) {
				clause.setWeightOnSentence(0.0);
			} else {
				if        (typeOfInitialWeights == ALL_ZERO) {
					clause.setWeightOnSentence(0.0);
				} else if (typeOfInitialWeights == RANDOM)   {
					clause.setWeightOnSentence(0.1 - Utils.random() / 5);
				} else if (typeOfInitialWeights == LOG_COUNTS_RATIO) {
					double   numSatisfiedGroundClauses = numSatisfiedGroundClausesInDatabase[i];
					double numUnsatisfiedGroundClauses = numberOfGroundings - numSatisfiedGroundClauses;
					
					if (  numSatisfiedGroundClauses < 0) { Utils.error("Should not be negative: numSatisfiedGroundClausesInDatabase = " + Utils.truncate(numSatisfiedGroundClauses,   0)); }
					if (numUnsatisfiedGroundClauses < 0) { Utils.error("Should not be negative: numUnsatisfiedGroundClauses = "         + Utils.truncate(numUnsatisfiedGroundClauses, 0)); }
					
					clause.setWeightOnSentence(Math.log((numSatisfiedGroundClauses + 1.0) / (numUnsatisfiedGroundClauses + 1.0)));
					if (debugLevel > 1) { Utils.println("% initWeights(#" + i + "):  #sat = " + Utils.truncate(numSatisfiedGroundClauses, 0) + " #unsat = " + Utils.truncate(numUnsatisfiedGroundClauses, 0) + " init wgt = " + Utils.truncate(clause.getWeightOnSentence(),4) + " for '" + clause + "'."); }					
				}
				
				currentWeights[i] = clause.getWeightOnSentence();
				sumWeights[    i] = clause.getWeightOnSentence();
				// Give the same weight to all the ground clauses.
				Collection<GroundClause> gndClauses = groundedMarkovNetwork.getAllGroundClauses(clause);
				if (gndClauses != null) for (GroundClause gndClause : gndClauses) { gndClause.setWeightOnSentence(clause.getWeightOnSentence()); }				
			}
		}
	}
	
	/**
	 * A method to learn the weights of clauses.
	 */
	public abstract Collection<Clause> learn(TimeStamp timeStamp);

	/**
	 * Outputs the clauses and their weights.
	 */
	public void print() {
		if (numberOfClausesUsed < 1) { Utils.println("\n% There were no closes for which to learn weights."); return ; }
		Utils.println("\n% The weighted clauses:");
		for (Clause clause : groundedMarkovNetwork.getAllClausesThatWereGrounded()) { Utils.println("%   " + clause.toString(Integer.MAX_VALUE)); }
	}	
	
	/**
	 * A single step of weight updates.
	 */
	protected abstract void updateWeights(TimeStamp timeStamp);	
	
	/**
	 * Return the values of the ground literals to their initial state.
	 * 
	 */
	protected void assignActualValuesToGroundLiterals(TimeStamp timeStamp) {
		if (numberOfClausesUsed < 1) { return; }
		Collection<GroundLiteral> gndLits = groundedMarkovNetwork.getAllGroundLiterals_ExpensiveVersion(); // TODO - remove _Expensive*
		if (gndLits != null) for (GroundLiteral gndLiteral : gndLits) {
			if (gndLiteral == null) {
		//		Utils.println("Null ground literal : skipping"); // Mod TVK
				continue;
			}
			if (holdInitialLiteralValues.get(gndLiteral) == null) {
		//		Utils.println("Null hold for ground literal : " + gndLiteral.toPrettyString() + " skipping"); // Mod TVK
				continue;	
			}
			gndLiteral.setValueOnly(holdInitialLiteralValues.get(gndLiteral), timeStamp); }
	}	
	

	
	public  void updateMissingLiterals() {
		if (Utils.getSizeSafely(groundedMarkovNetwork.task.getHiddenLiterals()) == 0 ||
				Utils.random() > missingValueUpdateRate) {
			// No hidden/missing data or not updating in this round
			return;
		}
		long start = System.currentTimeMillis();
		// TODO(tushar) : Do we need to reset/save these values ? Or does sampling take care?
		groundedMarkovNetwork.task.setAllQueryVariablesToTheirTrainingValues(); // Set the values of the ground literals to that in the training set.
		List<GroundLiteral> marked_lits = new ArrayList<GroundLiteral>(groundedMarkovNetwork.getAllGroundLiterals_ExpensiveVersion());
		Set<GroundLiteral> qLits = groundedMarkovNetwork.task.getQueryLiterals();
		marked_lits.removeAll(qLits);
		SAT solver = new SampleSAT(groundedMarkovNetwork, AllOfInference.prior_for_being_true_default, 1, 100);	
		solver.solve(marked_lits, null, true);
	
		double[] sumNumSatisfiedClauses = new double[numberOfClausesUsed];
		Gibbs gibbsSampler = null;
//		MCSAT MCSatSampler = null;
		if (MCMCsamplingTypeForEM == GIBBS_SAMPLING) {
			gibbsSampler = new Gibbs(groundedMarkovNetwork, AllOfInference.prior_for_being_true_default);
			// Don't flip the query literals.
			gibbsSampler.setFixedLiterals(qLits);
		} else {
			Utils.error("Not implemented yet");
		}
		for (int i = 0; i < numMCMCIterationsForEM; i++) {
			if (MCMCsamplingTypeForEM == GIBBS_SAMPLING) {
				gibbsSampler.getNextSample();
			} else {
				Utils.error("Not implemented yet");
			}
			for (int j = 0; j < numberOfClausesUsed; j++) {
				Clause clause = indexToClause[j];
				double newEst = groundedMarkovNetwork.numberOfSatisfiedGroundClauses(clause);
				sumNumSatisfiedClauses[j] += newEst;
			}
		}
		for (int i = 0; i < numberOfClausesUsed; i++) {
			numSatisfiedGroundClausesInDatabase[i] = sumNumSatisfiedClauses[i] / numMCMCIterationsForEM;
			/*Utils.println("% Number of new satisfied training clauses " +
					 Utils.truncate(numSatisfiedGroundClausesInDatabase[i], 3) + " for '" +
					 indexToClause[i] + "'.");*/
		}
		long end       = System.currentTimeMillis();
		double timeTaken = (end - start) / 1000.0;
		 Utils.println("Took " + Utils.truncate(timeTaken, 3) + " seconds to perform EM");
	}
	
	/** 
	 * Prints the weights of the clauses. Useful for debugging purposes.
	 */
	public void printClauseWeights() {
		for (int j = 0; j < numberOfClausesUsed; j++) { 
    		Clause clause = indexToClause[j];
    		Utils.println(clause.toString());
		}
	}
	/**
	 * Provide a '+=' capability.  These maps are used instead of arrays for code robustness, even if at a lost of some cpu time.
	 * @param map
	 * @param increment
	 */	
	protected Double increment(Map<Clause,Double> map, Clause clause, double increment) {
		Double lookup = map.get(clause);
		if (lookup == null) { // If not in there, default to 0.0. 
			map.put(clause, increment);
			return increment;
		}
		else {
			Double result = map.get(clause) + increment;
			map.put(clause, result);
			return result;
		}
	}
	/**
	 * Provide a '++' capability.  These maps are used instead of arrays for code robustness, even if at a lost of some cpu time.
	 * @param map
	 * @param increment
	 */	
	protected Double increment(Map<Clause,Double> map, Clause clause) {
		return increment(map, clause, 1.0);
	}
	/**
	 * Provide a '*=' capability.  These maps are used instead of arrays for code robustness, even if at a lost of some cpu time.
	 * @param map
	 * @param increment
	 */	
	protected Double multiply(Map<Clause, Double> map, Clause clause, double multipler) {
		Double lookup = map.get(clause);
		if (lookup == null) { // If not in there, default to 0.0.   (Maybe should default to 1?  But Java would default a Double to 0.0, so we'll do that.
			return 0.0;
		}
		else {
			Double result = map.get(clause) * multipler;
			map.put(clause, result);
			return result;
		}
	}
}