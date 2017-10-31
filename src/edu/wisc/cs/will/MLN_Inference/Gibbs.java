package edu.wisc.cs.will.MLN_Inference;
import java.util.*;
import java.util.Map.Entry;

import edu.wisc.cs.will.MLN_Task.Block;
import edu.wisc.cs.will.MLN_Task.GroundLiteral;
import edu.wisc.cs.will.MLN_Task.GroundedMarkovNetwork;
import edu.wisc.cs.will.MLN_Task.TimeStamp;
import edu.wisc.cs.will.Utils.Utils;

/**
 * This class implements Gibbs Sampling.
 * 
 * @author pavan and shavlik
 */
public class Gibbs  extends AllOfInference {
	private final static int    debugLevel = 1;
	
	private final static int    doubleMinExponentBase2 = -1022; // In Java 1.6 this is Double.MIN_EXPONENT.
	private final static int    doubleMaxExponentBase2 =  1023; // In Java 1.6 this is Double.MAX_EXPONENT.
	private final static double doubleMinExponentBaseE = doubleMinExponentBase2 * Math.log(2);
	private final static double doubleMaxExponentBaseE = doubleMaxExponentBase2 * Math.log(2);
	private final static double maxRange               = doubleMaxExponentBaseE - doubleMinExponentBaseE;
	
	private GroundedMarkovNetwork groundedMarkovNetwork;
	
	// Literals that shouldn't be flipped, they are evidence for this run.  
	private Set<GroundLiteral> fixedLiterals;
		
	public Gibbs(GroundedMarkovNetwork groundedMarkovNetwork, double priorProbOfBeingTrue) {
		this.groundedMarkovNetwork = groundedMarkovNetwork;
		this.prior_for_being_true  = priorProbOfBeingTrue;
		fixedLiterals = new HashSet<GroundLiteral>();
	}
	
	public int getStepsPerSample() {
		return 1; // Could argue this should be the number of literals to consider, but that isn't how the others are counted.
	}
	
	/**
	 * Generate the next Gibbs sample. Sample each literal based on its conditional probability.
	 */
	public void getNextSample() {
		// First need to properly set all literals in blocks. 
		Map<GroundLiteral,Block> blocks = groundedMarkovNetwork.getAllBlocks();
		TimeStamp timeStamp = (GroundedMarkovNetwork.doMajorDebug ? new TimeStamp("Gibbs: getNextSample()") : null);
		if (blocks != null) {
			for (Entry<GroundLiteral,Block> entry : blocks.entrySet()) {
				Block block = entry.getValue();
				block.initValues(timeStamp);			
				if (block.valuesFixed()) { continue; }
				int numCombinations = block.getNumCombinations();
				// To avoid under or over flows, do in two passes to find minimum value and use that to set offset.  Also check for the range of exponents (max-min) used.
				double[] weightSatisfiedClauses = new double[numCombinations];
				double   smallestSum            = Double.POSITIVE_INFINITY;
				double   largestSum             = Double.NEGATIVE_INFINITY;
				int      index                  = 0;
				do { // Walk through all the states of this block.  Keep track of the smallest and largest sums.
					double thisBlockSum = block.sumSatisfiedClauses();
					weightSatisfiedClauses[index++] = thisBlockSum;
					if (thisBlockSum < smallestSum) { smallestSum = thisBlockSum; }
					if (thisBlockSum > largestSum)  { largestSum  = thisBlockSum; }
				} while (block.moveToNextState(timeStamp));
				if (index != numCombinations) {	Utils.error("Bug in code: numCombinations in block is not what it should be.");	}
				
				double[] probTrue = new double[numCombinations]; // Only used if haveLargeExponentRange=true;
				double   probSum  = 0.0; // This is the denominator, i.e. the normalizing term.
				double   offset   = smallestSum - doubleMinExponentBaseE; // This is used in an attempt to avoid overflow (and underflow).
				boolean  haveLargeExponentRange = false;
				if (largestSum - smallestSum > maxRange) { // Use Pavan's code [double for-loops] here.  Could also simply set to 0 all those that would underflow, but this version should be OK (unless 'weightSatisfiedClauses[j] - weightSatisfiedClauses[i]' goes out of range ...). 
					if (debugLevel > 0) { Utils.println("Have too large of range for exponents [" + smallestSum + "," + largestSum + "], so need to rewrite this code."); } 
					haveLargeExponentRange = true;
					for (int i = 0; i < numCombinations; i++) {
						double denominator = 1.0;
						for (int j = 0; j < numCombinations; j++) { // Use e^a / (e^a + e^b + e^c) = 1 / (1 + e^[b-a] + e^[c-a]).
							if (j != i) denominator += Math.exp(weightSatisfiedClauses[j] - weightSatisfiedClauses[i]);					
						}
						probTrue[i] = 1.0/denominator;
						probSum    += probTrue[i];
					}
				} else {
					for (int i = 0; i < numCombinations; i++) {	
						probSum  += Math.exp(weightSatisfiedClauses[i] - offset); // All numbers will stay in range.
					}
				}
				// Do a roulette-wheel calculation to decide which state to use.
				double rand = Utils.random() * probSum;
				double sum  = 0.0;
				for (int i = 0; i < numCombinations; i++) {
					sum += (haveLargeExponentRange ? probTrue[i] : Math.exp(weightSatisfiedClauses[i] - offset));
					if (rand <= sum) {
						block.setState(i, timeStamp);
						break;
					}
				}
			}
		}
		
		// For each ground literal NOT in a block, flip its Boolean value proportional to its weight when true vs. its weight when false.
		Collection<GroundLiteral> gndLits = groundedMarkovNetwork.getAllGroundLiterals_ExpensiveVersion(); // TODO - remove _Expensive*();
    	//	Utils.writeMe("Use with lazy?");
		if (gndLits != null) for (GroundLiteral literal : gndLits) if (literal.getBlock() == null) {
			// Dont flip fixedLiterals
			if (fixedLiterals != null && fixedLiterals.contains(literal)) {
				//	Utils.println("Leave "+literal.toString() + " unchanged ");
				continue;
			}
				
			// Set value only doesn't update the clauses, which is used to calculate the weights.
			// TODO Maybe do a similar change for blocks. 
			// literal.setValueOnly(true, timeStamp);
			literal.setValue(true, groundedMarkovNetwork, timeStamp, false);
			double weightSatisfiedClausesWhenTrue  = literal.getWeightSatisfiedClauses();
			// literal.setValueOnly(false, timeStamp);
			literal.setValue(false, groundedMarkovNetwork, timeStamp, false);
			double weightSatisfiedClausesWhenFalse = literal.getWeightSatisfiedClauses();			
			
			// A small trick to avoid Math.exp's from overflowing.  From:  e^pos / (e^pos + e^neg) = 1 / (1 + e^[neg-pos]).
			double probTrue = 1.0 / (1.0 + Math.exp(weightSatisfiedClausesWhenFalse - weightSatisfiedClausesWhenTrue));
			// literal.setValueOnly(Utils.random() < probTrue, timeStamp);
			literal.setValue(Utils.random() < probTrue, groundedMarkovNetwork, timeStamp, false);
			if (debugLevel > 1) { 
				Utils.println("% GIBBS: " + ":  wgt(true)  = " + Utils.truncate(weightSatisfiedClausesWhenTrue,  1)
										  + ",  wgt(false) = " + Utils.truncate(weightSatisfiedClausesWhenFalse, 1)
										  + ",  prob = "       + Utils.truncate(probTrue, 6) 
										  + ", choice = "      + literal.getValue() + " for " + literal);
			}			
		}
	}

	public Set<GroundLiteral> getFixedLiterals() {
		return fixedLiterals;
	}

	public void setFixedLiterals(Set<GroundLiteral> fixedLiterals) {
		this.fixedLiterals = fixedLiterals;
	}	
}