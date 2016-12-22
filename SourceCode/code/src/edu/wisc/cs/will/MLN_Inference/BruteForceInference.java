package edu.wisc.cs.will.MLN_Inference;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.MLN_Task.Block;
import edu.wisc.cs.will.MLN_Task.GroundClause;
import edu.wisc.cs.will.MLN_Task.GroundLiteral;
import edu.wisc.cs.will.MLN_Task.GroundedMarkovNetwork;
import edu.wisc.cs.will.MLN_Task.MLN_Task;
import edu.wisc.cs.will.MLN_Task.MLNreductionProblemTooLargeException;
import edu.wisc.cs.will.MLN_Task.TimeStamp;
import edu.wisc.cs.will.Utils.Utils;

/**
 * This class looks at all possible groundings of all the literals, and just computes the probability of each query literal in a brute-force fashion.
 * 
 * @author pavan and shavlik
 */
public class BruteForceInference extends Inference {
	private final static int debugLevel = 1;
	
	public double warnIfThisManyCombos = 1e7; // Warn if there are more than 10M combinations.
	
	// We do the complete inference on each Markov blanket, one by one.
	// These are the blocks, the ground literals, the query literals, and the ground clauses in the current Markov blanket.
	private Map<GroundLiteral,Block>  currentBlocks;  // TODO blocks
	private Collection<GroundLiteral> currentSatisfiableLiterals;  // We walk through these and assume they are in order, so need to use this special type of Set.
	private Collection<GroundClause>  currentSatisfiableClauses;   // Clauses in the local blanket.
	private Collection<GroundLiteral> flexibleGroundLiteralsComputed = new HashSet<GroundLiteral>(4); // Some query literals are coupled to others.  Some 'hidden' literals will be here as well, but that is fine.
	
	private Map<GroundLiteral,Double> sumWeightSatisfiedClausesWhenLiteralEqualsTrue;  // TODO - put in an array for faster access and updating.
	private Map<GroundLiteral,Double> sumWeightSatisfiedClausesWhenLiteralEqualsFalse;
	
	public BruteForceInference(GroundedMarkovNetwork groundedMarkovNetwork) {
		super(groundedMarkovNetwork);
		if (debugLevel > 0) { 
			Utils.println("\n% BruteForceInference");
			Utils.println("%  Query       Literals: " + Utils.limitLengthOfPrintedList(groundedMarkovNetwork.task.getQueryLiterals(),        10));
			Utils.println("%  PosEvidence Literals: " + Utils.limitLengthOfPrintedList(groundedMarkovNetwork.task.getPosEvidenceLiterals(),  10));
			Utils.println("%  NegEvidence Literals: " + Utils.limitLengthOfPrintedList(groundedMarkovNetwork.task.getNegEvidenceLiterals(),  10));
			Utils.println("%  Hidden      Literals: " + Utils.limitLengthOfPrintedList(groundedMarkovNetwork.task.getHiddenLiterals(),       10));
			Utils.println("%  Clauses:              " + Utils.limitLengthOfPrintedList(groundedMarkovNetwork.getAllClausesThatWereGrounded(),10));
		}
		if (Utils.getSizeSafely(groundedMarkovNetwork.task.getQueryLiterals()) < 1) { Utils.error("There needs to be some query literals."); }
		
		sumWeightSatisfiedClausesWhenLiteralEqualsTrue  = new HashMap<GroundLiteral,Double>(4);
		sumWeightSatisfiedClausesWhenLiteralEqualsFalse = new HashMap<GroundLiteral,Double>(4);
	}
	
	protected void initForTheseFlexibleLiterals(Collection<GroundLiteral> lits) {
		if (lits != null) for (GroundLiteral flexibleGroundLiteral : lits) if (!groundedMarkovNetwork.task.isaEvidenceLiteral(flexibleGroundLiteral)) {
			sumWeightSatisfiedClausesWhenLiteralEqualsTrue.put( flexibleGroundLiteral, 0.0);
			sumWeightSatisfiedClausesWhenLiteralEqualsFalse.put(flexibleGroundLiteral, 0.0);
		}	
	}
	
	public List<InferenceResult> findQueryState(Collection<GroundLiteral> queryGndLiterals, Map<GroundLiteral,String> documentationForQueries) throws MLNreductionProblemTooLargeException {
		if (debugLevel > 0) { Utils.println("\n% Entering 'findQueryState' with query literals = " + Utils.limitLengthOfPrintedList(queryGndLiterals, 25)); }
		currentSatisfiableLiterals = groundedMarkovNetwork.getAllGroundLiterals_ExpensiveVersion(); // OK to use expensive case, since should be small since we're brute-forcing anyway.
		TimeStamp timeStamp =  (GroundedMarkovNetwork.doMajorDebug ? new TimeStamp("BruteForceInference: findQueryState") : null);
		groundedMarkovNetwork.initializeForTheseQueries(queryGndLiterals);
		initForTheseFlexibleLiterals(currentSatisfiableLiterals); 
		flexibleGroundLiteralsComputed.clear();
		int counter = 0;
		for (GroundLiteral queryGroundLiteral : queryGndLiterals) {
			if (groundedMarkovNetwork.task.isaEvidenceLiteral(queryGroundLiteral)) { Utils.error("Found evidence in the queries: " + queryGroundLiteral); } 
			if (debugLevel > 0) { Utils.println("\n% In findQueryState:  query literal = " + queryGroundLiteral.toStringLiteralOnly() + ",  flexibleGroundLiteralsComputed = " + Utils.limitLengthOfPrintedList(flexibleGroundLiteralsComputed, 10)); }
			if (flexibleGroundLiteralsComputed.contains(queryGroundLiteral)) { continue; } // Have already processed this ground literal.
			Object currentMarker = groundedMarkovNetwork.pushCurrentMarkovBlanket(queryGroundLiteral, this);
			currentSatisfiableClauses = groundedMarkovNetwork.getAllGroundClauses_ExpensiveVersion(); // OK to use expensive case, since should be small since we're brute-forcing anyway.
			if (groundedMarkovNetwork.countOfMarkedGroundClauses() < currentSatisfiableClauses.size()) { 
				Utils.println(" groundedMarkovNetwork.countOfMarkedGroundClauses() = " + Utils.comma(groundedMarkovNetwork.countOfMarkedGroundClauses()));
				Utils.println(" currentSatisfiableClauses                          = " + Utils.comma(currentSatisfiableClauses));
				Utils.limitLengthOfPrintedList(currentSatisfiableClauses, 25);
				Utils.writeMe("Need to remove the unmarked clauses."); 
			}
			if (debugLevel > 0) {
				if (currentSatisfiableLiterals != null) for (GroundLiteral lit : currentSatisfiableLiterals) { lit.setValueOnly(true, null); } // Do this for better printouts.
				Utils.println("%   The current ground clauses for query #" + Utils.comma(++counter) + " = '" + queryGroundLiteral.toStringLiteralOnly() + "':");
				if (Utils.getSizeSafely(currentSatisfiableClauses) < 1)                                 { Utils.println("%     NONE."); }
				if (currentSatisfiableClauses != null) for (GroundClause c : currentSatisfiableClauses) { Utils.println("%     " + c.toStringLiteralOnly());  }
			}
			if (debugLevel > 0) {
				Utils.println("%   The current ground literals for this query:");
				if (Utils.getSizeSafely(currentSatisfiableLiterals) < 1)                                     { Utils.println("%     NONE."); }
				if (currentSatisfiableLiterals != null) for (GroundLiteral lit : currentSatisfiableLiterals) { Utils.println("%     " + lit.toStringLiteralOnly()); }
			}
			if (Utils.getSizeSafely(currentSatisfiableLiterals) < 1) { continue; }
			flexibleGroundLiteralsComputed.addAll(currentSatisfiableLiterals);
			int    numberOfLiteralsToToggle = Utils.getSizeSafely(currentSatisfiableLiterals);
			double numberCombos             = Math.pow(2.0, numberOfLiteralsToToggle);
			if (debugLevel > 0 || numberCombos >= warnIfThisManyCombos) { Utils.println("%   There are " + numberOfLiteralsToToggle + " relevant satisfiable literals, so " + Utils.truncate(numberCombos, 0) + " combinations to consider."); }
			sampleAllCombinations(groundedMarkovNetwork.task, 0, 0, timeStamp);
			if (debugLevel > 0 && currentSatisfiableLiterals != null) for (GroundLiteral gLit : currentSatisfiableLiterals) {
				Utils.println("%  Sums" +
						" for: " + gLit.toStringLiteralOnly());
				Utils.println("%     when true: "  + Utils.truncate(sumWeightSatisfiedClausesWhenLiteralEqualsTrue.get( gLit), 2) + 
							      ", when false: " + Utils.truncate(sumWeightSatisfiedClausesWhenLiteralEqualsFalse.get(gLit), 2));
			}
			groundedMarkovNetwork.popGroundThisMarkovNetwork(currentMarker);
		}	
		
		result = new ArrayList<InferenceResult>(Utils.getSizeSafely(queryGndLiterals));
		for (GroundLiteral gLit : queryGndLiterals) {
			if (     groundedMarkovNetwork.task.isaPositiveEvidenceLiteral(gLit)) { // TODO - if evidence is weighted, then convert to a probability and use that.
				result.add(new InferenceResult(gLit, 1.0, (documentationForQueries == null ? "" : documentationForQueries.get(gLit))));
			}
			else if (groundedMarkovNetwork.task.isaNegativeEvidenceLiteral(gLit)) {
				result.add(new InferenceResult(gLit, 0.0, (documentationForQueries == null ? "" : documentationForQueries.get(gLit))));
			}
			else {
				double numer       =         sumWeightSatisfiedClausesWhenLiteralEqualsTrue.get( gLit);
				double denom       = numer + sumWeightSatisfiedClausesWhenLiteralEqualsFalse.get(gLit);
				double probability = (denom <= 0.0 && numer <= 0.0 ? 0.5 : numer / denom);
			
				result.add(new InferenceResult(gLit, probability, (documentationForQueries == null ? "" : documentationForQueries.get(gLit))));
			}
		}
		addAnyQueriesInEvidence(result);
		Collections.sort(result, inferenceResultComparator); // LEAST probable will be in front.
		return result;
	}
	
	/**
	 * A recursive method which recursively assigns all possible truth assignments to all ground literals.
	 * 
	 * @param literalIndex Assign true and false to the literal at literalIndex
	 * and recursively call sampleAllCombinations with literalIndex + 1.
	 */
	public void sampleAllCombinations(MLN_Task task, int blockIndex, int literalIndex, TimeStamp timeStamp) {
		if (blockIndex < Utils.getSizeSafely(currentBlocks)) {
			Block block = currentBlocks.get(blockIndex);
			block.initValues(timeStamp);
			boolean newStateExists = true;
			do {
				sampleAllCombinations(task, blockIndex + 1, literalIndex, timeStamp);
				newStateExists = block.moveToNextState(timeStamp);
			} while (newStateExists);		
		} else if (Utils.getSizeSafely(currentSatisfiableLiterals) > 0) {
			GroundLiteral literal = Utils.getIthItemInCollectionUnsafe(currentSatisfiableLiterals, literalIndex);
			if (debugLevel > 0) { Utils.println("%  In sampleAllCombinations(" + blockIndex + "," + literalIndex + ") with literal = '" + literal.toStringLiteralOnly() + "'"); }
			if (literalIndex == (currentSatisfiableLiterals.size() - 1)) { // At last literal.
				// All literals have some truth assignment.
				if (literal.getBlock() != null) {
					updateSumSatisfiedClauses(task);
				} else {
					if (debugLevel > 1) { Utils.println("%   Use: " + literal.toStringLiteralOnly() + " = " + literal.getValue()); }
					updateSumSatisfiedClauses(task);			
					literal.flipSpeculative();			
					if (debugLevel > 1) { Utils.println("%   Use: " + literal.toStringLiteralOnly() + " = " + literal.getValue()); }
					updateSumSatisfiedClauses(task);			
					literal.flipSpeculative();
				}				
			} else {
				if (literal.getBlock() != null) {
					sampleAllCombinations(task, blockIndex, literalIndex + 1, timeStamp);
				} else { // Try both settings for this literal (will be 'on hold' until reached end of list of literals).
					if (debugLevel > 1) { Utils.println("%   Use: " + literal.toStringLiteralOnly() + " = " + literal.getValue()); }
					sampleAllCombinations(task, blockIndex, literalIndex + 1, timeStamp);
					literal.flipSpeculative();
					if (debugLevel > 1) { Utils.println("%   Use: " + literal.toStringLiteralOnly() + " = " + literal.getValue()); }
					sampleAllCombinations(task, blockIndex, literalIndex + 1, timeStamp);
					literal.flipSpeculative();
				}				
			}
		} else { updateSumSatisfiedClauses(task); }
	}
	
	/**
	 * Compute the (unnormalized) probability of the world with the current truth assignment.
	 * Add this to the probability counts of the current query literals.	 
	 */
	private void updateSumSatisfiedClauses(MLN_Task task) {	
		double satWeight = groundedMarkovNetwork.getWeightShortageOfCurrentlySatisfiedClauses(true);
		if (debugLevel > 2) { Utils.println("%      Final result: weightShortageOfCurrentlySatisfiedClauses = " + Utils.truncate(satWeight, 3)); }
		// Update probabilities of the current query literals.
		if (debugLevel > 0) { 
			Utils.print("%   Current world state: ");
			boolean firstTime = true;
			for (GroundLiteral queryliteral : currentSatisfiableLiterals) {
				if (firstTime) { firstTime = false; } else { Utils.print(","); }
				Utils.print(" " + queryliteral.toStringLiteralOnly() + " = " + queryliteral.getValue());
			}
		}
		if (debugLevel > 0) { Utils.println(""); }
		for (GroundLiteral queryliteral : currentSatisfiableLiterals) {
			if (debugLevel >  0) { Utils.print("%        Add exp(" + Utils.truncate(satWeight, 3) + ") to the " + (queryliteral.getValue() ? "'true' " : "'false'") + " case for '" + queryliteral.toStringLiteralOnly() + "'."); }
			if (debugLevel == 1) { Utils.println(""); }
			if (queryliteral.getValue()) { 
				Double oldWgt = sumWeightSatisfiedClausesWhenLiteralEqualsTrue.get( queryliteral);
				if (oldWgt == null) { Utils.error("Could not find '" + queryliteral + "' in " + sumWeightSatisfiedClausesWhenLiteralEqualsTrue);  }
				sumWeightSatisfiedClausesWhenLiteralEqualsTrue.put(    queryliteral,   oldWgt + Math.exp(satWeight));
				if (debugLevel > 1) { Utils.println("   Old sum: " + Utils.truncate(oldWgt, 3) + "  New sum: " +  Utils.truncate(sumWeightSatisfiedClausesWhenLiteralEqualsTrue.get( queryliteral), 3)); }
			} else {
				Double oldWgt = sumWeightSatisfiedClausesWhenLiteralEqualsFalse.get(queryliteral);
				if (oldWgt == null) { Utils.error("Could not find '" + queryliteral + "' in " + sumWeightSatisfiedClausesWhenLiteralEqualsFalse); }
				sumWeightSatisfiedClausesWhenLiteralEqualsFalse.put(   queryliteral,   oldWgt + Math.exp(satWeight));
				if (debugLevel > 1) { Utils.println("   Old sum: " + Utils.truncate(oldWgt, 3) + "  New sum: " +  Utils.truncate(sumWeightSatisfiedClausesWhenLiteralEqualsFalse.get( queryliteral), 3)); }
			}
		}
	}
}