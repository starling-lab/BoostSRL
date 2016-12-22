package edu.wisc.cs.will.MLN_Inference;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.wisc.cs.will.MLN_Task.GroundLiteral;
import edu.wisc.cs.will.MLN_Task.GroundedMarkovNetwork;
import edu.wisc.cs.will.MLN_Task.MLNreductionProblemTooLargeException;
import edu.wisc.cs.will.Utils.Utils;

/**
 * This is the abstract base Inference class.
 * 
 * MCSAT Inference -  computes marginal probabilities of each query literal in the presence of hard-to-satisfy clauses (?).
 * --------------------------------------------------------------------------------------------------------------
 *   findQueryState (inherited from MCMCInference):
 *      for numberOfMCMCtrials trials, do a burn-in and then count statistics over each sample
 *      getNewSample(): calls SampleSAT
 *
 * SampleSAT - samples quasi-uniformly from those states that (quasi) satisfy a set of clauses
 * --------------------------------------------------------------------------------------------------------------
 *   either does a WalkSAT (i.e., greedy) move or a SA (random, but probabilistically accept) move
 *
 * MaxWalkSAT - tries to set literals to maximize the weighted sum of satisfied clauses.
 * --------------------------------------------------------------------------------------------------------------
 * 
 * 
 * @author pavan and shavlik
 */
public abstract class Inference extends AllOfInference {
	@SuppressWarnings("unused")
	private static final int debugLevel = 0;
	
	protected GroundedMarkovNetwork      groundedMarkovNetwork;
	protected List<InferenceResult>      result;
	protected Map<GroundLiteral,String>  documentationForQueries;
	protected InferenceResultComparator  inferenceResultComparator = new InferenceResultComparator();
	// Literals that shouldn't be flipped, they are evidence for this run.  
	protected Set<GroundLiteral>         fixedLiterals = null;
	
	public Inference(GroundedMarkovNetwork groundedMarkovNetwork) {
		this.groundedMarkovNetwork = groundedMarkovNetwork;
	}	
	public List<InferenceResult> findQueryState(Collection<GroundLiteral> queryGndLiterals) throws MLNreductionProblemTooLargeException {
		return findQueryState(queryGndLiterals, null); // Default case when no 'documentation' map provided.
	}
	
	/**
	 * Do the inference and find the probabilities or most probable states of the query literals.
	 */
	public    abstract List<InferenceResult> findQueryState(Collection<GroundLiteral> queryGndLiterals, Map<GroundLiteral,String> documentationForQueries) throws MLNreductionProblemTooLargeException;
	protected abstract void    initForTheseFlexibleLiterals(Collection<GroundLiteral> flexibleGndLiterals);
	
	protected void addAnyQueriesInEvidence(Collection<InferenceResult> results) {
		Collection<GroundLiteral> posEvidInQueries = groundedMarkovNetwork.task.posEvidenceInQueryLiterals;
		if (posEvidInQueries != null) for (GroundLiteral gLit : posEvidInQueries) { 
			results.add(new InferenceResult(gLit, 1.0, "This literal is in the positive evidence."));
		}
		Collection<GroundLiteral> negEvidInQueries = groundedMarkovNetwork.task.negEvidenceInQueryLiterals;
		if (negEvidInQueries != null) for (GroundLiteral gLit : negEvidInQueries) { 
			results.add(new InferenceResult(gLit, 0.0, "This literal is in the negative evidence."));
		}
	}
	
	/**
	 * Display the query literals and the probability that they are true.
	 */
	public void displayOutput() {
		displayOutput(1000); // Do the LOWEST and HIGHEST.  (Most likely lots of ties on bottom, so might want to change later.)
	}
	public void displayOutput(int maxToReport) { // This assumes maxToReport is EVEN; not that big of deal to worry about losing one item if it is odd.
		if (result == null) {
			Utils.println("% Inference hasn't been done yet.");
			return;
		}
		int size = result.size();
		if (size <= maxToReport) {
			for (InferenceResult inferenceResult : result) { 
				Utils.println(inferenceResult.toStringProbAndLiteralOnly("%  ")); 
			}
		} else {
			for (int i = 0; i < maxToReport / 2; i++) { Utils.println(result.get(i       ).toStringProbAndLiteralOnly("%  ")); }
			Utils.println("%  ... skipping the middle " + Utils.comma(size - maxToReport) + " results.");
			for (int i = maxToReport / 2; i > 0; i--) { Utils.println(result.get(size - i).toStringProbAndLiteralOnly("%  ")); }
		}
	}	

	private double minProb = 1e-6; // Don't want to take logs of zero.  M-estimates will prevent this (assuming M != 0), but still might want to further 'hedge' one's probability estimates (so this should really be a tuned parameter).
	private double maxProb = 1.0 - minProb;
	public double reportOnTheseExamples(Set<GroundLiteral> posQueryLiterals, Set<GroundLiteral> negQueryLiterals, int maxToReportPos, int maxToReportNeg) {
		if (result == null) {
			Utils.println("% Inference hasn't been done yet.");
			return -1.0;
		}
		if (Utils.getSizeSafely(posQueryLiterals) + Utils.getSizeSafely(negQueryLiterals) <= 0) { return -1.0; }
		// See page 7 of http://ftp.cs.wisc.edu/machine-learning/shavlik-group/goadrich.ilp07.pdf
		double meanCrossEntroyPos = 0.0;
		double meanCrossEntroyNeg = 0.0;
		int    size               = result.size();
		int posCounter = 0; int posReported = 0;
		int negCounter = 0; int negReported = 0;
		Utils.println("\n% Results on the " + Utils.comma(size) + " training examples (at most " + Utils.comma(maxToReportPos) + " pos and " + Utils.comma(maxToReportNeg) + " neg examples will be reported)."); 
		if (Utils.getSizeSafely(result) > 0) for (int i = size - 1; i >= 0; i--) { // Report the HIGHEST PROB. negatives.
			InferenceResult iResult = result.get(i);
			GroundLiteral   gLit    = iResult.groundLiteral;
			
			// Allow a literal to be in both the positive and negative examples, even if that should rarely/never happen.
			if (negQueryLiterals != null && negQueryLiterals.contains(gLit)) { negCounter++;
				if (++negReported <= maxToReportNeg) { Utils.println("%   Sorted example  #" + Utils.comma(i+1) + " is negative.  Its predicted probability = " + Utils.truncate(iResult.probability, 3)); }
				meanCrossEntroyNeg += Math.log(Math.max(minProb, Math.min(1.0 - iResult.probability, maxProb)));
			}	
		}
		if (Utils.getSizeSafely(result) > 0) for (int i = 0; i < size; i++) { // Report the LOWEST PROB. positives.
			InferenceResult iResult = result.get(i);
			GroundLiteral   gLit    = iResult.groundLiteral;
			if (posQueryLiterals != null && posQueryLiterals.contains(gLit)) {  posCounter++;
				if (++posReported <= maxToReportPos) { Utils.println("%   Sorted example #" + Utils.comma(i+1) + " is positive.  Its predicted probability = " + Utils.truncate(iResult.probability, 3)); }
				meanCrossEntroyPos += Math.log(Math.max(minProb, Math.min(iResult.probability, maxProb)));
			}
		}
		int numbPos = Utils.getSizeSafely(posQueryLiterals);
		int numbNeg = Utils.getSizeSafely(negQueryLiterals);
		if (numbPos != posCounter) { Utils.waitHere("numbPos = " + Utils.comma(numbPos) + " but posCounter = " + Utils.comma(posCounter)); }
		if (numbNeg != negCounter) { Utils.waitHere("numbNeg = " + Utils.comma(numbNeg) + " but negCounter = " + Utils.comma(negCounter)); }
		double result = (meanCrossEntroyPos + meanCrossEntroyNeg) /  Math.max(1, numbPos + numbNeg);
		int maxToReport = maxToReportPos + maxToReportNeg;
		if (maxToReport > 0) { Utils.println("% The mean cross entropy for the " + Utils.comma(numbPos) + " positive and the " + Utils.comma(numbNeg) + " negative examples is " + Utils.truncate(result, 4) + "."); }
		if (maxToReport > 0) { Utils.println("%   The mean cross entropy for just the positive examples is " + Utils.truncate(meanCrossEntroyPos / Math.max(1, numbPos), 4) + " = " + Utils.truncate(meanCrossEntroyPos, 4)+ " / " + Utils.comma(numbPos) + "."); }
		if (maxToReport > 0) { Utils.println("%   The mean cross entropy for just the negative examples is " + Utils.truncate(meanCrossEntroyNeg / Math.max(1, numbNeg), 4) + " = " + Utils.truncate(meanCrossEntroyNeg, 4)+ " / " + Utils.comma(numbNeg) + "."); }
		return result;
	}
	public Set<GroundLiteral> getFixedLiterals() {
		return fixedLiterals;
	}
	public void setFixedLiterals(Set<GroundLiteral> fixedLiterals) {
		this.fixedLiterals = fixedLiterals;
	}

	public void cleanupSampleGenerator() {
		return;
	}
}