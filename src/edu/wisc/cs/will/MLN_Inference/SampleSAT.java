package edu.wisc.cs.will.MLN_Inference;
import java.util.Collection;

import edu.wisc.cs.will.MLN_Task.GroundClause;
import edu.wisc.cs.will.MLN_Task.GroundLiteral;
import edu.wisc.cs.will.MLN_Task.GroundedMarkovNetwork;
import edu.wisc.cs.will.MLN_Task.TimeStamp;
import edu.wisc.cs.will.Utils.Utils;

/**
 * SampleSAT, which is a hybrid of MaxWalkSAT and Simulated Annealing.  
 * Samples quasi-uniformly from those states that (quasi) satisfy a set of clauses.
 * 
 *   W.Wei, J. Erenrich, and B. Selman.
 *   Towards efficient sampling: Exploiting random-walk strategies. 
 *   In Proceedings of the Nineteenth National Conference on Artificial Intelligence, San Jose, CA, 2004. AAAI Press. 
 * 
 * @author pavan and shavlik
 */
public class SampleSAT extends MaxWalkSAT {	
	private static final int    debugLevel = 1;
	
	public  static final double probOfWalkSAT_default                  =   0.50; // Wei, Erenrich, and Selma, AAAI-04 suggest this should be 0.5.
	public  static final double temperatureSA_default                  =  10.00; // Over time this becomes a values so that about 1/e of the bad moves are accepted.
	public  static final int    maxNumStepsAfterSoln_sampleSAT_default =  10;
	
	// With probability p, we choose a WalkSAT step; with probability (1-p), we choose a simulated-annealing step.
	public  double p                    = probOfWalkSAT_default;
	public  double T                    = temperatureSA_default;  // The 'temperature' in simulated annealing.
	public  int    maxNumStepsAfterSoln = maxNumStepsAfterSoln_sampleSAT_default; // We walk (mostly by simulated-annealing steps) for some time even after reaching a solution.
	
	public  double fractionOfStepsAsNumberToSetRandomly = 1.0; // Don't reset ALL ground literals when restarting randomly, since too many might need to be set to reach a satisfying state.
	
	public SampleSAT(GroundedMarkovNetwork groundedMarkovNetwork, double priorProbOfBeingTrue) {
		super(groundedMarkovNetwork, priorProbOfBeingTrue);
	}
	public SampleSAT(GroundedMarkovNetwork groundedMarkovNetwork, double priorProbOfBeingTrue, int maxNumberOfStarts, int maxNumberOfFlips) {
		super(groundedMarkovNetwork, priorProbOfBeingTrue, maxNumberOfStarts, maxNumberOfFlips);
	}		
	public SampleSAT(GroundedMarkovNetwork groundedMarkovNetwork, double priorProbOfBeingTrue, int maxNumberOfStarts, int maxNumberOfFlips,
				     double probOfWalkSAT,   double temperatureSA,  int maxNumStepsAfterSoln) {
		super(groundedMarkovNetwork, priorProbOfBeingTrue, maxNumberOfStarts, maxNumberOfFlips);
		p = probOfWalkSAT;
		T = temperatureSA;
		this.maxNumStepsAfterSoln = maxNumStepsAfterSoln;
	}

	public int getStepsPerSample() {
		return Math.max(maxNumberOfStarts * maxNumberOfFlips, maxNumStepsAfterSoln); // Doesn't include maxNumStepsAfterSoln nor early stopping should a solution be found.
	}
	
	protected int numberChangesMadeBySimulatedAnnealing = 0;
	private   double totalTimeSpentSolving = 0.0;
	// If markedClauses = null, that means 'check all clauses' (i.e., the set is too big to copy).  But if the caller has a small subset, it can explicitly provide that.
	public int solve(Collection<GroundLiteral> markedLiterals, Collection<GroundClause> markedClauses, boolean reportFlag) {
		reportFlagOn = reportFlag;
		int stepsTakenThisTime = 0;
		int numStepsAfterSolution = 0; // This also acts like a Boolean, indicating (if positive) that a solution has been found.
		bestCost      = Double.POSITIVE_INFINITY;
		boolean  done = false;
		trial++;
		endTimer1(); // This also restarts the timer.
		endTimer2();
		String msgForStart = (debugLevel > 0 && reportFlagOn ? "SampleSAT #" + Utils.comma(trial) + ":" : "SampleSAT:");	
		TimeStamp timeStamp = (GroundedMarkovNetwork.doMajorDebug ? new TimeStamp("SampleSAT: trial=" + trial) : null);	
		double probOfRandomStateDuringInit = (fractionOfStepsAsNumberToSetRandomly * maxNumberOfFlips) / groundedMarkovNetwork.getNumberOfGroundLiterals();
		init(markedLiterals, markedClauses, msgForStart, probOfRandomStateDuringInit); seeIfBestCost("SampleSAT", this, "[initial random state]", timeStamp);
		for (int i = 0; i < maxNumberOfStarts; i++) {
			if (numStepsAfterSolution == 0 && i > 0) { init(markedLiterals, markedClauses, msgForStart, probOfRandomStateDuringInit); seeIfBestCost("SampleSAT", this, (debugLevel > 0 ? "[(re)initial random state #" + Utils.comma(trial) + "." + i + "]": "[(re)initial random state]"), timeStamp); } // Restart at a random position if not at a solution.
			endTimer2(); // This also restarts the timer.
			if (debugLevel > 1) { Utils.println("\n% SampleSAT start #" + Utils.comma(trial) + "." + (i + 1) + ", total flips = " + Utils.comma(flips) + (i > 0 ? ".  Last SampleSAT walk took " + Utils.truncate(timeTaken2, 3) + " seconds." : ".")); }
			if (debugLevel > 2) { Utils.print(    "%     "); }
			for (int j = 0; j < maxNumberOfFlips; j++) {
				flips++;
				stepsTakenThisTime++;
				timeStamp = (GroundedMarkovNetwork.doMajorDebug ? new TimeStamp("SampleSAT: trial=" + Utils.comma(trial) + ", start=" + Utils.comma(i + 1) + ", flip=" + Utils.comma(flips)) : null);
				if (Utils.random() < p) { // MaxWalkSAT step
					GroundClause unsatisfiedClause = getActiveClauseRandomly(markedClauses, timeStamp);
					if (unsatisfiedClause == null) {				
						if (numStepsAfterSolution > maxNumStepsAfterSoln) {	done = true; break;}
						//if (debugLevel > 2) { Utils.println("%   Reaching a solution on step #" + Utils.comma(stepsTakenThisTime) + "."); }				
						if (debugLevel > 3 && reportFlagOn) {
							Utils.println("% State after reaching a solution on step #" + Utils.comma(stepsTakenThisTime) + ":");
							groundedMarkovNetwork.reportGroundLiteralState(25);
						}											
						if (numStepsAfterSolution == 0) {  // Have reached a solution - no more active clauses.
							if (debugLevel > 1 && reportFlagOn) { Utils.println("% SampleSAT: Have no more active clauses."); }
							numStepsAfterSolution++; 
						}
					} else {
						if (debugLevel > 2 && reportFlagOn) { Utils.print((numStepsAfterSolution == 0 ? "w" : "W") + unsatisfiedClause.getLength()); }
						boolean changed = doWalkSAT(unsatisfiedClause, markedClauses, timeStamp);
						if (changed) { numberChangesMadeByWalkSAT++; }
						numberWalkSATcalls++;
					}
				} else { // Perform SA.
					if (debugLevel > 2 && reportFlagOn) { Utils.print(numStepsAfterSolution == 0 ? "s" : "S"); }
					boolean changed = doSimulatedAnnealing(markedLiterals, markedClauses, timeStamp);
					if (changed) { numberChangesMadeBySimulatedAnnealing++; }
					if (numStepsAfterSolution > 0) {
						if (debugLevel > 3 && reportFlagOn) {
							Utils.println("% Simulated annealing state:");
							groundedMarkovNetwork.reportGroundLiteralState(25);
						}			
					}
				}
				seeIfBestCost("SampleSAT", this, (debugLevel > 0 && reportFlagOn ? "[trial=" + Utils.comma(trial) + ", start=" + Utils.comma(i + 1) + ", flip=" + Utils.comma(j + 1) + ", total=" + Utils.comma(flips) + "]" : "[end of flip]"), timeStamp); // Check after every flip, since calculation is easy.			
				if (numStepsAfterSolution > 0) {				
					numStepsAfterSolution++;
					// Don't stop here unless at a solution (i.e., no active clauses).
					if (numStepsAfterSolution > maxNumStepsAfterSoln &&	getActiveClauseRandomly(markedClauses, timeStamp) == null) { done = true; break; }
				}
			}
			if (debugLevel > 2) { Utils.println(""); }
			if (done) { break; } // Exit the outer FOR loop.
		}
		// Assign the best solution to the literals.
		timeStamp = (GroundedMarkovNetwork.doMajorDebug ? new TimeStamp("SampleSAT: trial=" + trial + " assign best solution") : null);
		assignBestSolutionToTheLiterals(markedLiterals, markedClauses, "SampleSAT", false, timeStamp);
		if (debugLevel > -10) {
			endTimer1();
			totalTimeSpentSolving += timeTaken1;
			if (reportFlagOn) { } // MOD TVK Utils.println("%     Took " + Utils.truncate(timeTaken1, 3) + " seconds for SampleSAT trial #" + Utils.comma(trial) + ", best score = " + Utils.truncate(bestCost, 3) + ". [Overall ave = " + Utils.truncate(totalTimeSpentSolving / trial, 3) + " sec]."); }
		}
		return stepsTakenThisTime;
	}
	
	/**
	 * A simulated-annealing step.
	 */
	private double simAnnealNumeratorTotal = 0.0;
	private int    simAnnealCalls          = 0;
	private double simAnnealAccepts        = 0.0;
	private boolean doSimulatedAnnealing(Collection<GroundLiteral> markedLiterals, Collection<GroundClause> markedClauses, TimeStamp timeStamp) {	
		GroundLiteral literalToFlip = Utils.chooseRandomFromThisCollection(markedLiterals);
		if (literalToFlip == null) { return false; }
		computeDeltaCost(literalToFlip);
		if (result0_computeDeltaCost <= 0.0) { // If an improvement (or tie), always accept.
			if (debugLevel > 1) { Utils.println("% SA picked '" + literalToFlip + " with deltaCost over all clauses = " + Utils.truncate(result0_computeDeltaCost, 2)); }
			flipLiteral(literalToFlip, markedClauses, result1_computeDeltaCost, timeStamp);	
			return true;
		} else {
			double probabilityOfFlip = Math.exp(-result0_computeDeltaCost / T);
			simAnnealNumeratorTotal += result0_computeDeltaCost;
			simAnnealCalls++;
			if (simAnnealCalls % 100 == 0) { // Periodically recompute the temperature so it becomes the average delta cost and, hence, the probability of accepting a bad move is 1/e.  TODO would be nice to use the MEDIAN instead of the MEAN, but that is harder to compute. 
				if (debugLevel > -22 && reportFlagOn) { Utils.println("%     Simulated annealing ratio: " + Utils.truncate(simAnnealNumeratorTotal, 2) + "/" + Utils.comma(simAnnealCalls) + " = " + Utils.truncate(simAnnealNumeratorTotal / simAnnealCalls, 2) + ".  T = " + Utils.truncate(T, 2)+ ".  Bad-move accept ratio = " + Utils.truncate(simAnnealAccepts/ simAnnealCalls, 2) + " (target value is roughly 1/e = 0.37)."); }
				double alpha = 1 / (simAnnealCalls / 10.0);
				T = alpha * T + (1 - alpha) * (simAnnealNumeratorTotal / simAnnealCalls);
				if (simAnnealCalls > 1000) { simAnnealCalls = 0; simAnnealAccepts = 0.0; simAnnealNumeratorTotal = 0.0; } // Clear every now and then so huge values do not overwhelm (i.e., skew the mean).
			}
			if (Utils.random() < probabilityOfFlip) {
				simAnnealAccepts++;
				if (debugLevel > 1) { Utils.println("% Even though it is a bad move, SA picked '" + literalToFlip + " with deltaCost over all clauses = " + Utils.truncate(result0_computeDeltaCost, 2)); }
				flipLiteral(literalToFlip, markedClauses, result1_computeDeltaCost, timeStamp);	
				return true;
			}
			return false;
		}						
	}	
}