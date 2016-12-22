package edu.wisc.cs.will.MLN_Inference;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import edu.wisc.cs.will.MLN_Task.GroundClause;
import edu.wisc.cs.will.MLN_Task.GroundLiteral;
import edu.wisc.cs.will.MLN_Task.GroundedMarkovNetwork;
import edu.wisc.cs.will.MLN_Task.TimeStamp;
import edu.wisc.cs.will.Utils.Utils;

/**
 * The MaxWalkSAT class.  Tries to set literals to maximize the weighted sum of satisfied clauses.
 * 
 *   H.Kautz, B.Selman,and Y.Jiang.
 *   A general stochastic approach to solving problems with hard and soft constraints. 
 *   In D.Gu, J.Du,and P.Pardalos, editors, The Satisfiability Problem: Theory and Applications, pages 573-586.
 *   American Mathematical Society, New York, NY,1997.
 * 
 * @author pavan and shavlik
 */
public class MaxWalkSAT extends SAT {
	private static final int debugLevel = 0;
	
	public  static final double probGreedyFlip_default            =  0.90; 
	public  static final double maxWalkSATbranchingFactor_default = 25.0;  // If more than this many literals in a clause, randomly sample so that about this many scored.  (Use a DOUBLE so we get a DOUBLE in a division below.)
	
	public               double maxWalkSATbranchingFactor = maxWalkSATbranchingFactor_default;		
	private              double probGreedyFlip            = probGreedyFlip_default;	
	protected            double bestCost                  = Double.POSITIVE_INFINITY;
	
	public MaxWalkSAT(GroundedMarkovNetwork groundedMarkovNetwork, double priorProbOfBeingTrue) {
		super(groundedMarkovNetwork, priorProbOfBeingTrue);		
	}	
	public MaxWalkSAT(GroundedMarkovNetwork groundedMarkovNetwork, double priorProbOfBeingTrue, int maxNumberOfStarts, int maxNumberOfFlips) {
		super(groundedMarkovNetwork, priorProbOfBeingTrue, maxNumberOfStarts, maxNumberOfFlips);		
	}	
	public MaxWalkSAT(GroundedMarkovNetwork groundedMarkovNetwork, double priorProbOfBeingTrue, int maxNumberOfStarts, int maxNumberOfFlips, double probGreedyFlip) {
		super(groundedMarkovNetwork, priorProbOfBeingTrue, maxNumberOfStarts, maxNumberOfFlips);
		this.probGreedyFlip = probGreedyFlip;
	}	
	
	/**
	 * At the end of this method, the ground literals will have truth assignments that (heuristically) maximize the sum of weights of satisfied clauses.
	 */
	protected int numberChangesMadeByWalkSAT = 0;
	protected int numberWalkSATcalls         = 0;
	// If markedClauses = null, that means 'check all clauses' (ie, the set is too big to copy).  But if the caller has a small subset, it can explicitly provide that.
	public int solve(Collection<GroundLiteral> markedLiterals, Collection<GroundClause> markedClauses, boolean reportFlag) {
		reportFlagOn = reportFlag;
		int stepsTakenThisTime = 0;
		trial++;
		TimeStamp timeStamp = (GroundedMarkovNetwork.doMajorDebug ? new TimeStamp("MaxWalkSAT: solve, trial=" + trial) : null);
		endTimer1(); // This also restarts the timer.
		endTimer2();
		bestCost     = Double.POSITIVE_INFINITY;
		boolean done = false;
		for (int i = 0; i < maxNumberOfStarts; i++) {
			endTimer2(); // This also restarts the timer.
			if (debugLevel > -1 && reportFlagOn) { Utils.println("\n% MaxWalkSAT start #" + Utils.comma(trial) + "." + (i + 1) + ", total flips = " + Utils.comma(flips) + (i > 0 ? ".  Last MaxWalkSAT walk took " + Utils.truncate(timeTaken2, 3) + " seconds." : ".")); }
			if (debugLevel > 2 && reportFlagOn) { Utils.print(    "%     "); }
			init(markedLiterals, markedClauses, "MaxWalkSAT #" + (i + 1) + ":", 1.0); // Start at a random position and initialize the activeClauses data structure.  Notice prob=1.0, so all literals will be randomly set.
			seeIfBestCost("MaxWalkSAT", this, (debugLevel > 0 ? "[initial random state #" + Utils.comma(trial) + "." + (i + 1) + "]": "[initial random state]"), timeStamp); if (bestCost <= 0.0) { break; }
			for (int j = 0; j < maxNumberOfFlips; j++) {
				timeStamp = (GroundedMarkovNetwork.doMajorDebug ? new TimeStamp("MaxWalkSAT solve: trial=" + Utils.comma(trial) + ", start=" + Utils.comma(i) + ", flip=" + Utils.comma(j)) : null);
				GroundClause activeClause = getActiveClauseRandomly(markedClauses, timeStamp);
				if (activeClause == null) {	done = true; break; } // If no active clauses, done.
				boolean changeMadeWalkSAT = false;
				boolean changeMadeRandom  = false;
				if (Utils.random() < probGreedyFlip) { if (debugLevel > 2) { Utils.print("w"); } changeMadeWalkSAT = doWalkSAT(          activeClause, markedClauses, timeStamp); numberWalkSATcalls++; } // Aim to maximize the score on this clause.
				else                                 { if (debugLevel > 2) { Utils.print("r"); } changeMadeRandom  = doRandomLiteralFlip(activeClause, markedClauses, timeStamp); }
				numberChangesMadeByWalkSAT += (changeMadeWalkSAT ? 1 : 0);
				flips++;
				stepsTakenThisTime++;
				if (changeMadeWalkSAT || changeMadeRandom) { seeIfBestCost("MaxWalkSAT", this, (debugLevel > -10 ? "[trial=" + Utils.comma(trial) + ", start=" + Utils.comma(i + 1) + ", flip=" + Utils.comma(j + 1) + ", total=" + Utils.comma(flips) + "]" : "[end of flip]"), timeStamp); if (bestCost <= 0.0) { break; }}
				if (debugLevel > 2 && reportFlagOn) { reportActiveClausesState(); }
			}
			if (debugLevel > 2 && reportFlagOn) { Utils.println(" DONE FLIPPING!"); }
			if (done) { break; }	
		}
		timeStamp = (GroundedMarkovNetwork.doMajorDebug ? new TimeStamp("MaxWalkSat: assignBestSolutionToTheLiterals") : null);
		assignBestSolutionToTheLiterals(markedLiterals, markedClauses, "MaxWalkSAT", reportFlagOn, timeStamp);
		return stepsTakenThisTime;
	}
	
	protected void assignBestSolutionToTheLiterals(Collection<GroundLiteral> markedLiterals, Collection<GroundClause> markedClauses, String caller, boolean flagOn, TimeStamp timeStamp) {
		if (debugLevel > 2 && flagOn) { Utils.println("% The best solution found by " + caller + "."); }
		groundedMarkovNetwork.restoreSavedStateOfGroundLiterals(timeStamp);
		doBookkeepingAtEndOfSample(markedLiterals, markedClauses, "Assigning the best solution.", flagOn, timeStamp); 
		if (debugLevel > -10 && flagOn) {
			endTimer1();
			Utils.println("%   Took " + Utils.truncate(timeTaken1, 3) + " seconds for " + caller + " trial #" + Utils.comma(trial) + ".   Final cost is " + Utils.truncate(bestCost, 2) + ".");
		}
	}
	
	protected void seeIfBestCost(String caller, Object obj, String msg, TimeStamp timeStamp) {
		double cost = getSumOfActiveClauses(timeStamp); // Need to MINIMIZE since we're talking about minimizing the cost.  Note that here this is the sum of the weights of pos-wgt'ed clauses that are NOT satisfied and the sum of abs(weight) of neg-wgt'ed clauses that ARE satisfied.  In the ideal case, this sum would be zero.
		if (debugLevel > 2 && reportFlagOn) { Utils.println("%    " + msg + "   current cost = " + Utils.truncate(cost, 3) + "  best = " + Utils.truncate(bestCost, 3)); }
		if (cost < bestCost) {
			double delta = cost - bestCost;
			bestCost = cost;
			String msg2 = " [saved " + Utils.truncate(delta, 3) + "]";
			groundedMarkovNetwork.saveCurrentStateOfGroundLiterals(timeStamp);
			if (debugLevel > 2 && reportFlagOn) { Utils.println("%       New best MaxWalkSAT, # active clauses = " + Utils.comma(countOfActiveClauses) + "  changesMadeByWalkSAT = " + Utils.comma(numberChangesMadeByWalkSAT) + "/" + Utils.comma(numberWalkSATcalls) + "   " + msg); }
			if (debugLevel > 1 && reportFlagOn) { Utils.println("%    New best cost = " + Utils.truncate(bestCost, 3) + " " + msg + msg2); }
		}
	}
	
	private boolean doRandomLiteralFlip(GroundClause gndClause, Collection<GroundClause> markedClauses, TimeStamp timeStamp) {
		if (groundedMarkovNetwork.doingLazyInference) { Utils.error("Should not call this when doingLazyInference=true!"); }
		int numOfLiterals = gndClause.getLength();
		if (numOfLiterals == 0) { return false; }
		int i = Utils.random0toNminus1(numOfLiterals);
		GroundLiteral gndLiteralToFlip = gndClause.getIthLiteral(i);
		if (gndLiteralToFlip.getBlock() != null) { computeDeltaCost(gndLiteralToFlip); } // A little extra computation, but it deals with blocks.
		else { result1_computeDeltaCost = -1; }
		TimeStamp timeStamp2 = (timeStamp != null ? new TimeStamp(timeStamp.getTimeStamp() + " doRandomLiteralFlip") : null);
		flipLiteral(gndLiteralToFlip, markedClauses, result1_computeDeltaCost, timeStamp2);
		return true;
	}
	
	/**
	 * A MaxWalkSAT step.
	 * 
	 * @param clause We will greedily flip one of the literals in this clause.
	 * @return true if have changed the setting of this clause's literals.
	 */
	private List<Integer> gLitIndexesToFlipArrayList = new ArrayList<Integer>(8);  // Reuse instead of creating multiple times.
	protected boolean doWalkSAT(GroundClause gndClause, Collection<GroundClause> markedClauses, TimeStamp timeStamp) {
		if (groundedMarkovNetwork.doingLazyInference) { Utils.error("Should not call this when doingLazyInference=true!"); }
		if (!gndClause.isActive()) { Utils.error("Always called for active clauses"); }
		int numOfLiterals = gndClause.getLength();
		if (numOfLiterals == 0) { return false; }
		double probOfScoringLiteral = 1.0;
		if (numOfLiterals > maxWalkSATbranchingFactor) { probOfScoringLiteral = numOfLiterals / maxWalkSATbranchingFactor; }
		double best0_computeDeltaCost =  0; // We only want flips that REDUCE the score.
		int    best1_computeDeltaCost = -1; // Records the OTHER literal (if non-negative value) that needs to be flipped (due to block constraints).
 		int literalToFlip = -1;
 		List<Integer> literalsToFlip = null; // Collect all TIES.
		if (debugLevel > 3 && reportFlagOn) { Utils.println("%    Considering " + (gndClause.getWeightOnSentence() < 0 ? "satisfied" : "unsatisfied") + (gndClause.isActive() ? "/active " : "/inactive ") + "clause " + gndClause.getInfo() + "."); }
		if (gndClause.getWeightOnSentence() < 0) {
			// For the satisfied clause with a NEGATIVE-weight case,
			// flip one of the literals whose truth value is the same as its 'sign' (i.e, flip a posLiteral that is true or a negLiteral that is false).
			// I.e., choose a literal that is currently satisfied.  This will increase chance of the the clause being UNSATISFIED.
			if (numOfLiterals == 0) {
				Utils.error("Have no literals to choose: " + gndClause);
			} else if (numOfLiterals < 2) { // With reduced clauses, will often only have one literal left, so worth having a special case.
				GroundLiteral gLit = gndClause.getIthLiteral(0);
				if (gndClause.getSignOfIthLiteral(0) != gLit.getValue()) {
					Utils.error("Have an satisfied (neg-wgt) singleton clause with its only literal being unsatisfied!  Literal '" + gLit + "' has value=" + gLit.getValue() +  " in clause (isActive=" + gndClause.isActive() +  " and isSat=" + gndClause.isSatisfiedCached() + "): '" + gndClause + "'.");
					}
				if (debugLevel > 1) { Utils.println("% Only one literal to flip in " + gndClause); }
				computeDeltaCost(gLit);
				// Note: we want to accept ties, since we want to sample all solutions.
				// TODO Find why causes the code to fail
			    if (result0_computeDeltaCost > best0_computeDeltaCost) { 
			        // This is not an error and is possible, as there can be two clauses with a single ground literal.
			    	// Utils.error("should not happen since only ACTIVE clauses should reach here! : " + gndClause.toPrettyString());
			    	return false;
			    } // Flipping does not help.
				flipLiteral(gLit, markedClauses, -1, timeStamp); // Need to call this since it also updates 'activeClauses'.
				return true;
			} else for (int i = 0; i < numOfLiterals; i++) if (probOfScoringLiteral > 0.9999999 || Utils.random() < probOfScoringLiteral) {
				GroundLiteral gndLiteral = gndClause.getIthLiteral(i);
				if (gndClause.getSignOfIthLiteral(i) == gndLiteral.getValue()) {  // I.e., this literal is TRUE in this clause.
					computeDeltaCost(gndLiteral);
					if (debugLevel > 2 && reportFlagOn) { Utils.println("%      Flipping literal #" + i + " leads to a delta cost of " + Utils.truncate(result0_computeDeltaCost, 3) + "."); }
					if (result0_computeDeltaCost < best0_computeDeltaCost) {
						best0_computeDeltaCost = result0_computeDeltaCost;
						best1_computeDeltaCost = result1_computeDeltaCost;
						literalToFlip  = i;
						literalsToFlip = null;					
					} else if (result0_computeDeltaCost == best0_computeDeltaCost) {
						if (literalsToFlip == null) {
							gLitIndexesToFlipArrayList.clear();
							literalsToFlip = gLitIndexesToFlipArrayList; // Don't build until second one encountered.
							literalsToFlip.add(literalToFlip);
						}
						literalsToFlip.add(i); // Grab a tie.
					}
				}
			}
		} else if (gndClause.getWeightOnSentence() > 0) {			
			// For the satisfied clause with a POSITIVE-weight case,
			// flip one of the literals whose truth value is the opposite of its sign.
			// I.e., choose a literal that is currently UNsatisfied.  This will increase chance of the the clause being SATISFIED.
			if (numOfLiterals == 0) {
				Utils.error("Have no literals to choose: " + gndClause);
			} else if (numOfLiterals < 2) { // With reduced clauses, will often only have one literal left, so worth having a special case.
				GroundLiteral gLit = gndClause.getIthLiteral(0);
				if (gndClause.getSignOfIthLiteral(0) == gLit.getValue()) { Utils.error("Have an unsatisfied singleton clause with its only literal being satisfied!  Literal '" + gLit + "' has value=" + gLit.getValue() +  " in clause (isActive=" + gndClause.isActive() +  " and isSat=" + gndClause.isSatisfiedCached() + "/" + gndClause.isSatisfiedCached() + "): '" + gndClause + "'."); }
				if (debugLevel > 1) { Utils.println("% Only one literal to flip in " + gndClause); }
				computeDeltaCost(gLit);
				if (result0_computeDeltaCost > best0_computeDeltaCost) {  // Flipping does not help.
					if (debugLevel > 1 && reportFlagOn) { Utils.println("% Could not find a change that improves: " + gndClause.getInfo() + "."); }
					return false;
				}
				flipLiteral(gLit, markedClauses, -1, timeStamp); // Need to call this since it also updates 'activeClauses'.
				return true;
			} else for (int i = 0; i < numOfLiterals; i++) if (probOfScoringLiteral > 0.9999999 || Utils.random() < probOfScoringLiteral) {
				GroundLiteral gndLiteral = gndClause.getIthLiteral(i);
				if (gndClause.getSignOfIthLiteral(i) != gndLiteral.getValue()) {  // I.e., this literal does not satisfy this clause. 
					computeDeltaCost(gndLiteral);
					if (debugLevel > 2 && reportFlagOn) { Utils.println("%      Flipping literal #" + i + " leads to a delta cost of " + Utils.truncate(result0_computeDeltaCost, 3) + "."); }
					if (result0_computeDeltaCost < best0_computeDeltaCost) {
						best0_computeDeltaCost = result0_computeDeltaCost;
						best1_computeDeltaCost = result1_computeDeltaCost;
						literalToFlip  = i;
						literalsToFlip = null;						
					} else if (result0_computeDeltaCost == best0_computeDeltaCost) {
						if (literalsToFlip == null) {
							gLitIndexesToFlipArrayList.clear();
							literalsToFlip = gLitIndexesToFlipArrayList; // Don't build until second one encountered.
							literalsToFlip.add(literalToFlip);
						}
						literalsToFlip.add(new Integer(i));
					}
				}
			}
		}
		if (debugLevel > 0 && reportFlagOn && literalsToFlip != null) { Utils.println("%  Numbers " + literalsToFlip + " are the literals to flip for '" + gndClause + "'."); }
		if (literalsToFlip != null) { // If ties, pick one (uniformly) randomly.
			literalToFlip = Utils.chooseRandomFromThisCollection(literalsToFlip);
		}
		if (debugLevel > 0 && reportFlagOn && literalToFlip >= 0) { Utils.println("%  Literal #" + literalToFlip + " is the chosen one to flip in '" + gndClause + "'.  " +  gndClause.getInfo()); }
		if (debugLevel > 0 && reportFlagOn && literalToFlip <  0) { Utils.println("%  Could not find a literal to flip in '" + gndClause + "'."); }
		if (literalToFlip < 0) { // Might not have found anything greedily (e.g., already at the maximum).
			// literalToFlip = Utils.random0toNminus1(numOfLiterals);
			if (debugLevel > 1) { Utils.println("% Could not find a change that improves: " + gndClause.getInfo() + "."); }
			return false;
		}
		
		flipLiteral(gndClause.getIthLiteral(literalToFlip), markedClauses, best1_computeDeltaCost, timeStamp);
		if (debugLevel > 1 && reportFlagOn) { Utils.println("% " + (best0_computeDeltaCost > 0 ? "Reduced" : "Increased")
																 + " total wgt'ed sum of satisfied clauses by " + Utils.truncate(Math.abs(best0_computeDeltaCost), 4) 
																 + " via flipping '" + gndClause.getIthLiteral(literalToFlip) 
																 + "' to " + gndClause.getIthLiteral(literalToFlip).getValue() + " in '" + gndClause + "'."); }
		return true;
	}		
}