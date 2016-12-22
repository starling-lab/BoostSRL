/**
 * 
 */
package edu.wisc.cs.will.stdAIsearch;

import edu.wisc.cs.will.Utils.Utils;

/**
 * @author shavlik
 *
 */
public abstract class ScoringFunction {
	protected StateBasedSearchTask task;

	/**
	 * 
	 */
	public ScoringFunction() {
	}
	public ScoringFunction(StateBasedSearchTask task) {
		this.task = task;
	}

	public void setSearchTask(StateBasedSearchTask task) {
		this.task = task;
	}

	public abstract double scoreThisNode(               SearchNode node) throws SearchInterrupted;
	/*
	public abstract double computeMaxPossibleScore(     SearchNode node) throws SearchInterrupted;
	public abstract double computeBonusScoreForThisNode(SearchNode node) throws SearchInterrupted; // ADD this to the normal score.  Might want to override the regular score to play tricks with insertion into OPEN (eg, used in ILP code). 
	*/
	public double computeMaxPossibleScore(SearchNode node) throws SearchInterrupted {
		Utils.waitHere("Wrong computeMaxPossibleScore?"); if (true) { Utils.error("Shouldn't happen?"); } // THESE ARE HERE TO TRAP SOME ODD BEHAVIOR ThAT POPPED UP ONCE WITH ILP SEARCH.  Can delete later (current date = 7/31/08).
		return Double.POSITIVE_INFINITY;
	}	
	public double computeBonusScoreForThisNode(SearchNode node) throws SearchInterrupted { // ADD this to the normal score.
		Utils.waitHere("Wrong computeBonusScoreForThisNode?"); if (true) { Utils.error("Shouldn't happen?"); } // THESE ARE HERE TO TRAP SOME ODD BEHAVIOR ThAT POPPED UP ONCE WITH ILP SEARCH.  Can delete later (current date = 7/31/08).
		return 0; // Might want to override the regular score to play tricks with insertion into OPEN (eg, used in ILP code). 
	}
	
	public void clearAnySavedInformation(boolean insideIterativeDeepening) {
		return;  // Don't make this abstract since it is unlikely that a scoring function will have something that needs resetting.
	}
}
