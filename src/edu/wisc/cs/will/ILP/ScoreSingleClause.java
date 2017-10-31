/**
 * 
 */
package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.ILP.LearnOneClause;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.ScoringFunction;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchNode;

/**
 * @author shavlik
 *
 */
public abstract class ScoreSingleClause extends ScoringFunction {
	protected final static int debugLevel = 0;   // Used to control output from this project (0 = no output, 1=some, 2=much, 3=all).
	
	LearnOneClause task;
	/**
	 * 
	 */
	public ScoreSingleClause() {
	}	
	public ScoreSingleClause(LearnOneClause task) {
		this.task = task;
	}
	
	public void setSearchTask(LearnOneClause task) {
		this.task = task;
	}
	
	public double computeBonusScoreForThisNode(SearchNode nodeRaw) throws SearchInterrupted { // ADD this to the normal score.
		// If a clause ends with a DETERMINATE literal, we want to allow it to be expanded
		// since the determinate literal by itself is of no help.
		SingleClauseNode node  = (SingleClauseNode)nodeRaw;
		//Utils.println("HERE!");
		if (node.endsWithBridgerLiteral()) {
			if (ScoreSingleClauseByAccuracy.debugLevel > 1) { Utils.println("COMPUTE BONUS (" + computeMaxPossibleScore(node) + "): " + node); }
			return computeMaxPossibleScore(node) - scoreThisNode(node); // Since bonus is ADDED, need to subtract the normal score so that the computed score is the total score.
		}
		return 0;
	}

}
