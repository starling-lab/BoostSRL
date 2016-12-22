/**
 * 
 */
package edu.wisc.cs.will.ILP;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchNode;
import edu.wisc.cs.will.FOPC.Constant;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author shavlik
 *
 */
public class ScoreSingleClauseByFbeta extends ScoreSingleClauseByAccuracy {
	
	public double beta = 1.0;
	
	public ScoreSingleClauseByFbeta() {
	}
	public ScoreSingleClauseByFbeta(double beta) {
		this.beta = beta;
	}

	public double computeMaxPossibleScore(SearchNode nodeRaw) throws SearchInterrupted {
		SingleClauseNode node  = (SingleClauseNode)nodeRaw;
		
		if (ScoreSingleClauseByAccuracy.debugLevel > 1) { Utils.println("%     computeMaxPossibleScore = " + (node.maxF(beta) - getPenalties(node, false, true)) + " for " + node); }
		return node.maxF(beta) - getPenalties(node, false, true); // In best case, could end up with NO singleton variables.
	}
	
	public double scoreThisNode(SearchNode nodeRaw) throws SearchInterrupted {
		SingleClauseNode node  = (SingleClauseNode)nodeRaw;
		if (!Double.isNaN(node.score)) { return node.score; }
		double           score = node.F(beta) - getPenalties(node, true, true); // Add small penalties as a function of length and the number of singleton vars (so shorter better if accuracy the same).

		if (ScoreSingleClause.debugLevel > 1) { Utils.println("%     Score = " + Utils.truncate(score, 3) + " (precision = " + Utils.truncate(node.F(beta), 3) + ") for clause:  " + node); }
		//if (node.posCoverage < Double.MIN_VALUE) { return Double.NaN; } // If a node cannot meet the minPosCoverage or theorem proving times out, score as NaN, which will prevent it from being added to OPEN.
		node.score = score;
		return score;
	}

}
