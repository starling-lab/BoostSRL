package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.ILP.LearnOneClause;
import java.util.List;

import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchNode;

public class ScoreSingleClauseByPminusNminusL extends ScoreSingleClause {

	public ScoreSingleClauseByPminusNminusL() {
	}

	public double multiplerForBodyCost       = 0.0000100; // This gets NEGATED below, ie this should be a POS number and it is a PENALTY.
	public double multiplierForSingletonVars = 0.0000010; // Ditto.
	public double multiplierForUniqueVars    = 0.0000001; // Ditto.  Count how many DIFFERENT variables there are.
	
	private double getPenalties(SingleClauseNode node, boolean includeSingletonCount) {
		List<Variable> allVars = node.collectAllVariables();
		return multiplerForBodyCost * node.getCost() 
			 + (includeSingletonCount ? multiplierForSingletonVars * node.countOfSingletonVars(allVars) : 0)
			 + multiplierForSingletonVars * node.countOfUniqueVars(allVars);
	}

	public double computeMaxPossibleScore(SearchNode nodeRaw) throws SearchInterrupted {
		SingleClauseNode node     = (SingleClauseNode)nodeRaw;
		if (!Double.isNaN(node.score)) { return node.score; }
		LearnOneClause   thisTask = task; 

		if (ScoreSingleClause.debugLevel > 1) { Utils.println("computeMaxPossibleScore = " + (node.getPosCoverage() - node.bodyLength()) + " for " + node); }
		node.score = node.getPosCoverage() - thisTask.getMEstimateNeg() - node.bodyLength() + 1; // This 'plus 1' isn't in the class name, but it comes from an MDL argument.  Not a big deal, since just a constant, but might matter if zero is the minimum acceptable score.
		return node.score;
	}
	
	public double scoreThisNode(SearchNode nodeRaw) throws SearchInterrupted {
		SingleClauseNode node     = (SingleClauseNode)nodeRaw;
		LearnOneClause   thisTask = task; 
		
		node.computeCoverage(); // Need to call this in case not already computed.
		double score = node.getPosCoverage() - node.negCoverage - thisTask.getMEstimateNeg() - node.bodyLength() + 1 - getPenalties(node, true); // See comment above about the "+ 1."
		
		if (node.getPosCoverage() < Double.MIN_VALUE) {return Double.NaN; } // If a node cannot meet the minPosCoverage or theorem proving times out, score as NaN, which will prevent it from being added to OPEN.
		
		if (ScoreSingleClause.debugLevel > 1) { Utils.println("Score = " + Utils.truncate(score, 3) + " for clause:  " + node); }
		return score;
	}
}
