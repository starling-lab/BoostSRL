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
public class ScoreSingleClauseByAccuracy extends ScoreSingleClause {
	/**
	 * There are some 'tie-breaking' things that adjust accuracy a little.
	 *   That is predicate names have costs, they are used to adjust the accuracy.
	 *   Also, there is a small penalty for each variable that only appears once.
	 *   Finally, there is a penalty for the number of unique variables there are.
	 */
	
	public double multiplerForBodyCost         = 0.0000100; // This gets NEGATED below, i.e. this should be a POS number and it is a PENALTY.
	public double multiplierForSingletonVars   = 0.0000010; // Ditto.
	public double multiplierForUniqueVars      = 0.0000001; // Ditto.  Count how many DIFFERENT variables there are.
	public double multiplierForUniqueConstants = 0.0000002; // Ditto.  Count how many DIFFERENT variables there are.
	
	private Set<PredicateName> pNamesSeen = new HashSet<PredicateName>(32);
	
	public ScoreSingleClauseByAccuracy() {
	}
	
	protected double getPenalties(SingleClauseNode node, boolean includeSingletonCount, boolean includeRepeatedPredicates) {
		List<Variable> allVariables = node.collectAllVariables();
		List<Constant> allConstants = node.collectAllConstants();
		if (includeRepeatedPredicates) { pNamesSeen.clear(); }
		double bodyCost        =                              node.getCost();
		double singletonVars   = (includeSingletonCount     ? node.countOfSingletonVars(allVariables)      : 0.0);
		double repeatedLits    = (includeRepeatedPredicates ? node.discountForRepeatedLiterals(pNamesSeen) : 0.0);
		double uniqueVars      =                              node.countOfUniqueVars(     allVariables);
		double uniqueConstants =                              node.countOfUniqueConstants(allConstants);
		if (ScoreSingleClauseByAccuracy.debugLevel > 2) { 
			if (bodyCost        > 0.0) { Utils.println("%       bodyCost             = +" + multiplerForBodyCost         + " * " + Utils.truncate(bodyCost,        3)); }
			if (singletonVars   > 0.0) { Utils.println("%       countOfSingletonVars = +" + multiplierForSingletonVars   + " * " + Utils.truncate(singletonVars,   3)); }
			if (repeatedLits    > 0.0) { Utils.println("%       repeatedliterals     = -" + multiplerForBodyCost         + " * " + Utils.truncate(repeatedLits,    3)); }
			if (uniqueVars      > 0.0) { Utils.println("%       unique vars          = +" + multiplierForUniqueVars      + " * " + Utils.truncate(uniqueVars,      3)); }
			if (uniqueConstants > 0.0) { Utils.println("%       unique constants     = +" + multiplierForUniqueConstants + " * " + Utils.truncate(uniqueConstants, 3)); }
		}
				
		return                              multiplerForBodyCost         * bodyCost 
			 + (includeSingletonCount     ? multiplierForSingletonVars   * singletonVars : 0.0)
			 - (includeRepeatedPredicates ? multiplerForBodyCost         * repeatedLits  : 0.0)
			 +                              multiplierForUniqueVars      * uniqueVars
			 +                              multiplierForUniqueConstants * uniqueConstants;
	}

	public double computeMaxPossibleScore(SearchNode nodeRaw) throws SearchInterrupted {
		SingleClauseNode node  = (SingleClauseNode)nodeRaw;
		
		if (ScoreSingleClauseByAccuracy.debugLevel > 1) { Utils.println("%     computeMaxPossibleScore = " + (node.maxPrecision() - getPenalties(node, false, true)) + " for " + node); }
		return node.maxPrecision() - getPenalties(node, false, true); // In best case, could end up with NO singleton variables.
	}
	
	public double scoreThisNode(SearchNode nodeRaw) throws SearchInterrupted {
		SingleClauseNode node  = (SingleClauseNode)nodeRaw;
		if (!Double.isNaN(node.score)) { return node.score; }
		double           score = node.precision() - getPenalties(node, true, true); // Add small penalties as a function of length and the number of singleton vars (so shorter better if accuracy the same).

		if (ScoreSingleClauseByAccuracy.debugLevel > 1) { Utils.println("%     Score = " + Utils.truncate(score, 3) + " (precision = " + Utils.truncate(node.precision(), 3) + ") for clause:  " + node); }
		//if (node.posCoverage < Double.MIN_VALUE) { return Double.NaN; } // If a node cannot meet the minPosCoverage or theorem proving times out, score as NaN, which will prevent it from being added to OPEN.
		node.score = score;
		return score;
	}

}
