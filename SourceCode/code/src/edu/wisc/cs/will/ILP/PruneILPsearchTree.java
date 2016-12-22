/**
 * 
 */
package edu.wisc.cs.will.ILP;

import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Constant;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.Pruner;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Type;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.Utils.MapOfLists;
import edu.wisc.cs.will.Utils.Utils;

/**
 * This pruner handles cases of predicates that are isaInterval's. Extensions to
 * this class should also call this class (or some of its methods) if their
 * methods have not found a reason to prune a node. To uses this pruner a) make
 * sure that an instance of this class (or a subclass) is provided to
 * LearnOneClause().
 * 
 * @author shavlik
 */
public class PruneILPsearchTree {
	public  int      pruneReportInterval               = 10000; // Can set to Integer.MAX_VALUE to in effect turn off this reporting.
	public  int      nodesPrunedDueToIntervalAnalysis  = 0; 
	public  int  nodesPrunedDueToSingleClauseAnalysis  = 0; 
	private LearnOneClause                      task  = null; // The ILP search algorithm for which this pruner "works."
		
	public PruneILPsearchTree(LearnOneClause task) {
		this.task = task;	
	}
	
	/**
         * @param node
	 * @param typesOfNewTerms 
         * @return Whether the given node should be pruned.
         */
	public boolean prune(SingleClauseNode node, Map<Term,Type> typesOfNewTerms) {
/*		if (node.formForPruning == null) {
			//protected Literal formForPruning  = null; // This and the next are used for pruning.
			//protected Map<Variable,NumericConstant> variablesToNumbers = null;

			SingleClauseNode parent = (SingleClauseNode) node.parentNode;
			Map<Term,Type> parentsNewTerms = parent.typesOfNewTerms;
			for (Term arg : node.literalAdded.arguments) {
				
			}
		}
*/
		//Utils.println("%  prune1 " + node.literalAdded);
		if (pruneBasedOnIntervalAnalysis(node)) {
			if (LearnOneClause.debugLevel > 2) { Utils.println("*** PRUNE " + node + " based on overlapping-interval analysis.");}
			nodesPrunedDueToIntervalAnalysis++;
			if (nodesPrunedDueToIntervalAnalysis % pruneReportInterval == 0) { Utils.println("% Have pruned " + Utils.comma(nodesPrunedDueToIntervalAnalysis) + " nodes due to overlapping-interval analysis."); }
			return true;
		}
		//Utils.println("%  prune2 " + node.literalAdded);
		if (pruneBasedOnSingletonHeads(node)) {
			if (LearnOneClause.debugLevel > 2) { Utils.println("*** PRUNE " + node + " based on 'prune' instructions.");}
			nodesPrunedDueToSingleClauseAnalysis++;
			ILPouterLoop caller = (task.caller instanceof ILPouterLoop ? (ILPouterLoop) task.caller : null);
			if (nodesPrunedDueToSingleClauseAnalysis % pruneReportInterval == 0) { 
				if (caller != null) {
					Utils.println("% Have pruned " +  Utils.comma(nodesPrunedDueToSingleClauseAnalysis) + 
							      " nodes due to 'prune' instructions (nodes created = " + Utils.comma(task.getNodesCreated())    + " this cycle and " + Utils.comma(task.getNodesCreated()    + caller.getTotal_nodesCreated())    + " in total" +
							      ", nodes expanded = "                                  + Utils.comma(task.getNodesConsidered()) + " this cycle and " + Utils.comma(task.getNodesConsidered() + caller.getTotal_nodesConsidered()) + " in total" + ").");
				} else {
					Utils.println("% Have pruned " +  Utils.comma(nodesPrunedDueToSingleClauseAnalysis) + 
						      " nodes due to 'prune' instructions (nodes created = " + Utils.comma(task.getNodesCreated())        + " this cycle and " + "?" + " in total" +
						      ", nodes expanded = "                                  + Utils.comma(task.getNodesConsidered())     + " this cycle and " + "?" + " in total" + ").");
				
				}
			}
			return true;
		}
		// If this wasn't the end of the class hierarchy, its parent would be called here to see if it wanted to prune this node.
		return false;
	}
	
	/**
         * See if this node's literal is in the BODY of some 'singleton' clause
         * whose head is already in the clause being built. I.e., if 'p(x) =>
         * q(x)' is the ONLY way to deduce q(x), and q(x) in the clause, no need
         * to consider adding p(x) since we know it must be true.
         * 
         * @param node
         * @return TODO Whether pruning occurred?
         */
	protected boolean pruneBasedOnSingletonHeads(SingleClauseNode node) { // This is a bit of a misnomer since hand-created prune's can happen for any reason.
		// First see if this node's literal is even in a singleton body.
		Literal       lit   = node.literalAdded;
		PredicateName pName = lit.predicateName;
		
		SingleClauseNode parent = node.getParentNode();
		if (parent == null) { return false; }
		MapOfLists<PredicateNameAndArity, Pruner> pruners = pName.getPruners(lit.getArity());
		if (pruners == null) { return false; }
		if (LearnOneClause.debugLevel > 1) { Utils.println("%  pruners for '" + pName + "' lit=" + lit + " [parent=" + parent + "] = " + pruners); }
		
		ChildrenClausesGenerator childrenGenerator = ((ChildrenClausesGenerator) task.childrenGenerator);
		Literal       initNumberedLit    = (childrenGenerator.cachedBindingListForPruning == null ? lit : lit.applyTheta(childrenGenerator.cachedBindingListForPruning.theta));
		BindingList   newBL              = childrenGenerator.bindVarsToUniqueConstants(initNumberedLit);
		Literal       numberedLit        = initNumberedLit.applyTheta(newBL.theta);
		
		// See if NULL is one of the pruners (NULL means nothing in the body needs to match).
		List<Pruner>  prunersMatchingNULL = pruners.getValues(null);
		if (prunersMatchingNULL != null) { // NOTE: there might be MULTIPLE pruners associated with NULL, eg f(x,0) and f(x,1).
			for (Pruner pruner : prunersMatchingNULL) if (pruner.isaMatch(numberedLit, null)) { // Don't worry about counts in this case.
				if (LearnOneClause.debugLevel > 1) { Utils.println("% Pruning '" + numberedLit + "', which needs no matcher in the clause body."); }
                return true;
			}
		}
		
		List<Literal> parentBody         = parent.getClauseBody();
		List<Literal> numberedClauseBody = childrenGenerator.numberedBodyForPruning.negLiterals;		
		
		// In a hash map of pruners, the literal is what needs to be in the clause already for this node to be pruned.
		// The integer is a run-time check to see if there currently are too many ways to derive the parent literal,
		// thereby violating any assumptions in place when the prune rule was created.
		int parentBodyLength = numberedClauseBody.size();
		for (int bodyCounter = 0; bodyCounter < parentBodyLength; bodyCounter++) {
			Literal       numberedBodyLit = numberedClauseBody.get(bodyCounter);
			PredicateNameAndArity parentPredicateNameAndArity = numberedBodyLit.getPredicateNameAndArity();
		    List<Pruner>  matchingPruners = pruners.getValues(parentPredicateNameAndArity);
		    if (matchingPruners != null) { // Have a possible hit.
		    	if (LearnOneClause.debugLevel > 1) { Utils.println("FOUND SOME MATCHING PRUNERS: " + matchingPruners); }
		        for (Pruner pruner : matchingPruners) if (pruner.isaMatch(numberedLit, numberedBodyLit)) {
				    	Literal regBodyLit = parentBody.get(bodyCounter);
				    	// TODO the below is buggy if FACTS DIRECTLY added about the parent predicate!
				    	if (pruner.warnIfPresentLiteralCount > 0 // Need the ORIGINAL body item here.
		                        && countMatchingDefiniteClauses(regBodyLit, task.getBackgroundKnowledge(), task.unifier) >= pruner.warnIfPresentLiteralCount) {
				    		int matchingRulesCount = countMatchingDefiniteClauses(regBodyLit, task.getBackgroundKnowledge(), task.unifier, true);
				            Utils.error("This pruner's count (" + Utils.comma(pruner.warnIfPresentLiteralCount) + ") is violated: '" + pruner + "'.  matchingRulesCount=" + Utils.comma(matchingRulesCount));
		                }
		                if (LearnOneClause.debugLevel > 1) { Utils.println("% Pruning '" + numberedLit + "' because of '" + numberedBodyLit + "'"); } //  + " due to: '" + pruner + "'."); }
		                return true;
		            }
		    }
		}
		// Don't check the head.  Note: it wasn't numbered above.
		return false;
	}
	
	protected boolean pruneBasedOnIntervalAnalysis(SingleClauseNode node) {
		SingleClauseNode parent = node.getParentNode();
		if (parent == null) { return false; } // No need to check anything here.
		
		Literal       literalBeingAdded = node.literalAdded;
		PredicateName pName             = literalBeingAdded.predicateName;
		int           arity             = literalBeingAdded.numberArgs();
		
		// This reasoning about redundant intervals is done at LEARNING time, not "problem-solving" time, and hence the arguments
		// in question need to be constants at the time this is pruning is done.  (It would be nice if this code RESTRUCTURED
		// this node's clause to INTERSECT two intervals, but that is a bit complicated since a clause is represented by a PATH
		// to the root, and many clauses share paths.  So simplifying learned clauses is left to other code.)
		if (pName.isaInterval_1D(arity)) {  // See if this predicate/arity is a 1D interval.  Note that a 1D interval is of the form [lower, upper) - i.e., inclusive on the lower bound and exclusive on the upper bound.  This allows disjoint, but abutting, intervals to be specified.
			// If so, we need to grab the lower and upper bounds for THIS literal.
			Term lower1 = literalBeingAdded.getLowerBoundary_1D();
			Term upper1 = literalBeingAdded.getUpperBoundary_1D();
			
			if (lower1 instanceof Constant && upper1 instanceof Constant) { // Must both be constants or we can't prune.
				// We now have to look through the other literals in the clause this node represents and see if
				//    a) there is another literal with the same predicate name and arity,
				//    b) that for all other arguments, the two literals are equal,
				//    c) that the literal's lower and upper bound, lower2 and upper2, satisfy one of the following
				//         i) upper2 <= lower1  // This new interval can never be true since it is disjoint from one already in the clause.
				//        ii) lower2 >= upper1  // Ditto.
				//       iii) lower2 >= lower1 and upper2 <= upper1 // This interval is totally inside the old one, so it will always be true.
				//
				// Notice that we want to allow this to work for NUMERIC constants as well as string constants,
				// where the user has defined "isLessThanOrEqualTo" and "isGreaterThanOrEqualTo." TODO
				boolean constantsAreNumeric = false;
				double  lower1asDouble      = -1.0; // Need to set to something to avoid compiler error/warning.
				double  upper1asDouble      = -1.0; // Ditto.
				Literal remainderOfLiteral  = literalBeingAdded.createLiteralWithMaskedBoundaries_1D();
				
				if (lower1 instanceof NumericConstant) {
					if (!(upper1 instanceof NumericConstant)) { Utils.error("In an interval, both lower and upper must be the same type of constants: " + literalBeingAdded); }
					constantsAreNumeric = true;
					lower1asDouble = ((NumericConstant) lower1).value.doubleValue();
					upper1asDouble = ((NumericConstant) upper1).value.doubleValue();
				} else {
					Utils.error("In an interval, currently both lower and upper must be numeric constants: " + literalBeingAdded);					
				}
				
				// Rather than creating a method in the SingleClauseNode class, do everything here for "locality" reasons.				
				while (parent != null) {
					Literal       literalBeingAddedHere = parent.literalAdded;
					PredicateName pNameHere             = literalBeingAddedHere.predicateName;
					int           arityHere             = literalBeingAddedHere.numberArgs();
					
					if (pName == pNameHere && arity == arityHere) {
						Term       lower2     = literalBeingAddedHere.getLowerBoundary_1D();
						Term       upper2     = literalBeingAddedHere.getUpperBoundary_1D();

						Literal remainderOfParent  = literalBeingAddedHere.createLiteralWithMaskedBoundaries_1D();
						// Utils.println("remainderOfLiteral=" + remainderOfLiteral + " and remainderOfParent=" + remainderOfParent); 
						if (remainderOfLiteral.equals(remainderOfParent)) {
							// If this node's arguments aren't numeric constants, simply skip over it.
							if (constantsAreNumeric) { // This is currently checked above, but leave in for future expansion.
								if (lower2 instanceof NumericConstant && upper2 instanceof NumericConstant) {
									double lower2asDouble = ((NumericConstant) lower2).value.doubleValue();
									double upper2asDouble = ((NumericConstant) upper2).value.doubleValue();
									
									if (LearnOneClause.debugLevel > 1) { Utils.println("  Comparing [" + lower2asDouble + "," + upper2asDouble + ") to [" + lower1asDouble + "," + upper1asDouble + ")"); }
									if (upper2asDouble <= lower1asDouble || lower2asDouble >= upper1asDouble) { return true; } // Cannot satisfy both intervals, so might as well prune.
									if (lower2asDouble >= lower1asDouble && upper2asDouble <= upper1asDouble) { return true; } // This new interval is subsumed by the old one, so no need to add it (i.e., will always be true).
								}
							} else { Utils.error("not yet implemented"); }
						}
					}
					parent = parent.getParentNode(); // Climb the search tree (i.e., walk backwards in the clause).
				}
			}
		}
		// To be written if ever needed ...
		if (pName.isaInterval_2D(arity)) { // See if this predicate is a 2D interval.
			Utils.error("Dealing with 2D intervals is not yet implemented.");
		}
		if (pName.isaInterval_3D(arity)) { // See if this predicate is a 3D interval.
			Utils.error("Dealing with 3D intervals is not yet implemented.");			
		}
		return false;		
	}
	
	public int countMatchingDefiniteClauses(Literal head, Iterable<Clause> clauses, Unifier unifier) {
		return countMatchingDefiniteClauses(head, clauses, unifier, false);
	}
	public int countMatchingDefiniteClauses(Literal head, Iterable<Clause> clauses, Unifier unifier, boolean reportMatches) {
		if (clauses == null) { return 0; }
		int counter = 0;
		for (Clause clause : clauses) if (clause.isDefiniteClause()) {
			if (unifier.unify(clause.posLiterals.get(0), head) != null) {
				if (reportMatches) { Utils.println("% matcher:\n% " + clause.toPrettyString("%  ")); }
				counter++; }
		}
		return counter;

	}
}
