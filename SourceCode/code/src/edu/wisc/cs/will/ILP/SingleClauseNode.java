/**
 * 
 */
package edu.wisc.cs.will.ILP;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.wisc.cs.will.Boosting.Common.SRLInference;
import edu.wisc.cs.will.Boosting.EM.HiddenLiteralState;
import edu.wisc.cs.will.Boosting.OneClass.PairWiseExampleScore;
import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.Utils.NumberGroundingsCalculator;
import edu.wisc.cs.will.DataSetUtils.ArgSpec;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.DataSetUtils.RegressionExample;
import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Constant;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.FunctionName;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateName.FunctionAsPredType;
import edu.wisc.cs.will.FOPC.PredicateSpec;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Type;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.ILP.Regression.BranchStats;
import edu.wisc.cs.will.ILP.Regression.RegressionInfoHolder;
import edu.wisc.cs.will.ILP.Regression.RegressionInfoHolderForMLN;
import edu.wisc.cs.will.ILP.Regression.RegressionInfoHolderForRDN;
import edu.wisc.cs.will.ILP.Regression.RegressionVectorInfoHolderForRDN;
import edu.wisc.cs.will.ResThmProver.HornClauseProver;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchNode;
import edu.wisc.cs.will.stdAIsearch.StateBasedSearchTask;

/**
 * @author shavlik
 *
 */
@SuppressWarnings("serial")
public class SingleClauseNode extends SearchNode implements Serializable{
	private final static boolean renameAllVariablesWheneverPrinting = true;
	
	protected Literal literalAdded    = null;
	//protected Literal formForPruning  = null; // This and the next are used for pruning.
	//protected Map<Variable,NumericConstant> variablesToNumbers = null;
	protected double  score           = Double.NaN; // Cache these to save recomputing (recomputing fast except for regression?).
	private double  posCoverage     = -1.0;     //   Also, each child node only stores the extensions to the clause body.
	protected double  negCoverage     = -1.0; // Everything is done with WEIGHTED examples (including the seeds).
	protected int     numberOfNewVars = 0;    // There is a max number of new (i.e., output) variables in a clause.  This is the total all the way to the root.
	protected PredicateSpec enabler; // This is the mode that was used to create this node.  Used (at least) when dropping a literal in a clause (so can tell if the later literals are still 'legally' present).  Not clear it is worth the space just for that, but might be useful somewhere down the road.  
	protected List<Type>                 typesPresent = null; // Keep track of the different types of terms added by this node.  If there is a need to reduce the size of nodes, could compute this when needed from the map below.
	protected List<AnnotatedLiteral>   dontReconsider = null; // If something is discarded at some point, don't reconsider it further down the search tree.  DON'T COPY (in buildNewAncestor) THIS WHEN REMOVING AN INTERMEDIATE LITERAL SINCE THAT INTERMEDIATE LITERAL MIGHT BE THE REASON FOR AN ENTRY (SO NEED TO RECREATE THE ONES THAT SHOULD HAVE BEEN KEPT).
	protected int                predicateOccurrences = 0;    // Count of how often this literal's predicate has occurred (this is a CUMULATIVE count from this node, assuming this predicate was added here, to the root).
	protected int    predicateOccurrencesPerFixedVars = 0;    // Count of how often this literal's predicate has occurred FOR THESE + and # variables (also a CUMULATIVE count).  This is how Aleph limits counts.
	protected List<Literal>            canonicalForm  = null; // Once put into a canonical form, cache it.
	protected Set<Example>  posExamplesThatFailedHere = null; // Record where each example fails to be satisfied.
	protected Set<Example>  negExamplesThatFailedHere = null; // Save space by not creating these until some examples fail at a node.
	protected Map<Type,List<Term>>           typesMap = null; // Also store this piece-by-piece at nodes (i.e., need to climb to root to collect/check all of them).
	private   Map<Term,Type>          typesOfNewTerms = null; // Record the types of new terms, if any, added here.  Used in at least the case where when evaluated on the full dataset a node has insufficient positive coverage to be kept.  This prevents it from being considered again.
	protected Map<Term,Integer>           depthOfArgs = null; // For each 'leaf term' (i.e., recur into functions) in this clause's literal, record its distance from the head.  An input var's depth is the depth of its parent.  An output var's depth is 1 + the max depth of all the input args in the literal.
	protected boolean                         pruneMe = false;// Can do some pruning here that the normal pruners don't handle.
	protected boolean                        timedOut = false;
	private   String                      extraString = null; // Used to augment the comment in the toString() with info about the examples that reach this node.
	
	private SingleClauseNode 	 startingNodeForReset = null; // Everytime we select new examples, we reset the scores but we lose the starting node information.(this is not a parent node when number of literals per node >1)
 
	// These two are only used for debugging.
	//transient protected static int                   nodeCounter =  0;
	//transient protected        int                   nodeID      = -1;
	
	public SingleClauseNode(StateBasedSearchTask task) {
		super(task);
	}
	public SingleClauseNode(SearchNode parentNode, Literal literalAdded) {
		this(parentNode, literalAdded, null, null, null, null, null);
	}
	public SingleClauseNode(SearchNode parentNode, Literal literalAdded, PredicateSpec enabler) {
		this(parentNode, literalAdded, null, enabler, null, null, null);
	}
	public SingleClauseNode(SearchNode parentNode, Literal literalAdded, Map<Term,Integer> argDepths, PredicateSpec enabler, List<Type> typesPresent, Map<Type,List<Term>> typesMap, Map<Term,Type> typesOfNewTerms) {
		super(parentNode);
		depthOfArgs          = argDepths;
		this.literalAdded    = literalAdded;
		this.enabler         = enabler;
		this.typesPresent    = typesPresent;
		this.typesMap        = typesMap;
		this.typesOfNewTerms = typesOfNewTerms;
		Map<Integer,List<Object>> constraints = literalAdded.predicateName.getConstrainsArgumentTypes(literalAdded.numberArgs());
		if (LearnOneClause.debugLevel > 2 && constraints != null) { Utils.println("constraints: " + constraints + " for " + literalAdded); }
		//Utils.println("literalAdded=" + literalAdded + " argDepths=" + argDepths + " enabler=" + enabler + " typesPresent=" + typesPresent + " typesMape=" + typesMap + " typesOfNewTerms=" + typesOfNewTerms);
		if (constraints != null) {
			LearnOneClause theTask = (LearnOneClause) task;
			for (Integer argNumber : constraints.keySet()) {
				if (argNumber > literalAdded.numberArgs()) { Utils.error("Internal bug ...  indexing mistake."); }
				Term    argN            = literalAdded.getArgument(argNumber - 1); // Counting starts from 0 internally but from 1 externally.
				Type    oldType         = getTypeOfThisTerm(argN);
				Type    newType         = (Type)    (constraints.get(argNumber).get(0)); // Use a list to pass back two things (not worth creating another class just for this ...).
				boolean pruneIfNoEffect = (Boolean) (constraints.get(argNumber).get(1));
				if (theTask.stringHandler.isaHandler.isa(oldType, newType)) {  // Nothing to do, since already of this type.
					if (LearnOneClause.debugLevel > 2) { Utils.println("%  New literal '" + literalAdded + "' constrains argument #" + argNumber + " (" + argN + ")\n% from type = '" + oldType + "' to type '" + newType + "', but '" + oldType + "' is more specific, so this has no effect."); }
					if (pruneIfNoEffect) { pruneMe = true; }
				} else if (theTask.stringHandler.isaHandler.isa(newType, oldType)) {
					if (LearnOneClause.debugLevel > 2) { Utils.println("%  New literal '" + literalAdded + "' constrains argument #" + argNumber + " (" + argN + ")\n% from type = '" + oldType + "' to type '" + newType + "'."); }
					// Update the type list stored at this node, overriding what is at a parent.
					if ( this.typesPresent    == null)        { this.typesPresent    = new ArrayList<Type>(1); }
					if ( this.typesOfNewTerms == null)        { this.typesOfNewTerms = new HashMap<Term,Type>(4); }
					if ( this.typesMap        == null)        { this.typesMap        = new HashMap<Type,List<Term>>(4); }
					if (!this.typesPresent.contains(newType)) { this.typesPresent.add(newType); }
					List<Term> newList = this.typesMap.get(newType);
					if (newList == null) { newList = new ArrayList<Term>(1); }
					newList.add(argN);  
					this.typesMap.put(newType, newList);
					this.typesOfNewTerms.put(argN, newType);
					if (LearnOneClause.debugLevel > 2) { Utils.println("% NOW getTypeOfThisTerm(argN)=" + getTypeOfThisTerm(argN)); }
				} else {
					if (LearnOneClause.debugLevel > 2) { Utils.println("%  New literal '" + literalAdded + "' constrains argument #" + argNumber + " (" + argN + ")\n%  from type = '" + oldType + "' to type '" + newType + "', but '" + oldType + "' is not more general than '" + newType + "', so this has no effect."); }
					if (pruneIfNoEffect) { pruneMe = true; }
				}
			} //Utils.waitHere("checking constrainers"); 
		}
		//nodeID = nodeCounter++;
	}
	
	public boolean acceptableScore(double minAcceptableNodeScore) {
		return score >= minAcceptableNodeScore;
	}
	public boolean matchesThisExample(Example ex, boolean isaPosExample) throws SearchInterrupted {
		if (getPosCoverage() < 0.0) { computeCoverage(); }
		if (isaPosExample) { return !posExampleAlreadyExcluded(ex); }
		return                      !negExampleAlreadyExcluded(ex);
	}
	
	protected Map<Term,Type> getTypesOfNewTerms() {
		return typesOfNewTerms;
	}
	protected void setTypesOfNewTerms(Map<Term, Type> typesOfNewTerms) {
		this.typesOfNewTerms = typesOfNewTerms;
	}
	protected void addTypeOfNewTerm(Term term, Type type) {
		if (typesOfNewTerms == null) { typesOfNewTerms = new HashMap<Term,Type>(4); }
		typesOfNewTerms.put(term, type);
	}
	protected Type getTypeOfThisTerm(Term arg) {
		if (LearnOneClause.debugLevel > 1) { Utils.println("what is current type of '" + arg + "'?   typesOfNewTerms: " + typesOfNewTerms + " for " + this); }
		if (typesOfNewTerms != null) {
			Type types = typesOfNewTerms.get(arg);
			if (types != null) { return types; }
		}
		if (getParentNode() == null) { return null; }
		return getParentNode().getTypeOfThisTerm(arg);
	}
	
	protected void markDepthOfLeafTerms(List<Term> arguments, int thisDepth) {
		if (arguments == null) { return; }
		for (Term arg : arguments) {
			if (arg instanceof Function) {
				markDepthOfLeafTerms( ((Function) arg).getArguments(), thisDepth);
			} else { depthOfArgs.put(arg, thisDepth); }
		}
	}
	
    protected boolean proveExampleBodies(LearnOneClause theILPtask, Literal target, List<List<Literal>> clauseBodies, Literal ex, BindingList bindings) throws SearchInterrupted {
        //Utils.println(" clauseBodies = " + clauseBodies);
    	if (Utils.getSizeSafely(clauseBodies) < 1) { 
    		if (bindings != null && bindings.theta.size() > 0) { bindings.theta.clear(); } // Revert to the empty binding list. 
    		return theILPtask.unifier.unify(target, ex, bindings) != null;
    	}
    	for (List<Literal> aBody : clauseBodies) {
            boolean result = proveExample(theILPtask, target, aBody, ex, bindings);
            if ( result == false ) return false;
        }
        return true;
    }

	// NOTE: bindings is passed in here to save memory-cell creation, not to constrain the unification.
	protected boolean proveExample(LearnOneClause theILPtask, Literal target, List<Literal> clauseBody, Literal ex, BindingList bindings) throws SearchInterrupted {
		if (bindings != null && bindings.theta.size() > 0) { bindings.theta.clear(); } // Revert to the empty binding list.
		bindings = ((LearnOneClause) task).unifier.unify(target, ex, bindings);		
		if (bindings == null) { return false; }
		List<Literal> query = bindings.applyTheta(clauseBody);
		//Utils.println("Try to prove: " + query + ".  Have these bindings to the example: " + bindings);		
		//BindingList bl2 = theILPtask.prover.proveConjunctiveQueryAndReturnBindings(query);
		//if (bl2 != null && clauseBody.size() < 2) {
		//	Utils.println("Try to prove: " + query);
		//	Utils.println("   result = " + theILPtask.prover.proveConjunctiveQueryAndReturnBindings(query));
		//}
		// if (LearnOneClause.debugLevel > 2) { Utils.println("  After binding example and target: bindings = " + bindings + "  query = " + query); }
		boolean  result = theILPtask.prove(query);
		//if (result) { Utils.println("  TRUE!"); } else { Utils.println("  FALSE!"); }  Utils.waitHere(); 
		if (LearnOneClause.debugLevel > 2 && !result) { Utils.println("%       " + query + " is false"); }
		return result;
		//return theILPtask.prove(query);
	}
	
	// Recursively climb to the root collecting all the literals.  Remember that the root holds the HEAD literal, and hence shouldn't be collected here.
	protected List<Literal> getClauseBody() {
		return getClauseBody(false);
	}
	protected List<Literal> getClauseBody(boolean stopAtCurrentStartingNode) {
		List<Literal> result;
		SingleClauseNode parent = getParentNode();
		boolean        stopHere = (stopAtCurrentStartingNode && this == ((LearnOneClause) task).currentStartingNode);
		if (!stopHere && parent != null) { 
			result = parent.getClauseBody(stopAtCurrentStartingNode);
			result.add(literalAdded); // Want to add to the END so the clause's literals are in the proper order.
		} else { 
			result = new ArrayList<Literal>(8);  // This makes sure a new list is being created.
		}
		return result;
	}
	protected List<Literal> getClauseBodyReversed() {
		List<Literal> result;
		SingleClauseNode parent = getParentNode();
		
		if (parent != null) { result = parent.getClauseBodyReversed();
							  result.add(0, literalAdded); }    // Want to add to the FRONT so the clause's literals are in reversed order.
		else                { result = new ArrayList<Literal>(8); } // This makes sure a new list is being created.
		return result;
	}

	protected Literal getClauseHead() {
		SingleClauseNode parent = getParentNode();
		
		if (parent != null) { return parent.getClauseHead(); }
		return literalAdded;
	}
	
	public Clause getClause() { // There are two climbs of the search tree, but that isn't a big deal since they are shallow.
		return getClause(false);
	}
	public Clause getClause(boolean onlyGetLocalAddition) { // If onlyGetLocalAddition, stop at gettingClauseBody at current starting node.
		List<Literal> headAsPosLiteralList = new ArrayList<Literal>(8);
		headAsPosLiteralList.add(getClauseHead());
		return ((LearnOneClause)task).stringHandler.getClause(headAsPosLiteralList, getClauseBody(onlyGetLocalAddition), extraString);
	}
	
	public Clause getLocallyAddedClause() {
		return getClause(true);
	}
	
	protected int bodyLength() {
		if (getParentNode() != null) { return 1 + getParentNode().bodyLength(); }
		return 0; // The root is 'true' and we don't count that literal.
	}
	
	protected double getCost() { // If predicates have costs, sum the costs. Otherwise all predicates 'cost' 1, so we can return length.
		LearnOneClause theTask = (LearnOneClause) task;
		if (theTask.stringHandler.getPredicatesHaveCosts()) {
			double total = 0.0;
			for (Literal lit : getClauseBody()) {  // TODO: use recursion instead of getting the clause body?
				if (LearnOneClause.debugLevel > 2) { Utils.println("%            cost = " + Utils.truncate(lit.predicateName.getCost(lit.numberArgs()), 3) +  " for lit = " + lit.predicateName + "/" + lit.numberArgs()); }
				total += lit.predicateName.getCost(lit.numberArgs());
			}
			return total;
		}
		return bodyLength();
	}

	// When the last literal is "determinate," it might be useful as a 'bridging' predicate.  This is used to give some "bonus points" in scoring this node.
	public boolean endsWithBridgerLiteral() {
		// return (literalAdded != null && literalAdded.isDeterminatePredicate());  TODO also treat 'determinates' as 'bridgers'?  What about numericFunctionsAsPred?
		return (literalAdded != null && literalAdded.isaBridgerLiteral());
	}
	
	// Find the parent that is 'count' many generations older.
	protected SingleClauseNode goBackThisManyGenerations(int count) {
		if (count <= 0 || getParentNode() == null) { return this; } // Be robust to count being too large.
		return getParentNode().goBackThisManyGenerations(count -1);
	}
	
	// Collect all the nodes between 'this' and the parent 'count' many generations older.
	protected List<SingleClauseNode> collectDescendantsOfThisAncestor(int count) {
		if (count > 0 && getParentNode() != null) { // Be robust to count being too large.
			List<SingleClauseNode> result = getParentNode().collectDescendantsOfThisAncestor(count - 1);
			result.add(this);
			return result;
		}
		return new ArrayList<SingleClauseNode>(4);
	}
	
	// Create a node that is a descendant and uses these literals (wrapped in SingleClauseNode's since other useful info is contained there).
	// Those literals that don't have the proper modes are discarded (some reordering of the literals might work, but too complex to search for such an ordering).
	protected SingleClauseNode buildNewAncestor(List<SingleClauseNode> newLiterals) throws SearchInterrupted {
		if (newLiterals == null) { return null; }

		// Create the next node if the current clause includes all of its required (ie, input) variables.
		int                    length         = newLiterals.size();
		SingleClauseNode       next           = newLiterals.get(0);
		Literal                newLiteral     = next.literalAdded;
		List<SingleClauseNode> newNewLiterals = (length <= 1 ? null : newLiterals.subList(1, length));
		
		// Tricky case: an input variable x of type HUMAN was added by the dropped literal.
		//              Now some OTHER input variable y of type HUMAN can be used, so need to change from x to y in next's literal.
		// Due to this tricky case, a simpler algorithm (explained below) is used.
		int counter = 0; // This is a "hacked up" way to do a double for loop.
		for (TypeSpec spec : next.enabler.getTypeSpecList()) {
			if (spec.mustBeBound()) { // See if all the necessary types for the first in newLiterals are present.
				// if (!isaVariablesOfThisTypePresentInChild(spec.isaType)) { // Due to the tricky case above, using a similar algo - namely, make sure that all input vars are still present.
				Term thisTerm = newLiteral.getArguments().get(counter); // Grab the required term and, if it is a variable, see if it still present.
				if (thisTerm instanceof Variable && !variableIsPresent((Variable) thisTerm)) {
					if (newNewLiterals == null) { return this; }  // Could not extend, but up to the point, had a legal node. (This might be the original node being extended - ie, no new nodes created - but the calling method can decide what to do in that case). 
					return buildNewAncestor(newNewLiterals);
				}
			}
			counter++;
		}
		// Need to COPY the current node (since it or some descendant might still be in OPEN).
		SingleClauseNode newNode = new SingleClauseNode(this, newLiteral, next.depthOfArgs, next.enabler, next.typesPresent, next.typesMap, next.typesOfNewTerms);  // Do NOT copy dontReconsider - see comment above for the reasons.
		// However, don't see if it fits into OPEN.  This will only be done on the final result (by the method that called this).
		newNode.computeCoverage();  // But do record the examples that failed here.
		
		// Now extend once more unless this was the last literal to add.
		if (length <= 1) { return newNode; }
		return newNode.buildNewAncestor(newNewLiterals);
	}	

	// For the given literal, collect all other instances of this predicate in the current clause.
	// Don't worry about matching (for now), other than confirming the number of args is the same.
	protected List<Literal> collectAllVariants(Literal newPredicate, PredicateSpec pSpec) {
		List<Literal> result = null;
		
		SingleClauseNode parent = getParentNode();
		if (parent != null) { result = parent.collectAllVariants(newPredicate, pSpec); }
		
		if (newPredicate.predicateName == literalAdded.predicateName  &&
		    newPredicate.numberArgs()  == literalAdded.numberArgs()) {
			if (result == null) { result = new ArrayList<Literal>(1); } // Create when needed.
			result.add(literalAdded);
		}
		return result;
	}

	protected boolean thisTermAppearsOnlyOnceInClause(Term termToCheck) { // TODO maybe should generalize to thisTermAppearsAtMostNtimeInClause (and maybe also write a "atLeastN" version).
		boolean result = help_thisTermAppearsOnlyOnceInClause(termToCheck, 0);
		return result;
	}
	protected boolean help_thisTermAppearsOnlyOnceInClause(Term termToCheck, int countSoFar) {
		// Utils.println("  help_thisTermAppearsOnlyOnceInClause: " + termToCheck + " at " + literalAdded);
		if (literalAdded.getArguments() != null) for (Term term : literalAdded.getArguments()) { 
			if (term == termToCheck) {	countSoFar++; }
			if (countSoFar > 1) { return false; } // Return false once count EXCEEDS 1.
		}
		SingleClauseNode parent = getParentNode();
		if (parent != null) { return parent.help_thisTermAppearsOnlyOnceInClause(termToCheck, countSoFar); }
		return (countSoFar == 1); // If at root, see if count=1.
	}
	
	protected boolean variableIsPresent(Variable var) {
		for (Term term : literalAdded.getArguments()) { if (term == var) return true; }
		// If not here, see if present in an ancestor.
		SingleClauseNode parent = getParentNode();
		if (parent != null) { return parent.variableIsPresent(var); }
		return false;
	}

	protected List<Term> termsOfThisTypePresentInChild(Type type) {
		List<Term> result = null;
		SingleClauseNode parent = getParentNode();
		
		if (parent != null) { result = parent.termsOfThisTypePresentInChild(type); }
		if (typesPresent != null) {
			List<Term> terms = getAllTypesPresent(type);
			if (terms != null) { 
				if (result == null) { result = new ArrayList<Term>(4); }
				result.addAll(terms);
			} 
		}
		return result;
	}
	
	// Find all terms added by this node that are of this type.
	// Handles hierarchical types.  If collectBelowType=true, then ok if the item is BELOW 'type' in the ISA hierarchy.
	// Eg, if type=animal and some term of type=dog is present, then return that term. (However, do NOT go the other way in the ISA hier.)
	// Otherwise, it is ok of the item is ABOVE 'type' in the ISA hierarchy.
	protected List<Term> getAllTypesPresent(Type type) {
		List<Term> allTerms = null;
		
		LearnOneClause theTask = (LearnOneClause) task;
		for (Type tp : typesPresent) if (theTask.stringHandler.isaHandler.isa(tp, type)) {
			List<Term> terms = typesMap.get(tp);
			if (terms != null) {
				if (allTerms == null) { allTerms = new ArrayList<Term>(4); }
				allTerms.addAll(terms);
			}
		}
		return allTerms;
	}
	
	// Variant of the above that simply CHECKS to see if there are any (ie, doesn't COLLECT them).
	protected boolean isaTermOfThisTypePresentInChild(Type type) {
		if (typesPresent != null) {
			List<Term> terms = getAllTypesPresent(type);  // This still new's new memory, so if this is a space-time hog, could create a cleaner version that only looks and doesn't touch.
			if (terms != null) { return true; } // Success since found this type.
		}
		// If not here, see if present in an ancestor.
		SingleClauseNode parent = getParentNode();
		if (parent != null) { return parent.isaTermOfThisTypePresentInChild(type); }
		return false;
	}	

	// Count how many times this predicate has occurred in this clause.	
	protected int countPredicateOccurrences(PredicateName pName, int arity) {
		if (literalAdded.predicateName == pName && literalAdded.numberArgs() == arity) { return predicateOccurrences; } // Store CUMMULATIVE counts at nodes (or could always count upwards and save an 'int' in the SingleClauseNode's).
		SingleClauseNode parent = getParentNode();
		if (parent != null) { return parent.countPredicateOccurrences(pName, arity); }
		return 0;
	}
	
	protected int countPredicateOccurrencesGivenInputArgs(PredicateName pName, int arity, List<Term> constantArgs) {
		// Utils.println("countPredicateOccurrencesGivenInputArgs: " + literalAdded + " vs. " + pName + "/" + arity + " constantArgs=" + constantArgs);
 		if (literalAdded.predicateName == pName && literalAdded.numberArgs() == arity && sameConstantArguments(arity, constantArgs)) { return predicateOccurrencesPerFixedVars; } // Store CUMMULATIVE counts at nodes (or could always count upwards and save an 'int' in the SingleClauseNode's).
		SingleClauseNode parent = getParentNode();
		if (parent != null) { return parent.countPredicateOccurrencesGivenInputArgs(pName, arity, constantArgs); }
		return 0;
	}
	
	// See if this node has these constant arguments.  When this is called, we know that predicateName/arity have been matched. 
	protected boolean sameConstantArguments(int arity, List<Term> constantArgs) {
		// Utils.println("sameConstantArguments: " + literalAdded + " vs.  constantArgs=" + constantArgs);
		List<Term> arguments = literalAdded.getArguments();
		for (int i =0; i < arity; i++) { // See if we get exact matches wherever the constantArgs do not equal null.
			if (constantArgs.get(i) != null && constantArgs.get(i) != arguments.get(i)) { return false; }
		}
 		return true;
	}
	
	protected Literal getTarget() {
		if (getParentNode() != null) { return getParentNode().getTarget(); }
		//if (!(this instanceof SingleClauseRootNode)) { Utils.error(); }
		return ((SingleClauseRootNode) this).target;
	}
	
	protected double wgtedCountOfPosExamplesCovered(List<Example> posExamples) throws SearchInterrupted {
		LearnOneClause   theILPtask = (LearnOneClause) task;
		SingleClauseNode parent     = getParentNode();
		Literal          target     = getTarget();
		List<Literal>    clauseBody = getClauseBody();  // To save space in OPEN, compute this when needed.
		double           total      = 0.0;

		// if (LearnOneClause.debugLevel > 2) { Utils.println("Evaluate: " + target + " :- " + clauseBody); }
		for (Example posEx : posExamples) if (parent == null || !parent.posExampleAlreadyExcluded(posEx)) { 
			if (proveExample(theILPtask, target, clauseBody, posEx, theILPtask.bindings)) { total += posEx.getWeightOnExample(); }
		}
		return total;
	}
	
	protected double wgtedCountOfNegExamplesCovered(List<Example> negExamples) throws SearchInterrupted {
		LearnOneClause   theILPtask = (LearnOneClause) task;
		SingleClauseNode parent     = getParentNode();
		Literal          target     = getTarget();
		List<Literal>    clauseBody = getClauseBody();  // To save space in OPEN, compute this when needed.
		double           total      = 0.0;
		
		for (Example negEx : negExamples) if (parent == null || !parent.negExampleAlreadyExcluded(negEx)) { 
			if (proveExample(theILPtask, target, clauseBody, negEx, theILPtask.bindings)) { total += negEx.getWeightOnExample(); }
		}
		return total;
	}
	
	public List<Example> collectExamplesReachingThisNode() {
		LearnOneClause theILPtask = (LearnOneClause) task;
		List<Example>  result     = null;
		
		try {
			computeCoverage();  // Make sure this node's clause has been applied.
			List<Example> pos = theILPtask.getPosExamples();
			if (pos != null) for (Example posEx : pos) if (!posExampleAlreadyExcluded(posEx)) {
				if (result == null) { result = new ArrayList<Example>(4); }
				result.add(posEx);
			}
			List<Example> negs = theILPtask.getNegExamples();
			if (negs != null) for (Example negEx : negs) if (!negExampleAlreadyExcluded(negEx)) { 
				if (result == null) { result = new ArrayList<Example>(4); }
				result.add(negEx);
			}
		}
		catch (SearchInterrupted e) {
			Utils.reportStackTrace(e);
			Utils.error("collectExamplesReachingThisNode encountered a problem.");
		}
		return result;
	}
	
	public int countOfSingletonVars(List<Variable> allVars) {
		List<Variable> singletons =  collectSingletonVars(allVars); // Wasted some space, but better than maintaining two minor variants of the same code. 
		
		if (singletons == null) { return 0; }
		return singletons.size();
	}
	
	public int countOfRepeatedLiterals(Set<PredicateName> pNames) {
		int localCount = 0;
		if (literalAdded != null) {
			if (pNames.contains(literalAdded.predicateName)) { localCount++; }
			else { pNames.add(literalAdded.predicateName); }
		}
		SingleClauseNode parent = getParentNode();
		if (parent != null) { return localCount + parent.countOfRepeatedLiterals(pNames); }
		return localCount;
	}
	
	// This should be a non-negative number (e.g., it will be subtracted elsewhere).
	// Give a discount on reusing a literal.  Currently the discount is hard-wired to reduce the cost
	// of the 2nd and subsequent uses by 10%,
	public double discountForRepeatedLiterals(Set<PredicateName> pNames) {
		double localDiscount = 0.0;
		if (literalAdded != null) {
			PredicateName pName = literalAdded.predicateName;
			if (pNames.contains(literalAdded.predicateName)) { localDiscount += 0.1 * pName.getCost(literalAdded.numberArgs()); }
			else { pNames.add(literalAdded.predicateName); }
		}
		SingleClauseNode parent = getParentNode();
		if (parent != null) { return localDiscount + parent.discountForRepeatedLiterals(pNames); }
		return localDiscount;
	}		
	
	public List<Variable> collectSingletonVars(List<Variable> allVars) {
		if (allVars == null) { return null; }
		List<Variable> singletons = null;
				
		for (Variable var : allVars) {
			int copiesOfVar = 0;
			for (Variable var2 : allVars) if (var == var2) {
				copiesOfVar++;
				if (copiesOfVar > 1) { break; }
			}
			if (copiesOfVar == 1) { 
				if (singletons == null) { singletons = new ArrayList<Variable>(4); }
				singletons.add(var);
			}
			if (copiesOfVar <  1) { Utils.error("Bug in countOfSingletonVars! " + allVars + "  " + this); }
		}		
		
		if (LearnOneClause.debugLevel > 2) { Utils.println("*** These '" + singletons + "' are the singleton variables in " + this); }
		return singletons;
	}
	
	public int countOfUniqueVars(List<Variable> allVars) {
		List<Variable> uniques =  collectUniqueVars(allVars); // Wasted some space, but better than maintaining two minor variants of the same code. 
		
		if (uniques == null) { return 0; }
		return uniques.size();
		
	}
	public List<Variable> collectUniqueVars(List<Variable> allVars) { // TODO - could simply return a set ...
		if (allVars == null) { return null; }
		List<Variable> seenVars = new ArrayList<Variable>(allVars.size());
		
		for (Variable var : allVars) {
			if (!seenVars.contains(var)) { seenVars.add(var); }
		}
		return seenVars;
	}
	
	public int countOfUniqueConstants(List<Constant> allConstants) {
		List<Constant> uniques =  collectUniqueConstants(allConstants); // Wasted some space, but better than maintaining two minor variants of the same code. 
		
		if (uniques == null) { return 0; }
		return uniques.size();
		
	}
	public List<Constant> collectUniqueConstants(List<Constant> allConstants) { // TODO - could simply return a set ...
		if (allConstants == null) { return null; }
		List<Constant> seenConstants = new ArrayList<Constant>(allConstants.size());
		
		for (Constant var : allConstants) {
			if (!seenConstants.contains(var)) { seenConstants.add(var); }
		}
		return seenConstants;
	}
	
	public List<Variable> collectAllVariables() {
		return collectAllVariables(null);
	}
	// Probably could make this code more space efficient ... TODO
	public List<Variable> collectAllVariables(List<Variable> listOfVars) {		
		List<Term> args = literalAdded.getArguments();		
		
		if (args != null && args.size() > 0) {
			for (Term term : args) if (term instanceof Variable) {
				if (listOfVars == null) { listOfVars = new ArrayList<Variable>(1); }
				listOfVars.add((Variable) term);
			}
		}
		SingleClauseNode parent = getParentNode();
		if (parent != null) { return parent.collectAllVariables(listOfVars); }
		return listOfVars;
	}
	
	public List<Constant> collectAllConstants() {
		return collectAllConstants(null);
	}
	// Probably could make this code more space efficient ... TODO
	public List<Constant> collectAllConstants(List<Constant> listOfConstants) {		
		List<Term> args = literalAdded.getArguments();		
		
		if (args != null && args.size() > 0) {
			for (Term term : args) if (term instanceof Constant) {
				if (listOfConstants == null) { listOfConstants = new ArrayList<Constant>(1); }
				listOfConstants.add((Constant) term);
			}
		}
		SingleClauseNode parent = getParentNode();
		if (parent != null) { return parent.collectAllConstants(listOfConstants); }
		return listOfConstants;
	}
	
	protected boolean acceptableCoverageOnPosSeeds() throws SearchInterrupted {
		LearnOneClause theILPtask = (LearnOneClause) task;
		double posSeedWgtedCount = 0.0;
	
		if (theILPtask.totalWeightOnPosSeeds > 0.0 && theILPtask.seedPosExamples != null) {
			if (LearnOneClause.debugLevel > 1) { Utils.println("   Score this on pos seeds: " + toString()); }
			posSeedWgtedCount = wgtedCountOfPosExamplesCovered(theILPtask.seedPosExamples);			
			//	Utils.println("posSeedWgtedCount = "  + posSeedWgtedCount + "   " + this);

//			if (theILPtask.clausesMustCoverFractPosSeeds * theILPtask.totalWeightOnPosSeeds <= Double.MIN_VALUE) {
//				Utils.waitHere("Do we want 'clausesMustCoverFractPosSeeds * totalWeightOnPosSeeds' to be: " + theILPtask.clausesMustCoverFractPosSeeds * theILPtask.totalWeightOnPosSeeds);
//			}
			
			if (posSeedWgtedCount < theILPtask.clausesMustCoverFractPosSeeds * theILPtask.totalWeightOnPosSeeds) { 
				if (LearnOneClause.debugLevel > 2) { Utils.println("   Discard '" + toString() + "' because not enough pos seed examples covered: " + posSeedWgtedCount + " of the total wgt'ed sum of " + theILPtask.totalWeightOnPosSeeds); }
				return false;
			}
		} else { // Comment this out if we really want this case.
			Utils.waitHere("Why totalWeightOnPosSeeds = " + theILPtask.totalWeightOnPosSeeds + " and |theILPtask.seedPosExamples| = " + Utils.comma(theILPtask.seedPosExamples));
		}
		if (LearnOneClause.debugLevel > 1 && theILPtask.seedPosExamples != null) { Utils.println("    Covers " + posSeedWgtedCount + " of the total wgt'ed sum (" + theILPtask.totalWeightOnPosSeeds + ") of pos seed examples.  " + this); }
		return true;
	}
	
	protected boolean acceptableCoverageOnNegSeeds() throws SearchInterrupted {
		LearnOneClause theILPtask = (LearnOneClause) task;
		double negSeedWgtedCount = 0;

		if (theILPtask.totalWeightOnNegSeeds > 0 && theILPtask.seedNegExamples != null) {
			if (LearnOneClause.debugLevel > 1) { Utils.println("   Score this on neg seeds: " + toString()); }
			negSeedWgtedCount = wgtedCountOfNegExamplesCovered(theILPtask.seedNegExamples);
			
			if (negSeedWgtedCount >= theILPtask.clausesMustNotCoverFractNegSeeds * theILPtask.totalWeightOnNegSeeds) { 
				if (LearnOneClause.debugLevel > 1) { Utils.println("  Discard '" + toString() + "' because too many neg seed examples covered:" + negSeedWgtedCount + " of total weighted sum of " + theILPtask.totalWeightOnNegSeeds); }
				return false;
			}
		}
		if (LearnOneClause.debugLevel > 1 && theILPtask.seedNegExamples != null) { Utils.println("    Covers " + negSeedWgtedCount + " of " + theILPtask.seedNegExamples.size() + " neg seed examples."); }
		return true;
	}	
	
	protected boolean acceptableCoverageOnSeeds() throws SearchInterrupted {
		return (acceptableCoverageOnPosSeeds() && acceptableCoverageOnNegSeeds());
	}
	
	// See if this clause matches at least the minimal required positive examples.
	protected boolean acceptableCoverageOnPosExamples() throws SearchInterrupted {
		LearnOneClause   theILPtask = (LearnOneClause) task;
		Literal          target     = getTarget();
		List<Literal>    clauseBody = getClauseBody();  // To save space in OPEN, compute this when needed.
		SingleClauseNode parent     = getParentNode();

		int    counter              = 0;
		double minCount             = theILPtask.getMinPosCoverage();
		for (Example posEx : theILPtask.getPosExamples()) if (parent == null || !parent.posExampleAlreadyExcluded(posEx)) { // Don't check HERE (i.e., start at parent) since we don't want to call computCoverage).
			if (LearnOneClause.debugLevel > 2) { Utils.println("  consider " + posEx + " [" + clauseBody + "]"); }
			if (proveExample(theILPtask, target, clauseBody, posEx, theILPtask.bindings)) { 
				counter += posEx.getWeightOnExample();
				if (LearnOneClause.debugLevel > 2) { Utils.println("    TRUE #" + counter); }
			}
			if (counter >= minCount) { return true; }
		}
		return false;
	}
	
	// Note that here we get missed examples, INCLUDING THOSE THAT FAILED AT EARLIER NODES.
	public Set<Example> getUptoKmissedPositiveExamples(int k) throws SearchInterrupted {
		if (k <= 0) { return null; }
		Set<Example>     results    = null;
		LearnOneClause   theILPtask = (LearnOneClause) task;
		Literal          target     = getTarget();
		List<Literal>    clauseBody = getClauseBody();  
		
		int counter = 0;
		List<List<Literal>> optimizedClauseBodies = getOptimizedClauseBodies(theILPtask, target, clauseBody);
		if (theILPtask.getPosExamples() != null) for (Example posEx : theILPtask.getPosExamples()) {
			// proveExample() clears the bindings, so no need to do so here.
			if (!proveExampleBodies(theILPtask, target, optimizedClauseBodies, posEx, theILPtask.bindings)) {
				if (results == null) { results = new HashSet<Example>(4); }
				results.add(posEx);
				counter++;
				if (counter >= k) { return results; }
			}
		}
		return results;
	}
	
	public Set<Example> getUptoKcoveredNegativeExamples(int k) throws SearchInterrupted {
		if (k <= 0) { return null; }
		Set<Example>     results    = null;
		LearnOneClause   theILPtask = (LearnOneClause) task;
		Literal          target     = getTarget();
		List<Literal>    clauseBody = getClauseBody();  
		
		int counter = 0;
		List<List<Literal>> optimizedClauseBodies = getOptimizedClauseBodies(theILPtask, target, clauseBody);
		if (theILPtask.getNegExamples() != null) for (Example negEx : theILPtask.getNegExamples()) {
			// proveExample() clears the bindings, so no need to do so here.
			if (proveExampleBodies(theILPtask, target, optimizedClauseBodies, negEx, theILPtask.bindings)) {
				if (results == null) { results = new HashSet<Example>(4); }
				results.add(negEx);
				counter++;
				if (counter >= k) { return results; }
			}
		}
		return results;
	}
		
	// TODO - should we store these results?
	private List<List<Literal>> getOptimizedClauseBodies(LearnOneClause theILPtask, Literal target, List<Literal> clauseBody) {
		if (Utils.getSizeSafely(clauseBody) < 1) { return null; }
		List<List<Literal>> optimizedClauseBodies = null;        
        try {
        	if (optimizedClauseBodies == null) { optimizedClauseBodies = theILPtask.getOptimizedClauseBodies(target, clauseBody); }
        } catch (Throwable e) {
			if (theILPtask.stringHandler.exceptionCount++ < HandleFOPCstrings.exceptionCountMax) { Utils.warning("% Exception thrown: Problem optimizing target = " + target + "\n with body = " + clauseBody); }
			optimizedClauseBodies = Collections.singletonList(clauseBody);
        }
        return optimizedClauseBodies;
	}
	
	// Only prove those examples covered by the parent node (but don't want to use too much space).
	public void computeCoverage() throws SearchInterrupted {
		LearnOneClause   theILPtask = (LearnOneClause) task;
		HornClauseProver prover     = theILPtask.getProver();
		Literal          target     = getTarget();
		List<Literal>    clauseBody = getClauseBody();  // To save space in OPEN, compute this when needed.
		SingleClauseNode parent     = getParentNode();
		boolean          firstTime            = false;
		boolean          tookTooLong          = false;
		long             totalResolutions     = 0;
		boolean          stopWhenUnacceptable = theILPtask.stopWhenUnacceptableCoverage; // Don't continue to prove examples when impossible to meet the minPosCoverage and minPrecision specifications.

		int localDebugLevel = Math.max(-2, LearnOneClause.debugLevel); // Change this line to get more info on false pos/negs.
		List<List<Literal>> optimizedClauseBodies = null;

		// To save time, if posCoverage is not going to reach theILPtask.minPosCoverage stop.
		if (getPosCoverage() < 0.0) {
			extraString = null; // Reset this whenever the coverage changes.
			if (localDebugLevel > 1) { Utils.println("%     computeCoverage: clauseBody = " + clauseBody); }
			double maxPossiblePosCoverage = 0.0;
			int    counter                = 0;
			int    numberPos              = Utils.getSizeSafely(theILPtask.getPosExamples());
			int    numberPosPossible      = 0;
			if (stopWhenUnacceptable) for (Example posEx : theILPtask.getPosExamples()) if (parent == null || !parent.posExampleAlreadyExcluded(posEx)) { // Don't look at THIS node or we'll have an infinite loop.
				maxPossiblePosCoverage += posEx.getWeightOnExample(); // See how much is possible
				numberPosPossible++;
			}
			setPosCoverage(0.0);
			firstTime = true;

			if (theILPtask.getPosExamples() != null) {
				HiddenLiteralState lastState = null;
				for (Example posEx : theILPtask.getPosExamples()) {
					if (parent == null || !parent.posExampleAlreadyExcluded(posEx)) { // Don't look at THIS node or we'll have an infinite loop.
						// Make sure the facts are set based on the hiddenstate required by the example
						// For EM
						// [
						if (posEx instanceof RegressionRDNExample) {
							RegressionRDNExample rex = (RegressionRDNExample)posEx;
							HiddenLiteralState  newState = rex.getStateAssociatedWithOutput();

							if (newState != null &&
									!newState.equals(lastState)) {
								Set<PredicateName> modifiedPredicates = new HashSet<PredicateName>();
								HiddenLiteralState.statePredicateDifference(lastState, newState, modifiedPredicates, target.predicateName.name);
								// Check if predicates present in the newly added node
								List<Literal> newLits = getClauseBody(true);
								for (Literal newLit : newLits) {
									// If a modified predicate is added, update the facts
									if (modifiedPredicates.contains(newLit.predicateName)) {
										theILPtask.updateFacts(lastState, newState, target.predicateName.name);
										lastState = newState;
										break;
									}
								}
							}
						}
						// ]
						counter++;
						if (optimizedClauseBodies == null) { optimizedClauseBodies = getOptimizedClauseBodies(theILPtask, target, clauseBody); }
						prover.setNodesCreated(0); // This counter gets reset when performSearch() is called, but that might not happen (eg, if the body is empty).
						// proveExample() clears the bindings, so no need to do so here.
						if (proveExampleBodies(theILPtask, target, optimizedClauseBodies, posEx, theILPtask.bindings)) {
							setPosCoverage(getPosCoverage() + posEx.getWeightOnExample());
						}
						else { if (localDebugLevel > 2) { Utils.println("%       MISSED POS (due to last literal): " + posEx); } // NOTE: this doesn't report those examples that failed EARLIER
						maxPossiblePosCoverage -= posEx.getWeightOnExample(); // Lost out on this.
						if (posExamplesThatFailedHere == null) { posExamplesThatFailedHere = new HashSet<Example>(); }
						posExamplesThatFailedHere.add(posEx);
						if (theILPtask.regressionTask && !theILPtask.oneClassTask) {
							if (cachedLocalRegressionInfoHolder == null) {  // Don't create until needed.
								cachedLocalRegressionInfoHolder = new LocalRegressionInfoHolder();
							}
							if (cachedLocalRegressionInfoHolder.cachedFalseStats == null) {
								cachedLocalRegressionInfoHolder.cachedFalseStats = theILPtask.getNewRegressionHolderForTask();
							}				   		

							if (!theILPtask.mlnRegressionTask) { // Example counting for MLN tasks later
								cachedLocalRegressionInfoHolder.getFalseStats().addFailureExample(posEx, 1, posEx.getWeightOnExample());
							}

						}
						} 
						totalResolutions += prover.getNodesCreated(); 
						if (localDebugLevel > 2) { Utils.println("       This POS example involved " + Utils.comma(prover.getNodesCreated()) + " resolutions: " + posEx); }
						if (totalResolutions > theILPtask.maxResolutionsPerClauseEval) { 
							if (localDebugLevel > 1) { Utils.waitHere("      Exceeded the limit of " + Utils.comma(theILPtask.maxResolutionsPerClauseEval) + " resolutions (this example took " + Utils.comma(prover.getNodesCreated()) + ")."); }
							tookTooLong = true; 
							extraString = "Coverage only partially computed- took too long to compute.";
							break; 
						}
						if (stopWhenUnacceptable && maxPossiblePosCoverage < theILPtask.getMinPosCoverage()) { 
							if (parent != null) { parent.addToDontConsiderThisLiteral(theILPtask, literalAdded.predicateName, literalAdded.getArguments(), typesOfNewTerms); }
							if (localDebugLevel > 1) { Utils.println("      posCoverage = " + Utils.truncate(getPosCoverage(), 3) + ",  maxPossiblePosCoverage = " + Utils.truncate(maxPossiblePosCoverage, 3) + " cannot meet the minPosCoverage (" + Utils.truncate(theILPtask.getMinPosCoverage(), 3) + "; skipping " + (numberPosPossible - counter) + " of the " + numberPosPossible + " examples that still remain from the original " + numberPos + " pos ex's) so setting coverage of this node to 0. [" + this + "]"); }
							setPosCoverage(0.0); 
							negCoverage = 0.0; 
							extraString = "Coverage only partially computed. (maxPossiblePosCoverage = " + Utils.truncate(maxPossiblePosCoverage, 3)
									+ " and MinPosCoverage = " + Utils.truncate(theILPtask.getMinPosCoverage(), 3) + ")";
							return; // No need continuing.
						}				
					}
				}
				if (theILPtask.regressionTask &&
						theILPtask.mlnRegressionTask &&
						posExamplesThatFailedHere != null) {
					int fraction = (posExamplesThatFailedHere.size()/(theILPtask.maxExamplesToSampleForScoring*2)) + 1;
					double prob = 1.0/(double)fraction;
					if (!theILPtask.sampleForScoring) {fraction =1;prob=1;}
					//Utils.println("False fraction=" + fraction + " prob=" + prob);
					for (Example posEx : posExamplesThatFailedHere) {
						// Make sure the facts are set based on the hiddenstate required by the example
						if (posEx instanceof RegressionRDNExample) {
							RegressionRDNExample rex = (RegressionRDNExample)posEx;
							HiddenLiteralState  newState = rex.getStateAssociatedWithOutput();
							if (newState != null &&
									!newState.equals(lastState)) {
								theILPtask.updateFacts(lastState, newState, target.predicateName.name);
								lastState = newState;
							}
						}
						if (Utils.random() < prob) {
							long num = 1;
							if (parent != null && parent != getRootNode()) { 
								num = parent.getNumberOfGroundingsForRegressionEx(posEx);
							}
							if (num == 0) {
								Utils.waitHere("Number of groundings = 0 for " + posEx + " with " + parent.getClause());
							}
							double output = ((RegressionExample) posEx).getOutputValue(); // Need to do everything with weighted counts.
							//Utils.println("adding "  + num + ":" + output + ":" + fraction);
							// TODO(test)
							// cachedLocalRegressionInfoHolder.localFalseStats.addNumOutput(num, output, fraction*posEx.getWeightOnExample(), ((RegressionRDNExample) posEx).getProbOfExample().getProbOfBeingTrue());
							cachedLocalRegressionInfoHolder.getFalseStats().addFailureExample(posEx, num, fraction*posEx.getWeightOnExample());
						}
					} 
				}
			}
		}

		// NOTE: Must not compare negCoverage to theILPtask.minPrecision since the task of ILP is to add literals until precision is acceptable.
		if (negCoverage < 0.0 && !tookTooLong) {
			extraString = null; // Reset this whenever the coverage changes.
			negCoverage = 0.0;
			firstTime = true;
			prover.setNodesCreated(0); // This counter gets reset when performSearch() is called, but that might not happen (e.g., if the body is empty).
			if (theILPtask.getNegExamples() != null) for (Example negEx : theILPtask.getNegExamples()) if (parent == null || !parent.negExampleAlreadyExcluded(negEx))  {
				if (optimizedClauseBodies == null) { optimizedClauseBodies = getOptimizedClauseBodies(theILPtask, target, clauseBody); }
				// proveExample() clears the bindings, so no need to do so here.
				if (proveExampleBodies(theILPtask, target, optimizedClauseBodies, negEx, theILPtask.bindings)) {
					if (localDebugLevel > 3) { Utils.println("%       COVERED NEG: " + negEx); }
					negCoverage += negEx.getWeightOnExample();
				}
				else { 
					if (negExamplesThatFailedHere == null) { negExamplesThatFailedHere = new HashSet<Example>(); }
					negExamplesThatFailedHere.add(negEx);
				}
				totalResolutions += prover.getNodesCreated(); 
				if (localDebugLevel > 2) { Utils.println("       This NEG example involved " + Utils.comma(prover.getNodesCreated()) + " resolutions: " + negEx); }
				if (totalResolutions > theILPtask.maxResolutionsPerClauseEval) { 
					if (localDebugLevel > 2) { Utils.waitHere("      Exceeded the limit of " + Utils.comma(theILPtask.maxResolutionsPerClauseEval) + " resolutions (this example took " + Utils.comma(prover.getNodesCreated()) + ")."); }
					tookTooLong = true; 
					extraString = "Coverage only partially computed - took too long to compute.";
					break; 
				}
			}
			if (localDebugLevel > 1) { Utils.println("      posCoverage = " + Utils.truncate(getPosCoverage(), 2) + " and negCoverage = " + Utils.truncate(negCoverage, 2) + "  " + this); }
		}

		if (tookTooLong) { // Would be nice to report more info regarding when the time-out occurred, but don't bother with extra counters.
			if (localDebugLevel > 1) { Utils.println("% Clause evaluation timed out with posCov = " + Utils.truncate(getPosCoverage(), 2) + " and negCov = " + Utils.truncate(negCoverage, 2) + " (total resolutions = " + Utils.comma(totalResolutions) + ") on:\n% " + this); }
			setPosCoverage(0.0); // When we abandon, we simply assume a clause is never true and never keep in the Gleaner.
			negCoverage = 0.0;
			timedOut    = true;
			extraString = "Coverage only partially computed- took too long to compute.";
		}
		// else if (firstTime && totalResolutions > 5000) { Utils.println(" total resolutions = " + totalResolutions + " for " + this); }
		// If this is the first time the coverage of this rule has been computed,
		// see if there is any need to continue searching (ie, if a rule covers ALL pos and NO neg examples, then can stop).  Might want to override this, say if collecting a range of good rules ala' Gleaner.
		if (firstTime && theILPtask.stopIfPerfectClauseFound && 
				!Utils.diffDoubles(getPosCoverage(), theILPtask.totalPosWeight) && negCoverage <= 0.0
				&& acceptableClauseExtraFilter(theILPtask)) { 
			// Be careful that setting this doesn't mess up what is being kept as the best node.  TODO - make sure that if the score of a perfect clause is insufficient (eg, m-estimate of accuracy is too low), this is caught early on.
			if (LearnOneClause.debugLevel > 0) { 
				Utils.println("%  Have found a perfect and acceptable clause, so can stop searching:\n% " + this); 
			}
			theILPtask.continueTheSearch = false;
		}
	}
	public boolean posExampleAlreadyExcluded(Example example) throws SearchInterrupted {
		if (getPosCoverage() < 0.0) { computeCoverage(); }
		if (posExamplesThatFailedHere != null && posExamplesThatFailedHere.contains(example)) { return true; }
		SingleClauseNode parent = getParentNode();
		if (parent == null) { return false; }
		return parent.posExampleAlreadyExcluded(example);
	}
	
	// Used to get examples on the false branch for a node
	public List<Example> posExampleFailedAtNode()  throws SearchInterrupted {
		if (getPosCoverage() < 0.0) { computeCoverage(); }
		if (this == ((LearnOneClause)task).currentStartingNode) {
			//if (posExamplesThatFailedHere == null) {
				return new ArrayList<Example>();
			//}
			//return new ArrayList<Example>(posExamplesThatFailedHere);
		}
		
		List<Example> failedExamples = null;
		if (posExamplesThatFailedHere != null) {
			failedExamples = new ArrayList<Example>(posExamplesThatFailedHere);
		} else {
			failedExamples = new ArrayList<Example>();
		}
		
		SingleClauseNode parent = getParentNode();
		if (parent == null) { return failedExamples; }
		failedExamples.addAll(parent.posExampleFailedAtNode());
		return failedExamples;
	}
	
	protected boolean negExampleAlreadyExcluded(Literal example) throws SearchInterrupted {
		if (negCoverage < 0.0) { computeCoverage(); }
		if (negExamplesThatFailedHere != null && negExamplesThatFailedHere.contains(example)) { return true; }
		SingleClauseNode parent = getParentNode();
		if (parent == null) { return false; }
		return parent.negExampleAlreadyExcluded(example);
	}
	
	public double precision () throws SearchInterrupted {
		LearnOneClause theILPtask = (LearnOneClause) task;

		if (getPosCoverage() < 0.0) { computeCoverage(); }
		// Assume this clause covers the m-estimated NEG examples but NOT the m-estimated POS examples.
		return getPosCoverage() / (getPosCoverage() + negCoverage + theILPtask.getMEstimateNeg());
	}
	
	// Compute m-estimated precision if all negs could be removed. (Note maxRecall is recall.)
	public double maxPrecision() throws SearchInterrupted {
		LearnOneClause theILPtask = (LearnOneClause) task;

		if (getPosCoverage() < 0.0) { computeCoverage(); }	
		// Assume this clause covers the m-estimated NEG examples but NOT the m-estimated POS examples.
		return getPosCoverage() / (getPosCoverage() + theILPtask.getMEstimateNeg());
	}
	
	public double recall() throws SearchInterrupted {
		LearnOneClause theILPtask = (LearnOneClause) task;

		if (getPosCoverage() < 0.0) { computeCoverage(); }
		// Assume this clause does NOT cover the m-estimated POS examples.
		return getPosCoverage() / (theILPtask.totalPosWeight + theILPtask.getMEstimatePos());
	}
	
	public double maxF(double beta) throws SearchInterrupted { // See http://en.wikipedia.org/wiki/Information_retrieval#F-measure		
		if (beta < 0) { Utils.error("Beta in F(Beta) must be non-negative: " + Utils.truncate(beta, 3) + " was provided."); }
		double precision = maxPrecision();		
		double recall    = recall();		
		
		double numer = (1 + beta) * precision * recall;
		double denom = beta * precision + recall;
		if (denom < Double.MIN_VALUE) { return 0; }
		return numer / denom;
	}
	
	public double F(double beta) throws SearchInterrupted { // See http://en.wikipedia.org/wiki/Information_retrieval#F-measure		
		if (beta < 0) { Utils.error("Beta in F(Beta) must be non-negative: " + Utils.truncate(beta, 3) + " was provided."); }
		double precision = precision();		
		double recall    = recall();		
		
		double numer = (1 + beta) * precision * recall;
		double denom = beta * precision + recall;
		if (denom < Double.MIN_VALUE) { return 0; }
		return numer / denom;
	}
	
	protected boolean canImprove(LearnOneClause thisTask) throws SearchInterrupted {  // Is it possible to improve this clause by adding another literal.
		if (getPosCoverage() < 0.0) { computeCoverage(); }
		LearnOneClause theILPtask = (LearnOneClause) task;
		
		// Note that minPrecision is the minimum required to be the "goal" node (i.e., if the best node doesn't score at least this much, the search fails).
		// So don't discard node just because they don't score that well.  Instead, look for the BEST possible score, and only
		// if that is too low can a node be ignored, since it can't be improved enough.
		// Also note that a node that took too long to evaluate will have posCoverage = negCoverage = 0 and this method will say it cannot be improved.
		if (getPosCoverage() <  theILPtask.getMinPosCoverage()) { 
			if (LearnOneClause.debugLevel > 1) { Utils.println("%  Do not expand since " + getPosCoverage() + " is below minimal positive weighted coverage of " + theILPtask.getMinPosCoverage()+ ".\n%    " + this); }
			return false;  // to do: also check if if it is possible to get minAcc (due to minEstimate)
		}
		
		if (thisTask.regressionTask) { return true; } // All tests BELOW here do no apply to categorization. 
		
		double bestPrecisionPossible = maxPrecision();
		if (bestPrecisionPossible <  theILPtask.minPrecision) { 
			if (LearnOneClause.debugLevel > 1) { Utils.println("%  Do not expand since cannot reach minimal precision of " + theILPtask.minPrecision + ".  The best possible precision (due to m-estimates) is " + bestPrecisionPossible + ".\n%    " + this); }
			return false;
		}
		if (!acceptableClauseExtraFilter(thisTask)) { return true; } // If a clause doesn't meet the 'acceptability' test, it can presumably be improved (e.g., might need to extend it, even if precision is 100%).
		if (negCoverage <= theILPtask.stopExpansionWhenAtThisNegCoverage) {
			if (LearnOneClause.debugLevel > 1) { Utils.println("%  Do not expand since no negative examples are covered.\n%    " + this); }
			return false;  // If no negs covered, adding literals wont help.
		}
		return true; // Still some neg's that could be eliminated.		
	}
	
	// This allows the user to say when a clause is acceptable for reasons other than recall, precision, or length.
	// E.g., in some work involving plan recognition, a learned rule must be a complete plan (i.e., reaches a final state),
	// rather than simply doing a good job of differentiating good from bad examples.
	// Also, if requireThatAllRequiredHeadArgsAppearInBody=true, see if this requirement is met.
	protected boolean acceptableClauseExtraFilter(LearnOneClause thisTask) {
		if (thisTask.requireThatAllRequiredHeadArgsAppearInBody && !allRequiredHeadArgsAppearInBody(thisTask)) { return false; }
		if (!allTheseArgsAppearinBody(getRequiredVariablesInBody()))    { return false; }
		// TODO need a better design here. 
		int counter = 0;
		if (thisTask.requiredBodyPredicatesForAcceptableClauses != null) for (Literal lit : thisTask.requiredBodyPredicatesForAcceptableClauses) {
			if (containsThisPredicate(lit.predicateName, lit.numberArgs())) {
				counter++;
			} // TODO - could speed up this code by seeing if impossible to meet the MIN specification, but probably not worth adding the extra code.
			if (counter > thisTask.maxRequiredBodyPredicates) { return false; } // Too many found (should then TURN OFF this search path, but that is not yet implemented - TODO).
		}
		boolean accept = (counter >= thisTask.minRequiredBodyPredicates && counter <=  thisTask.maxRequiredBodyPredicates);
		if (LearnOneClause.debugLevel > 0 && !accept) {  Utils.println("%  Unacceptable rule because # of literals (" + counter + ") is not in [" + thisTask.minRequiredBodyPredicates+ ", " + thisTask.maxRequiredBodyPredicates + "].\n%    " + this); } 
		return accept;
	}
	
	private Collection<Variable> getRequiredVariablesInBody() {
		if (getParentNode() != null) { return getParentNode().getRequiredVariablesInBody(); }
		return ((SingleClauseRootNode) this).requiredBodyVariablesInTarget;
	}
	
	public SingleClauseRootNode getRootNode() {
		if (this instanceof SingleClauseRootNode) { return (SingleClauseRootNode) this; }
		if (getParentNode() != null) { return getParentNode().getRootNode(); }
		Utils.error("Could not reach the root node from: " + this);
		return null;
	}
	
	protected List<Term> getVariablesInTarget() {
		if (getParentNode() != null) { return getParentNode().getVariablesInTarget(); }
		//if (!(this instanceof SingleClauseRootNode)) { Utils.error(); }
		return ((SingleClauseRootNode) this).variablesInTarget;
	}
	
	protected boolean allRequiredHeadArgsAppearInBody(LearnOneClause thisTask) {		
		SingleClauseRootNode root = getRootNode();
		if (root.targetArgSpecs == null) { Utils.error("Need mapFromTermToArgSpec to be set!"); }
		if (LearnOneClause.debugLevel > 1) { Utils.println("% targetArgSpecs = " + root.targetArgSpecs); }
		for (ArgSpec argSpec : root.targetArgSpecs) if (argSpec.arg instanceof Variable) {
			if (LearnOneClause.debugLevel > 1) { Utils.println("  Variable " + argSpec.arg + " has type " + argSpec.typeSpec); }
			if ((thisTask.allTargetVariablesMustBeInHead || argSpec.typeSpec.mustBeBound()) 
					&& !variableAppearsInThisClause((Variable) argSpec.arg)) { 
				if (LearnOneClause.debugLevel > 0) {  Utils.println("%  Unacceptable rule because it is missing this required head var: '" + argSpec.arg + "'\n%    " + this); }
					return false;
			}
		}	
		return true;
	}
	
	protected boolean allTheseArgsAppearinBody(Collection<Variable> requiredVars) {
		if (Utils.getSizeSafely(requiredVars) < 1) { return true; }
		for (Variable var : requiredVars) {
			if (!variableAppearsInThisClause(var)) {
				if (LearnOneClause.debugLevel > 0) {  Utils.println("Unacceptable rule because it is missing this required head var: '" + var + "'.\n " + this); }
				return false; 
			}
		}
		return true;
	}
	
	protected boolean variableAppearsInThisClause(Variable var) {
		if (getParentNode() == null) { return false; } // We do not want to check the FIRST literal, since that is the head.
		if (literalAdded.containsThisVariable(var)) { return true; }
		
		return getParentNode().variableAppearsInThisClause(var);
	}
	
	protected boolean containsThisPredicate(PredicateName pName, int arity) {
		if (literalAdded.predicateName == pName && literalAdded.numberArgs() == arity) { return true; }
		if (getParentNode() == null) { return false; }
		return getParentNode().containsThisPredicate(pName, arity);
	}
	
	// If this literal is already in the clause or in the "dontReconsider" list, then it should be skipped over.
	protected boolean dontConsiderThisLiteral(boolean discardDuplicateLiterals, Literal candidate, Map<Term,Type> newTermsInLiteral) {
		if (discardDuplicateLiterals && literalAdded != null && literalAdded.equals(candidate)) { 
			if (LearnOneClause.debugLevel > 2) { Utils.println("  CANNOT ADD: '" + candidate + "' since already in clause."); }
			return true; 
		}
		if (dontReconsider != null) {
			for (AnnotatedLiteral badLit : dontReconsider) if (badLit.equals(candidate, newTermsInLiteral)) { 
				if (LearnOneClause.debugLevel > 2) { Utils.println("  CANNOT ADD: '" + candidate + " [with new terms=" + newTermsInLiteral + "]' since '" + badLit + "' in clause's bad list."); }
				return true;
			}
		}
		SingleClauseNode parent = getParentNode();
		if (parent == null) { return false; }
		return parent.dontConsiderThisLiteral(discardDuplicateLiterals, candidate, newTermsInLiteral);
	}
	
	protected void addToDontConsiderThisLiteral(LearnOneClause thisTask, PredicateName predName, List<Term> args, Map<Term,Type> thisTypesOfNewTerms) {
		if (dontReconsider == null) { dontReconsider = new ArrayList<AnnotatedLiteral>(1); }
		Map<Term,Type> typesOfNewTermsInTheseArgs = null;
		if (thisTypesOfNewTerms != null) {
			for (Term term : args) { // Only keep those new terms (if any) that are in this 'rejected' literal.  (Could see if ALL are there, and if so, no need to copy, but seems better to simply always copy.)
				if (thisTypesOfNewTerms.containsKey(term)) {
					if (typesOfNewTermsInTheseArgs == null) { typesOfNewTermsInTheseArgs = new HashMap<Term,Type>(4); }
					typesOfNewTermsInTheseArgs.put(term, thisTypesOfNewTerms.get(term));
				}
			}
		}
		dontReconsider.add(new AnnotatedLiteral(thisTask.stringHandler, predName, args, typesOfNewTermsInTheseArgs));
	}
	
	protected void reportBadList() {
		if (dontReconsider != null) { Utils.println("    Bad list: " + dontReconsider); }
		SingleClauseNode parent = getParentNode();
		if (parent != null) { parent.reportBadList(); }
	}
	
	protected void reportTypesPresent() {
		if (typesPresent != null) { Utils.println("    Types present: " + typesPresent); }
		SingleClauseNode parent = getParentNode();
		if (parent != null) { parent.reportTypesPresent(); }
	}
	
	protected void reportTypedVariablesPresent() {
		if (typesPresent != null) { Utils.println("    Typed variables present: " + typesMap); }
		SingleClauseNode parent = getParentNode();
		if (parent != null) { parent.reportTypedVariablesPresent(); }
	}
	
	protected boolean literalAlreadyInClause(Literal candidate) {
		if (literalAdded == null)               { return false; }
		if (literalAdded.equals(candidate))     { return true;  }
		SingleClauseNode parent = getParentNode();
		if (parent == null)                     { return false; }
		return parent.literalAlreadyInClause(candidate);
	}
	
	// The depth of an argument measures its shortest path, in terms of the number of new variables, to the head.
	protected Integer getDepthOfArgument(Term item) {
		if (depthOfArgs == null) { Utils.error("Should not have depthOfArgs=null!"); }
		Integer integer = depthOfArgs.get(item);
		
		if (integer != null) { return integer; }
		SingleClauseNode parent = getParentNode();
		if (parent == null)  { return null; }
		return parent.getDepthOfArgument(item);
	}
	
	public Clause convertBodyToCounter() {
		return convertBodyToCounter(true);
	}
	public Clause convertBodyToCounter(boolean countUniqueBindings) {
		String         predNamePostfix = (countUniqueBindings ? "UniqueBindings" : "Proofs");
		LearnOneClause theILPtask      = (LearnOneClause) task;
		Literal        counterBody     = theILPtask.stringHandler.getLiteral(theILPtask.stringHandler.getPredicateName("count" + predNamePostfix));
		Variable       counterVariable = (Variable) theILPtask.stringHandler.getVariableOrConstant(theILPtask.stringHandler.usingPrologNotation() ? "CountOf" + predNamePostfix : "countOf" + predNamePostfix);
		
		Literal       newHead = getNewHead(counterVariable);
		
		List<Literal> clauseBody = getClauseBody();
		if (clauseBody == null || clauseBody.size() < 1) { return null; }
		Clause clauseInsideCounter = theILPtask.stringHandler.getClause(null, clauseBody, extraString);
		List<Term> arguments2 = new ArrayList<Term>(2);
		arguments2.add(theILPtask.stringHandler.getSentenceAsTerm(clauseInsideCounter, predNamePostfix));
		arguments2.add(counterVariable);		
		counterBody.setArguments(arguments2);
		
		List<Literal> newPosLits = new ArrayList<Literal>(1);
		newPosLits.add(newHead);
		List<Literal> newNegLits = new ArrayList<Literal>(1);
		newNegLits.add(counterBody);
		return theILPtask.stringHandler.getClause(newPosLits, newNegLits, extraString);
	}	

	protected Literal getNewHead(Variable resultsVariable) {
		LearnOneClause theILPtask = (LearnOneClause) task;
		Literal       clauseHead  = getClauseHead(); 
		PredicateName featureName = theILPtask.stringHandler.getPredicateName("featureFor_" + clauseHead.predicateName);
		Literal       newHead     = theILPtask.stringHandler.getLiteral(featureName);
		List<Term>    oldArgs     = clauseHead.getArguments();
		List<Term> arguments2 = new ArrayList<Term>(oldArgs.size());
		arguments2.addAll(oldArgs);
		arguments2.set(oldArgs.size() - 2, resultsVariable); // Assumes the second-to-last argument in a function is the VALUE.
		newHead.setArguments(arguments2);
		return newHead;
	}
	
	/*
	 * If all of these literals in this body are determinate with a numeric type, add a Product calculations, 
	 * e.g.: 'featureFor_distanceAB(A, B, C, Product, E) :- xPos(A, B, F, E), xPos(A, C, I, E) }, Product is F * I.'
	 * 
	 * TODO make this code more robust.  Eg, add 'isNonVar(F), isaNonVar(I)' predicates, etc.
	 */
	public Clause convertDeterminateBodyToProduct() {

	//	Literal       clauseHead = getClauseHead(); 
		List<Literal> clauseBody = getClauseBody();
		
		if (clauseBody == null || clauseBody.size() < 1) { return null; } // TODO handle case of ONE argument specially.

		LearnOneClause theILPtask      = (LearnOneClause) task;
		Variable       productVariable = (Variable) theILPtask.stringHandler.getVariableOrConstant(theILPtask.stringHandler.usingPrologNotation() ? "ProductOfNumericValues" : "productOfNumericValues"); // Use a variable name where a name collision is unlikely. 
		
		List<Term> termsToMultiply = null;
		// Check that ALL body predicates are determinate literals of a numeric type.  If not, return null.
		PredicateName guard         = null;
		List<Literal> guardLiterals = null;
		for (Literal bodyLit : clauseBody) {
			PredicateName pName     = bodyLit.predicateName;
			int           numericArg = pName.returnFunctionAsPredPosition(FunctionAsPredType.numeric, bodyLit.numberArgs());
			
			if (numericArg < 1) { return null; }
			if (termsToMultiply == null) { termsToMultiply = new ArrayList<Term>(2); }
			Term argToMult = bodyLit.getArgument(numericArg - 1); // Convert from a counter that starts at 1 to one that starts at 0.
			// Cannot test if this argument is numeric until bound, so leave this to Java's runtime debugging (TODO check data for any such erroneous data).			
			termsToMultiply.add(argToMult);
			
			if (guard == null) {
				guard = theILPtask.stringHandler.standardPredicateNames.number;
				guardLiterals = new ArrayList<Literal>(clauseBody.size());
			}
			Literal guardLit = theILPtask.stringHandler.getLiteral(guard, argToMult); // This needs to be negated.
			guardLiterals.add(guardLit);
		}

		// Create a literal of the form:  Value is A * B * C. 
		Literal        newHead      = getNewHead(productVariable); 
		Term           productValue = newHead.getArgument(newHead.numberArgs() - 2);
		PredicateName  productName  = theILPtask.stringHandler.standardPredicateNames.is;  productName.printUsingInFixNotation = true;
		Literal        finalLiteral = theILPtask.stringHandler.getLiteral(productName); // This needs to be negated.
	//	finalLiteral.setPrintUsingInFixNotation();
		List<Term> arguments2 = new ArrayList<Term>(2);
		arguments2.add(productValue);
		finalLiteral.setArguments(arguments2);
		
		// Next build up the items being multiplied.
		Term rhs = null;
		for (Term multiplicant : termsToMultiply) {
			if (rhs == null) {
				rhs = multiplicant;
			}
			else {
				FunctionName fName = theILPtask.stringHandler.getFunctionName("*");  fName.printUsingInFixNotation = true;
				Function     mult  = theILPtask.stringHandler.getFunction(fName);
			//	mult.setPrintUsingInFixNotation();
				List<Term> arguments3 = new ArrayList<Term>(2);
				arguments3.add(rhs);
				arguments3.add(multiplicant);
				mult.setArguments(arguments3);
				rhs = mult;				
			}
		}
		List<Term> arguments4 = finalLiteral.getArguments();
		arguments4.add(rhs);
		finalLiteral.setArguments(arguments4);
		
		// Add this new literal to the end of the clause body.
		List<Literal> newPosLits = new ArrayList<Literal>(1);
		newPosLits.add(newHead);
		List<Literal> newNegLits = new ArrayList<Literal>(1);
		newNegLits.addAll(clauseBody);
		newNegLits.addAll(guardLiterals);
		newNegLits.add(finalLiteral);
		return theILPtask.stringHandler.getClause(newPosLits, newNegLits, extraString);
	}
		
    @Override
	public String toString() {
		LearnOneClause theILPtask = (LearnOneClause) task;
		// String result = "Node #" + nodeID + ": "
		String result = "";
		boolean firstTime = true;
		List<Literal> clauseBody = getClauseBody();
		Literal       clauseHead = getClauseHead();
		
		if (renameAllVariablesWheneverPrinting) {
			List<Literal> posLits = new ArrayList<Literal>(1);
			posLits.add(clauseHead);
			Clause c = theILPtask.stringHandler.getClause(posLits, clauseBody, extraString);
			c = (Clause) theILPtask.stringHandler.renameAllVariables(c);
			clauseBody = c.negLiterals;
			clauseHead = c.posLiterals.get(0);
		}

		if (Utils.getSizeSafely(clauseBody) <= 0) { 
			result += clauseHead;
		}
		else if (theILPtask.stringHandler.usingStdLogicNotation()) {
			for (Literal literal : clauseBody) { 
				if (firstTime) { firstTime = false; } else { result += " ^ "; } 
				result += literal;  // Note that in "rule" form, we want unnegated literals.
			}
			result += " => " + clauseHead;
		}
		else {
			result += clauseHead + " :- ";
			for (Literal literal : clauseBody) { 
				if (firstTime) { firstTime = false; } else { result += ", "; } 
				result += literal;  // Note that in "rule" form, we want unnegated literals.
			}
		}
		
		if (getPosCoverage() < 0 && negCoverage < 0) return result; // This node is only a candidate and has not yet been scored.
	//	return result + ".  [covers " 
	//                      + Utils.truncate(posCoverage) + "/" + Utils.truncate(theILPtask.totalPosWeight) + " pos, " 
	//						+ Utils.truncate(negCoverage) + "/" + Utils.truncate(theILPtask.totalNegWeight) + " neg] depthOfArgs=" + depthOfArgs;
//		if (extraString == null) {
//			extraString = Example.makeLabel(collectExamplesReachingThisNode()); // A bit wasteful to collect all the examples rather than walking through them.  But the latter would require repeating the makeLabel code.
//			if (extraString == null) { extraString = ""; } // Mark that it has been processed (i.e., it is non-null).
//			else                     { extraString = " " + extraString; }
//		}
//		if (theILPtask.regressionTask) {
//			try {
//				return result + ".  [E(var) = " + Utils.truncate(regressionFit(true), 4) + ", covers " + Utils.truncate(posCoverage) + "/" + Utils.truncate(theILPtask.totalPosWeight) + " examples]" + extraString;
//			} catch (SearchInterrupted e) {
//				Utils.reportStackTrace(e);
//				Utils.error("Problem in SingleClauseNode.");
//			}
//		}
		return result + ".  [covers " 
		                    + Utils.truncate(getPosCoverage()) + "/" + Utils.truncate(theILPtask.totalPosWeight) + " pos, " 
		                    + Utils.truncate(negCoverage) + "/" + Utils.truncate(theILPtask.totalNegWeight) + " neg]" + (extraString == null ? "" : extraString);
	}
 
    /////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    
    // Code for regression trees.  Assumes LEAVES HOLD CONSTANTS (i.e., the group's mean).
    // and that we care to score examples not covered by the clause the same as those covered
    // (this makes sense when learning a TREE; if just learning rules, can set theILPtask.multiplerOnFailedRegressionExamples = 0 or a small positive number).
    
    public double penaltyForNonDiscrNode() throws SearchInterrupted {
    	// TODO(MLNTEST)
		//RegressionNodeInfoHolderForMLN holder = getRegressionNodeInfoHolderForMLN();
    	RegressionInfoHolder holder = getRegressionInfoHolder();
		double s1 = getPenaltyForNonDisc(holder.getTrueStats());
		double s2 = getPenaltyForNonDisc(holder.getFalseStats());

		return s1 + s2; 	
    }
    private double getPenaltyForNonDisc(BranchStats stats) {
    	double pos = stats.getNumPositiveOutputs();
    	double neg = stats.getNumNegativeOutputs();
    	double p = pos/(pos+neg);
    	if (pos+neg==0) { 
    		return 0;
    	}
    	return 1 - (Math.pow(p, 2) + Math.pow((1-p), 2));	
    }
    
    protected double square(double x) { return x * x; }
    
    public double oneClassScore() throws SearchInterrupted {
    	LearnOneClause loc = ((LearnOneClause)this.task);
    	List<Example> failedEgs = posExampleFailedAtNode();
    	
    	//return loc.occScorer.calculateScore(
    	//return Math.random();
    	 return loc.occScorer.calculateKernelScore(
    				PairWiseExampleScore.removeFromCopy(loc.getPosExamples(), failedEgs),
    				failedEgs, depth);
    }
    
	public double regressionFit() throws SearchInterrupted {
		return regressionFit(true);
	}
	public double regressionFitForMLNs() throws SearchInterrupted {
		LearnOneClause  theILPtask = (LearnOneClause) task;
		
		if (!theILPtask.constantsAtLeaves) { Utils.error("Have not yet implemented constantsAtLeaves = false."); }
		if ( theILPtask.normToUse != 2)    { Utils.error("Have not yet implemented normToUse = " + theILPtask.normToUse + "."); }
		if (this.timedOut) { 
			Utils.println("Giving INF score for " + this.getClause() +
					" as it timed out. The examples on true and false branch are incorrect.");
			return Double.POSITIVE_INFINITY;  
		}
		//TODO(MLNTEST)
		RegressionInfoHolder holder = getRegressionInfoHolder();
		if (holder.totalExampleWeightAtSuccess() < theILPtask.getMinPosCoverage() ||
			holder.totalExampleWeightAtFailure() < theILPtask.getMinPosCoverage()) { 
			//Utils.println("minpos" + theILPtask.getMinPosCoverage() + "tbs: " + holder.trueBranchStats.getNumExamples() + " " + holder.falseBranchStats.getNumExamples() );
			return Double.POSITIVE_INFINITY;  // Bad clauses get posCoverage=0 and we don't want to keep such clauses.  Remember we NEGATE the score, so a high score here is bad.
		}
		double result = 0;
		if (holder.getTrueStats() != null) { result += getMLNCost(holder.getTrueStats()); } else { Utils.waitHere("Why is true stats null?" + this.literalAdded); }
		if (holder.getFalseStats() != null) { result += getMLNCost(holder.getFalseStats()); } else { Utils.waitHere("Why is false stats null?"+ this.literalAdded); }
		
//		RegressionNodeInfoHolderForMLN holder = getRegressionNodeInfoHolderForMLN();
//		if (holder.trueBranchStats.getNumExamples() < theILPtask.getMinPosCoverage() ||
//			holder.falseBranchStats.getNumExamples() < theILPtask.getMinPosCoverage()) { 
//			//Utils.println("minpos" + theILPtask.getMinPosCoverage() + "tbs: " + holder.trueBranchStats.getNumExamples() + " " + holder.falseBranchStats.getNumExamples() );
//			return Double.POSITIVE_INFINITY;  // Bad clauses get posCoverage=0 and we don't want to keep such clauses.  Remember we NEGATE the score, so a high score here is bad.
//		}
//		
//		double result = 0;
//		if (holder.trueBranchStats != null) {
//			double trueCost = getMLNCost(holder.trueBranchStats);
//			result += trueCost;
//			if (result == 0) {
//				//Utils.println("true: "  + holder.trueBranchStats.toString());
//			}
//		//	Utils.println("True Result: " + result);
//		}
//		if (holder.falseBranchStats != null) {
//			double falseCost = getMLNCost(holder.falseBranchStats);
//			result += falseCost;
//			if (result == 0) {
//				//Utils.println("false: "  + holder.falseBranchStats.toString());
//			}
//			if (falseCost == 0 && result != 0) {
//				//Utils.waitHere("true:"+ holder.trueBranchStats.toString());
//			}
//			
//		}
//		//Utils.println("True+False Result: " + result + "/ " + (holder.trueBranchStats.numExamples+holder.falseBranchStats.numExamples) + " for " + this.getClause(true));
//		Utils.println("Score for:" + this.getClause(true) + ":" + result);
//		if (!Utils.diffDoubles(result, 0.0)) {
//			return Double.POSITIVE_INFINITY;  
//		}
		return result;
	}
	
	
	
	private double getMLNCost(BranchStats stats) {
		//double lambda = stats.getLambda();
		double result = 0;
		if (stats.getSumOfNumGroundingSquared() > 0) {
			//Utils.println(stats.toString());
			result = stats.getWeightedVariance(); //stats.sumOfOutputSquared - (Math.pow(stats.sumOfOutputAndNumGrounding, 2)/stats.getSumOfNumGroundingSquared());
		}
		// lambda * lambda * stats.sumOfNumGroundingSquared
				// - 2 * lambda * stats.sumOfOutputAndNumGrounding 
				// + stats.sumOfOutputSquared;
		
		// Scaled by number of examples
		if (stats.getNumExamples() == 0) {
			if (result != 0) {
				Utils.println(stats.toString());
				Utils.waitHere("Result is not zero but examples are!!");
			}
			return 0;
		}
		
		if (result < 0) {
			if (Math.abs(result) < 1e-8 ) {
				result = 0;
			} else {
				Utils.waitHere(result +":"+ stats.toString());
				result=0;
			}
		}
	//	Utils.println(stats.toString());
		// result /= stats.numExamples;
		return result;
	}
	public double regressionFit(boolean computeWeightedAverage) throws SearchInterrupted { // This is the expected variance after this node is evaluated (divided by the wgt'ed number of examples if computeWeightedAverage=true).
		LearnOneClause  theILPtask = (LearnOneClause) task;
		
		if (!theILPtask.constantsAtLeaves) { Utils.error("Have not yet implemented constantsAtLeaves = false."); }
		if ( theILPtask.normToUse != 2)    { Utils.error("Have not yet implemented normToUse = " + theILPtask.normToUse + "."); }

		if (getRegressionInfoHolder().totalExampleWeightAtSuccess() < theILPtask.getMinPosCoverage() ||
			getRegressionInfoHolder().totalExampleWeightAtFailure() < theILPtask.getMinPosCoverage()) {
			if (LearnOneClause.debugLevel > 2) {
				Utils.println("regressionFit:\n weightedCountOfExamplesThatSucceed = " + getRegressionInfoHolder().totalExampleWeightAtSuccess() 
									      + "\n weightedCountOfExamplesThatFail    = " + getRegressionInfoHolder().totalExampleWeightAtFailure()
									      + "\n getMinPosCoverage                  = " + theILPtask.getMinPosCoverage());
			}
			return Double.POSITIVE_INFINITY;  // Bad clauses get posCoverage=0 and we don't want to keep such clauses.  Remember we NEGATE the score, so a high score here is bad.
		}
			
		
		// TODO(test)
		if (!computeWeightedAverage) {
			return getRegressionInfoHolder().variance();
		}
		
		
		return getRegressionInfoHolder().weightedVarianceAtSuccess() + getRegressionInfoHolder().weightedVarianceAtFailure();
		/*
		RegressionNodeInfoHolder holder = getRegressionNodeInfoHolder();
		// Utils.println("Regression score for " + this.getClause(true));
		if (holder.weightedCountOfExamplesThatSucceed < theILPtask.getMinPosCoverage() || holder.weightedCountOfExamplesThatFail < theILPtask.getMinPosCoverage()) { 
			if (LearnOneClause.debugLevel > 2) {
				Utils.println("regressionFit:\n weightedCountOfExamplesThatSucceed = " + holder.weightedCountOfExamplesThatSucceed 
									      + "\n weightedCountOfExamplesThatFail    = " + holder.weightedCountOfExamplesThatFail
									      + "\n getMinPosCoverage                  = " + theILPtask.getMinPosCoverage());
			}
			return Double.POSITIVE_INFINITY;  // Bad clauses get posCoverage=0 and we don't want to keep such clauses.  Remember we NEGATE the score, so a high score here is bad.
		}
		//Utils.println("minCov = " + theILPtask.getMinPosCoverage() + " posWgt = " + holder.weightedCountOfExamplesThatSucceed + " negWgt = " +  holder.weightedCountOfExamplesThatFail + "  " + this);
		
		if (false) {
			Utils.println("");
			Utils.println("% weightedCountOfExamplesThatFailed    = " + holder.weightedCountOfExamplesThatFail);
			Utils.println("% weightedCountOfExamplesThatSucceeded = " + holder.weightedCountOfExamplesThatSucceed);
			Utils.println("% meanOnExamplesThatFailed             = " + (holder.totalOfOutputValuesOfExamplesThatFail   / holder.weightedCountOfExamplesThatFail));
		//	Utils.println("% meanOnExamplesThatFailed             = " + meanIfFalse());
			Utils.println("% meanOnExamplesThatSucceeded          = " + (holder.totalOfOutputValuesOfExamplesThatSucceed / holder.weightedCountOfExamplesThatSucceed));
		//	Utils.println("% meanOnExamplesThatSucceeded          = " + meanIfTrue());
			Utils.println("% varianceOnExamplesThatFailed         = " + holder.varianceOnExamplesThatFail);
			Utils.println("% varianceOnExamplesThatSucceeded      = " + holder.varianceOnExamplesThatSucceed);
		//	Utils.println("% OVERALL AVERAGE (should be constant): " + ( (getTotalOfOutputValuesOfExamplesThatFailed() + holder.totalOfOutputValuesOfExamplesThatSucceededHere) / (holder.weightedCountOfExamplesThatFailed + holder.weightedCountOfExamplesThatSucceeded)));
		}
		
		// Normalize to a 'per example' value so that other penalty terms can be added to a normalized number (assuming that the outputs are normalized to, say, [0,1] or [-0.5, 0,5].  TODO - do this normalization.
		return        (holder.weightedCountOfExamplesThatFail * holder.varianceOnExamplesThatFail + holder.weightedCountOfExamplesThatSucceed * holder.varianceOnExamplesThatSucceed)
				/ (computeWeightedAverage 
					? (holder.weightedCountOfExamplesThatFail                                     + holder.weightedCountOfExamplesThatSucceed)
				    : 1);
				    */
	}

	
	public RegressionInfoHolder getTotalFalseBranchHolder() {
		if (this == ((LearnOneClause) task).currentStartingNode) {
			return null;
		} // For this calculation don't want to go past the current root (but for other cases we do - i.e., when looking for eligible variables to reuse).
		if (getPosCoverage() < 0) { Utils.error("This should not happen."); } // Should only call via regressionFit (or at least after regressionFit is called). 
		SingleClauseNode parent = getParentNode();
		if (parent != null) { return cachedLocalRegressionInfoHolder.getFalseStats().addFailureStats(parent.getTotalFalseBranchHolder()); }
		return cachedLocalRegressionInfoHolder.getFalseStats();
	}
	
	// TODO(test)	
//	public BranchStats getTotalFalseBranchStats() {
//		if (this == ((LearnOneClause) task).currentStartingNode) {
//			return new BranchStats(); 
//		} // For this calculation don't want to go past the current root (but for other cases we do - i.e., when looking for eligible variables to reuse).
//		if (posCoverage < 0) { Utils.error("This should not happen."); } // Should only call via regressionFit (or at least after regressionFit is called). 
//		SingleClauseNode parent = getParentNode();
//		if (parent != null) { return getLocalFalseBranchStats().add(parent.getTotalFalseBranchStats()); }
//		return getLocalFalseBranchStats();
//	}
//	public BranchStats getLocalFalseBranchStats() {
//		if (cachedLocalRegressionInfoHolder == null) {
//			Utils.println("Clause:"+getClause());
//			return new BranchStats(); 
//		}
//		return cachedLocalRegressionInfoHolder.localFalseStats;
//	}

	/*
	public double getTotalProbabilityScoreThatFailed() {
		if (this == ((LearnOneClause) task).currentStartingNode) { return 0.0; } // For this calculation don't want to go past the current root (but for other cases we do - i.e., when looking for eligible variables to reuse).
		if (posCoverage < 0) { Utils.error("This should not happen."); } // Should only call via regressionFit (or at least after regressionFit is called). 
		SingleClauseNode parent = getParentNode();
		if (parent != null) { return getLocalProbabilityScoreThatFailed() + parent.getTotalProbabilityScoreThatFailed(); }
		return getLocalProbabilityScoreThatFailed();
	}
	private double getLocalProbabilityScoreThatFailed() {
		if (cachedLocalRegressionInfoHolder == null) { return 0.0; } // This should always exist at this point, but play it safe.
		return cachedLocalRegressionInfoHolder.totalProbabilityScoreThatFailedHere;
	}
	
	protected double getTotalSquaredOfOutputValuesThatFailed() {
		if (this == ((LearnOneClause) task).currentStartingNode) { return 0.0; } // For this calculation don't want to go past the current root (but for other cases we do - i.e., when looking for eligible variables to reuse).
		if (posCoverage < 0) { Utils.error("This should not happen."); } // Should only call via regressionFit (or at least after regressionFit is called). 
		SingleClauseNode parent = getParentNode();
		if (parent != null) { return getLocalTotalSquaredOfOutputValuesThatFailed() + parent.getTotalSquaredOfOutputValuesThatFailed(); }
		return getLocalTotalSquaredOfOutputValuesThatFailed();
	}
	private double getLocalTotalSquaredOfOutputValuesThatFailed() {
		if (cachedLocalRegressionInfoHolder == null) { return 0.0; } // This should always exist at this point, but play it safe.
		return cachedLocalRegressionInfoHolder.totalSquaredOfOutputValuesThatFailedHere;
	}
	
	protected double getTotalOfOutputValuesOfExamplesThatFailed() {
		if (this == ((LearnOneClause) task).currentStartingNode) { return 0.0; }  // See comment above.
		if (posCoverage < 0) { Utils.error("This should not happen."); } // Should only call via regressionFit (or at least after regressionFit is called). 
		SingleClauseNode parent = getParentNode();
		if (parent != null) { return  getLocalTotalOfOutputValuesOfExamplesThatFailed() + parent.getTotalOfOutputValuesOfExamplesThatFailed(); }
		return getLocalTotalOfOutputValuesOfExamplesThatFailed();
	}	
	private double getLocalTotalOfOutputValuesOfExamplesThatFailed() {
		if (cachedLocalRegressionInfoHolder == null) { return 0.0; } // This should always exist at this point, but play it safe.
		return cachedLocalRegressionInfoHolder.totalOfOutputValuesOfExamplesThatFailedHere;
	}
	*/
	
	public double[] meanVectorIfTrue() {
		return getRegressionInfoHolder().meanVectorAtSuccess();
	}
	
	public double[] meanVectorIfFalse() {
		return getRegressionInfoHolder().meanVectorAtFailure();
	}
	
	public double meanIfTrue() throws SearchInterrupted {
		// TODO(test)
		// Utils.println("Calculated mean from " + getRegressionInfoHolder().totalExampleWeightAtSuccess());
		return getRegressionInfoHolder().meanAtSuccess();
		/*
		RegressionNodeInfoHolder holder = getRegressionNodeInfoHolder();	
		if (((LearnOneClause)task).useProbabilityWeights) {
			//Utils.error("Disabled prob wts");
			return holder.totalOfOutputValuesOfExamplesThatSucceed /holder.weightedProbabilityScoreThatSucceed;  
		}
		return holder.totalOfOutputValuesOfExamplesThatSucceed / holder.weightedCountOfExamplesThatSucceed;
		*/ 
	}
	
	public double meanIfFalse() throws SearchInterrupted {
		// TODO(test)
		return getRegressionInfoHolder().meanAtFailure();
		
		/*
		RegressionNodeInfoHolder holder = getRegressionNodeInfoHolder();
		if (((LearnOneClause)task).useProbabilityWeights) {
			//Utils.error("Disabled prob wts");
			return holder.totalOfOutputValuesOfExamplesThatFail / holder.weightedProbabilityScoreThatFail;  
		}

		return holder.totalOfOutputValuesOfExamplesThatFail /holder.weightedCountOfExamplesThatFail;
		*/
	}
	public double mlnRegressionForTrue() throws SearchInterrupted {
		// TODO(MLNTEST)
		//RegressionNodeInfoHolderForMLN holder = getRegressionNodeInfoHolderForMLN();
		//return holder.trueBranchStats.getLambda(((LearnOneClause)task).useProbabilityWeights);
		RegressionInfoHolder holder = getRegressionInfoHolder();
		return holder.meanAtSuccess();
	}
	public double mlnRegressionForFalse() throws SearchInterrupted {
		// TODO(MLNTEST)
		//RegressionNodeInfoHolderForMLN holder = getRegressionNodeInfoHolderForMLN();
		//return holder.falseBranchStats.getLambda(((LearnOneClause)task).useProbabilityWeights);
		RegressionInfoHolder holder = getRegressionInfoHolder();
		return holder.meanAtFailure();
	}
	
	public SingleClauseNode getStartingNodeForReset() {
		return startingNodeForReset;
	}
	public void setStartingNodeForReset(SingleClauseNode startingNodeForReset) {
		this.startingNodeForReset = startingNodeForReset;
	}
	public String reportRegressionRuleAsString(boolean examplesFlipFlopped) throws SearchInterrupted {
		String result = "FOR " + getClauseHead() + " ";
		
		List<Literal> bodyLits = getClauseBody();
		if (Utils.getSizeSafely(bodyLits) < 1) { result += "output = " + Utils.truncate(examplesFlipFlopped ? meanIfFalse() : meanIfTrue(), 6); }
		else {
			boolean firstTime = true;
			result += "IF (";
			for (Literal lit : bodyLits) {
				if (firstTime) { firstTime = false; } else { result += ", "; }
				result += lit;
			}
			result += ") THEN output = " + Utils.truncate(examplesFlipFlopped ? meanIfFalse() : meanIfTrue(), 6) + " ELSE output = " + Utils.truncate(examplesFlipFlopped ? meanIfTrue() : meanIfFalse(), 6);
		}
		return result + ";" + (extraString == null ? "" : " // " + extraString);
	}
	
	// If TRUE, then this branch will become a LEAF.
	public boolean acceptableScoreFalseBranch(double minAcceptableScore) throws SearchInterrupted {
		LearnOneClause theILPtask = (LearnOneClause) task;	
		if (theILPtask.regressionTask) {
			// TODO(test)
			double variance = 0 ;
			if (theILPtask.oneClassTask) {
				variance = getVarianceFalseBranch();
			} else {
				variance = getRegressionInfoHolder().varianceAtFailure() ;
				Utils.println("Comparing variance: " + variance + " to score=" + minAcceptableScore + " #egs=" + getRegressionInfoHolder().totalExampleWeightAtFailure());
			}
			return variance <= minAcceptableScore;
			/*RegressionNodeInfoHolder holder = getRegressionNodeInfoHolder();		
			return holder.varianceOnExamplesThatFail <= minAcceptableScore;*/
		}

		double precision = precisionOnFailedExamples();
		if (precision       >= minAcceptableScore) { return true; } // Have a sufficiently pure POS set after splitting.
		if ((1 - precision) >= minAcceptableScore) { return true; } // Have a sufficiently pure NEG set after splitting.
		return false;		
	}	
	// This is a bit cpu-intensive, but unless this is called multiple times, no need to cache it. 
	private double precisionOnFailedExamples() throws SearchInterrupted {
		LearnOneClause theILPtask = (LearnOneClause) task;

		if (getPosCoverage() < 0.0) { computeCoverage(); }
		double posCoverageFailed = 0.0;
		double negCoverageFailed = 0.0;
		for (Example posEx : theILPtask.getPosExamples()) if (posExampleAlreadyExcluded(posEx)) { posCoverageFailed += posEx.getWeightOnExample(); }
		for (Example negEx : theILPtask.getNegExamples()) if (negExampleAlreadyExcluded(negEx)) { negCoverageFailed += negEx.getWeightOnExample(); }
			
		// Assume this clause covers the m-estimated NEG examples but NOT the m-estimated POS examples.
		return posCoverageFailed / (posCoverageFailed + negCoverageFailed + theILPtask.getMEstimateNeg());
	}
	
	public double getVarianceTrueBranch() throws SearchInterrupted {
		return getVarianceTrueBranch(false);
	}
	public double getVarianceTrueBranch(boolean computeMean) throws SearchInterrupted {
		LearnOneClause theILPtask = (LearnOneClause) task;
		if (theILPtask.oneClassTask) {
			return theILPtask.occScorer.getVariance(PairWiseExampleScore.removeFromCopy(theILPtask.getPosExamples(), posExampleFailedAtNode()));
		}
		if (theILPtask.regressionTask) {
			// TODO(test)
			RegressionInfoHolder holder = getRegressionInfoHolder();
			if (computeMean && holder.totalExampleWeightAtSuccess() > 0.0) { return  holder.varianceAtSuccess(); }
			return holder.weightedVarianceAtSuccess();
			/*
			RegressionNodeInfoHolder holder = getRegressionNodeInfoHolder();
			if (computeMean && holder.weightedCountOfExamplesThatSucceed > 0.0) { return  holder.varianceOnExamplesThatSucceed /  holder.weightedCountOfExamplesThatSucceed; }
			return holder.varianceOnExamplesThatSucceed;*/
		}
		return -1.0; // If discrete-valued return this to indicate "not relevant."
	}

	
	public double getVarianceFalseBranch() throws SearchInterrupted {
		return getVarianceFalseBranch(false);
	}
	public double getVarianceFalseBranch(boolean computeMean) throws SearchInterrupted {
		LearnOneClause theILPtask = (LearnOneClause) task;
		
		if (theILPtask.oneClassTask) {
			return theILPtask.occScorer.getVariance(this.posExampleFailedAtNode());
		}
		if (theILPtask.regressionTask) {
			// TODO(test)
						RegressionInfoHolder holder = getRegressionInfoHolder();
						if (computeMean && holder.totalExampleWeightAtFailure() > 0.0) { return  holder.varianceAtFailure(); }
						return holder.weightedVarianceAtFailure();
						/*
			RegressionNodeInfoHolder holder = getRegressionNodeInfoHolder();
			if (computeMean && holder.weightedCountOfExamplesThatFail > 0.0) { return  holder.varianceOnExamplesThatFail /  holder.weightedCountOfExamplesThatFail; }
			return holder.varianceOnExamplesThatFail;*/
		}
		return -1.0; // If discrete-valued return this to indicate "not relevant."
	}
	
	// If TRUE, then this branch will become a LEAF.
	public boolean acceptableScoreTrueBranch(double acceptableScore) throws SearchInterrupted {	
		LearnOneClause theILPtask = (LearnOneClause) task;
		if (theILPtask.regressionTask) {	
			// TODO(test)
			//if (!theILPtask.mlnRegressionTask) {
				double variance = 0;
				if (theILPtask.oneClassTask) {
					variance = getVarianceTrueBranch();
				} else {
					variance = getRegressionInfoHolder().varianceAtSuccess() ;
					Utils.println("Comparing variance: " + variance + " to score=" + acceptableScore+ " #egs=" + getRegressionInfoHolder().totalExampleWeightAtSuccess());
				}	
				
				return variance <= acceptableScore;
			//} else {
//				RegressionNodeInfoHolderForMLN holder = getRegressionNodeInfoHolderForMLN();
				//return (holder.trueBranchStats.getWeightedVariance() / holder.trueBranchStats.getNumExamples()) <= acceptableScore;
			//}
		}
		
		double precision = precision();
		if (precision       >= acceptableScore) { return true; } // Have a sufficiently pure POS set after splitting.
		if ((1 - precision) >= acceptableScore) { return true; } // Have a sufficiently pure NEG set after splitting.
		
		return false;
	}
	
	protected LocalRegressionInfoHolder cachedLocalRegressionInfoHolder  = null; // Waste a little space for non-regression problems, but only one pointer.
	
	// TODO(test)
	private RegressionInfoHolder getRegressionInfoHolder() {
		if (cachedLocalRegressionInfoHolder == null) { 
			cachedLocalRegressionInfoHolder = new LocalRegressionInfoHolder();
		}
        // TODO(test)
		/*
		if (cachedLocalRegressionInfoHolder.resultsHolder == null) {
			LearnOneClause theILPtask = (LearnOneClause) task;
			cachedLocalRegressionInfoHolder.resultsHolder = new RegressionNodeInfoHolder(theILPtask, this);
		}
		*/
		LearnOneClause theILPtask = (LearnOneClause) task;

		/*
		if (!theILPtask.mlnRegressionTask && cachedLocalRegressionInfoHolder.resultsHolder == null) {
			cachedLocalRegressionInfoHolder.resultsHolder = new RegressionInfoHolderForRDN();
			if (cachedLocalRegressionInfoHolder.cachedFalseStats == null) {
				cachedLocalRegressionInfoHolder.cachedFalseStats =  new RegressionInfoHolderForRDN();
			}
		}
		if (theILPtask.mlnRegressionTask && cachedLocalRegressionInfoHolder.resultsHolder == null) {
			cachedLocalRegressionInfoHolder.resultsHolder = new RegressionInfoHolderForMLN();
			if (cachedLocalRegressionInfoHolder.cachedFalseStats == null) {
				cachedLocalRegressionInfoHolder.cachedFalseStats =  new RegressionInfoHolderForRDN();
			}
		}
		*/
		if (cachedLocalRegressionInfoHolder.resultsHolder == null) {
			cachedLocalRegressionInfoHolder.resultsHolder = theILPtask.getNewRegressionHolderForTask();
			if (cachedLocalRegressionInfoHolder.cachedFalseStats == null) {
				cachedLocalRegressionInfoHolder.cachedFalseStats = theILPtask.getNewRegressionHolderForTask();
			}
			try {
				cachedLocalRegressionInfoHolder.resultsHolder.populateExamples((LearnOneClause)task, this);
			} catch (SearchInterrupted e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		return cachedLocalRegressionInfoHolder.resultsHolder;
	}
	// TODO(test)
	/*
	private RegressionNodeInfoHolder getRegressionNodeInfoHolder() throws SearchInterrupted {
		if (cachedLocalRegressionInfoHolder == null) { 
			cachedLocalRegressionInfoHolder = new LocalRegressionInfoHolder();
		}
 
		if (cachedLocalRegressionInfoHolder.resultsHolder == null) {
			LearnOneClause theILPtask = (LearnOneClause) task;
			cachedLocalRegressionInfoHolder.resultsHolder = new RegressionNodeInfoHolder(theILPtask, this);
		}
		
	return cachedLocalRegressionInfoHolder.resultsHolder;
	
	}*/
	
//	public RegressionNodeInfoHolderForMLN getRegressionNodeInfoHolderForMLN() throws SearchInterrupted {
//		if (cachedLocalRegressionInfoHolder == null) { 
//			cachedLocalRegressionInfoHolder = new LocalRegressionInfoHolder();
//		}
//		if (cachedLocalRegressionInfoHolder.mlnResultsHolder == null) {
//			LearnOneClause theILPtask = (LearnOneClause) task;
//			cachedLocalRegressionInfoHolder.mlnResultsHolder = new RegressionNodeInfoHolderForMLN(theILPtask, this);
//		}
//		return cachedLocalRegressionInfoHolder.mlnResultsHolder;
//	}

	// Used when creating a recursive call in a tree-structured task.
	protected void resetAssumingAllExamplesCovered() throws SearchInterrupted {
		LearnOneClause theILPtask = (LearnOneClause) task;
		setPosCoverage(Example.getWeightOfExamples(theILPtask.getPosExamples()));
		negCoverage = Example.getWeightOfExamples(theILPtask.getNegExamples());
		score = Double.NaN;
		if (theILPtask.regressionTask) { resetRegressionNodeInfoHolder(); }
	}
	
	protected void resetRegressionNodeInfoHolder() throws SearchInterrupted {
		if (cachedLocalRegressionInfoHolder == null) {
			return; 
		}
		cachedLocalRegressionInfoHolder.reset();
        // TODO(test)
		/*
		if (cachedLocalRegressionInfoHolder.resultsHolder != null) {
			cachedLocalRegressionInfoHolder.resultsHolder.reset((LearnOneClause) task, this);
		}
		if (cachedLocalRegressionInfoHolder.mlnResultsHolder != null) {
			cachedLocalRegressionInfoHolder.mlnResultsHolder.reset((LearnOneClause) task, this);
		}
		*/ 
	}
	
	public int numberOfBridgersInBody(SingleClauseNode nodeAtWhichThisSearchStarted) {
		if (this == nodeAtWhichThisSearchStarted) { return 0; } // Only count bridgers locally in tree-structured runs.
		int total = (endsWithBridgerLiteral() ? 1 : 0);
		if (getParentNode() == null) { return total; }
		return total + getParentNode().numberOfBridgersInBody(nodeAtWhichThisSearchStarted);
	}

    public SingleClauseNode getParentNode() {
        return (SingleClauseNode) super.getParentNode();
    }

    public Literal getLiteralAdded() {
        return literalAdded;
    }
    

    class LocalRegressionInfoHolder {	// These are used for regression, so lower nodes can be scored quickly (at the cost of another instance variable,. but designed to only 'waste' one pointer when not doing regressiion.
        // TODO(test)
		 //protected double totalOfOutputValuesOfExamplesThatFailedHere = 0.0;
        //protected double  totalSquaredOfOutputValuesThatFailedHere    = 0.0;
        // private double totalProbabilityScoreThatFailedHere = 0.0;
        // protected BranchStats localFalseStats 			=	new BranchStats();
    	
        // TODO(test)
        // protected RegressionNodeInfoHolder resultsHolder;
        // protected RegressionNodeInfoHolderForMLN mlnResultsHolder;
        
        // TODO(test)
        protected RegressionInfoHolder resultsHolder;
        // Keep it separate from the results holder that is used for computing mean/variance
        // Maybe not needed but better to be safe.
        protected RegressionInfoHolder cachedFalseStats;
        
        public LocalRegressionInfoHolder() {
        }


        public RegressionInfoHolder getFalseStats() {
        	
        	// TODO(test)
        	return cachedFalseStats;
        }
        protected void reset() {
            // TODO(test)
        	
            //totalOfOutputValuesOfExamplesThatFailedHere = 0.0;
            //totalSquaredOfOutputValuesThatFailedHere    = 0.0;
            // localFalseStats = new BranchStats();
        	cachedFalseStats = null;
            
        }

    }

    // TODO(test)
    /*
    class RegressionNodeInfoHolder {

        protected double totalOfOutputValuesOfExamplesThatSucceed = 0.0;
        protected double totalSquaredOfOutputValuesThatSucceed    = 0.0;
        protected double totalOfOutputValuesOfExamplesThatFail    = 0.0;
        protected double totalSquaredOfOutputValuesThatFail       = 0.0;
        protected double weightedCountOfExamplesThatSucceed       = 0.0;
        protected double weightedCountOfExamplesThatFail          = 0.0;
        protected double weightedProbabilityScoreThatSucceed	  = 0.0;
        protected double weightedProbabilityScoreThatFail		  = 0.0;
        protected double varianceOnExamplesThatSucceed            = 0.0;
        protected double varianceOnExamplesThatFail               = 0.0;

		public RegressionNodeInfoHolder(LearnOneClause theILPtask, SingleClauseNode caller) throws SearchInterrupted {
            reset(theILPtask, caller);
        }

        protected void reset(LearnOneClause theILPtask, SingleClauseNode caller) throws SearchInterrupted {
            totalOfOutputValuesOfExamplesThatSucceed = 0.0;
            totalSquaredOfOutputValuesThatSucceed    = 0.0;
            totalOfOutputValuesOfExamplesThatFail    = 0.0;
            totalSquaredOfOutputValuesThatFail       = 0.0;
            weightedCountOfExamplesThatSucceed       = 0.0;
            weightedCountOfExamplesThatFail          = 0.0;
            weightedProbabilityScoreThatSucceed		 = 0.0;
            weightedProbabilityScoreThatFail		 = 0.0;
            varianceOnExamplesThatSucceed            = 0.0;
            varianceOnExamplesThatFail               = 0.0;
            if (!theILPtask.regressionTask) { Utils.error("Should call this when NOT doing regression."); }
            if (caller.posCoverage < 0.0) { caller.computeCoverage(); }
            for (Example posEx : theILPtask.getPosExamples()) {
                double weight = posEx.getWeightOnExample();
                double output = ((RegressionExample) posEx).getOutputValue();
                double deno = 1;
                if (theILPtask.useProbabilityWeights) {
                	double prob   = ((RegressionRDNExample)posEx).getProbOfExample();
                	//boolean truth = ((RegressionRDNExample)posEx).isOriginalTruthValue();
                	deno   = prob * (1-prob);
                	if (deno < 0.1) {
                		deno = 0.1; 
                	}
                }
                
                if (!caller.posExampleAlreadyExcluded(posEx)) {
                    totalOfOutputValuesOfExamplesThatSucceed += output * posEx.getWeightOnExample();
                    totalSquaredOfOutputValuesThatSucceed    += caller.square(output) * posEx.getWeightOnExample();
                    weightedCountOfExamplesThatSucceed       += weight;
                    weightedProbabilityScoreThatSucceed      += weight * deno; 
                }
//             NOTE: cannot do this, since we only want to go back as far as examples that reached the currentStartingNode.
//                else {
//                	if (caller.getParentNode() == null ||
//                		!caller.getParentNode().posExampleAlreadyExcluded(posEx)) {
//                		totalOfOutputValuesOfExamplesThatFail    += output;
//                		totalSquaredOfOutputValuesThatFail       += caller.square(output);
//                		weightedCountOfExamplesThatFail          += weight;
//                	}
//                }
//                
            }

            if(((LearnOneClause)caller.task).currentStartingNode == caller) {
				Utils.waitHere("Starting node is same as current node for " + caller.getClause());
			}
            weightedCountOfExamplesThatFail       = theILPtask.totalPosWeight - weightedCountOfExamplesThatSucceed;
           totalOfOutputValuesOfExamplesThatFail = caller.getTotalOfOutputValuesOfExamplesThatFailed(); //caller.getTotalOfOutputValuesOfExamplesThatFailed();
           totalSquaredOfOutputValuesThatFail    = caller.getTotalSquaredOfOutputValuesThatFailed(); //getTotalSquaredOfOutputValuesThatFailed();
           if (theILPtask.useProbabilityWeights) {
        	   weightedProbabilityScoreThatFail = caller.getTotalProbabilityScoreThatFailed();
           }
            varianceOnExamplesThatFail
                    = (weightedCountOfExamplesThatFail    <= 0.0 ? 0.0
                            : (totalSquaredOfOutputValuesThatFail                        / weightedCountOfExamplesThatFail)
                                - caller.square(totalOfOutputValuesOfExamplesThatFail    / weightedCountOfExamplesThatFail));

            varianceOnExamplesThatSucceed
                    = (weightedCountOfExamplesThatSucceed <= 0.0 ? 0.0
                            :  (totalSquaredOfOutputValuesThatSucceed                    / weightedCountOfExamplesThatSucceed)
                                - caller.square(totalOfOutputValuesOfExamplesThatSucceed / weightedCountOfExamplesThatSucceed));
        }
    }
*/
   
    
    public HashMap<Example, Set<BindingList>> cachedBindingLists = new HashMap<Example, Set<BindingList>>();
    private boolean cacheBLs = false;
	public void resetGroundingCache() {
		cachedBindingLists = null;
	}
	
	public long getNumberOfGroundingsForRegressionEx(Example eg) {
		initGroundingCalc();
		LearnOneClause learnClause = ((LearnOneClause)task);
	//	Utils.println("Computing groundings for " + eg + " at " + this.getClause());
		BindingList theta = learnClause.unifier.unify(this.getClauseHead(), eg.extractLiteral());
		long cached_num = ((RegressionRDNExample)eg).lookupCachedGroundings(this);
		if (cached_num >=0) {
		//	Utils.waitHere("Already computed the groundings for " + eg + " at " + this.getClause() + " as " + cached_num);
			return cached_num;
		}
		if(cachedBindingLists.containsKey(eg)) {
			cachedBindingLists.remove(eg);
		}
		/*
		if (cachedBindingLists.containsKey(eg)) {
			Set<BindingList> bls = cachedBindingLists.get(eg);
			for (BindingList bl : bls) {
				Utils.println(bl.toString());
			}
			 Utils.waitHere("Already cached bl for " + eg + " at " + this.getClause() + " Num: " + bls.size());
			
			return bls.size();
		}*/
		// Utils.println(theta.toString());
		long num = 0;
		if (getParentNode() != getRootNode() &&
			getParentNode() != null && getParentNode().cachedBindingLists.containsKey(eg)) {
			for (BindingList bl : getParentNode().cachedBindingLists.get(eg)) {
				BindingList bl2 = new BindingList(theta.collectBindingsInList());
				bl2.addBindings(bl);
				// Utils.println("Partial:" + bl2);
				num += getNumberOfGroundingsForRegressionEx(eg, bl2, true);
			}
		} else {
			num = getNumberOfGroundingsForRegressionEx(eg, theta, false);
		}
		if (num < 10) {
			// Easy to recompute the bindings.
			cachedBindingLists.remove(eg);
		}
		if (num == 0) {
			Utils.waitHere("Number of groundings = 0 for " + eg + " with " + getClause() + " BL: " + theta + " Lit: " + literalAdded);
		}
		
		if (cachedBindingLists.containsKey(eg)) {
			Set<BindingList> cachedbl = cachedBindingLists.get(eg);
			if (cachedbl.size() != num) {
				for (BindingList bindingList : cachedbl) {
					Utils.println(bindingList.toString());
				}
				Utils.waitHere("Incorrect groundings : " + num + " for the bl: " + cachedbl );
				
			}
		}
		((RegressionExample)eg).cacheNumGroundings(this, num);
		return num;
	}
	private NumberGroundingsCalculator groundingsCalc = null;
	private void initGroundingCalc() {
		if (groundingsCalc == null) {
			groundingsCalc = new NumberGroundingsCalculator(((LearnOneClause)this.task).context);
		}
	}
	
	public long getNumberOfGroundingsForRegressionEx(Example eg, BindingList theta, boolean isPartial) {
		//LearnOneClause learnClause = ((LearnOneClause)task);
		long num = 1;
		// Check if we can just re-use the groundings from before
		Literal localLit = this.literalAdded.applyTheta(theta);
		if (!isPartial) {
			if (getParentNode() != null && getParentNode() != getRootNode()) {
				num = ((RegressionExample)eg).lookupCachedGroundings(getParentNode());
			}
			// No point in re-using if we haven't cached them
			if (num >= 0) {
				if (groundingsCalc.canLookupLiteral(localLit)) {
					if (groundingsCalc.isaFact(localLit)) {
						((RegressionExample)eg).cacheNumGroundings(this, num);
						return num;	
					}
					Utils.waitHere("num gndings shouldn't be 0 for " + eg + " Lit:" + localLit + " BL: " + theta + " Clause: " + this.getClause());
					//((RegressionExample)eg).cacheNumGroundings(this, 0);
					return 0;
				}
			}
		}
		
		List<Literal> new_body = theta.applyTheta(this.getClauseBody());
		//Clause clause = learnClause.getStringHandler().getClause(new_body, true);
		/*
		List<Literal> newNeg=theta.applyTheta(this.getClauseBody());
		List<Literal> newPos=theta.applyTheta(this.getClause().posLiterals);
		Clause clause = learnClause.getStringHandler().getClause(newPos, newNeg);
		
		Set<BindingList> blSet = null;
		if (cacheBLs) { blSet = new HashSet<BindingList>();}
		// Add this example 
		learnClause.getContext().getClausebase().assertFact(eg);
		long pos_num = learnClause.numberOfGroundings(clause, blSet); 
		learnClause.getContext().getClausebase().retractAllClausesWithUnifyingBody(eg);
		long neg_num = learnClause.numberOfGroundings(clause, blSet);
		num = pos_num - neg_num;
		*/
		Set<BindingList> blSet = null;
		if (cacheBLs) { blSet = new HashSet<BindingList>();}
		//num = learnClause.numberOfGroundings(clause, blSet);
		num = groundingsCalc.countGroundingsForConjunction(new_body, new ArrayList<Literal>(), blSet);
		if (num <= 0) {
			// Utils.waitHere("Number of groundings: " + num + " for " + eg + " in " + this.getClause());
		}
		if (cacheBLs) {
			for (BindingList new_bl : blSet) {
				new_bl.addBindings(theta);
			}
		
			if (!cachedBindingLists.containsKey(eg)) {
				if (!blSet.isEmpty()) {
					cachedBindingLists.put(eg, blSet);
				}
			} else {
				if (!isPartial) {
					Set<BindingList> cachedbl = cachedBindingLists.get(eg);
						for (BindingList bindingList : cachedbl) {
							Utils.println(bindingList.toString());
						}
					Utils.waitHere("Already has cached bindings for " + eg + " at " + this.getClause()+ "but no cached groundings: " + ((RegressionExample)eg).lookupCachedGroundings(this));
				}
				cachedBindingLists.get(eg).addAll(blSet);
			}
		}
	
		return num;
	}
	
	/**
	 * @return the posCoverage
	 */
	public double getPosCoverage() {
		return posCoverage;
	}
	/**
	 * @param posCoverage the posCoverage to set
	 */
	public void setPosCoverage(double posCoverage) {
		this.posCoverage = posCoverage;
	}


	// TODO(tvk) find what common with regression node info 
//
//	class RegressionNodeInfoHolderForMLN {
//
//		protected BranchStats trueBranchStats=null;
//		protected BranchStats falseBranchStats=null;
//
//		public RegressionNodeInfoHolderForMLN(LearnOneClause theILPtask, SingleClauseNode caller) throws SearchInterrupted {
//			reset(theILPtask, caller);
//		}
//
//		protected void reset(LearnOneClause theILPtask, SingleClauseNode caller) throws SearchInterrupted {
//			trueBranchStats = new BranchStats();
//			
//			falseBranchStats = new BranchStats();
//			
//
//			if (!theILPtask.regressionTask) { Utils.error("Should call this when NOT doing regression."); }
//			int size = 0;
//			for (Example posEx : theILPtask.getPosExamples()) {
//				if (!caller.posExampleAlreadyExcluded(posEx)) {
//					size++;
//				}
//			}
//			int fraction = (size / (theILPtask.maxExamplesToSampleForScoring*2))+1;
//			double prob = 1.0/(double)fraction;
//			if (!theILPtask.sampleForScoring) {fraction =1; prob=1;}
//			// Utils.println("True fraction=" + fraction + " prob=" + prob);
//			if (caller.getPosCoverage() < 0.0) { caller.computeCoverage(); }
//			for (Example posEx : theILPtask.getPosExamples()) {
//				//double weight = posEx.getWeightOnExample();
//				
//				// Weight handled inside addNumOutput
//				double output = ((RegressionExample) posEx).getOutputValue();
//				if (!caller.posExampleAlreadyExcluded(posEx)) {
//					if (Utils.random() < prob) {
//						long num = 1;
//						if (caller != caller.getRootNode()) {
//							num  = caller.getNumberOfGroundingsForRegressionEx(posEx);
//						}
//						if (num == 0) {
//							Utils.waitHere("Number of groundings = 0 for " + posEx + " with " + caller.getClause());
//							num = 1;
//						}
//						//Utils.println("adding "  + num + ":" + output + ":" + fraction);
//						trueBranchStats.addNumOutput(num, output, fraction*posEx.getWeightOnExample(),((RegressionRDNExample) posEx).getProbOfExample().getProbOfBeingTrue());
//					}
//				}
//				/* else {
//                	if (theILPtask.isaTreeStructuredTask()) {
//                		if (caller.getParentNode() == null ||
//                			!caller.getParentNode().posExampleAlreadyExcluded(posEx)) {
//                			long num = 1;
//                			if (caller.getParentNode() != null) {
//                				num = ((RegressionExample)posEx).lookupCachedGroundings(caller.getParentNode());
//                				if (num == -1) {
//                					Utils.error("The parent node for " + caller.getClause() + " has no cache for " + posEx);
//                				}
//                			}
//                			falseBranchStats.addNumOutput(num, output);
//                		}
//                	}
//                }*/
//			}
//				//if (theILPtask.isaTreeStructuredTask()) {
//			if(((LearnOneClause)caller.task).currentStartingNode == caller) {
//				Utils.waitHere("Starting node is same as current node for " + caller.getClause());
//			}
//			
//		// TODO(test)
//			 falseBranchStats = new BranchStats().add(caller.getTotalFalseBranchStats());
//		
//			if (!theILPtask.isaTreeStructuredTask()) {
//				// Automatically has weight of zero.
//				falseBranchStats.setZeroLambda();
//			}
//			if (falseBranchStats.getNumExamples() == 0) {
//				//Utils.println("No examples on false branch:"+caller.toString());
//			}
//			
//		}
//	}
//

}
