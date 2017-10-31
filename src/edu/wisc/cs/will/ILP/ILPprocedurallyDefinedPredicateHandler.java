/**
 * 
 */
package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.ILP.LearnOneClause;
import java.util.List;

import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.ProcedurallyDefinedPredicateHandler;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author shavlik
 *
 */
public class ILPprocedurallyDefinedPredicateHandler extends	ProcedurallyDefinedPredicateHandler {
    private LearnOneClause task;
	/**
	 * 
     *
     * @param task
     */
	public ILPprocedurallyDefinedPredicateHandler(LearnOneClause task) {

		this.task = task;

	}

    @Override
    public boolean canHandle(PredicateName predicateName, int arity) {
        if ( predicateName == task.procDefinedEnoughDiffMatches )                return true;
        if ( predicateName == task.procDefinedForConstants )                     return true;
        if ( predicateName == task.procDefinedNeedForNewVariables && arity >= 2) return true;
        return false;
    }



	public BindingList handle(HornClauseContext context,Literal literal, Unifier unifier, BindingList bindingList) {
		PredicateName pred = literal.predicateName;
		List<Term>    args = literal.getArguments();
		int           size = args.size();
		
		// If there is a need to make sure no variables are in the arguments, one can use: confirmAllVarsAreBound() below.

		// This built-in predicate is used to make sure that some POS seeds can match a new clause with DIFFERENT bindings for the newly added literal.
		// This prevents creating clauses like "p(x) :- q(x,y), q(x,z)" unless the two q's can be differently instantiated for some POS seeds.
		if (pred == task.procDefinedEnoughDiffMatches) {
			Term firstLiteral = args.get(0); // This literal (which has been "reified" to a term), must be different from ALL of the rest.
			if (size > 1) for (Term otherLiteral : args.subList(1, size)) {
				if (firstLiteral.equals(otherLiteral)) { return null; }  // Found a duplicate.  Note that 'equivalent' is stricter than 'variant' - though they are the same when no variables.  Shouldn't have variables here, but if so, seems ok to say different vars are acceptable ...
			}
			return bindingList;  // Acceptable since different than all other reified literals.
		}	
		
		// Need to collect the constants to which variables are bound.
		if (pred == task.procDefinedForConstants) {
			task.collectConstantBindings(args); // "Call back" to the task with the bindings so they can be used to fill arguments.
			return null; // We're collecting ALL bindings for the arguments, so we need to ALSO fail here.
		}
		
		// See if the binding for the first argument does NOT appear elsewhere in the arguments.  These shows that it is possible to bind the first argument in a way different than the others. 
		if (pred == task.procDefinedNeedForNewVariables) {
			if (size < 2) { Utils.error("Must have more than one arg in " + pred); }
			List<Term> sublist = args.subList(1, size);
			
			// NOTE: be careful if making a new string each time, which is a performance hit, but we might want to get the literal in there in case there is a problem.
			if (!confirmAllVarsAreBound("procDefinedNeedForNewVariables: ", sublist, false)) {
				return null; // If some other variable is unbound, then could use that and no need for the new variable, at least on this proof path.
			}			
			// See if the new variable was not bound, which can happen if negation-by-failure involved (and maybe other times?  TODO think this through better).
			if (args.get(0) instanceof Variable) { return bindingList; }
			return (argUsedElsewhere(args.get(0), args.subList(1, size)) ? null : bindingList);
		}
		
		Utils.error("Unknown procedurally defined predicate for ILP: " + literal); // This literal will be negated, so "turn off" the printing of a negation symbol.
		return null;
	}
	
	// See if the first argument is also appears elsewhere in this list of arguments.
	private boolean argUsedElsewhere(Term firstTerm, List<Term> otherArgs) {
		if (otherArgs != null) for (Term other : otherArgs) { if (firstTerm == other) { return true; }}
		return false;
	}
	
}
