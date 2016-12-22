/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import java.util.List;
import java.util.Set;

import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import java.util.HashSet;

/** This handler manages built-in's like equals, different, <, >, <=, >=, etc.
 *
 * @author twalker
 */
public abstract class ProcedurallyDefinedPredicateHandler {
    protected Set<PredicateNameAndArity> hashOfSupportedPredicates;

    public ProcedurallyDefinedPredicateHandler() {
        
    }

    public boolean canHandle(PredicateName predicateName, int arity) {
        return canHandle(new PredicateNameAndArity(predicateName, arity));
    }
    
    public boolean canHandle(PredicateNameAndArity predicateNameAndArity) {
        return hashOfSupportedPredicates != null && hashOfSupportedPredicates.contains(predicateNameAndArity);
    }
    
    public void addHandledPrediate(PredicateNameAndArity predicateNameAndArity) {
        if ( hashOfSupportedPredicates == null ) hashOfSupportedPredicates = new HashSet<PredicateNameAndArity>();
        hashOfSupportedPredicates.add(predicateNameAndArity);
    }

    /** Handle evaluation of the literal.
     *
     * canHandle should be called previous to this to determine if this
     * ProcedurallyDefinedPredicateHandler can handle the predicate
     * defined by this literal.
     * 
     * @param context 
     * @param literal Literal to handle.
     * @param unifier Unifier to use.
     * @param bindingList Binding list, initially empty, that will contain the bindings generated during handling.
     * @return The binding list, or null if evaluation of the literal failed.
     * @throws SearchInterrupted Thrown if an error occurs which interpts the evaluation of the literal.
     */
    public abstract BindingList handle(HornClauseContext context, Literal literal, Unifier unifier, BindingList bindingList) throws SearchInterrupted;

    protected boolean confirmAllVarsAreBound(String message, List<Term> args, boolean throwErrorIfVarFound) {
		if (args != null) for (Term arg : args) if (arg instanceof Variable) {
			if (throwErrorIfVarFound) { Utils.error(message + "Cannot have an unbound variable in the arguments of this procedurally defined literal:\n " + args); }
		    return false;
		}
		return true;
	}

}
