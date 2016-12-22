package edu.wisc.cs.will.FOPC;

import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.Utils.Utils;
import java.io.Serializable;

@SuppressWarnings("serial")
public class Unifier extends AllOfFOPC implements Serializable {
	protected static final int debugLevel = 0;  // Used to control output from this class (0 = no output, 1=some, 2=much, 3=all).

    protected static long unificationCount = 0;

    public final static Unifier UNIFIER = new Unifier();
    
	// Could use statics to perform unification since no "state" involved, but use an instance for safety.  
	// Notice that the binding list is changed (rather than copied).
	// So be careful when passing in binding lists (notice the first method below creates a fresh binding list).
	
	// To save space, do NOT rename expressions via substitution of bound variables, but instead always recursively look up in the binding list.
	// This code is basically the same as in the next method.  But save a function call (and allow different reporting when debugging).
	public BindingList unify(Literal lit1, Literal lit2) {
		if (lit1.predicateName == lit2.predicateName && lit1.numberArgs() == lit2.numberArgs()) {
			if (Unifier.debugLevel > 0) { Utils.println("Consider unifying literals " + lit1 + " and " + lit2 + "."); }
			BindingList result = unify(lit1.getArguments(), lit2.getArguments(), new BindingList());
			if (Unifier.debugLevel > 0) { Utils.println(" Result = " + result); }
			return result;
		}
		else {
			if (Unifier.debugLevel > 0) { Utils.println(" Literals " + lit1 + " and " + lit2 + " do not unify."); }
			return null;
		}
	}
	public BindingList unify(Literal lit1, Literal lit2, BindingList bindingList) {		
		if (lit1.predicateName == lit2.predicateName && lit1.numberArgs() == lit2.numberArgs()) {
			if (Unifier.debugLevel > 0) { Utils.println("Consider unifying literals " + lit1 + " and " + lit2 + " with bindings " + bindingList + "."); }
			BindingList result =  unify(lit1.getArguments(), lit2.getArguments(), bindingList);
			if (Unifier.debugLevel > 0) { Utils.println(" Result = " + result); }
			return result;
		}
		else {
			if (Unifier.debugLevel > 0) { Utils.println(" Literals " + lit1 + " and " + lit2 + " do not unify."); }
			return null;  // We need to be be sure we differentiate a FAILED unification from one with no variable bindings.  NULL means failed and an empty list means success w/o needing any bindings.
		}
	}
	
	public BindingList unify(Term term1, Term term2) {
		return unify(term1, term2, new BindingList());
	}

    public BindingList unify(Sentence s1, Sentence s2, BindingList bl) {
        return SentenceUnifier.unify(s1,s2,bl);
    }

    public BindingList unify(Sentence s1, Sentence s2) {
        return SentenceUnifier.unify(s1, s2, null);
    }


	// Provide 'internal' access, but require use of 'self documenting' name.
	public BindingList unifyAssumingSameNumberOfArgs(List<Term> args1, List<Term> args2, BindingList bindingList) {
		return unify(args1, args2, bindingList);
	}
	private BindingList unify(List<Term> args1, List<Term> args2, BindingList bindingList) {
		// The calling code checks arguments sizes, so no need to do that here.
		// TAW: I normally wouldn't trust an external check...the check should probably be skipped
		// TAW: on the outside call and done internally here.  JWS: I'd agree, except this is a 'private'		
		
		// Since the unifier is being mainly used in a learning-from-examples setting, there will be lots of constants.
		// so do a quick skim to see if ever paired arguments involve different constants.  If so, can fail immediately.
		if (args1 == null) { return bindingList; } // Since #args checked already, can do this simple check.
		int count = args1.size();
		for(int index = 0; index < count; index++) {
			Term term1 = args1.get(index);
			Term term2 = args2.get(index);
			
			if (term1 != term2 && term1 instanceof Constant && term2 instanceof Constant) {
				if (Unifier.debugLevel > 1) { Utils.println("  FAILED because a pair of constants don't match: '" + term1 + "' and '" + term2 + "'."); } 
				return null;
			}
		}
		
		for(int index = 0; index < count; index++) {
			Term term1 = args1.get(index);
			Term term2 = args2.get(index);
			
			bindingList = unify(term1, term2, bindingList);
			if (bindingList == null) { 
				if (Unifier.debugLevel > 1) { Utils.println("  FAILED when unifying the arguments."); }
				return null;
			}
		}
		
		if (Unifier.debugLevel > 2) { Utils.println("  Argument lists " + args1 + " and " + args2 + " unify with theta = " + bindingList); }
		return bindingList;
	}
	
	// The built-in EQUALS(Term1, Term2) needs to access this.
	public BindingList unify(Term term1, Term term2, BindingList bindingList) {	
		if (Unifier.debugLevel > 1) { Utils.println(" Consider unifying terms " + term1 + " and " + term2 + " with bindings " + bindingList + "."); }
		if (term1 instanceof Constant && term2 instanceof Constant) {			
			return term1 == term2 ? bindingList : null;  // Could call 'equivalent' here, but save the function call since this called quite often.
		}
		else if (term1 instanceof Variable) {
			return unifyVariable((Variable) term1, term2, bindingList);			
		}
		else if (term2 instanceof Variable) {
			return unifyVariable((Variable) term2, term1, bindingList);	
		}
		else if (term1 instanceof Function && term2 instanceof Function) {
			Function f1 = ((Function) term1);
			Function f2 = ((Function) term2);
			
			if (f1.functionName == f2.functionName && f1.numberArgs() == f2.numberArgs()) {
				return unify(f1.getArguments(), f2.getArguments(), bindingList);
			}
			else {
				if (Unifier.debugLevel > 1) { Utils.println(" FAILED since predicate name and/or number of arguments don't match."); }
				return null;
			}
		}
		else if (term1 instanceof LiteralAsTerm && term2 instanceof LiteralAsTerm) {
			LiteralAsTerm f1 = ((LiteralAsTerm) term1);
			LiteralAsTerm f2 = ((LiteralAsTerm) term2);
			
			if (f1.itemBeingWrapped.predicateName == f2.itemBeingWrapped.predicateName && f1.itemBeingWrapped.numberArgs() == f2.itemBeingWrapped.numberArgs()) {
				if (Unifier.debugLevel > 0) { Utils.println("Consider unifying LiteralAsTerm " + f1 + " and " + f2 + " with bindings " + bindingList + "."); }
				BindingList result =  unify(f1.itemBeingWrapped.getArguments(), f2.itemBeingWrapped.getArguments(), bindingList);
				if (Unifier.debugLevel > 0) { Utils.println(" Result = " + result); }
				return result;
			}
			else {
				if (Unifier.debugLevel > 1) { Utils.println(" FAILED since predicate name and/or number of arguments don't match."); }
				return null;
			}
		}
        else if (term1 instanceof SentenceAsTerm && term2 instanceof SentenceAsTerm) {
            SentenceAsTerm s1 = ((SentenceAsTerm)term1);
            SentenceAsTerm s2 = ((SentenceAsTerm)term2);

            return unify(s1.sentence, s2.sentence, bindingList);
        }
		else {
			if (Unifier.debugLevel > 1) { Utils.println("  These terms do not match: " + term1 + " and " + term2); }
			return null;
		}
	}
	
	private BindingList unifyVariable(Variable var, Term term, BindingList bindingList) {
		Term lookedupVar  = var;
		Term lookedupTerm = term;
		Term temp_lookedupVar = bindingList.lookup(var);
		
		if (temp_lookedupVar != null) { lookedupVar = temp_lookedupVar; }
		if (term instanceof Variable) {
			Term temp_lookedupTerm = bindingList.lookup((Variable) term);
			
			if (temp_lookedupTerm != null) { lookedupTerm =  temp_lookedupTerm; }
		}
		
		// If anything changed in a lookup, recur (note that either of the two variables might become a more complex term after lookup.
		if ((var != null && !var.equals(lookedupVar)) || (term != null &&!term.equals(lookedupTerm))) { // If anything changed due to a lookup, recur.
			if (Unifier.debugLevel > 2) { Utils.println("  Recur on unify var: " +  var + " -> " + lookedupVar + " and "
															  			         + term + " -> " + lookedupTerm); }
			return unify(lookedupVar, lookedupTerm, bindingList);
		}
		else if (var != null && var.equals(term)) {
			if (Unifier.debugLevel > 2) { Utils.println("  " + var + " and " + term + " unify with theta: " + bindingList); }
			return bindingList;
		}
		// We are NOT implementing the 'occurs check' but if we did it would go here.  JWS added (7/25/10) a partial occurs check (for functions that are lists).
		else {
			boolean success = bindingList.addBindingFailSoftly(var, term);
			if (!success) { return null; }
			if (Unifier.debugLevel > 2) { Utils.println("  " + var + " and " + term + " unify with new binding " + var + ":" + term + " and theta: " + bindingList); }
			return bindingList;
		}
	}

	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return toString(precedenceOfCaller, bindingList);
	}
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return "<this is an instance of the Unifier class>";
	}

    public static long getUnificationCount() {
        return unificationCount;
    }

    public static void increaseUnificationCount() {
        unificationCount++;
    }
    
	@Override
	public Unifier applyTheta(Map<Variable, Term> bindings) {
		Utils.println("Why call this on a unifier?");
		return null;
	}
	
	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return 0;
	}


}
