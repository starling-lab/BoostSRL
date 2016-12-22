/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import java.util.ArrayList;
import java.util.List;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import edu.wisc.cs.will.Utils.Utils;
import java.util.Collection;
import java.util.Collections;

/**
 * @author shavlik
 * 
 * Binding lists return the results of unification.
 *
 */
public class BindingList extends AllOfFOPC {
	public HashMap<Variable,Term> theta;
	/**
	 * 
	 */
	public BindingList() {
		theta = createMap(0);
	}
	public BindingList(HashMap<Variable,Term> theta) {
		this.theta = theta;
	}
	
	// This is rarely used, but keep it for debugging etc (it is currently only used when in the read-eval-print loop of the resolution theorem prover.
	public BindingList(List<Binding> bindings) {
		theta = createMap(0);

		if (bindings != null) {
            for (Binding bind : bindings) {
                theta.put(bind.var, bind.term);
            }
        }
	}
	
	public void addBindings(List<Binding> bindings) {
		if (bindings != null) for (Binding bind : bindings) { 
			Term existingBinding = lookup(bind.var);
			if (existingBinding == null) { theta.put(bind.var, bind.term); continue; }
			else if (existingBinding != bind.term) {
				if (bind.term instanceof Variable && existingBinding == lookup((Variable) bind.term)) { continue; } // Both bound to same thing, which is fine.
				Utils.error("Asking to bind '" + bind.var + "' to '" + bind.term + "', but it is already bound to '" + existingBinding + "'.");
			}
		}
	}
	
	public void addBindings(BindingList bl) {
		addBindings(bl.collectBindingsInList());
	}

	@SuppressWarnings("unchecked")
	public BindingList copy() {
		if (theta.isEmpty()) { return new BindingList(); }

        HashMap newMap = createMap(theta.size());
        newMap.putAll(theta);

		return new BindingList(newMap);
	}

    /** Creates a new theta map.
     *
     * I offloading this to a small helper so that I could easily change the type of
     * map that was created without changing it in 5 different places.
     *
     * @return A new theta map.
     */
    private HashMap<Variable,Term> createMap(int size) {

        int realSize = Math.max(16, (int)Math.ceil(size * 0.75f)+1);

        return new HashMap<Variable,Term>(realSize);
    }

    public Map<Variable, Term> getTheta() {
        return theta == null ? Collections.EMPTY_MAP : theta;
    }

	// We can't do any in-place replacements at the top-level here since a given list can be combined with several other lists.
	public List<Literal> applyTheta(List<Literal> literals1, List<Literal> literals2) {
		if (Sentence.debugLevel > 2) { Utils.println("Apply theta = " + theta + "\n to literals " + literals1 + " and " + literals2); }
		if (theta == null || theta.size() == 0) { // No need to change any of the literals if no variable bindings.
			if (literals1 == null) { return literals2; }
			if (literals2 == null) { return literals1; }
			
			List<Literal> literals1Copy = new ArrayList<Literal>(literals1);
			literals1Copy.addAll(literals2);
			return literals1Copy;
		}
		if (literals1 == null) { return applyTheta(literals2); }
		if (literals2 == null) { return applyTheta(literals1); }

		List<Literal> literals1copy = applyTheta(literals1); // applyTheta will do a top-level COPY (even if not needed).
		literals1copy.addAll(applyTheta(literals2));
		return literals1copy;
	}

	public List<Literal> applyTheta(List<Literal> literals) { // Note that the above code assumes this will make a top-level copy (but the above wont call this if theta is empty or the list is).
		if (literals == null) { return null; }
		if (theta    == null || theta.size() == 0) { return literals; } // No need to apply the empty list of bindings.
		List<Literal> result = new ArrayList<Literal>(literals.size());
		for (Literal literal : literals) {	
			result.add(literal.applyTheta(theta));  // Since Java doesn't do dynamic casting, need to put applyTheta's in the FOPC classes.
		}
		return result;
	}

	public Clause reverseSubst(Clause c) {
		List<Literal> pLits = new ArrayList<Literal>(c.getPosLiteralCount());
		List<Literal> nLits = new ArrayList<Literal>(c.getNegLiteralCount());
		
		if (c.posLiterals != null) for (Literal pLit : c.posLiterals) { pLits.add(reverseSubst(pLit)); }
		if (c.negLiterals != null) for (Literal nLit : c.negLiterals) { nLits.add(reverseSubst(nLit)); }
		
		return (Clause) c.stringHandler.getClause(pLits, nLits).setWeightOnSentence(c.getWeightOnSentence());
	}
	
	public Literal reverseSubst(Literal lit) {
		if (lit.numberArgs() < 1) { return lit; }
		Literal newLit = lit.stringHandler.getLiteral(lit.predicateName);
		List<Term> args = new ArrayList<Term>(newLit.numberArgs());
		for (Term arg : lit.getArguments()) {
			//Term newTerm = reverseSubst(arg);
			args.add(reverseSubst(arg));
		}
	//	Utils.println("old = " + lit + " new args = " + args);
		newLit.setArguments(args);
		return newLit;
	}

	public Term reverseSubst(Term term) {
		Variable revVar = reverseLookup(term);
		if (revVar != null) { return revVar; } // Should this recur, in case there is a chain of bindings?
		if (term instanceof Function) {
			Function f    = (Function) term;
			if (f.numberArgs() < 1) { return f; }
			Function newF = (Function.isaConsCell(term) ? term.stringHandler.getConsCell(f.functionName, null) : term.stringHandler.getFunction(f.functionName));
			List<Term> args = new ArrayList<Term>(f.numberArgs());
			for (Term arg : f.getArguments()) {
				//Term newTerm = reverseSubst(arg);
				args.add(reverseSubst(arg));
			}
			newF.setArguments(args);
			return newF;
		}
		return term;
	}

    /** Returns the current mapping of variable to term, recursively.
     *
     * This does a lookup of the variable recursively.  @see getMapping(Variable)
     * for non-recursive lookups.  Only variables are looked up
     * recursively.  Terms containing variables are not and will require
     * an applyTheta call to resolve completely.
     *
     * @param var
     * @return
     */
	public Term lookup(Variable var) { // Could save this method call.
		Term result = theta.get(var);
		if (result == null) { return null; }
        if (result == var ) { return result; }
		if (result instanceof Variable) { // Do a recursive lookup.
			Term result2 = lookup((Variable) result);
			if (result2 == null) { return result; } { return result2; }
		}
		return result;
	}

    /** Returns the current mapping of variable to term, non-recursively.
     *
     * This does a lookup of the variable non-recursively.  @see lookup(Variable)
     * for recursive lookups.
     *
     * @param var
     * @return
     */
    public Term getMapping(Variable var) {
		Term result = theta.get(var);

		return result;
	}

    /** Returns the mapped term for the variable of name variableName.
     *
     * All variable in the map are compared to variableName.
     *
     * If no matching variables are found, this method returns null.
     * If one is found, the mapping is resolve via getMapping(Variable) and returned.
     * If multiple mappings are found, this method throws a AmbiguousVariableLookup
     * exception.
     *
     * In order to guarantee that only a single match exist, the complete set of
     * mapping must be examined, making this a linear time lookup, instead of a
     * constant time lookup if the actual variable is used.
     *
     * @param variableName Variable name to look for.
     * @return If one match is found, returns the resolved mapping, otherwise null.
     */
    public Term getMapping(String variableName) throws AmbiguousVariableLookup {

        Term result = null;

        if ( theta != null ) {
            Variable foundVariable = null;
            for (Variable variable : theta.keySet()) {
                boolean oldValue = variable.getStringHandler().printVariableCounters;

                try {
                    variable.getStringHandler().printVariableCounters = false;
                    if ( variable.getName().equals(variableName)) {
                        if ( foundVariable == null ) foundVariable = variable;
                        else throw new AmbiguousVariableLookup("Variable name " + variableName + " was ambiguous during BindingList lookup.");
                    }
                }
                finally {
                    variable.getStringHandler().printVariableCounters = oldValue;
                }

            }

            if ( foundVariable != null ) {
                result = getMapping(foundVariable);
            }
        }

        return result;
    }

    public int size() {
        return theta.size();
    }


    public Collection<Variable> getVariables() {
        if (theta == null) {
            return Collections.emptySet();
        }
		return theta.keySet();
    }

	public Variable reverseLookup(Term term) { // Could save this method call.
		boolean hold = term.stringHandler.usingStrictEqualsForFunctions();
		term.stringHandler.setUseStrictEqualsForFunctions(false);
		if (theta == null || !theta.containsValue(term)) {
			term.stringHandler.setUseStrictEqualsForFunctions(hold);
		//	Utils.println("reverseLookup: no match to " + term);
			return null; // Saves time?
		}
		
		for (Variable var : theta.keySet()) {
			Term trm = theta.get(var);
			
			if (term.equals(trm)) { 
				term.stringHandler.setUseStrictEqualsForFunctions(hold);
			//	Utils.println("reverseLookup:  match to " + term + " so return " + var);
				return var; 
			}
		}
		/* Replaced this by the above JWS 9/4/10.
		Set<Entry<Variable,Term>> entrySet = theta.entrySet();
		for(Entry<Variable,Term> entry : entrySet) {
			if (term == entry.getValue()) { return entry.getKey(); }
		}
		*/
		Utils.error("ContainsValue found " + term + " in " + theta + ", but this code could not.");
		term.stringHandler.setUseStrictEqualsForFunctions(hold);
		return null;
	}
	
	// Provide a way to do a lookup without needing to create a HashMap.
	public static Term lookup(Variable var, List<Binding> bindings) {
		if (bindings == null) { return null; }
		for (Binding b : bindings) {
			if (b.var == var) { return b.term; }
		}
		return null;
	}

	public boolean addBindingFailSoftly(Variable var, Term term) {
		if (help_addBinding(var, term, false)) { return true; }
		if (term instanceof Variable) { return help_addBinding((Variable) term, var, false); } // This is probably already checked below, but try again nevertheless.
		return false;
	}
	public boolean addBinding(Variable var, Term term) {
		return help_addBinding(var, term, true);
	}
	private boolean help_addBinding(Variable var, Term term, boolean errorIfProblem) {
		if (theta.containsKey(var)) { 
			Term oldAnswer = theta.get(var);
			if (oldAnswer == term) { return true; } // Already there, which is fine.
			if (oldAnswer instanceof Variable) { addBinding((Variable) oldAnswer, term); return true; }
			else if (term instanceof Variable) { 
			//	Utils.waitHere("help_addBinding: " + var + " -> " + term);  THIS MIGHT BE BUGGY ...
				Variable v = (Variable) term;
				// Have something like ?X->term and asking to do ?X->?Y.  Then do ?Y->term if ?Y is not yet bound.
				if (!theta.containsKey(v)) {  // If this term is a variable and is not already in the binding list, then just return the binding for it.
					theta.put(v, oldAnswer);	
					return true;
				} // Could handle more, but wait on this until a concrete case arises.
			}
			if (errorIfProblem) {
				Utils.error("Cannot addBinding(" + var + "," + term +") because '" + var + "' is already bound to '" + theta.get(var) + "'.");
			}
			return false;
		}
		if (Function.isaConsCell(term)) {
			ConsCell consCell =  ConsCell.ensureIsaConsCell(term.stringHandler, term);
		//	Utils.println("add binding: " + var + " -> " + term);
			if (consCell.memberViaEq(var)) { 
				if (errorIfProblem) { Utils.error("This would be circular: " + var + " -> " + term); }
				return false;
			}
		}
		theta.put(var, term);	
		return true;
	}
    
    public void addBindingWithoutOccursCheck(Variable var, Term term) {
		if ( theta == null ) theta = new HashMap<Variable, Term>();
        theta.put(var, term);
	}
	
	public void removeBinding(Variable var) {
		if (theta.containsKey(var)) { theta.remove(var); }
		else { Utils.error("Cannot find " + var + " in " + theta); }
	}

	// Collect all the bindings in the HashMap.
	public List<Binding> collectBindingsInList() {
		if (Utils.getSizeSafely(theta) < 1) { return null; }  // Might want to instead return the empty list?
		List<Binding> results = new ArrayList<Binding>(theta.size());
		for (Variable var : theta.keySet()) {
			results.add(new Binding(var, theta.get(var)));
		}
		return results;
	}

	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return theta.toString();
	}
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		StringBuilder stringBuilder = new StringBuilder();
        stringBuilder.append("{");
        boolean first = true;
		for (Variable var : theta.keySet()) {
			Term trm = theta.get(var);
			
			if ( first == false ) { stringBuilder.append(", "); } else { first = false; }
            stringBuilder.append(var.toString(bindingList)).append("=").append(trm.toString(bindingList));
		}
        /* Replaced by the above JWS 9/4/10.
        for (Entry<Variable, Term> entry : theta.entrySet()) {
            if ( first == false ) stringBuilder.append(", ");

            stringBuilder.append(entry.getKey().toString(bindingList)).append("=").append(entry.getValue().toString(bindingList));

            first = false;
        }
        */
        stringBuilder.append("}");

        return stringBuilder.toString();
	}

    public String toString() {
        return toString(null);
    }

	@Override
	public BindingList applyTheta(Map<Variable, Term> bindings) {
		Utils.error("Should not call applyTheta on a Binding List.");
		return this;
	}

    /** Applies the Theta bindings to all of the terms of this bindingList.
     *
     * This method is used to apply the bindings in the provided map to the
     * terms in this map.
     * 
     * @param bindings
     */
    public void applyThetaInPlace(Map<Variable, Term> bindings) {

        for (Entry<Variable, Term> entry : theta.entrySet()) {
            Term t2 = entry.getValue().applyTheta(bindings);
            entry.setValue(t2);
        }
    }
	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return (theta.containsKey(v) ? 1 : 0);
	}

    public boolean isEmpty() {
        return theta == null || theta.isEmpty();
    }

    public BindingList getBindings(Collection<Variable> variables) {
        BindingList bl = new BindingList();

        for (Variable variable : variables) {
            bl.addBinding(variable, getMapping(variable));
        }

        return bl;
    }

    public static class AmbiguousVariableLookup extends RuntimeException {

        /**
		 * 
		 */
		private static final long serialVersionUID = 1L;

		public AmbiguousVariableLookup(String message) {
            super(message);
        }

        public AmbiguousVariableLookup() {
        }
        
    }
}
