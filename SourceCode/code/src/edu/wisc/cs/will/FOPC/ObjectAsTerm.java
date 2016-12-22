/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import java.util.Collection;
import java.util.Map;

import edu.wisc.cs.will.Utils.Utils;

/**
 * @author shavlik
 *
 */
@SuppressWarnings("serial")
public class ObjectAsTerm extends Term {
	public Object item;
	
	/**
	 * Wrap an arbitrary item in a Term.  Don't operate on it.
	 */
	protected ObjectAsTerm(HandleFOPCstrings stringHandler, Object item, boolean warnIfWrappingTerm) {
		this.stringHandler = stringHandler;
		if (warnIfWrappingTerm && item instanceof Term) { Utils.error("The ObjectAsTerm class is unneccesary when asked to wrap terms: " + item); }
		this.item = item;
	}
	public Term applyTheta(Map<Variable,Term> bindings) {
		return this; // BUGGY if item is a variable that should have theta applied to it or contains such a variable (but this shouldn't be used in this case).
	}
	public Collection<Variable> collectFreeVariables(Collection<Variable> boundVariables) {
		return null;
	}
	public Term copy(boolean recursiveCopy) {
		return this;
	}

    @Override
    public Term copy2(boolean recursiveCopy, BindingList bindingList) {
        return this;
    }


	
    @Override
    public Sentence asSentence() {
        return null;
    }

    @Override
    public BindingList isEquivalentUptoVariableRenaming(Term that, BindingList bindings) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    
	@Override
	public int hashCode() { // Need to have equal objects produce the same hash code.
		final int prime = 31;
		int result = 1;
		result = prime * result + ((item == null) ? 0 : item.hashCode());
		return result;
	}	
	public boolean equals(Object other) {
		if (this == other) { return true; }
		if (!(other instanceof ObjectAsTerm)) { return false; }
		return this.item == ((ObjectAsTerm) other).item;
	}
	public boolean containsVariables() {
		return false;
	}
	public BindingList variants(Term term, BindingList bindings) {
		if (equals(term)) { return bindings; }
		return null;
	}
	
	public boolean freeVariablesAfterSubstitution(BindingList theta) {
		return false;
	}

	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return toString(precedenceOfCaller, bindingList);
	}
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return "objectAsTerm(" + item + ")";
	}
	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return (item == v ? 1 : 2); // This is probably inadequate.  Maybe always return 2 if a non-match to be safe?
	}

}
