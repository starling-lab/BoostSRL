/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * @author shavlik
 *
 */
@SuppressWarnings("serial")
public abstract class Constant extends Term {
	
	private Set<Literal> generatorsOfThisConstantsTypes; // Helps track down errors in type inference.

	/**
	 * 
	 */
	protected Constant() { } // Compiler complains without this (for subtypes).
	protected Constant(HandleFOPCstrings stringHandler) { // DON'T CALL THESE DIRECTLY.  GO VIA HandleFOPCstrings.
		this.stringHandler = stringHandler;
	}

	public Constant applyTheta(Map<Variable,Term> theta) {
		return this;
	}

    public Constant applyTheta(BindingList bindings) {
        return (Constant) super.applyTheta(bindings);
    }

	public Constant copy(boolean recursiveCopy) { // No need to dive into constants (even to change their type spec's?).
		return this;
	}

    @Override
    public Term copy2(boolean recursiveCopy, BindingList bindingList) {
        return this;
    }
	
	public Collection<Variable> collectFreeVariables(Collection<Variable> boundVariables) {
		return null;
	}

    @Override
    public Sentence asSentence() {
        return null;
    }
	
	@Override
	public int hashCode() { // Need to have equal objects produce the same hash code.
		return super.hashCode();
	}
	// Are these two constants equal?  Must be the same object. (Should this be equal within epsilon for numbers?  The HandleFOPCstrings class deals with this.)
	public boolean equals(Object other) {
		return (this == other);
	}
	
	public boolean containsVariables() {
		return false;
	}
	
	// Variants and Equivalent mean the same for constants.
	public BindingList variants(Term other, BindingList bindings) {
		if (this == other) { return bindings; }
		return null;
	}

	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return 0;
	}
	
	public abstract String getName();
	
//	public void addGeneratorOfThisConstantsType(Literal generator) {
//		if (generatorsOfThisConstantsTypes == null) { generatorsOfThisConstantsTypes = new HashSet<Literal>(4); }
//		generatorsOfThisConstantsTypes.add(generator);
//	}
//	public Set<Literal> getGeneratorOfThisConstantsType() {
//		return generatorsOfThisConstantsTypes;
//	}
}
