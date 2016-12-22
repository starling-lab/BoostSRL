/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.FOPC.visitors.TermVisitor;
import java.util.Collection;
import java.util.Map;


/**
 * @author shavlik
 *
 * This is a dummy class that allows a Literal to be put in a place where a Term is needed.  (Used for dealing with Prolog cuts.)
 */
@SuppressWarnings("serial")
public class LiteralAsTerm extends Term {
	public Literal itemBeingWrapped;
	/**
	 * 
	 */
	protected LiteralAsTerm(HandleFOPCstrings stringHandler, Literal itemBeingWrapped) {
		this.stringHandler    = stringHandler;
		this.itemBeingWrapped = itemBeingWrapped;
	}

    @Override
	public boolean freeVariablesAfterSubstitution(BindingList theta) {
		if (itemBeingWrapped == null || theta == null) { return false; }
		return itemBeingWrapped.containsFreeVariablesAfterSubstitution(theta);
	}
	
    @Override
	public Term applyTheta(Map<Variable,Term> bindings) {
		return stringHandler.getLiteralAsTerm(itemBeingWrapped.applyTheta(bindings));
	}

    @Override
	public Collection<Variable> collectFreeVariables(Collection<Variable> boundVariables) {
		return itemBeingWrapped.collectFreeVariables(boundVariables);
	}

    @Override
	public Term copy(boolean recursiveCopy) {
		if (recursiveCopy) { 
			Literal newLit = itemBeingWrapped.copy(recursiveCopy);
			return stringHandler.getLiteralAsTerm(newLit);
		}
		return stringHandler.getLiteralAsTerm(itemBeingWrapped);
	}

    @Override
	public Term copy2(boolean recursiveCopy, BindingList bindingList) {
		if (recursiveCopy) {
			Literal newLit = itemBeingWrapped.copy2(recursiveCopy, bindingList);
			return stringHandler.getLiteralAsTerm(newLit);
		}
		return stringHandler.getLiteralAsTerm(itemBeingWrapped);
	}

    @Override
    public Sentence asSentence() {
        return itemBeingWrapped;
    }
	
	@Override
	public int hashCode() { // Need to have equal objects produce the same hash code.
		final int prime = 31;
		int result = 1;
		result = prime * result + ((itemBeingWrapped == null) ? 0 : itemBeingWrapped.hashCode());
		return result;
	}	
    @Override
	public boolean equals(Object other) {
		if (this == other) { return true; }
		if (!(other instanceof LiteralAsTerm)) { return false; }
		return itemBeingWrapped.equals(((LiteralAsTerm) other).itemBeingWrapped); 
	}

    @Override
    public BindingList isEquivalentUptoVariableRenaming(Term that, BindingList bindings) {
        if (that instanceof LiteralAsTerm) return null;

        LiteralAsTerm literalAsTerm = (LiteralAsTerm) that;

        return this.itemBeingWrapped.isEquivalentUptoVariableRenaming(literalAsTerm.itemBeingWrapped, bindings);

    }



    @Override
	public boolean containsVariables() {
		return itemBeingWrapped.containsVariables();
	}

    @Override
	public BindingList variants(Term term, BindingList bindings) {
		// if (this == term) { return bindings; }// Need to collect the matched variables (so they don't get matched to another variable elsewhere).
		if (!(term instanceof LiteralAsTerm)) { return null; }
		LiteralAsTerm termAsLiteralAsTerm = (LiteralAsTerm) term;
		return itemBeingWrapped.variants(termAsLiteralAsTerm.itemBeingWrapped, bindings);
	}

    @Override
	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return itemBeingWrapped.toPrettyString(newLineStarter, precedenceOfCaller, bindingList);
	}
    @Override
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return itemBeingWrapped.toString(precedenceOfCaller, bindingList);
	}

    @Override
    public <Return,Data> Return accept(TermVisitor<Return,Data> visitor, Data data) {
        return visitor.visitLiteralAsTerm(this, data);
   }

	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		int total = 0;
		if (itemBeingWrapped != null) { for (Term arg : itemBeingWrapped.getArguments()) { total += arg.countVarOccurrencesInFOPC(v); } }
		return total;
	}
}
