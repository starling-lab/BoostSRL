/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import java.util.Collection;
import java.util.Map;
import java.util.List;

import edu.wisc.cs.will.Utils.Utils;

/**
 * @author shavlik
 *
 */
@SuppressWarnings("serial")
public class TermAsSentence extends Sentence {

    public Term term;

    /**
     * This is a dummy class.  It is used, during parsing, to hold a term inside something of type sentence.
     * E.g. it is needed when dealing with:  (-5) < X.
     * The '(-5)' could be arbitrarily complex (e.g., wrapped in more parentheses), and until the '<' is encountered, we don't know it is grammatical.
     */
    protected TermAsSentence(HandleFOPCstrings stringHandler, Term term) {
        this.term = term;
        this.stringHandler = stringHandler;
        if (term == null) {
            Utils.error("Cannot have term=null here.");
        }
    }

    @Override
    public Collection<Variable> collectAllVariables() {
        return collectFreeVariables(null);
    }

    @Override
    public Collection<Variable> collectFreeVariables(Collection<Variable> boundVariables) {
        Utils.error("Should not be called.");
        return null;
    }

    @Override
    public Sentence copy(boolean recursiveCopy) {
        Utils.error("Should not be called.");
        return null;
    }

    @Override
    public Sentence copy2(boolean recursiveCopy, BindingList bindingList) {
        Utils.error("Should not be called.");
        return null;
    }


    @Override
    public boolean containsTermAsSentence() {
        return true;
    }

    @Override
    public boolean containsFreeVariablesAfterSubstitution(BindingList theta) {
        if (term == null || theta == null) {
            return false;
        }
        return term.freeVariablesAfterSubstitution(theta);
    }

    @Override
    public TermAsSentence applyTheta(Map<Variable, Term> bindings) {
        Term newTerm = term.applyTheta(bindings);
        return new TermAsSentence(stringHandler, newTerm);
    }

    @Override
    public TermAsSentence applyTheta(BindingList bindingList) {
        if (bindingList != null) {
            return applyTheta(bindingList.theta);
        }
        else {
            return this;
        }
    }

    @Override
    public int hashCode() { // Need to have equal objects produce the same hash code.
        final int prime = 31;
        int result = 1;
        result = prime * result + ((term == null) ? 0 : term.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object other) {
        if (this == other) {
            return true;
        }
        if (!(other instanceof TermAsSentence)) {
            return false;
        }
        return term.equals(((TermAsSentence) other).term);
    }

    @Override
    public boolean containsVariables() {
        return term.containsVariables();
    }

    @Override
    public BindingList variants(Sentence other, BindingList bindings) {
        // if (this == other) { return bindings; } // Need to collect the matched variables (so they don't get matched to another variable elsewhere).
        if (!(other instanceof TermAsSentence)) {
            return null;
        }
        return term.variants(((TermAsSentence) other).term, bindings);
    }

    @Override
    public BindingList isEquivalentUptoVariableRenaming(Sentence that, BindingList bindings) {
        if (that instanceof TermAsSentence == false) {
            return null;
        }
        TermAsSentence termAsSentence = (TermAsSentence) that;

        return this.term.isEquivalentUptoVariableRenaming(termAsSentence.term, bindings);
    }

    // Clausal-form converter stuff.
    @Override
    protected boolean containsThisFOPCtype(String marker) {
        return false;
    }

    @Override
    protected TermAsSentence convertEquivalenceToImplication() {
        return this;
    }

    @Override
    protected TermAsSentence eliminateImplications() {
        return this;
    }

    @Override
    protected TermAsSentence negate() {
        Utils.error("TermAsSentence's should not be encountered by the clause-converter code.");
        return null;
    }

    @Override
    protected TermAsSentence moveNegationInwards() {
        Utils.error("TermAsSentence's should not be encountered by the clause-converter code.");
        return null;
    }

    @Override
    protected TermAsSentence skolemize(List<Variable> outerUniversalVars) {
        return this; // Cannot go in any further.
    }

    @Override
    protected Sentence distributeDisjunctionOverConjunction() {
        return this; // Cannot go in any further.
    }

    @Override
    protected Sentence distributeConjunctionOverDisjunction() {
        return this;
    }

    @Override
    public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
        return " >>> " + term.toPrettyString(newLineStarter, precedenceOfCaller, bindingList) + " <<< ";
    }

    @Override
    public String toString(int precedenceOfCaller, BindingList bindingList) {
        return " >>> " + term.toString(precedenceOfCaller, bindingList) + " <<< ";
    }

	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		if (term == null) { return 0; }
		return term.countVarOccurrencesInFOPC(v);
	}
}
