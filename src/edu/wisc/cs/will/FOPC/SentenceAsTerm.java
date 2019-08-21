/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import java.util.Collection;
import java.util.Map;

import edu.wisc.cs.will.FOPC.visitors.TermVisitor;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author shavlik
 *
 */
@SuppressWarnings("serial")
public class SentenceAsTerm extends Term {
	public  Sentence sentence;
	private String   wrapperPredicate = null;  // Record a note on who 'created' this SentenceAsTerm, since this code assumes they are only internally created.

	/** FOPC sentences can be terms in some Prolog constructs, e.g. once( (p(x), q(x), r(x)) ).
     *
     * @param stringHandler
     * @param s
     * @param wrapperPredicate 
     */  
	protected SentenceAsTerm(HandleFOPCstrings stringHandler, Sentence s, String wrapperPredicate) {
		sentence              = s;
		this.wrapperPredicate = wrapperPredicate;
		this.stringHandler    = stringHandler;
		if (s == null) { Utils.error("Cannot have sentence=null."); }  // The code below checks for sentence=null in case this is requirement is later dropped.
		//if (wrapperPredicate == null) { Utils.warning("Should not have wrapperPredicate=" + wrapperPredicate); }
	}

	public boolean freeVariablesAfterSubstitution(BindingList theta) {
		if (sentence == null || theta == null) { return false; }
		return (sentence == null ?  false : sentence.containsFreeVariablesAfterSubstitution(theta));
	}

    public SentenceAsTerm applyTheta(BindingList bindings) {
        return (SentenceAsTerm) super.applyTheta(bindings);
    }
	public SentenceAsTerm applyTheta(Map<Variable,Term> bindings) {
		Sentence newSentence = (sentence == null ? null : sentence.applyTheta(bindings));
		return new SentenceAsTerm(stringHandler, newSentence, wrapperPredicate);
	}
	
	public Collection<Variable> collectFreeVariables(Collection<Variable> boundVariables) {
		return (sentence == null? null : sentence.collectFreeVariables(boundVariables));
	}
	
	public SentenceAsTerm copy(boolean recursiveCopy) {
		if (recursiveCopy) {
			Sentence newSentence = (sentence == null ? null : sentence.copy(recursiveCopy));
			return new SentenceAsTerm(stringHandler, newSentence, wrapperPredicate);
		}
		return new SentenceAsTerm(stringHandler, sentence, wrapperPredicate);
	}

    public SentenceAsTerm copy2(boolean recursiveCopy, BindingList bindingList) {
		if (recursiveCopy) {
			Sentence newSentence = (sentence == null ? null : sentence.copy2(recursiveCopy, bindingList));
			return new SentenceAsTerm(stringHandler, newSentence, wrapperPredicate);
		}
		return new SentenceAsTerm(stringHandler, sentence, wrapperPredicate);
	}

    @Override
    public Sentence asSentence() {
        return sentence;
    }

    @Override
    public Clause asClause() {
        return sentence.convertToClause();
    }


    @Override
    public BindingList isEquivalentUptoVariableRenaming(Term that, BindingList bindings) {
        if (that instanceof SentenceAsTerm == false) return null;

        SentenceAsTerm sentenceAsTerm = (SentenceAsTerm) that;

        return this.sentence.isEquivalentUptoVariableRenaming(sentenceAsTerm.sentence, bindings);


    }


	
	@Override
	public int hashCode() { // Need to have equal objects produce the same hash code.
		final int prime = 31;
		int result = 1;
		result = prime * result + ((sentence == null) ? 0 : sentence.hashCode());
		return result;
	}	
	public boolean equals(Object other) {
		if (!(other instanceof SentenceAsTerm)) { return false; }
		if (sentence == null)                   { return other == null; }
		return sentence.equals(((SentenceAsTerm) other).sentence);
	}
	
	public boolean containsVariables() {
		return (sentence == null? false : sentence.containsVariables());
	}
	
	public BindingList variants(Term term, BindingList bindings) {
		if (!(term instanceof SentenceAsTerm)) { return null; }
		if (sentence == null)                  { if (term == null) { return bindings; } return null; }
		return sentence.variants(((SentenceAsTerm) term).sentence, bindings);
	}

	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		if (sentence == null) { return null; }
		if (sentence instanceof Clause && ((Clause) sentence).posLiterals == null) {
			String result = "";
			boolean firstTime = true;
			for (Literal nLit : ((Clause) sentence).negLiterals) {
				if (firstTime) { firstTime = false; } else { result += ", "; }
				result += nLit.toString(precedenceOfCaller, bindingList);
			}
			return result;
		}
		//Utils.error("Doesn't meet the expectation of being inside a negation-by-failure (or the like):\n " + sentence);
		return sentence.toPrettyString(newLineStarter, precedenceOfCaller, bindingList);  // Simply print the Sentence, though this might not properly get read back in.
	}

	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return toPrettyString("", precedenceOfCaller, bindingList);
	}

    @Override
   public <Return,Data> Return accept(TermVisitor<Return,Data> visitor, Data data) {
        return visitor.visitSentenceAsTerm(this, data);
    }

	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		if (sentence == null) { return 0; }
		return sentence.countVarOccurrencesInFOPC(v);
	}
}
