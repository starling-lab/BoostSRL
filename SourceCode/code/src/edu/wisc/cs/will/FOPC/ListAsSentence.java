/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import java.util.Collection;
import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.Utils.Utils;

/**
 * @author shavlik
 *
 */
@SuppressWarnings("serial")
public class ListAsSentence extends Sentence {

    protected List<Sentence> objects;

    private boolean processItemsInList; // If false, leave the items in 'objects' untouched.

    /**
     * This is a way to wrap a list of anything.
     * CURRENTLY ALL THE SUPPORTING METHODS RETURN SOMETHING REASONABLE, BUT IF processItemsInList=true THIS NEEDS TO BE REWRITTEN.
     * See ListAsTerm for guidance if new code is needed.
     *
     * @param stringHandler
     * @param objects 
     */
    protected ListAsSentence(HandleFOPCstrings stringHandler, List<Sentence> objects) {
        this(stringHandler, objects, false);
    }

    protected ListAsSentence(HandleFOPCstrings stringHandler, List<Sentence> objects, boolean processItemsInList) {
        this.stringHandler = stringHandler;
        this.objects = objects;
        this.processItemsInList = processItemsInList;
        if (objects == null) {
            this.processItemsInList = false;
        }
    }

    @Override
    public Sentence applyTheta(Map<Variable, Term> bindings) {
        if (processItemsInList) {
            Utils.writeMe();
        }
        return this;
    }

    @Override
    public Sentence applyTheta(BindingList bindingList) {
        if (bindingList != null) {
            return applyTheta(bindingList.theta);
        }
        else {
            return this;
        }
    }

    @Override
    public Collection<Variable> collectAllVariables() {
        if (processItemsInList) {
            Utils.writeMe();
        }
        return null;
    }

    @Override
    public Collection<Variable> collectFreeVariables(Collection<Variable> boundVariables) {
        if (processItemsInList) {
            Utils.writeMe();
        }
        return null;
    }

    @Override
    public boolean containsFreeVariablesAfterSubstitution(BindingList theta) {
        if (processItemsInList) {
            Utils.writeMe();
        }
        return false;
    }

    @Override
    public boolean containsTermAsSentence() {
        if (processItemsInList) {
            Utils.writeMe();
        }
        return false;
    }

    @Override
    protected boolean containsThisFOPCtype(String marker) {
        if (processItemsInList) {
            Utils.writeMe();
        }
        return false;
    }

    @Override
    protected Sentence convertEquivalenceToImplication() {
        if (processItemsInList) {
            Utils.error("Unable to convert equivalence to implication in ListAsSentence");
        }
        return this;
    }

    @Override
    public Sentence copy(boolean recursiveCopy) {
        if (processItemsInList) {
            Utils.writeMe();
        }
        return this;
    }

    @Override
    public Sentence copy2(boolean recursiveCopy, BindingList bindingList) {
        if (processItemsInList) {
            Utils.writeMe();
        }
        return this;
    }


    @Override
    protected Sentence distributeDisjunctionOverConjunction() {
        if (processItemsInList) {
            Utils.writeMe();
        }
        return this;
    }

    @Override
    protected Sentence distributeConjunctionOverDisjunction() {
        if (processItemsInList) {
            Utils.writeMe();
        }
        return this;
    }

    @Override
    protected Sentence eliminateImplications() {
        if (processItemsInList) {
            Utils.error("Unable to eliminate implications of ListAsSentence");
        }
        return this;
    }

    @Override
    public boolean equals(Object other) {
        if (processItemsInList) {
            Utils.writeMe();
        }
        return other == this;
    }

    @Override
    public boolean containsVariables() {
        if (processItemsInList) {
            Utils.writeMe();
        }
        return true;
    }

    @Override
    protected Sentence moveNegationInwards() {
        if (processItemsInList) {
            Utils.error("Unable to move negation inwards on ListAsSentence");
        }
        return this;
    }

    @Override
    protected Sentence negate() {
        if (processItemsInList) {
            Utils.writeMe();
        }
        return this; // Probably should add a NOT().
    }

    @Override
    protected Sentence skolemize(List<Variable> outerUniversalVars) {
        if (processItemsInList) {
            Utils.writeMe();
        }
        return this;
    }

    @Override
    public BindingList variants(Sentence other, BindingList bindings) {
        if (processItemsInList) {
            Utils.writeMe();
        }
        return bindings;
    }

    @Override
    public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
        if (processItemsInList) {
            Utils.writeMe();
        }
        return toString(precedenceOfCaller, bindingList);
    }

    @Override
    public String toString(int precedenceOfCaller, BindingList bindingList) {
        if (processItemsInList) {
            Utils.writeMe();
        }
        return toString();
    }

    public List<Sentence> getObjects() {
        return objects;
    }

    public void setObjects(List<Sentence> objects) {
        this.objects = objects;
    }

    @Override
    public BindingList isEquivalentUptoVariableRenaming(Sentence that, BindingList bindings) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		int total = 0;
		if (objects != null) { for (Sentence s : objects) { total += s.countVarOccurrencesInFOPC(v); } }
		return total;
	}

    
}
