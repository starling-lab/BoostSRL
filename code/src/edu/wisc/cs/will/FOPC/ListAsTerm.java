/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.FOPC.visitors.TermVisitor;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.Utils.Utils;

/**
 * @author shavlik
 *
 */
@SuppressWarnings("serial")
public class ListAsTerm extends Term {
	protected List<Term> objects;
	private boolean processItemsInList; // If false, leave the items in 'objects' untouched.
	
	/**
	 * This is a way to wrap a list of anything as an argument to an FOPC function.
	 */
	protected ListAsTerm(HandleFOPCstrings stringHandler, List<Term> objects) {
		this(stringHandler, objects, true);
	}
	protected ListAsTerm(HandleFOPCstrings stringHandler, List<Term> objects, boolean processItemsInList) {
		this.stringHandler       = stringHandler;
		this.objects            = objects;
		this.processItemsInList = processItemsInList;
		if (objects == null) { this.processItemsInList = false; }
	}
	
	public Term applyTheta(Map<Variable,Term> bindings) {
		if (processItemsInList) {
			List<Term> newObjects = new ArrayList<Term>(Utils.getSizeSafely(objects));
			for (Term t : objects) { newObjects.add(t.applyTheta(bindings)); }
			return stringHandler.getListAsTerm(newObjects);
		}
		return this;
	}

	public boolean freeVariablesAfterSubstitution(BindingList theta) {
		if (objects == null || theta == null) { return false; }
		if (processItemsInList) {
			for (Term t : objects) if (t.freeVariablesAfterSubstitution(theta)) { return true; }
		}
		return false;
	}

	public Collection<Variable> collectFreeVariables(Collection<Variable> boundVariables) {
		if (processItemsInList) {
			List<Variable> result = new ArrayList<Variable>(1);
			for (Term t : objects) {
				Collection<Variable> tempVarList = t.collectFreeVariables(boundVariables);
				
				if (tempVarList != null) { for (Variable var : tempVarList) if (!result.contains(var)) { result.add(var); }}
			}
			return result;
		}
		return null;
	}

	public Term copy(boolean recursiveCopy) {
		if (processItemsInList && recursiveCopy) {
			List<Term> newObjects = new ArrayList<Term>(objects.size());
			for (Term t : objects) { newObjects.add(t.copy(recursiveCopy)); }
			return stringHandler.getListAsTerm(newObjects);
		}
		return stringHandler.getListAsTerm(objects);
	}

    public Term copy2(boolean recursiveCopy, BindingList bindingList) {
		if (processItemsInList && recursiveCopy) {
			List<Term> newObjects = new ArrayList<Term>(objects.size());
			for (Term t : objects) { newObjects.add(t.copy2(recursiveCopy, bindingList)); }
			return stringHandler.getListAsTerm(newObjects);
		}
		return stringHandler.getListAsTerm(objects);
	}

    @Override
    public Sentence asSentence() {
        return null;
    }
	
	@Override
	public int hashCode() { // Need to have equal objects produce the same hash code.
		final int prime = 31;
		int result = 1;
		result = prime * result + ((objects == null) ? 0 : objects.hashCode());
		return result;
	}	
	public boolean equals(Object other) {
		if (this == other) { return true; }
		if (!(other instanceof ListAsTerm)) { return false; }
		int size = objects.size();
		ListAsTerm otherAsListAsTerm = (ListAsTerm) other;
		if (size != otherAsListAsTerm.objects.size()) { return false; }
		for (int i = 0; i < size; i++) {
			if (!(objects.get(i).equals(otherAsListAsTerm.objects.get(i)))) { return false; }
		}
		return true;
	}

	public boolean containsVariables() {
		if (processItemsInList) {
			for (Term t : objects) if (t.containsVariables()) { return true; }
		}
		return false;
	}

	public BindingList variants(Term term, BindingList bindings) {
		if (this == term) { return bindings; }
		if (!(term instanceof ListAsTerm)) { return null; }
		int size = objects.size();
		ListAsTerm termAsListAsTerm = (ListAsTerm) term;
		if (size != termAsListAsTerm.objects.size()) { return null; }
		for (int i = 0; i < size; i++) {
			bindings = objects.get(i).variants(termAsListAsTerm.objects.get(i), bindings);
			if (bindings == null) { return null; }
		}
		return bindings;
	}

	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return toString(precedenceOfCaller, bindingList);
	}

    @Override
    public BindingList isEquivalentUptoVariableRenaming(Term that, BindingList bindings) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    

	public String toString(int precedenceOfCaller, BindingList bindingList) {
        if ( objects == null ) {
            return "listAsTerm([])";
        }
		return "listAsTerm(" + objects + ")";
	}

   @Override
   public <Return,Data> Return accept(TermVisitor<Return,Data> visitor, Data data) {
        return visitor.visitListAsTerm(this, data);
   }
   
   @Override
   public int countVarOccurrencesInFOPC(Variable v) {
		int total = 0;
		if (objects != null) { for (Term arg : objects) { total += arg.countVarOccurrencesInFOPC(v); } }
		return total;
   }

    public List<Term> getObjects() {
        return objects;
    }

   
}
