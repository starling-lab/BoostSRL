/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import java.io.IOException;
import java.io.Serializable;
import java.util.Collection;
import java.util.Collections;
import java.util.Map;

import edu.wisc.cs.will.FOPC.visitors.TermVisitor;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author shavlik
 *
 */
@SuppressWarnings("serial")
public abstract class Term extends AllOfFOPC implements Serializable, SLDQuery, Comparable<Term>, SentenceOrTerm {
	protected TypeSpec          typeSpec;
	transient protected HandleFOPCstrings stringHandler; // Add another field to everything so it can access this, and hence access things like lowercaseMeansVariable.
	
	/**
	 * 
	 */
	protected Term() {} // DON'T CALL THESE DIRECTLY.  GO VIA HandleFOPCstrings.
	protected Term(HandleFOPCstrings stringHandler) {
		this.stringHandler = stringHandler;
	}
	
	public TypeSpec getTypeSpec() {
		return typeSpec;
	}

	// Only allow ONE type per term?  Note: numbers should not have spec's.
	public void clearTypeSpec() { 
		typeSpec = null;
	}
	// Only allow ONE type per term?  Note: numbers should not have spec's.
	public void setTypeSpec(TypeSpec typeSpec) {
		setTypeSpec(typeSpec, true);
	}
	public void setTypeSpec(TypeSpec typeSpec, boolean complainIfSet) {
		if (     typeSpec == null) { return; }
		if (this.typeSpec == null) { this.typeSpec = typeSpec; return; }

		if (complainIfSet && !this.typeSpec.equals(typeSpec) && !this.typeSpec.isNotYetSet()) { 
			//Utils.error(   "Cannot set the type of '" + this + "' to '" + typeSpec + "' since it already is of type '" + this.typeSpec + "'.");
		}
		
		int newMode =      typeSpec.mode;
		int oldMode = this.typeSpec.mode;
		if (newMode != oldMode) { this.typeSpec.mode = newMode; }
		Type newType = typeSpec.isaType;
		Type oldType = this.typeSpec.isaType;
		if (newType == oldType) { return; }
		if ( stringHandler.isaHandler.isa(oldType, newType)) { return; } // Keep the more specific type.
		if (!stringHandler.isaHandler.isa(newType, oldType)) { Utils.error("Cannot set the type of '" + this + "' to '" + typeSpec + "' since it already is of type '" + this.typeSpec + "'\nand neither is an subclass of the other"); }
		this.typeSpec.isaType = newType;
	}

	public void setTypeSpecRegardless(TypeSpec typeSpec) {
		if (typeSpec == null) { Utils.error("setTypeSpecRegardless: cannot have typeSpec=null."); }
		this.typeSpec.isaType = typeSpec.isaType;
	}
	
	public Term copyAndRenameVariables() {
		stringHandler.pushVariableHash();
		Term result = copy(true);
		stringHandler.popVariableHash();
		result.typeSpec = typeSpec;
		return result;
	}

    public Term applyTheta(BindingList bindings) {
        if ( bindings == null || bindings.theta == null ) {
            return this;
        }
		return applyTheta(bindings.theta);
    }
	public abstract Term           applyTheta(Map<Variable,Term> bindings) ;
	public abstract Term           copy(boolean recursiveCopy);
    public abstract Term           copy2(boolean recursiveCopy, BindingList bindingList);
 //	public abstract int            hashCode();
	//public abstract boolean        equals(Object other);
	public abstract BindingList    variants(Term term, BindingList bindings);
	public abstract boolean        containsVariables();
	public abstract boolean        freeVariablesAfterSubstitution(BindingList theta);
	public abstract Collection<Variable> collectFreeVariables(Collection<Variable> boundVariables);
	
	public boolean isGrounded() { return !containsVariables(); }


	@Override
	public int compareTo(Term otherTerm) { // Could be made more efficient for subclasses if this ends up taking too much time.
		return toString().compareTo(otherTerm.toString());
	}
	
    /** Returns the term in the form of a sentence.
     *
     * Not all terms have sentence representations.  For example, there is no
     * sentence representation for a NumericConstant.  If no sentence representation
     * exists, null is returned.
     *
     * @return Sentence representation of this term, or null if one does not exist.
     */
    public abstract Sentence       asSentence();
    /** Returns the Term as a clause.
     *
     * @param <Return>
     * @param <Data>
     * @param visitor
     * @param data
     * @return Clause represented by the term, or null if one does not exist.
     */
    public Clause         asClause() { return null; }

    public Term asTerm() {
        return this;
    }

    public Literal asLiteral() {
        Utils.error("Term '" + this + "' can not be converted to a Literal.");
        return null;
    }

    public <Return,Data> Return accept(TermVisitor<Return,Data> visitor, Data data) {
        return visitor.visitOtherTerm(this, data);
    }

	public Collection<Variable> collectAllVariables() {
		return collectFreeVariables(null);
	}
    
    

    public Clause getNegatedQueryClause() throws IllegalArgumentException {
        // We are going to just wrap the term in a literal for now.  The prover
        // probably won't know how to handle this yet, but that should be an easy enough
        // change to make.

        return stringHandler.getClause(null, Collections.singletonList(stringHandler.getTermAsLiteral(this)));
    }

    public boolean isVariant(Term thatTerm) {
        return variants(thatTerm, new BindingList() ) != null;
    }

    public boolean                       isEquivalentUptoVariableRenaming(Term that) {
        return this.isEquivalentUptoVariableRenaming(that, new BindingList()) != null;
    }

    public abstract BindingList          isEquivalentUptoVariableRenaming(Term that, BindingList bindings);

	
   /** Methods for reading a Object cached to disk.
    *
    * @param in
    * @throws java.io.IOException
    * @throws java.lang.ClassNotFoundException
    */
    private void readObject(java.io.ObjectInputStream in) throws IOException, ClassNotFoundException {
        if ( in instanceof FOPCInputStream == false ) {
            throw new IllegalArgumentException(getClass().getCanonicalName() + ".readObject() input stream must support FOPCObjectInputStream interface");
        }

        in.defaultReadObject();

        FOPCInputStream fOPCInputStream = (FOPCInputStream) in;

        this.stringHandler = fOPCInputStream.getStringHandler();
    }

    public HandleFOPCstrings getStringHandler() {
        return stringHandler;
    }

    


}
