package edu.wisc.cs.will.FOPC;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.Utils.Utils;
import java.io.Serializable;
import java.util.Collections;

@SuppressWarnings("serial")
public class PredicateSpec extends AllOfFOPC implements Serializable {
	private List<Term>     signature;
	private List<TypeSpec> typeSpecList;
	private PredicateName  owner;
	private boolean        isaILPmode; // If true, then can be used to generate children in an ILP search.

	
	private PredicateSpec() {		
	}

	protected PredicateSpec(List<Term> signature, List<TypeSpec> typeSpecList, PredicateName owner, boolean isaILPmode) {
		this.signature    = signature;
		this.typeSpecList = typeSpecList;
		this.owner        = owner;
		this.isaILPmode   = isaILPmode;
	}
	
	// Create a copy, but without all the type specifications.
	public PredicateSpec strip() {
		PredicateSpec newSpec = new PredicateSpec();
		newSpec.typeSpecList = new ArrayList<TypeSpec>(this.typeSpecList.size());
		for (TypeSpec tspec : typeSpecList) {
			newSpec.typeSpecList.add(new TypeSpec(tspec.isaType, tspec.stringHandler));
		}
		newSpec.owner        = this.owner;
		newSpec.isaILPmode   = this.isaILPmode;
		newSpec.signature    = this.signature;
		return newSpec;
	}

	// Stick these arguments in the leaf nodes of this spec's signature.
	public List<Term> applyArgsToSignature(HandleFOPCstrings stringHandler, List<Term> args) {
		return help_applyArgsToSignature(stringHandler, signature, 0, args);
	}

	private List<Term> help_applyArgsToSignature(HandleFOPCstrings stringHandler, List<Term> sig, int counter, List<Term> args) {
		if (debugLevel > 2) { Utils.print("%  " + owner + ": applyArgs = " + args + " to signature = " + sig + " counter = " + counter); }
		if (args == null || sig == null) { Utils.error("Should not have args=null nor sig=null here."); }
		List<Term> result = new ArrayList<Term>(sig.size());
		if (args.size() != sig.size()) { Utils.error("Have args = " + args + " but sig = " + sig); }
		for (Term item : sig) {
			if (item instanceof Constant) {
				result.add(args.get(counter));
				counter++;
			} else if (item instanceof Function) {
				Function f = (Function) item;
				result.add(stringHandler.getFunction(f.functionName, help_applyArgsToSignature(stringHandler, f.getArguments(), counter, args), f.typeSpec));
				counter += f.countLeaves();				
			} else { Utils.error("Should not have item=" + item + " sig=" + sig + " args=" + args); }
		}
		if (debugLevel > 2) { Utils.println("  result = " + result); }
		return result;
	}
	
	public List<Term> getSignature() {
		return signature;
	}

	public List<TypeSpec> getTypeSpecList() {
		return typeSpecList;
	}

    public TypeSpec getTypeSpec(int argument) {
        if (typeSpecList == null) {
            return null;
        }
        else {
            return typeSpecList.get(argument);
        }
    }

    public TypeModeAndSignature getTypeModeAndSignature(int argument) {
        return new TypeModeAndSignature(typeSpecList.get(argument), signature.get(argument));
    }

    public List<TypeModeAndSignature> getTypeModeAndSignatureList() {
        List<TypeModeAndSignature> list = new ArrayList<TypeModeAndSignature>();

        for (int i = 0; i < signature.size(); i++) {
            list.add(getTypeModeAndSignature(i));
        }

        return list;
    }

    public int getArity() {
        if (typeSpecList == null) {
            return 0;
        }
        return typeSpecList.size();
    }

	public void setTypeSpecList(List<TypeSpec> typeSpecList) {
		this.typeSpecList = typeSpecList;
	}

	public boolean isaILPmode() {
		return isaILPmode;
	}

	public void setIsaILPmode(boolean isaILPmode) {
		this.isaILPmode = isaILPmode;
	}

	public PredicateName getOwner() {
		return owner;
	}

	@Override
	public int hashCode() { // Need to have equal objects produce the same hash code.
		final int prime = 31;
		int result = 1;
		result = prime * result + ((owner        == null) ? 0 : owner.hashCode());
		result = prime * result + ((typeSpecList == null) ? 0 : typeSpecList.hashCode());
		result = prime * result + ((signature    == null) ? 0 : signature.hashCode());
		return result;
	}

    @Override
	public boolean equals(Object otherAsObject) { // TODO also check signature!
		if (!(otherAsObject instanceof PredicateSpec)) { return false; }
		PredicateSpec other = (PredicateSpec) otherAsObject;
		if (owner        != other.owner)         { return false; }
		if (typeSpecList == other.typeSpecList)  { return true;  } // This will handle case where both are null.
		if (typeSpecList == null || other.typeSpecList == null) { return false; }
		if (typeSpecList.size() != other.typeSpecList.size())   { return false; }
		int size = typeSpecList.size();
		for (int i = 0; i < size; i++) {
			TypeSpec one = typeSpecList.get(i);
			TypeSpec two = other.typeSpecList.get(i);
			if (one == null || two == null) { 
				if (one == null && two == null) { continue; }
				return false;
			}
			if (!one.equals(two)) { return false; }
		}
		return true;
	}

    @Override
	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return "signature = " + signature + ", types = " + typeSpecList;
	}

    @Override
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return "signature = " + signature + ", types = " + typeSpecList;
	}

    
	@Override
	public PredicateSpec applyTheta(Map<Variable, Term> bindings) {
		return this;
	}

	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return 0;
	}

    public static class TypeModeAndSignature {
        public TypeSpec typeAndMode;
        public Term signature;

        public TypeModeAndSignature(TypeSpec typeAndMode, Term signature) {
            this.typeAndMode = typeAndMode;
            this.signature = signature;
        }

        @Override
        public boolean equals(Object obj) {
            if (obj == null) {
                return false;
            }
            if (getClass() != obj.getClass()) {
                return false;
            }
            final TypeModeAndSignature other = (TypeModeAndSignature) obj;
            if (this.typeAndMode != other.typeAndMode && (this.typeAndMode == null || !this.typeAndMode.equals(other.typeAndMode))) {
                return false;
            }
            if (this.signature != other.signature && (this.signature == null || !this.signature.equals(other.signature))) {
                return false;
            }
            return true;
        }

        @Override
        public int hashCode() {
            int hash = 7;
            hash = 67 * hash + (this.typeAndMode != null ? this.typeAndMode.hashCode() : 0);
            hash = 67 * hash + (this.signature != null ? this.signature.hashCode() : 0);
            return hash;
        }

        @Override
        public String toString() {
            return typeAndMode + ":" + signature ;
        }

        

        
    }

}
