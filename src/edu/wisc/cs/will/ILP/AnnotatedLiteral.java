package edu.wisc.cs.will.ILP;

import java.io.Serializable;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Type;
import edu.wisc.cs.will.FOPC.Variable;

/**
 * @author shavlik
 *
 *  This class allows for annotated literals.
 *  
 */
@SuppressWarnings("serial")
public class AnnotatedLiteral extends Literal implements Serializable {
	Map<Term,Type> newTerms; // Record terms that are NEW in this literal. 
	/**
	 * 
	 */
	public AnnotatedLiteral(HandleFOPCstrings stringHandler, PredicateName predName, List<Term>args, Map<Term,Type> newTerms) {
		super(stringHandler, predName, args);
		this.newTerms = newTerms;
	}
	
	@Override
	public int hashCode() { // Need to have equal objects produce the same hash code.
		final int prime = 31;
		int result = 1;
		result = prime * result + (getArguments() == null ? 0 : getArguments().hashCode());
		result = prime * result + (newTerms       == null ? 0 : newTerms.hashCode());
		return result;
	}	
	// See if these two literals are equivalent EXCEPT where they introduce new variables.
	// E.g., p(x,y) and p(x,z) are equivalent iff BOTH y and z are new variables.
	// Note: p(x,y,y) and p(x,z,w) are NOT equivalent even if y, z, and w are all new variables.
	protected boolean equals(Literal other, Map<Term,Type> newTermsInOtherLiteral) { 
		if (predicateName != other.predicateName) { return false; }
		int len1 =       numberArgs();
		int len2 = other.numberArgs();
		if (len1 != len2) { return false; }
		Map<Variable,Variable> newVarsFound = null;
		
		for (int i = 0; i < len1; i++) { // Should do with a dual-for loop, but this is easier-to-read code and the argument lists shouldn't be too long.
			Term term1 =       getArgument(i);
			Term term2 = other.getArgument(i);
			
			if (term1.equals(term2) && term1 instanceof Variable && newTerms != null && newTerms.containsKey(term1)) {  // If the two terms are equivalent and NOT a new term, that is great.
				continue;
			}
			// Otherwise must both be new variables.
			if (term1 instanceof Variable && newTerms               != null &&               newTerms.containsKey(term1) && // Otherwise they must both be new variables of the same type.
				term2 instanceof Variable && newTermsInOtherLiteral != null && newTermsInOtherLiteral.containsKey(term2) &&
				newTerms.get(term1) == newTermsInOtherLiteral.get(term2)) {   // Can use == here since type strings are uniquely mapped to type instances.
				if (newVarsFound == null) { newVarsFound = new HashMap<Variable,Variable>(4); }
				Variable var1    = (Variable) term1;
				Variable var2    = (Variable) term2;
				Variable lookup1 = newVarsFound.get(var1);
				Variable lookup2 = newVarsFound.get(var2);
				if (lookup1 == null && lookup2 == null) { // Neither variable seen yet.  Record that they have been matched.
					newVarsFound.put(var1, var1);
					if (var2 != var1) { newVarsFound.put(var2, var1); }
					continue;
				}
				else if (lookup1 != null && lookup2 != null && lookup1 == lookup2) { // Both variables mapped to the same variable. 
					continue;
				}
				else { return false; } // One variable but not both have already been seen (or both have been seen but map to different variables).
			}
			return false;
		}
		return true; // Successfully matched all the terms.
	}
	
	public String toString() {
		if (newTerms == null) { return  super.toString(); }
		return super.toString() + " [newVterms=" + newTerms + "]";
	}

}
