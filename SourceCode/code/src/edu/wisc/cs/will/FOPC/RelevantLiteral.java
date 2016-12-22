/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.FOPC.PredicateName;

/**
 * Allow the user to say that some predicate is relevant to the concept being learned.
 * The anticipated use is that the relevance strength will be mapped to a cost on a literal in a clause,
 * with higher relevance being lower cost.  However that is up to the code that uses this class.
 * 
 * There (currently) is no 'neutral' relevance - it is assumed that predicate/arity's not in a RelevantLiteral will implicitly have that value.
 * 
 * 
 * @author shavlik
 *
 */
public class RelevantLiteral {	
	
	private PredicateName     pName;
	private int               arity    = -1;  // If negative, any arity is fine. 
	private int               argument = -1;  // If set, says which ARGUMENT is relevant (counts from 1).  TODO - figure out what we'll do with this.
	private RelevanceStrength strength = RelevanceStrength.RELEVANT; // Default to saying something is relevant. 

	/**
	 * Constructors for RelevantLiteral instances.
	 */
	public RelevantLiteral(PredicateName pName) {
		this.pName = pName;	
	}
	public RelevantLiteral(PredicateName pName, int arity) {
		this(pName);
		this.arity = arity;	
	}
	public RelevantLiteral(PredicateName pName, RelevanceStrength strength) {
		this(pName);
		this.strength = strength;		
	}
	public RelevantLiteral(PredicateName pName, int arity, RelevanceStrength strength) {
		this(pName, arity);
		this.strength = strength;		
	}
	public RelevantLiteral(PredicateName pName, int arity, int argument) {
		this(pName, arity);
		this.argument = argument;
	}
	public RelevantLiteral(PredicateName pName, int arity, int argument, RelevanceStrength strength) {
		this(pName, arity, strength);
		this.argument = argument;
	}	

	// See if this instance's relevance strength is  this strong.
	public boolean isThisRelevant(RelevanceStrength strength) {
		return this.strength == strength;
	}	
	
	// See if this instance's relevance strength is at least this strong.
	public boolean atLeastThisRelevant(RelevanceStrength strength) {
		return this.strength.compareTo(strength) >= 0;
	}	
	
	// See if this instance's relevance strength is no more than this strong.
	public boolean atMostThisRelevant(RelevanceStrength strength) {
		return this.strength.compareTo(strength) <= 0;
	}
	
	   public PredicateNameAndArity getPredicateNameAndArity() {
           return new PredicateNameAndArity(pName, arity);
       }
	
	// The accessor methods.
	public PredicateName getPName() {
		return pName;
	}
	public void setPName(PredicateName name) {
		pName = name;
	}
	public int getArity() {
		return arity;
	}
	public void setArity(int arity) {
		this.arity = arity;
	}
	public int getArgument() {
		return argument;
	}
	public void setArgument(int argument) {
		this.argument = argument;
	}
	public RelevanceStrength getStrength() {
		return strength;
	}
	public void setStrength(RelevanceStrength strength) {
		this.strength = strength;
	}
	
	public String toString() {
		return "Relevant: " + pName + "/" + arity + " strength=" + strength;
	}

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final RelevantLiteral other = (RelevantLiteral) obj;
        if (this.pName != other.pName && (this.pName == null || !this.pName.equals(other.pName))) {
            return false;
        }
        if (this.arity != other.arity) {
            return false;
        }
        if (this.argument != other.argument) {
            return false;
        }
        if (this.strength != other.strength) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        int hash = 5;
        hash = 23 * hash + (this.pName != null ? this.pName.hashCode() : 0);
        hash = 23 * hash + this.arity;
        hash = 23 * hash + this.argument;
        hash = 23 * hash + (this.strength != null ? this.strength.hashCode() : 0);
        return hash;
    }

    

}
