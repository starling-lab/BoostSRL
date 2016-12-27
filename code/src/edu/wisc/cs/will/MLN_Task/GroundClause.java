package edu.wisc.cs.will.MLN_Task;
import java.util.*;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.Utils.Utils;

/**
 * A GroundClause class composed of GroundLiterals.
 * Contains utility methods like the change of cost
 * when a particular literal is flipped.
 * 
 * 
 * Make cases of these for use by GroundThisMarkovNetwork
 *  - only those literals that are satisfiable
 *  - keep a representsThisMany int
 *  
 *  - assume ALWAYS true, so need to 'subtract' out the #false
 *  - if always false: if current settings are in the false's
 * 
 * @author pavan and shavlik
 */
public class GroundClause extends Clause {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	// TODO the FOPC classes probably should have these as well, but then need to be careful about adding or subtracting literals.
	private boolean isSatisfiedCached = true;  // Store this so no need to repeatedly compute.  Default is that clauses are satisfied.
	private boolean isActive          = false; // use this instead of making sets. 
	private Object  marker            = null;
	public  short   age               = 0; // Used to get rid of old 'lazy' clauses.
	private List<Term> freeVarBindings = null; //  Sometimes we need to use VARIABLE bindings to show that two ground clauses are the same.
	
	public GroundClause(MLN_Task task, Clause parent, double multiplier, List<Term> freeVarBindings, TimeStamp timeStamp) {
		super(task.stringHandler, null, null);
		// Now need to convert the parent's literals to grounded versions.
		if (parent.posLiterals != null) for (Literal pLit : parent.posLiterals) {
			if (posLiterals == null) { posLiterals = new ArrayList<Literal>(1); }
			posLiterals.add(task.getCanonicalRepresentative(pLit));
		}
		if (parent.negLiterals != null) for (Literal nLit : parent.negLiterals) {
			if (negLiterals == null) { negLiterals = new ArrayList<Literal>(1); }
			negLiterals.add(task.getCanonicalRepresentative(nLit));
		}
		this.freeVarBindings = freeVarBindings;
		setWeightOnSentence(parent.getWeightOnSentence());
		setLiteralInfo(timeStamp);  // Need to recompute length, etc.
	}
	public GroundClause(HandleFOPCstrings stringHandler, GroundLiteral literal, boolean literalIsPos, TimeStamp timeStamp) {
		super(stringHandler, literal, literalIsPos);
		this.freeVarBindings = null;
		setLiteralInfo(timeStamp);  // Need to recompute length, etc.
	}
	protected GroundClause(Clause parent, List<Literal> posLiterals, List<Literal> negLiterals, double multiplier, List<Term> freeVarBindings, TimeStamp timeStamp) { // These literals should be GroundLiterals, but need to be Literal for the super() constructor.
		super(parent.getStringHandler(), posLiterals, negLiterals);
		this.setWeightOnSentence(multiplier * parent.getWeightOnSentence());
		this.freeVarBindings = freeVarBindings;
		setWeightOnSentence(parent.getWeightOnSentence());
		setLiteralInfo(timeStamp);
	}
	
	public List<Term> getFreeVarBindings() {
		return freeVarBindings;
	}
	
	public void setLiteralInfo(TimeStamp timeStamp) {
		// Connect this ground clause and its ground literals.
		if (negLiterals != null) for (Literal nLit : negLiterals) {
			((GroundLiteral) nLit).addGndClause(this);
		}
		if (posLiterals != null) for (Literal pLit : posLiterals) {
			((GroundLiteral) pLit).addGndClause(this);
		}
		checkIfSatisfied(timeStamp);
	}
	
	public void setMarker(Object marker) {
		if (marker != null) { age = 0; } // In case this is a lazy clause, also note that it was recently marked.
		this.marker = marker;
	}
	public Object getMarker() {
		return marker;
	}
	
    @Override
	public int hashCode() {
		if (stringHandler.usingStrictEqualsForClauses()) { return super.hashCode(); }
		final int prime = 31;
		int result = 1;
		result = prime * result + ((freeVarBindings == null) ? 0 : freeVarBindings.hashCode());
		return result;
	}
	
    @Override
	public boolean equals(Object other) {
		if (this == other) { return true; } 

		if (stringHandler.usingStrictEqualsForClauses()) { return false; }
		return sameGroundingDifferentInstances(other); // Note: we already did the "same instance" test.
	}
	
	// We want to see here if duplicate groundings from the SAME PARENT.
	public boolean sameGroundingDifferentInstances(Object other) {
		if (this == other) { return false; } // SAME instances
				
		if (!(other instanceof GroundClause)) { return false; }
		GroundClause otherAsGroundClause = (GroundClause) other;
	
		if (freeVarBindings == null) { Utils.error("Should not call this if size = 0"); } // Note: for clauses with NO variables, make an empty list.
		if (getLength() != otherAsGroundClause.getLength()) { return false; }
		if (freeVarBindings.size() != otherAsGroundClause.freeVarBindings.size()) { return false; }
		for (int i = 0 ; i < freeVarBindings.size(); i++) {
			if (freeVarBindings.get(i) != otherAsGroundClause.freeVarBindings.get(i)) { return false; }
		}
		return true;
	}
	
	public boolean sameClause(GroundClause gndClause) {
		if (this == gndClause) { return true; }
		if (getLength() != gndClause.getLength()) { return false; }
		for (int i = 0; i < getLength(); i++) {
			if (getIthLiteral(i) != gndClause.getIthLiteral(i)) { return false; }
		}
		return true;
	}
	
	// Override by updating the type.
    @Override
	public GroundLiteral getIthLiteral(int i) {
		return (GroundLiteral) super.getIthLiteral(i);
	}
	
	/**
	 * Flip the boolean value of the ith literal.
	 * @param i Index of the literal whose value is to be flipped.
	 */
	public void flipIthLiteral(int i, GroundedMarkovNetwork groundedMarkovNetwork, TimeStamp timeStamp) {
		GroundLiteral gLit = getIthLiteral(i);
		Utils.waitHere("jwsjwsjws");
		gLit.setValue(!gLit.getValue(), groundedMarkovNetwork, timeStamp);  // Assumes the ground literal will reset all the isSatisfied of its clauses.
	}
	
	/**
	 * The change in cost if a particular GroundLiteral is flipped.
	 * 
	 * @param literal A particular GroundLiteral
	 * @return The change in cost if literal is flipped.
	 */
	public double deltaCostIfFlip(GroundLiteral gLit) {
		boolean satisfiedBeforeFlip = isSatisfiedCached;
		boolean satisfiedAfterFlip  = checkIfSatisfiedIfThisGroundLiteralIsFlipped(gLit);
		
		if (debugLevel > 2) { Utils.println("%         Before/after=" + satisfiedBeforeFlip + "/" + satisfiedAfterFlip + " for '" + gLit + "'=" + gLit.getValue() + " [active=" + isActive + ", sat=" + isSatisfiedCached + "] " + getInfo()); }
		// Note that COSTs are BAD and in MLNs, higher weights are BETTER, so cost = - change in weight.
		if ( satisfiedBeforeFlip ==  satisfiedAfterFlip) { return  0.0;    } // Did not change state of clause.
		if ( satisfiedBeforeFlip && !satisfiedAfterFlip) { return  wgtSentence; } // Turn OFF clause if flipped.
		if (!satisfiedBeforeFlip &&  satisfiedAfterFlip) { return -wgtSentence; } // Turn ON  clause if flipped.
		Utils.error("Should not reach here: before=" + satisfiedBeforeFlip + " and after=" + satisfiedAfterFlip);
		return Double.NaN;
	}
	
	/**
	 * The change in cost if a particular GroundLiteral in a BLOCK is flipped.
	 * 
	 * @param block A Block that groups ground literals
	 * @param turnOnIndex Turn on this grounding
	 * @param turnOffIndex Turn off this grounding
	 * @return The change in cost if literal is flipped.
	 */
	public double deltaCostIfBlockFlip(Block block, int turnOnIndex, int turnOffIndex) {
		boolean satisfiedBeforeFlip = isSatisfiedCached;
		boolean satisfiedAfterFlip  = isSatisfiedIfThisBlockPairChangeHappens(block, turnOnIndex, turnOffIndex);

		// Note that COSTs are BAD and in MLNs, higher weights are BETTER, so cost = - change in weight.
		if ( satisfiedBeforeFlip ==  satisfiedAfterFlip) { return  0;      } // Did not change state of clause.
		if ( satisfiedBeforeFlip && !satisfiedAfterFlip) { return  wgtSentence; } // Turn OFF clause if flipped.
		if (!satisfiedBeforeFlip &&  satisfiedAfterFlip) { return -wgtSentence; } // Turn ON  clause if flipped.
		Utils.error("Should not reach here: before=" + satisfiedBeforeFlip + " and after=" + satisfiedAfterFlip);
		return Double.NaN;
	}
	
	// See if processing this block on/off pair changes the truth value of this ground literal.
	public boolean isSatisfiedIfThisBlockPairChangeHappens(Block block, int turnOnIndex, int turnOffIndex) {
		if (getLength() < 1) { return false; }
		GroundLiteral gLit1 = (turnOnIndex  < 0 ? null : block.getGndLiterals().get(turnOnIndex ));
		GroundLiteral gLit2 = (turnOffIndex < 0 ? null : block.getGndLiterals().get(turnOffIndex));
		boolean  gLit1WouldChange = (gLit1 == null ? false : gLit1.getValue() == false);
		boolean  gLit2WouldChange = (gLit2 == null ? false : gLit2.getValue() == true);
		if (gLit1 == gLit2) { gLit1 = null; } // If they are equal, then the convention is that the 'off' wins out.  TODO - rethink this, since maybe we should simply flip (ie, as is, only flip if OFF).
		if (!gLit1WouldChange) { gLit1 = null; }
		if (!gLit2WouldChange) { gLit2 = null; }
		// If either gLit survives, see if it will have the proper sign AFTER it is flipped.
		for (int i = 0; i < getLength(); i++) {
			GroundLiteral thisLit = getIthLiteral(i);	
			if (thisLit == gLit1 || thisLit == gLit2) { if (thisLit.getValue() != getSignOfIthLiteral(i)) { return true; } }
			else                                        if (thisLit.getValue() == getSignOfIthLiteral(i)) { return true; }
		}		
		return false;
	}
	
	//private TimeStamp timeStampLastChecked; // Used for debugging. 
	//private TimeStamp timeStampLastChanged;
	//private TimeStamp prev_timeStampLastChecked; 
	//private TimeStamp prev_timeStampLastChanged;
	public boolean checkIfSatisfied(TimeStamp timeStamp) {
		boolean newSat = checkIfSatisfiedIfThisGroundLiteralIsFlipped(null);
		//prev_timeStampLastChecked = timeStampLastChecked;
		//timeStampLastChecked      = timeStamp;
		if (isSatisfiedCached != newSat) { 
			isSatisfiedCached         = newSat;
		 // prev_timeStampLastChanged = timeStampLastChanged;
		 // timeStampLastChanged      = timeStamp; 
		}
		return isSatisfiedCached;
	}	
	public String getInfo() {
		String result = "";

		//if (prev_timeStampLastChecked != null) { result += "[prev checked: " + prev_timeStampLastChecked + "]\n%   "; }	
		//if (     timeStampLastChecked != null) { result += "[last checked: " +      timeStampLastChecked + "]\n%   "; }
		//if (prev_timeStampLastChanged != null) { result += "[prev changed: " + prev_timeStampLastChanged + "]\n%   "; }
		//if (     timeStampLastChanged != null) { result += "[last changed: " +      timeStampLastChanged + "]\n%   "; }		
		return result + groundClauseSettingToString();
	}
	
	/**
	 * @return True if the GroundClause is satisfied, assuming the Ground Literal (if any) provided has its sign flipped.
	 */	
	// See if this clause is satisfied IF the truth value of this ground literal is flipped.
	public boolean checkIfSatisfiedIfThisGroundLiteralIsFlipped(GroundLiteral gLit) { // Be sure to check ALL literals here, even if not marked.
		if (getLength() < 1) { return false; }
		for (int i = 0; i < getLength(); i++) {
			GroundLiteral thisLit = getIthLiteral(i); if (thisLit == null) { Utils.error("should not have thisLit=null"); }
			//Utils.println("%      " + thisLit + " = " + thisLit.getValue() + " sign = " + getSignOfIthLiteral(i));
			if (thisLit == gLit) { if (thisLit.getValue() != getSignOfIthLiteral(i)) { return true; } }
			else                   if (thisLit.getValue() == getSignOfIthLiteral(i)) { return true; }
		}		
		return false;
	}
	
	public boolean isSatisfiedCached() {
		return isSatisfiedCached;
	}
	public boolean isActive() {
		return isActive; // Let external code define and compute this.
	}
	public void setActive(boolean value) {
		isActive = value;
	}
	
	// Create a string the shows the literals and their current values.
	public String groundClauseSettingToString() {
		int counter = 0;
		String result = returnWeightString() + "[ ";
		if (posLiterals != null) for (Literal posLit : posLiterals) {
			if (++counter > 25) { return result += " ... ]"; }
			result += "posLit: " + posLit + "=" + ((GroundLiteral) posLit).getValueAndInfo() + " ";
		}
		if (negLiterals != null) for (Literal negLit : negLiterals) {
			if (++counter > 25) { return result += " ... ]"; }
			result += "negLit: " + negLit + "=" + ((GroundLiteral) negLit).getValueAndInfo() + " ";
		}
		return result += "]";
	}	
	public String groundClauseSettingToString(GroundThisMarkovNetwork groundedMarkovNetwork) {
		int counter = 0;
		String result = returnWeightString() + markerForGndClause(groundedMarkovNetwork) + "[ ";
		if (posLiterals != null) for (Literal posLit : posLiterals) {
			if (++counter > 25) { return result += " ... ]"; }
			result += "posLit: " + markerForGndLit((GroundLiteral) posLit, groundedMarkovNetwork) + posLit + "=" + ((GroundLiteral) posLit).getValueAndInfo() + " ";
		}
		if (negLiterals != null) for (Literal negLit : negLiterals) {
			if (++counter > 25) { return result += " ... ]"; }
			result += "negLit: " + markerForGndLit((GroundLiteral) negLit, groundedMarkovNetwork) + negLit + "=" + ((GroundLiteral) negLit).getValueAndInfo() + " ";
		}
		return result += "]";
	}
	private String markerForGndClause(GroundThisMarkovNetwork groundedMarkovNetwork) {
		if (groundedMarkovNetwork.isaMarkedGroundClause(this)) { return "*"; } else { return ""; }
	}
	private String markerForGndLit(GroundLiteral gLit, GroundThisMarkovNetwork groundedMarkovNetwork) {
		if (groundedMarkovNetwork.isaMarkedGroundLiteral(gLit)) { return "*"; } else { return ""; }
	}
	
	public void writeMarkedLiteralsOnly(GroundedMarkovNetwork groundedMarkovNetwork) {
		boolean isMarkedClause = groundedMarkovNetwork.isaMarkedGroundClause(this);
		if (isMarkedClause) { Utils.println("This clause is marked.  Marked literals follow."); } else { Utils.println("This clause is not marked.  Marked literals follow."); }
		int counter = 0;
		if (posLiterals != null) for (Literal posLit : posLiterals) if (groundedMarkovNetwork.isaMarkedGroundLiteral((GroundLiteral) posLit)) {
			if (++counter > 100) { Utils.println("  marked pos lit: " + posLit + " = " + ((GroundLiteral) posLit).getValueAndInfo() + "."); }
		}
		if (negLiterals != null) for (Literal negLit : negLiterals) if (groundedMarkovNetwork.isaMarkedGroundLiteral((GroundLiteral) negLit)) {
			if (++counter > 100) { Utils.println("  marked neg lit: " + negLit + " = " + ((GroundLiteral) negLit).getValueAndInfo() + "."); }
		}
	}
	
	public void writeUnMarkedLiteralsOnly(GroundedMarkovNetwork groundedMarkovNetwork) {
		boolean isMarkedClause = groundedMarkovNetwork.isaMarkedGroundClause(this);
		if (isMarkedClause) { Utils.println("This clause is marked.  Unmarked literals follow."); } else { Utils.println("This clause is not marked.  Unmarked literals follow."); }
		int counter = 0;
		if (posLiterals != null) for (Literal posLit : posLiterals) if (!groundedMarkovNetwork.isaMarkedGroundLiteral((GroundLiteral) posLit)) {
			if (++counter < 100) { Utils.println("  unmarked pos lit #" + counter + ": " + posLit + " = " + ((GroundLiteral) posLit).getValueAndInfo() + "."); }
			if (isMarkedClause &&  ((GroundLiteral) posLit).getValue()) { Utils.println("     SATISFIES THE CLAUSE BUT IS MARKED! " + posLit); }
		}
		counter = 0;
		if (negLiterals != null) for (Literal negLit : negLiterals) if (!groundedMarkovNetwork.isaMarkedGroundLiteral((GroundLiteral) negLit)) {
			if (++counter < 100) { Utils.println("  unmarked neg lit#" + counter + " " + negLit + " = " + ((GroundLiteral) negLit).getValueAndInfo() + "."); }
			if (isMarkedClause && !((GroundLiteral) negLit).getValue()) { Utils.println("     SATISFIES THE CLAUSE BUT IS MARKED! " + negLit); }
		}
	}
	
	public boolean containsThisGroundLiteral(GroundLiteral gLit) {
		if (posLiterals != null) if (posLiterals.contains(gLit)) { return true; }
		if (negLiterals != null) if (negLiterals.contains(gLit)) { return true; }
		return false;
	}
	public boolean isaPosLiteral(GroundLiteral gLit) {
		return (posLiterals != null && posLiterals.contains(gLit));
	}
	public boolean isaNegLiteral(GroundLiteral gLit) {
		return (negLiterals != null && negLiterals.contains(gLit));
	}
	
	public boolean allOtherLiteralsAreUnmarked(GroundLiteral gLit) { // OK if gLit is marked or not.
		for (int i = 0; i < getLength(); i++) { 
			GroundLiteral gLitOther = getIthLiteral(i);
			if (gLitOther != gLit && gLitOther.getMarker() != null) { return false; } // Have found another marked literal.
		  // if (gLitOther == gLit && gLitOther.getMarker() == null) { return false; } // Utils.error("This gLit = '" + gLit + "' is not marked!"); }
		}
		return true;
	}
	
	// See if this is a unit clause ONLY considering the marked literals.
	public boolean isaUnitClauseUsingOnlyMarkedFeatures(Object markerInUse) {
		int size    = getLength();
		if (size < 2) { return true; }
		int counter = 0;
		for (int i = 0; i < size; i++) if (getIthLiteral(i).getMarker() == markerInUse) { counter++; }
		return (counter < 2);
	}
	// See if satisfied ONLY considering the UNmarked literals.
	public boolean isSatisfiedViaUnmarkedFeatures() {
		for (int i = 0; i < getLength(); i++) if (getIthLiteral(i).getMarker() == null) { 
			if (getIthLiteral(i).getValue() == getSignOfIthLiteral(i)) { return true; }
		}
		return false;
	}
    @Override
	public String toPrettyString() {
		String result = super.toPrettyString(Integer.MIN_VALUE);
		result += " (is_satisfied_cached = " + isSatisfiedCached + ") ";
		return result;
	}
	
	public String toStringLiteralOnly() {
		// TODO: pass in a flag so that toStringLiteralOnly called on each literal ...
		String result = super.toPrettyString(Integer.MIN_VALUE);
	//	result += " (is_satisfied_cached = " + isSatisfiedCached + ") ";
		return result;
	}
}
