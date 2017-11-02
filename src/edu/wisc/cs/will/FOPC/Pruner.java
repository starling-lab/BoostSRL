/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.Utils.Utils;

/**
 * @author shavlik
 *
 * Instances of this class hold information needed for a pruning a node from an ILP search.
 * This doesn't really belong in the FOPC class, but the PredicateName instance needs it, and putting it here avoids a circularity.
 *
 */
public class Pruner {
	public Literal prunableLiteral;  // No need to add this literal to a clause that contains 'ifPresentLiteral.'
	public Literal ifPresentLiteral;
	public int     warnIfPresentLiteralCount; // If 'ifPresentLiteral' is the head of this many or more clauses, throw an error.  A negative value means "ignore this test."
	public int     truthValue = 0;            // TruthValue: -1 means 'prune because false', 1 means because true, and 0 means unknown.
	
	/**
	 * 
	 */
	public Pruner(Literal prunableLiteral, Literal ifPresentLiteral, int warnIfPresentLiteralCount, int truthValue) {
		this.prunableLiteral           = prunableLiteral;
		this.ifPresentLiteral          = ifPresentLiteral;
		this.warnIfPresentLiteralCount = warnIfPresentLiteralCount;
		this.truthValue                = truthValue;
		if (warnIfPresentLiteralCount == 0) {
			Utils.error("Setting warnIfPresentLiteralCount=0 in a Pruner instance is invalid since it will always lead to a warning.\n  Use a negative number to mean 'do not check.'");
		}
	}
	
	/**
         * @param thisPrunableLiteral
         * @param thisIfPresentLiteral
         * @param unifier
         * @return Whether the given literals match this pruner.
         */
	public boolean isaMatch(Literal thisPrunableLiteral, Literal thisIfPresentLiteral) {
		BindingList bindings = Unifier.UNIFIER.unify(thisPrunableLiteral, prunableLiteral);
		
		if (bindings == null) { return false; }		
		if (thisIfPresentLiteral != null) { // NULL in this case means nothing needs to be present in the body.
			bindings = Unifier.UNIFIER.unify(thisIfPresentLiteral, ifPresentLiteral, bindings);
		}
		if (false && bindings != null) {
			Utils.println("Matched pruner: ");
			Utils.println("  candidate: " + thisPrunableLiteral);
			Utils.println("             " + prunableLiteral);
			Utils.println("    present: " + (thisIfPresentLiteral == null ? null : thisIfPresentLiteral));
			Utils.println("             " + ifPresentLiteral);
			Utils.println("   bindings: " + bindings);
		} 
		return (bindings != null);
	}

	public String toPrettyString() {
		return "Can prune '" + prunableLiteral + "' if " + ifPresentLiteral + " is present (and cannot be derived " + warnIfPresentLiteralCount + " or more times).";
	}

	public String toString() {
		if (warnIfPresentLiteralCount > 0) { return "pruner("+ prunableLiteral + ", " + ifPresentLiteral + ", " + warnIfPresentLiteralCount + ")"; }
		return "pruner("+ prunableLiteral + ", " + ifPresentLiteral + ")";
	}

}
