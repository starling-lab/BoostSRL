package edu.wisc.cs.will.MLN_Task;

import edu.wisc.cs.will.FOPC.BindingList;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.wisc.cs.will.FOPC.Constant;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.Utils.Utils;

/**
 * A GroundLiteral class.
 * 
 * Note: GroundLiterals are never negated (nor should they have weights other than infinity).  This is done so they can be canonically represented.
 *       Users of GroundLiterals need to manage whether or not they are negated (e.g., by keeping them in separate lists, sets, etc.).
 * 
 * @author pavan and shavlik
 */
public class GroundLiteral extends Literal {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	//private static int counter = 0; // For helping debugging.	
	private boolean            value = false; // The truth value of the GroundLiteral.  These default to false.
	public  boolean  hasBeenInterned = false; //  All the ground clauses containing this literal have been computed.
	private Block                      block; // The block this ground literal is contained in.
	private Set<GroundClause>   gndClauseSet; // Ground literals need to point to the ground clauses in which they appear.
	//private int                         id;
	private Object                    marker;
	public  boolean          inLinkedList = false; // Used to avoid linear lookups.
	//private boolean  freezeThisLiteral = false;

	// These are protected because ground literals should be created via MLN_Task.getCanonicalRepresentative().
	protected GroundLiteral(HandleFOPCstrings stringHandler, PredicateName pName) {
		super(stringHandler, pName);
		block = null;
		//id = ++counter;
		//Utils.println("Creating: " + pName + " #" + id);
		//Utils.error("who is the caller?");
	}
	protected GroundLiteral(HandleFOPCstrings stringHandler, PredicateName pName, List<Term> gndTerms) {
		this(stringHandler, pName);
		for (Term term : gndTerms) if (!(term instanceof Constant)) { Utils.error("Error: '" + term + "' is a non-constant term in the constructor of GroundLiteral."); }
		this.setArguments(gndTerms);
	}
	protected GroundLiteral(Literal parent, List<Term> gndTerms) {
		this(parent.getStringHandler(), parent.predicateName, gndTerms);
	//	this.printUsingInFixNotation = parent.getPrintUsingInFixNotation();
	}
	public GroundLiteral(Literal parent) { // Note we don't check here that all arguments are constants (and some facts do slip through, intentionally, with variables in them - see factsWithVariables in GroundThisMarkovNetwork).
		this(parent.getStringHandler(), parent.predicateName);
		List<Term> arguments2 = new ArrayList<Term>(parent.numberArgs());  // For zero-arity literals, we do this to prevent accessing nulls and also so parentheses print, ie 'p()' instead of 'p'.
		if (parent.numberArgs() > 0) {
			arguments2.addAll(parent.getArguments());
		}
		setArguments(arguments2);
		this.setWeightOnSentence(parent.getWeightOnSentence());
	//	this.printUsingInFixNotation = parent.getPrintUsingInFixNotation();
	}
	
	public void setMarker(Object marker) {
		this.marker = marker;
	}
	public Object getMarker() {
		return marker;
	}
	/*
	public void freeze() {
		freezeThisLiteral = true;
	}	
	public void unfreeze() {
		freezeThisLiteral = false;
	}	
	public boolean getFreeze() {
		return freezeThisLiteral;
	}
	public void setFreeze(boolean freezeValue) {
		freezeThisLiteral = freezeValue;
	}
	*/
	
	public Set<GroundLiteral> getNeighbors() {
		Set<GroundLiteral> neighbors = null;
		for (GroundClause gndClause : gndClauseSet) {
			int length = gndClause.getLength();
			for (int i = 0; i < length; i++) {
				GroundLiteral gLit = gndClause.getIthLiteral(i);
				if (gLit != this && (neighbors == null || !neighbors.contains(gLit))) {
					if (neighbors == null) { neighbors = new HashSet<GroundLiteral>(4); }
					neighbors.add(gLit);
				}
			}
		}
		if (debugLevel > 1) { Utils.println("Neighbors: "); for (GroundLiteral gndLit : neighbors) { Utils.println("   " + gndLit);	} }
		return neighbors;
	}
	
	/**
	 * Flip the boolean value of the GroundLiteral.
	 */
	public void flipFinal(GroundedMarkovNetwork groundedMarkovNetwork, TimeStamp timeStamp) {
		if (gndClauseSet == null) { Utils.error("Have gndClauseSet=null for '" + this + "'."); }
		setValue(!value, groundedMarkovNetwork, timeStamp);		
	}
	public void flipSpeculative() {
		value = !value;
	}
	
	public void setGndClauseSet(Set<GroundClause> gndClauseSet) {
		this.gndClauseSet = gndClauseSet;
	}
	
	/**
	 * @return The Set of GroundClauses this literal appears in.
	 */
	public Set<GroundClause> getGndClauseSet() {
		return gndClauseSet;
	}
	
	/**
	 * Empties the GroundClauseList
	 */
	public void clearGndClauseSet() {
		if (gndClauseSet == null) { gndClauseSet = new HashSet<GroundClause>(4); }
		else { gndClauseSet.clear(); }
	}
	
	
	/**
	 * @param gndClause The GroundClause to be added to the GroundClause List.
	 */
	public void addGndClause(GroundClause gndClause) {
		if (gndClauseSet == null) { clearGndClauseSet(); }
		gndClauseSet.add(gndClause); // Since a set, will handle duplicates.
	//	Utils.println("% GL: Size of gnd clauses for " + toString(Integer.MIN_VALUE) + " : "+ Utils.getSizeSafely(getGndClauseSet()) + " after adding " + gndClause.toPrettyString());
	}	
	
	/**
	 * @param value Assign this to the truth value of the GroundLiteral.
	 */
	public void setValue(boolean value, GroundedMarkovNetwork groundedMarkovNetwork, TimeStamp timeStamp) {
		setValue(value, groundedMarkovNetwork, timeStamp, true);
	}
	//private TimeStamp prev_timeStampOfLastSetValue;
	//private TimeStamp       timeStampOfLastSetValue;
	public void setValue(boolean value, GroundedMarkovNetwork groundedMarkovNetwork, TimeStamp timeStamp, boolean complain) {
		//prev_timeStampOfLastSetValue = timeStampOfLastSetValue;
		//timeStampOfLastSetValue = timeStamp;
		this.value = value;
		if (groundedMarkovNetwork == null) { return; }
		updateAllContainingGroundClauses(groundedMarkovNetwork, timeStamp, complain); //JWSJWS
	}
	public void setValueOnly(boolean value, TimeStamp timeStamp) {
		this.value = value; // Only set this value.  Don't update all clauses containing this literal.  Note: this is dangerous unless another setValue is called soon!
		//prev_timeStampOfLastSetValue = timeStampOfLastSetValue;
		//timeStampOfLastSetValue = timeStamp;
	}
	
	public String getValueAndInfo() {
		String result = ""; // "[" + prev_timeStampOfLastSetValue + "," + timeStampOfLastSetValue + "] ";
		if (value) { return "true" + result; }
		return "false" + result;
	}
	
	private void updateAllContainingGroundClauses(GroundedMarkovNetwork groundedMarkovNetwork, TimeStamp timeStamp, boolean complainIfInconsistent) {
		if (gndClauseSet == null) { Utils.error("Have gndClauseSet=null for '" + this + "'."); }
		for (GroundClause gndClause : gndClauseSet) if (groundedMarkovNetwork.isaMarkedGroundClause(gndClause)) {
			boolean old    = gndClause.isSatisfiedCached();
			boolean result = gndClause.checkIfSatisfied(timeStamp);  // TODO - depending on sign and value of ground lit and clause state, might not need to check
			if (complainIfInconsistent && gndClause.getWeightOnSentence() > 0 && !old &&  result && !gndClause.isActive()) { Utils.error("due to, '" + this + "' = " + value + ", this clause is becoming satisfied (and inactive) but it is already inactive: " + gndClause.getInfo()); }
			if (complainIfInconsistent && gndClause.getWeightOnSentence() > 0 &&  old && !result &&  gndClause.isActive()) { Utils.error("due to, '" + this + "' = " + value + ", this clause is becoming unsatisfied (and active) but it is already active: "   + gndClause.getInfo()); }
			if (complainIfInconsistent && gndClause.getWeightOnSentence() < 0 &&  old && !result && !gndClause.isActive()) { Utils.error("due to, '" + this + "' = " + value + ", this clause is becoming satisfied (and inactive) but it is already inactive: " + gndClause.getInfo()); }
			if (complainIfInconsistent && gndClause.getWeightOnSentence() < 0 && !old &&  result &&  gndClause.isActive()) { Utils.error("due to, '" + this + "' = " + value + ", this clause is becoming unsatisfied (and active) but it is already active: "   + gndClause.getInfo()); }
	 	}
	}
	
	/**
	 * @return The truth value of the GroundLiteral.
	 */
	public boolean getValue() {
		return value;
	}
	
	public void setBlock(Block block) {
		this.block = block;
	}
	
	public Block getBlock() {
		return block;
	}
	
	/**
	 * Look at the Ground Clauses the literal appears in, and compute the
	 * sum of weights of satisfied clauses.
	 * 
	 * @param literal The GroundLiteral of interest.
	 * @return Return sum of weights of satisfied clauses.
	 */
	public double getWeightSatisfiedClauses() {
		if (gndClauseSet == null) {	return 0; }
		double weightSatisfiedClauses = 0;
		
		for (GroundClause currClause : gndClauseSet) {			
			if (currClause.isSatisfiedCached()) { 
				weightSatisfiedClauses += currClause.getWeightOnSentence();
			} 
		}
		return weightSatisfiedClauses;
	}
	

	public boolean matchesThisGroundLiteral(Literal other) {
		if (this == other) { return true; }
		if (predicateName != other.predicateName)   { return false; }
		int thisNumberOfArgs = numberArgs();
		if (thisNumberOfArgs != other.numberArgs()) { return false; }
		for (int i = 0; i < thisNumberOfArgs; i++) {
			Term thisTerm  =       getArgument(i);
			Term otherTerm = other.getArgument(i);
			if (!thisTerm.equals(otherTerm)) { return false; }
		}
		return true;
	}
	
	// Note: any duplicates may well be correct, depending on how the reduction occurred.
	public boolean checkForDuplicateGroundings() {
		Set<GroundClause> clauseList = getGndClauseSet();
		if (clauseList == null) { return false; }
		int counter1 = 0;
		int counter2 = 0;
		for (GroundClause currClause1 : clauseList) {
			counter1++;
			for (GroundClause currClause2 : clauseList) {
				counter1++;
				if (currClause1.sameGroundingDifferentInstances(currClause2)) {
					Utils.warning("Have dups groundings!  Clauses #" + counter1 + " and #" + counter2 + " for '" + 
									this + "'.  GndClause = '" + currClause1 + "' (freeVarBindings=" + currClause1.getFreeVarBindings() +
									").");
					return true;
				}
			}
		}
		return false;
	}
	
	public String toStringLiteralOnly() {
		return super.toString(Integer.MAX_VALUE);
	}

	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return "{ value = " + value + " : " + super.toString(precedenceOfCaller, bindingList) + "}";
	}

		
}