package edu.wisc.cs.will.MLN_Inference;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Map.Entry;

import edu.wisc.cs.will.MLN_Task.Block;
import edu.wisc.cs.will.MLN_Task.GroundClause;
import edu.wisc.cs.will.MLN_Task.GroundLiteral;
import edu.wisc.cs.will.MLN_Task.GroundedMarkovNetwork;
import edu.wisc.cs.will.MLN_Task.TimeStamp;
import edu.wisc.cs.will.Utils.Utils;

/**
 * This is an abstract base class for SAT solvers.
 * 
 * In these SAT solvers, we deal with only ground clauses
 * and ground literals, i.e, the propositionalization has
 * already been done before this point. 
 * 
 * @author pavan and shavlik
 */
public abstract class SAT extends AllOfInference {	
	private static final int     debugLevel   = 0;	
	private static final boolean checkForBugs = GroundedMarkovNetwork.doMajorDebug; //JWSJWSJWS
	private static final boolean checkForBugsExtraHard = checkForBugs && false; 
	
	public  static final int           maxNumberOfStarts_default =   1;
	public  static final int           maxNumberOfFlips_default  = 1000;
	
	protected final boolean     randFlipInBlock = true; // When flipping the state of literals in blocks, choose randomly?  Otherwise choose greedily.
	protected int      result1_computeDeltaCost = -1;   // The chosen partner literal if in a block. Reuse instead of repeatedly creating a double array (the old version).
	protected double   result0_computeDeltaCost =  0.0; // The cost.
	
	protected GroundedMarkovNetwork groundedMarkovNetwork;	
	// The active clauses at any point of time are marked on the groundClauses themselves.
	// An ACTIVE CLAUSE is either an unsatisfied clause with a positive weight or a satisfied clause with a negative weight.
	protected int                      maxNumberOfStarts = maxNumberOfStarts_default; // Maximum number of tries.
	protected int                      maxNumberOfFlips  = maxNumberOfFlips_default;  // Maximum number of flips in any given try.
	 
	protected int                      trial = 0;  // Count number of 'solves' performed.
	protected int                      flips = 0;  // Count number of 'flips'  performed.
	protected double                   priorProbOfBeingTrue = 0.5;
	
	protected boolean                  alwaysUseHashSetForActiveClauses = false; // Once true, stick with the hash set forever is this variable is set to true.
	protected boolean                  neverUseHashSetForActiveClauses  = false; // Ditto (of sorts).
		
	protected SAT() { // Used when LazySAT() invoked.
	}
	public SAT(GroundedMarkovNetwork groundedMarkovNetwork, double priorProbOfBeingTrue) {
		this.groundedMarkovNetwork = groundedMarkovNetwork;
		this.priorProbOfBeingTrue  = priorProbOfBeingTrue;
		if (groundedMarkovNetwork.getNumberOfGroundClauses()  < 1) { Utils.error("Have no ground clauses!");  }
		if (groundedMarkovNetwork.getNumberOfGroundLiterals() < 1) { Utils.error("Have no ground literals!"); }
	}
	public SAT(GroundedMarkovNetwork groundedMarkovNetwork, double priorProbOfBeingTrue, int maxNumberOfStarts, int maxNumberOfFlips) {
		this(groundedMarkovNetwork, priorProbOfBeingTrue);
		this.maxNumberOfStarts = maxNumberOfStarts;
		this.maxNumberOfFlips  = maxNumberOfFlips;
	}
	
	public int getStepsPerSample() {
		return maxNumberOfStarts * maxNumberOfFlips;
	}
	
	/**
	 * Start at a random position and initialize the activeClauses data structure.
	 */
	private boolean haveCalledInit = false;
	protected void init(Collection<GroundLiteral> markedLiterals, Collection<GroundClause> markedClauses, String msg, double probOfRandomStateDuringInit) {
		if (checkForBugsExtraHard && !haveCalledInit) { checkGroundClauseGroundLiteralConnections(); }
		TimeStamp timeStamp = (checkForBugs ? new TimeStamp(msg + "SATinit") : null);
		// Since we expect to have only a few active clauses to start, we'll use the hash table to start.
		if (neverUseHashSetForActiveClauses)  { switchOffActiveClauseHashSet("init", 0, groundedMarkovNetwork.getNumberOfGroundClauses()); }
		else                                  { switchToActiveClauseHashSet( "init", 0, groundedMarkovNetwork.getNumberOfGroundClauses()); }
		if (useGreedyInitialStates) {
			greedyStartPosition(markedLiterals, markedClauses, msg, timeStamp);
		}
		else {
			randomStartPosition(markedLiterals, markedClauses, msg, probOfRandomStateDuringInit, timeStamp);
		}
		if (debugLevel > -10 && reportFlagOn) { reportStatsSinceLastReport(msg); } // Periodically report statistics.
		if (checkForBugs && !checkStateOfAllClauses(timeStamp)) { Utils.error("Check out the mismatches above."); }	// TODO MOVE TO groundedMarkovNetwork and don't always call  TODO
		haveCalledInit = true;
	}

	// See if all the literals in each ground clause point back to the ground clause.  Return FALSE if something looks odd.
	public boolean checkGroundClauseGroundLiteralConnections() {
		int counter = 0;
        GroundClause gndClause = groundedMarkovNetwork.getFirstMarkedGroundClause();
        while (gndClause != null) {
			if (gndClause.getLength() > 0) for (int i = 0; i < gndClause.getLength(); i++) {
				GroundLiteral gLit = gndClause.getIthLiteral(i);
				if (!groundedMarkovNetwork.isaMarkedGroundLiteral(gLit)) {
					counter++;
					Utils.println("% MISMATCH #" + counter+ ": ground literal '" + gLit + "' is not marked but this clause is: " + gndClause);
					if (counter >= 100) { Utils.println("% Will not show any more mismatches."); return false; }
				}
				if (!gLit.getGndClauseSet().contains(gndClause)) {
					counter++;
					Utils.println("% MISMATCH #" + counter+ ": ground literal '" + gLit + "' does not point back to ground clause: " + gndClause);
					if (counter >= 100) { Utils.println("% Will not show any more mismatches."); return false; }
				}
			}
            gndClause = groundedMarkovNetwork.getNextMarkedGroundClause();
		}
		if (counter > 0) { Utils.error("Check out messages above."); }
		return (counter < 1);
	}
	// Return FALSE if something looks odd.
	public boolean checkStateOfAllClauses(TimeStamp timeStamp) {
		int counter = 0;
		TimeStamp newTimeStamp = (timeStamp == null ? null : new TimeStamp("checkStateOfAllClauses: " + timeStamp));
        GroundClause gndClause = groundedMarkovNetwork.getFirstMarkedGroundClause();
        while (gndClause != null) {
			boolean oldSat = gndClause.isSatisfiedCached();
			boolean newSat = gndClause.checkIfSatisfied(timeStamp);
			if (oldSat != newSat) { ++counter; Utils.println("% Current timestamp=" + newTimeStamp + "  MISMATCH #" + counter + ": oldSat/newSat = " + oldSat + "/"    + newSat +                                            "   " + gndClause.getInfo()); }
			if (gndClause.getWeightOnSentence() > 0.0 &&  newSat &&  gndClause.isActive()) { ++counter; Utils.println("% MISMATCH #" + counter + ": active (pos wgt) but sat="   + newSat + "   " + gndClause.getInfo()); }
			if (gndClause.getWeightOnSentence() < 0.0 && !newSat &&  gndClause.isActive()) { ++counter; Utils.println("% MISMATCH #" + counter + ": active (neg wgt) but sat=" + newSat + "   " + gndClause.getInfo()); }
			if (counter >= 100) { Utils.println("% Will not show any more mismatches."); return false; }
		    gndClause = groundedMarkovNetwork.getNextMarkedGroundClause();
        }
		return (counter < 1);
	}
	
	private boolean   deferred_updateActiveClauseInformation     = false; // Mark that this last call to updateActiveClauseInformation was 'speculative' and should not be done unless necessary (e.g., when the next add/remove of 'active' happens).
	private String    deferred_updateActiveClauseInformation_msg = null;
	private TimeStamp deferredTimeStamp                          = null;
	// TODO on the last call, we might only care to know how many clauses are active (i.e., no need to add to a hash table).
	//      maybe use a diff version that simply does this count if requested?
	private void updateActiveClauseInformation(Collection<GroundClause> markedClauses, String msg, TimeStamp timeStamp, boolean doRightNow) {
		clearActiveClauseState(); // Recover any memory used, even if doRightNow=false;
		if (!doRightNow) { 
			if (debugLevel > 1) { Utils.println("& DEFERRING an update of active-clause information: " + msg); }
			if (deferred_updateActiveClauseInformation) { Utils.error("Two deferred_updateActiveClauseInformation's in a row!"); }
			deferred_updateActiveClauseInformation     = true; 
			deferred_updateActiveClauseInformation_msg = msg; 
			deferredTimeStamp                          = timeStamp;
			return; 
		}
		if (debugLevel > 1) { Utils.println("\n% " + (deferred_updateActiveClauseInformation ? "Deferred: " : "") + msg + " Update settings for grounded clauses."); }
		deferred_updateActiveClauseInformation     = false;
		deferred_updateActiveClauseInformation_msg = null;
		deferredTimeStamp                          = null;
		int marked    = 0;
		int actives   = 0;
		int inactives = 0;
		
        GroundClause           gndClause = null;
        Iterator<GroundClause> iterator  = null;
        boolean                useMarked = (markedClauses == null);
        if (useMarked) {                           gndClause = groundedMarkovNetwork.getFirstMarkedGroundClause(); }
        else {iterator = markedClauses.iterator(); gndClause = (iterator.hasNext() ? iterator.next() : null);      } 
        while (gndClause != null) {
			if (debugLevel > 1 && marked < 10) { Utils.print("       " + gndClause.getInfo() + "  "); }
			marked++;
			double weight = gndClause.getWeightOnSentence();
			// Initialize the activeClauses list.   Notice here we call isSatisfied() so we will recompute the truth values of all ground clauses.
			boolean isSat = gndClause.checkIfSatisfied(timeStamp);
			markInactiveClause(gndClause);
			// if (debugLevel > 1) Utils.print("%SAT: Clause: " + gndClause.getInfo());
			if      (!isSat && weight > 0) {   actives++; addToActiveClauses(gndClause, markedClauses); if (debugLevel > 1) { Utils.println("ACTIVE (unsat)"); }}
			else if ( isSat && weight < 0) {   actives++; addToActiveClauses(gndClause, markedClauses); if (debugLevel > 1) { Utils.println("ACTIVE (sat)");   }}
			else                           { inactives++;                                               if (debugLevel > 1) { Utils.println("INACTIVE (" + (isSat ? "sat" : "unsat") + ")."); }}
			if (useMarked) { gndClause = groundedMarkovNetwork.getNextMarkedGroundClause(); }
			else {gndClause = (iterator.hasNext() ? iterator.next() : null); }
		}
		countOfAdds      -= actives; // Don't count these INITIAL adds.
		totalCountOfAdds -= actives;
		if (countOfAdds < 0) { Utils.error("Have countOfAdds < 0!"); }
		if (debugLevel > -11 && reportFlagOn) { Utils.println("%   After updateActiveClauseInformation (marked=" + Utils.comma(marked) + "): There currently are " + Utils.comma(countOfActiveClauses) + " active clauses (out of " + Utils.comma(marked) + "), with a weighted sum of " + Utils.truncate(activeClausesSum, 2) + "."); }
		if (actives != countOfActiveClauses) { Utils.error("actives [" + Utils.comma(actives) + "] != countOfActiveClauses [" + Utils.comma(countOfActiveClauses) + "]."); }
		if (marked < 1) { Utils.error("There are no marked clauses!  countOfMarkedGroundClauses="  + Utils.comma(groundedMarkovNetwork.countOfMarkedGroundClauses())); }
		if (debugLevel > 1) { Utils.println(""); }	
	}
	
	// Note: this leaves things in an inconsistent state, which is OK since the next thing that should happen is an init(). 
	protected void doBookkeepingAtEndOfSample(Collection<GroundLiteral> markedLiterals, Collection<GroundClause> markedClauses, String msg, boolean reportFlagOn, TimeStamp timeStamp) {
		if (useActiveClausesHashSet) {	activeClauses.clear(); }
		if (markedClauses == null) { // Need to walk through all clauses in this case.
			GroundClause gndClause = groundedMarkovNetwork.getFirstMarkedGroundClause();
			while (gndClause != null) { 
				gndClause.setMarker(null);
				gndClause = groundedMarkovNetwork.getNextMarkedGroundClause();
			}
		} else for (GroundClause gndClause : markedClauses) { gndClause.setMarker(null); } 
		if (markedLiterals == null) {
			GroundLiteral gndLiteral = groundedMarkovNetwork.getFirstMarkedGroundLiteral();
			while (gndLiteral != null) { 
				gndLiteral.setMarker(null);
				gndLiteral = groundedMarkovNetwork.getNextMarkedGroundLiteral();
			}
		} else for (GroundLiteral gLit : markedLiterals)  { gLit.setMarker(null); }
	}
	
	// The next group manages adding/removing from activeClauses.
	
	// We don't, in the default case, keep a list of active clauses since adding/removing to that can be time consuming.
	// The cost of this design decision is that when we need a random active clause, we need to spend a good deal of time
	// if they are rare.  If we have troubles, we will switch to the HashSet variant.
	public    int  maxTriesAtGettingActiveClause   = 1000;  // If ever get this many inactive clauses in a row, give up on the default strategy.
	public    int  maxTriesAtGettingActiveLiteral  = 1000;  // If ever get this many inactive literal in a row,throw an error.
	private   long failuresAtGettingActiveClause   = 0; // if this becomes too extreme, switch to keeping explicit hashSets. 
	private   long successessAtGettingActiveClause = 0;
	protected int  countOfActiveClauses            = 0;
	protected int  last_countOfActiveClauses       = 0;
	private   int  countOfAdds                     = 0; // This is only done PER init, so no need for a 'long.'
	private   int  countOfRemoves                  = 0;
	private   long totalCountOfAdds                = 0;
	private   long totalCountOfRemoves             = 0;
	private   double   activeClausesSum            = 0.0;
	private   long     usedHashSetCount            = 0;
	private   int      turnedOnHashSetCount        = 0;
	private   boolean  useActiveClausesHashSet     = true; // Usually it makes sense to start using this (it trades off space for improved time).
	private   Set<GroundClause> activeClauses;	

	private long hold_failuresAtGettingActiveClause   = -1;
	private long hold_successessAtGettingActiveClause = -1;
	private int  countOfReports = 0;
	private void reportStatsSinceLastReport(String msg) {
		long deltaFailures  = failuresAtGettingActiveClause   - hold_failuresAtGettingActiveClause;
		long deltaSuccesses = successessAtGettingActiveClause - hold_successessAtGettingActiveClause;
		hold_failuresAtGettingActiveClause   = failuresAtGettingActiveClause;
		hold_successessAtGettingActiveClause = successessAtGettingActiveClause;
		
		if (deltaFailures > failuresAtGettingActiveClause) { return; } // This is the first init().
		if (++countOfReports % 10 != 0) { return; }
		Utils.println("\n% There currently are " + Utils.comma(countOfActiveClauses) + " active clauses with a weighted sum of " + Utils.truncate(activeClausesSum, 2) + ".");
		Utils.println(  "%  Since the last report, there were " + Utils.comma(countOfAdds) + " adds and " + Utils.comma(countOfRemoves) + " removals from the active-clause list.");
		Utils.println(  "%  In total, there were " + Utils.comma(totalCountOfAdds) + " adds and " + Utils.comma(totalCountOfRemoves) + " removals from the active-clause list.");
		if (useActiveClausesHashSet) { Utils.println("%  Currently using a hash table of size " + Utils.comma(activeClauses) + " to store the active clauses." + (turnedOnHashSetCount > 1 ? "  It has been turned off and back on " + Utils.comma(turnedOnHashSetCount - 1) + " times." : "")); }
		if (usedHashSetCount > 0)    { Utils.println("%  Have used the hash table " + Utils.comma(usedHashSetCount) + " times to get a random active clause."); }
		if (deltaSuccesses + deltaFailures > 0) {
			Utils.println("%  Also, since the last report, there were " + Utils.comma(deltaSuccesses) +
							" successful random attempts to get an active clause\n%  and " + Utils.comma(deltaFailures) +
							" failed attempts, so successful 1 in " + Utils.truncate((deltaFailures + deltaSuccesses) / (double)deltaSuccesses, 2) + " tries.");
		}
		if (failuresAtGettingActiveClause + successessAtGettingActiveClause > 0) {
			Utils.println("%  Overall there were " + Utils.comma(successessAtGettingActiveClause) +
							" successful random attempts to get an active clause\n%  and " + Utils.comma(failuresAtGettingActiveClause) +
							" failed attempts, so successful 1 in " + Utils.truncate((successessAtGettingActiveClause + failuresAtGettingActiveClause) / (double)successessAtGettingActiveClause, 2) + " tries.");
		}
		countOfAdds    = 0;
		countOfRemoves = 0;	
		int errors = 0;
		if (countOfActiveClauses < 0) {
			errors++;
			Utils.println("Should not have a NEGATIVE count of active clauses: " + Utils.comma(countOfActiveClauses) + ".");
		}
		TimeStamp timeStamp = (checkForBugs ? new TimeStamp("reportStatsSinceLastReport: " + (msg == null ? "" : msg)) : null);
		errors += (checkStateOfAllClauses(timeStamp) ? 0 : 1);
		if (errors > 0) {
			Utils.error("Aborting due to the above errors.");
		}
	}
	
	protected void clearAllMarkedClauses() {
		if (useActiveClausesHashSet) {
			
		}
	}
	
	
	protected void clearActiveClauseState() {
		activeClausesSum   = 0.0;
		last_countOfActiveClauses = countOfActiveClauses; // In case some caller wants to print the final count.
		countOfActiveClauses = 0;  // Still count regardless of whether or not a hard table is in use, since cheap to do so, plus good for error checking,
		if (activeClauses != null) { activeClauses.clear(); }
		if (useActiveClausesHashSet) {
			if (activeClauses == null) { activeClauses = new HashSet<GroundClause>(1024); }
			if (useActiveClausesHashSet && countOfActiveClauses != activeClauses.size()) {
				Utils.error("Have a mismatch between countOfActiveClauses = " + Utils.comma(countOfActiveClauses) +
							" and |activeClauses| = " + Utils.comma(activeClauses) + ".");
			}
			activeClauses.clear();
		}
		if (!neverUseHashSetForActiveClauses && !useActiveClausesHashSet && // See if the random access is not working very well.
				(failuresAtGettingActiveClause - successessAtGettingActiveClause) > 100000 && 
				(1000 * successessAtGettingActiveClause < failuresAtGettingActiveClause)) { 
			Utils.println("\n% Switching permanently to using hash tables for active clauses.  Success rate of randomly grabbing an active clause:  1 in " 
							+ Utils.truncate((failuresAtGettingActiveClause + successessAtGettingActiveClause) / (double)successessAtGettingActiveClause, 2) + ".");
			switchToActiveClauseHashSet( "clearActiveClauseStateA", countOfActiveClauses, groundedMarkovNetwork.getNumberOfGroundClauses());
			alwaysUseHashSetForActiveClauses = true;
		}
	}
	protected void addToActiveClauses(GroundClause gndClause, Collection<GroundClause> markedClauses) {
		if (deferred_updateActiveClauseInformation) { updateActiveClauseInformation(markedClauses, deferred_updateActiveClauseInformation_msg, deferredTimeStamp, true); }
		if (!groundedMarkovNetwork.isaMarkedGroundClause(gndClause))                     { Utils.error("This clause is not properly marked (active=" + gndClause.isActive() + ",useActiveClausesHashSet=" + useActiveClausesHashSet + "): '" + gndClause.getInfo() + "'."); }
		if (gndClause.isActive() == true  || (useActiveClausesHashSet && !activeClauses.add(gndClause))) { Utils.error("Is already an active clause (active="        + gndClause.isActive() + ",useActiveClausesHashSet=" + useActiveClausesHashSet + "): '" + gndClause.getInfo() + "'."); }
		countOfActiveClauses++; // Still count regardless, since cheap to do so.
		activeClausesSum += gndClause.getWeightOnSentence();
		countOfAdds++; totalCountOfAdds++;
		if ( gndClause.isSatisfiedCached() && gndClause.getWeightOnSentence() > 0.0) { Utils.error("Setting active a pos-wgt clause that is satisfied: " + gndClause.getInfo()); }
		if (!gndClause.isSatisfiedCached() && gndClause.getWeightOnSentence() < 0.0) { Utils.error("Setting active a neg-wgt clause that is satisfied: " + gndClause.getInfo()); }
		if (debugLevel > 2 && haveCalledInit) { Utils.println("% Setting active=true for " + gndClause.getInfo()); }
		gndClause.setActive(true);
	}
	protected void removeFromActiveClauses(GroundClause gndClause, Collection<GroundClause> markedClauses) {
		if (deferred_updateActiveClauseInformation) { updateActiveClauseInformation(markedClauses, deferred_updateActiveClauseInformation_msg, deferredTimeStamp, true); }
		if (!groundedMarkovNetwork.isaMarkedGroundClause(gndClause)) { Utils.error("This clause is not properly marked (active=" + gndClause.isActive() + ",useActiveClausesHashSet=" + useActiveClausesHashSet + "): '" + gndClause.getInfo() + "'."); }
		if (gndClause.isActive() == false || (useActiveClausesHashSet && !activeClauses.remove(gndClause))) { Utils.error("Could not remove since not an active clause (active=" + gndClause.isActive() + ",useActiveClausesHashSet=" + useActiveClausesHashSet + "): '" + gndClause.getInfo() + "'"); } 
		countOfActiveClauses--; // Still count regardless of using the HashSet, since cheap to do so.
		activeClausesSum -= gndClause.getWeightOnSentence();
		countOfRemoves++; totalCountOfRemoves++;
		if (!gndClause.isSatisfiedCached() && gndClause.getWeightOnSentence() > 0.0) { Utils.error("Setting inactive a pos-wgt clause that is not satisfied: " + gndClause.getInfo()); }
		if ( gndClause.isSatisfiedCached() && gndClause.getWeightOnSentence() < 0.0) { Utils.error("Setting inactive a neg-wgt clause that is satisfied: " + gndClause.getInfo()); }
		if (debugLevel > 2) { Utils.println("% Setting active=false for " + gndClause.getInfo()); }
		gndClause.setActive(false);
	}
	protected void markInactiveClause(GroundClause gndClause) {
		gndClause.setActive(false);
	}
	int onOffCounter = 0;
	private void switchToActiveClauseHashSet(String caller, int countOfActiveClauses, int size) {
		if (neverUseHashSetForActiveClauses) { Utils.error("Should not reach here with neverUseHashSetForActiveClauses=true"); }
		if (useActiveClausesHashSet) { return; }
		Utils.println("%      Turn ON  hash table for SAT.  [caller=" + caller + ",  count of active clauses = " + Utils.comma(countOfActiveClauses) + ", size = " + Utils.comma(size) + "]"); if (++onOffCounter > 1) { Utils.error("Too many turn ONs!"); }
		useActiveClausesHashSet = true;
		if (activeClauses == null) { activeClauses = new HashSet<GroundClause>(1024); }
		activeClauses.clear();
		if (countOfActiveClauses > 0)  {
			// Now fill the active clauses set.
			GroundClause gndClause = groundedMarkovNetwork.getFirstMarkedGroundClause();
			while (gndClause != null) {
				if (gndClause.isActive()) { activeClauses.add(gndClause); }
				gndClause = groundedMarkovNetwork.getNextMarkedGroundClause();
			}
        }
		if (countOfActiveClauses != activeClauses.size()) { Utils.error("countOfActiveClauses != |activeClauses|  " + Utils.comma(countOfActiveClauses) + " vs. " + Utils.comma(activeClauses)); }
	}
	private void switchOffActiveClauseHashSet(String caller, int countOfActiveClauses, int size) {
		if (alwaysUseHashSetForActiveClauses) { Utils.error("Should not reach here with alwaysUseHashSetForActiveClauses=true"); }
		if (!useActiveClausesHashSet|| alwaysUseHashSetForActiveClauses) { return; }
		Utils.println("%      Turn OFF hash table for SAT.  [caller=" + caller + ",  count of active clauses = " + Utils.comma(countOfActiveClauses) + ", size = " + Utils.comma(size) + "]"); if (--onOffCounter < 0) { Utils.error("Too many turn OFFs!"); }
		useActiveClausesHashSet = false;
		if (activeClauses == null) { activeClauses = new HashSet<GroundClause>(1024); } // Shouldn't be necessary, but leave it here.
		activeClauses.clear();
	}
	
	/** 
	 * Uniformly select at random an active clause, and return it.
	 * 
	 * @return Returns a random active clause.  Returns null if there is no such clause.
	 */
	protected GroundClause getActiveClauseRandomly(Collection<GroundClause> markedClauses, TimeStamp timeStamp) {
		if (deferred_updateActiveClauseInformation) { updateActiveClauseInformation(markedClauses, deferred_updateActiveClauseInformation_msg, timeStamp, true); }
		if (debugLevel > 3) { Utils.println("% getActiveClauseRandomly: countOfActiveClauses=" + countOfActiveClauses); }
		if (countOfActiveClauses < 1) { return null; }
		int size = groundedMarkovNetwork.getNumberOfGroundClauses(); // TODO rethink these numbers for when a hash table should be used.
		if (!alwaysUseHashSetForActiveClauses && useActiveClausesHashSet && 10 * countOfActiveClauses > size  && size > 1000000 && size < 10000000) {
			// If using a large hash set, but the actives have grown to be more than 10% of all clauses, switch back.  Also make sure the size is big enough that we don't want to store all of them (but not too big).
			switchOffActiveClauseHashSet("getActiveClauseRandomly_HashtableButActiveClausesLarge", countOfActiveClauses, size);
			return getActiveClauseRandomly(markedClauses, timeStamp);
		}
		// Don't turn back on too often, since costly to rebuild the actives hash table.
		if (!neverUseHashSetForActiveClauses && !useActiveClausesHashSet && 100 * countOfActiveClauses < size && size > 1000000 && size < 10000000) {
			// If not using the hash set, but the actives have shrunk to be less than 1% of all clauses, switch to the hash table (unless the size is really huge; in that case, we don't want to spend the space).
			switchToActiveClauseHashSet("getActiveClauseRandomly_NoHashtableButActiveClausesTooSmall", countOfActiveClauses, size);
			return getActiveClauseRandomly(markedClauses, timeStamp);
		}
		
		if (useActiveClausesHashSet) {
			usedHashSetCount++;
			return checkSelectedActiveClause(Utils.chooseRandomFromThisCollection(activeClauses), timeStamp, true);
		}
		int counter = 0; // Could start at a random location, then walk though until an active clause hit, but that would be a biased sample (e.g., an active clause that has N inactive clauses before it would have more chances the larger N is).
		int limit = Math.min(size + 100, maxTriesAtGettingActiveClause);
		while (counter++ <= limit) {
			GroundClause gndClause = groundedMarkovNetwork.getRandomGroundClause();
			if (groundedMarkovNetwork.isaMarkedGroundClause(gndClause) && gndClause.isActive()) {
				successessAtGettingActiveClause++; 
				return checkSelectedActiveClause(gndClause, timeStamp, false);
			}
			failuresAtGettingActiveClause++;
		}
		// If sampling fails, switch to the hash table.
		switchToActiveClauseHashSet("getActiveClauseRandomly_TooManyRandomSamples", countOfActiveClauses, groundedMarkovNetwork.getNumberOfGroundClauses());
		return getActiveClauseRandomly(markedClauses, timeStamp);
	}
	private GroundClause checkSelectedActiveClause(GroundClause gndClause, TimeStamp timeStamp, boolean usingHashSet) {
		boolean wasWarned = false;
		if (deferred_updateActiveClauseInformation) {  wasWarned = true; Utils.warning("Should not have deferred_updateActiveClauseInformation=" + deferred_updateActiveClauseInformation + " here."); }
		if (!gndClause.isActive())                  {  wasWarned = true; Utils.warning("Should not reach here with an inactive clause!"); }
		if ((gndClause.getWeightOnSentence() > 0 &&  gndClause.isSatisfiedCached()) ||
			(gndClause.getWeightOnSentence() < 0 && !gndClause.isSatisfiedCached())) {
			boolean oldSat = gndClause.isSatisfiedCached();
			boolean newSat = gndClause.checkIfSatisfied(timeStamp);
			if (checkForBugsExtraHard && checkStateOfAllClauses(timeStamp)) { wasWarned = true; }
			Utils.error("This" + (gndClause.getWeightOnSentence() > 0 ? " pos-wgt" : " neg-wgt") + " clause is considered active, but doesn't seem to be: [usingHashSet=" + 
						usingHashSet + ",wasSatCached=" + oldSat + ",isSatCached=" + newSat + "]   " + gndClause.getInfo()); 
		}
		if (wasWarned) { Utils.error("Need to address the warnings above."); }
		return gndClause;
	}
	
	////////////////////////////////////////////////////////////////////////////////////////////////////////////
	
	protected void reportActiveClausesState() {
		Utils.println("\n% The state of the variables:");
		groundedMarkovNetwork.reportGroundLiteralState(25);
		Utils.println("\n% The state of the active clauses:" + (countOfActiveClauses < 1 ? " none." : ""));
		if (countOfActiveClauses > 0) {
			GroundClause gndClause = groundedMarkovNetwork.getFirstMarkedGroundClause();
			while (gndClause != null) {
				double weight = gndClause.getWeightOnSentence();
				Utils.print("%    " + gndClause.getInfo() + "  "); 
				if      (!gndClause.isSatisfiedCached() && weight > 0) { Utils.println("ACTIVE (unsat)"); }
				else if ( gndClause.isSatisfiedCached() && weight < 0) { Utils.println("ACTIVE (sat)");   }
				else    { Utils.println("INACTIVE (" + (gndClause.isSatisfiedCached() ? "sat" : "unsat") + ")."); }
				gndClause = groundedMarkovNetwork.getNextMarkedGroundClause();
			}
        }
	}
	
	private void helpStartPosition() {
		// Clear any deferred updates, since all will be reset and then an update called.
		deferred_updateActiveClauseInformation     = false;
		deferred_updateActiveClauseInformation_msg = null;
		deferredTimeStamp                          = null;
	}
	
	/**
	 * Random truth assignments for the literals.
	 */
	private void randomStartPosition(Collection<GroundLiteral> markedLiterals, Collection<GroundClause> markedClauses, String msg, double probOfRandomStateDuringInit, TimeStamp timeStampOfCaller) {
		helpStartPosition();
		if (debugLevel > 1) { Utils.println("\n% Initial variable settings."); }
		// TODO - handle blocks
		TimeStamp timeStamp = (GroundedMarkovNetwork.doMajorDebug 
								? new TimeStamp("SAT:randomStartPosition " + (timeStampOfCaller == null ? "" : timeStampOfCaller))
								: null);
		if (groundedMarkovNetwork.getAllBlocks() != null) { // Handle the examples in blocks.  ADD MARKERS TO BLOCKS?  NO, since marking literals does it for us?
			Utils.writeMe("TODO - handle blocks");
			Set< Entry<GroundLiteral,Block>> blockSet = groundedMarkovNetwork.getAllBlocks().entrySet();
			for (Entry<GroundLiteral,Block> entry : blockSet) {
				Block block = entry.getValue();		
				block.setRandomValues(timeStamp); // Randomly choose one of the possible states.
			}
		}
		// Handle the literals NOT in blocks.  Set each one randomly.
        GroundLiteral           gLit     = null;
        Iterator<GroundLiteral> iterator = null;
        boolean                 useMarked = (gLit == null);
        if (useMarked) {                             gLit = groundedMarkovNetwork.getFirstMarkedGroundLiteral(); }
        else { iterator = markedLiterals.iterator(); gLit = (iterator.hasNext() ? iterator.next() : null);       }
		while (gLit != null) {
			if (gLit.getBlock() == null) { 
				if (Utils.random() <= probOfRandomStateDuringInit)  { // Only randomize those that are marked and limit the number that are flipped.
					gLit.setValueOnly(Utils.random() < priorProbOfBeingTrue, timeStamp);
					if (debugLevel > 2) { Utils.println("%    " + gLit + " = " + gLit.getValue()); }
				}
			} else { Utils.waitHere("Has the code for blocks() been checked?"); }
			if (useMarked) { gLit = groundedMarkovNetwork.getNextMarkedGroundLiteral(); }
			else { gLit = (iterator.hasNext() ? iterator.next() : null); }
		}				
		updateActiveClauseInformation(markedClauses, msg, timeStamp, true);
	}
	/**
	 * Set all the literals to their preferred truth value, disregarding all the other literals.
	 * (I.e., see if weighted sum more when it is a positive literal or when it is a negative literal.)
	 * @param msg
	 * @param timeStampOfCaller
	 */
	private void greedyStartPosition(Collection<GroundLiteral> markedLiterals, Collection<GroundClause> markedClauses, String msg, TimeStamp timeStampOfCaller) {
		// Greedily set all literals to their best truth value independent of all others.
		// TODO - handle blocks
		helpStartPosition();
		TimeStamp timeStamp = (GroundedMarkovNetwork.doMajorDebug 
								? new TimeStamp("SAT:greedyStartPosition " + (timeStampOfCaller == null ? "" : timeStampOfCaller))
								: null);
        GroundLiteral           gLit     = null;
        Iterator<GroundLiteral> iterator = null;
        boolean                 useMarked = (markedLiterals == null);
        if (useMarked) {                             gLit = groundedMarkovNetwork.getFirstMarkedGroundLiteral(); }
        else { iterator = markedLiterals.iterator(); gLit = (iterator.hasNext() ? iterator.next() : null);       }
		while (gLit != null) {
			double sumIfPos = 0.0;
			double sumIfNeg = 0.0;
			for (GroundClause gndClause : gLit.getGndClauseSet()) {
				if (gndClause.isaPosLiteral(gLit)) { sumIfPos += gndClause.getWeightOnSentence(); }
				else                               { sumIfNeg += gndClause.getWeightOnSentence(); }
			}
			gLit.setValue(sumIfPos >= sumIfNeg, null, timeStamp);
			if (gLit.getBlock() != null) { Utils.waitHere("Has the code for blocks() been checked?"); }
			if (useMarked) { gLit = groundedMarkovNetwork.getNextMarkedGroundLiteral(); }
			else { gLit = (iterator.hasNext() ? iterator.next() : null); }
		}
		updateActiveClauseInformation(markedClauses, msg, timeStamp, true);
	}
	
	/**
	 * Find the best assignment of truth values to the literals.
	 */
	// If markedClauses = null, that means 'check all clauses' (ie, the set is too big to copy).  But if the caller has a small subset, it can explicitly provide that.	
	public abstract int solve(Collection<GroundLiteral> markedLiterals, Collection<GroundClause> markedClauses, boolean report); // Return number of steps taken.
		
	/**
	 * Computes the change in cost if a particular literal is flipped.
	 * 
	 * @param literalToFlip The literal under consideration
	 * @return Returns an array of two doubles. The first value is the change in cost. 
	 * The second value is the otherIndexToFlip (if necessary, due to block constraints). Else the second value is -1.
	 */
	protected void computeDeltaCost(GroundLiteral literalToFlip) {
		result1_computeDeltaCost = -1; // If dealing with a block, need to turn off this item.
		Block block = literalToFlip.getBlock();
		if (literalToFlip.getBlock() == null) {
			Set<GroundClause> clauseList = literalToFlip.getGndClauseSet();
			if (Utils.getSizeSafely(clauseList) < 1) { Utils.error("The clause list should not be empty for '" + literalToFlip + "'."); }
	 		
			result0_computeDeltaCost = 0; 		
	 		for (GroundClause gndClause : clauseList) if (groundedMarkovNetwork.isaMarkedGroundClause(gndClause)) { // Look at all the clauses involving this literal. Sum impacts of the flip.			
	 			double delta = gndClause.deltaCostIfFlip(literalToFlip);
	 			if (debugLevel > 2) { Utils.println("%   Delta cost = " + Utils.truncate(delta, 3) + " by flipping '" + literalToFlip + "' to " + !literalToFlip.getValue() + " in '" + gndClause + "'."); }
	 			result0_computeDeltaCost += delta; 
	 		}
	 		return;
		} else {	
			Utils.writeMe("Have not yet fixed the BLOCK code?");
			int otherIndexToFlip = -1;
			if (block.valuesFixed()) { // Cannot change this block, so nothing to do.
				result0_computeDeltaCost = 0.0;
				return;
			}
			int   n                  = block.getNumTrueLiterals();   // Current number of true literals (might be less than maximum for 'at-most k' case).
			int   size               = block.getSize();              // The number of items in the block.
			int   literalToFlipIndex = block.indexOf(literalToFlip); // Record location of the passed-in literal.
			
			if (block.isExactly() || (!literalToFlip.getValue() && n >= block.getK())) { // See if need to maintain "exactly k are true" or are at the maximum number of literals in this block that can be true (use >= instead of == for robustness).
				// A different ground literal in the block has to be flipped to satisfy the block constraint.
				if (randFlipInBlock) { // Randomly choose another literal to flip on.
					int turnOnIndex  = 0;
					int turnOffIndex = 0;
					
					if (literalToFlip.getValue()) { // If the literalToFlip is TRUE, randomly choose one of the (size-k) false literals with uniform probability.
						otherIndexToFlip = Utils.random1toN(size - n);
						// Need to find the 'otherIndexToFlip'-th item that is FALSE.
						// E.g., if otherIndexToFlip = 5 and items 1 and 4 are already TRUE, then we need to use the 7th item.
						for (int i = 0; i < size; i++) {
							if (block.isTrue(i)) { otherIndexToFlip++; }
						}					
						turnOnIndex      = otherIndexToFlip;
						turnOffIndex     = literalToFlipIndex;
					} else { // Otherwise choose an item that is already true and turn it off.
						otherIndexToFlip = block.getCurrentTrueIndices()[ Utils.random1toN(n)];
						turnOnIndex      = literalToFlipIndex;
						turnOffIndex     = otherIndexToFlip;
					}			
					
					double deltaCost = computeDeltaCostInBlock(block, turnOnIndex, turnOffIndex);			
					result0_computeDeltaCost = deltaCost;
					result1_computeDeltaCost = otherIndexToFlip;
					return;
				} else { // Choose the otherIndexToFlip in a greedy way - the one which gives the best deltaCost.
					result0_computeDeltaCost = Double.POSITIVE_INFINITY;
					if (literalToFlip.getValue()) {	// If the literal to flip is ON, look at all OFF literals and find best scorer.				
						for (int i = 0; i < size; i++) if (!block.isTrue(i)) {
							double deltaCost = computeDeltaCostInBlock(block, i, literalToFlipIndex);
							if (deltaCost < result0_computeDeltaCost) {
								result0_computeDeltaCost = deltaCost;
								result1_computeDeltaCost = i;
							}
						}
					} else { // If the literal to flip is OFF, look at all ON literals and find best scorer.
						for (int i = 0; i < n; i++) { // Slightly faster than walking through the full list. 
							int currTrueIndex = block.getCurrentTrueIndicesUnsafe()[i]; // OK to be unsafe, since won't walk pass nth item.
							double deltaCost = computeDeltaCostInBlock(block, literalToFlipIndex, currTrueIndex);
							if (deltaCost < result0_computeDeltaCost) {
								result0_computeDeltaCost = deltaCost;
								result1_computeDeltaCost = currTrueIndex;
							}
						}
					}
					return;
				}			
			} else { // Have not yet reached the maximum number of ON literals.  So flip the current literal and calculate cost of doing so.
				Set<GroundClause> clauseList = literalToFlip.getGndClauseSet();
				if (clauseList == null) { Utils.error("Error (bug in code): The clause list should not be empty.");	}
		 		
				double deltaCost = 0; 		
		 		for (GroundClause gndClause : clauseList) if (groundedMarkovNetwork.isaMarkedGroundClause(gndClause)) { 			
		 			deltaCost += gndClause.deltaCostIfFlip(literalToFlip);
		 		}
		 		result0_computeDeltaCost = deltaCost;
			}			
		}		
	}
	
	private double computeDeltaCostInBlock(Block block, int turnOnIndex, int turnOffIndex) {		
		double deltaCost = 0;
		// This is written in a "wordy" form so that there isn't a need to create a NEW set of ground clauses (i.e., the UNION of both).
		// Note: this means that we need to avoid double counting.
		Set<GroundClause> clausesToConsider1 = block.getGndLiterals().get(turnOnIndex ).getGndClauseSet();
		Set<GroundClause> clausesToConsider2 = block.getGndLiterals().get(turnOffIndex).getGndClauseSet();
		if (clausesToConsider1 == null || clausesToConsider2 == null) { Utils.error("Have a literal without a clause set!"); }
		for (GroundClause gndClause : clausesToConsider1) if (groundedMarkovNetwork.isaMarkedGroundClause(gndClause)) { 
			deltaCost += gndClause.deltaCostIfBlockFlip(block, turnOnIndex, turnOffIndex);
		}
		// Be sure to check for clauses in which BOTH items appear.  Count these only ONCE (i.e., in the above for-loop).
		for (GroundClause gndClause : clausesToConsider2) if (groundedMarkovNetwork.isaMarkedGroundClause(gndClause) && !clausesToConsider1.contains(gndClause)) {
			deltaCost += gndClause.deltaCostIfBlockFlip(block, turnOnIndex, turnOffIndex);
		}		
		return deltaCost;
	}
	
	/**
	 * Actually flip the ground literal, and update activeClauses.
	 * 
	 * @param gLit
	 */
	protected void flipLiteral(GroundLiteral gLit, Collection<GroundClause> markedClauses, int otherIndexToFlip, TimeStamp timeStamp) {
		Block block = gLit.getBlock();
		if (otherIndexToFlip == -1) { // No need to flip another literal.
			Set<GroundClause> clauseList = gLit.getGndClauseSet();
			if (debugLevel > 2) { Utils.println("\n% Will flip '" + gLit + "' from '" + gLit.getValue() +  "'; it is in " + Utils.comma(clauseList) + " ground clauses."); }
			if (clauseList == null) { Utils.error("Error (Bug in code): The clause list should not be empty."); }
	 		if (block != null) { 
	 			int index = block.indexOf(gLit);
	 			if (gLit.getValue()) { block.turnOff(index, timeStamp); } 
	 			else                 { block.turnOn( index, timeStamp); }
	 		}
	 		gLit.flipFinal(groundedMarkovNetwork, timeStamp);		 		
	 		for (GroundClause currClause : clauseList) if (groundedMarkovNetwork.isaMarkedGroundClause(currClause)) { 			
	 			double deltaCost = -currClause.deltaCostIfFlip(gLit); // Since have just done this flip, we NEGATE here.
	 			if (debugLevel > 0 && deltaCost != 0.0) { Utils.println("%    " + (deltaCost > 0.0 ? "ACTIVATE" : "DEACTIVATE") + " deltaCost = " + Utils.truncate(deltaCost, 2) + " for " + currClause.getInfo() + "."); }
	 			// When the satisfiability of a clause is unchanged (or its weight = 0), deltaCost = 0.
	 			// If weight is < 0 and it BECOMES   satisfied, deltaCost will be POSITIVE.
	 			// If weight is > 0 and it BECOMES unsatisfied, deltaCost will be POSITIVE.
	 			//   - in both of the above case, the clauses meets the definition of being an ACTIVE CLAUSE.
	 			if      (deltaCost > 0.0) { addToActiveClauses(     currClause, markedClauses); } 
	 			// If weight is < 0 and it BECOMES unsatisfied, deltaCost will be NEGATIVE.
	 			// If weight is > 0 and it BECOMES   satisfied, deltaCost will be NEGATIVE.
	 			else if (deltaCost < 0.0) { removeFromActiveClauses(currClause, markedClauses); }
	 		}		
		} else {
			if (block.valuesFixed()) { Utils.writeMe("Should not chose literals that cannot be flipped."); return; } // Cannot change anything.			
			int literalIndex = block.indexOf(gLit);		
			int turnOnIndex;
			int turnOffIndex;
			if (gLit.getValue()) { // See if literal is true.  If so, turn if OFF.				
				turnOnIndex  = otherIndexToFlip;
				turnOffIndex = literalIndex;
			} else {				
				turnOnIndex  = literalIndex;
				turnOffIndex = otherIndexToFlip;
			}
			block.flipFinal(turnOnIndex, turnOffIndex, groundedMarkovNetwork, timeStamp);
			Set<GroundClause> affectedClauses1 = block.getGndLiterals().get(turnOnIndex ).getGndClauseSet();
			Set<GroundClause> affectedClauses2 = block.getGndLiterals().get(turnOffIndex).getGndClauseSet();
			for (GroundClause currClause : affectedClauses1) if (groundedMarkovNetwork.isaMarkedGroundClause(currClause))  {
				double deltaCost = -currClause.deltaCostIfBlockFlip(block, turnOnIndex, turnOffIndex); // Since have just done this flip, we NEGATE here.
				// See comments above for the reason for adding or removing.
				if      (deltaCost > 0.0) { addToActiveClauses(     currClause, markedClauses); }
				else if (deltaCost < 0.0) { removeFromActiveClauses(currClause, markedClauses); }
			}
			// Be sure to not double count.
			for (GroundClause currClause : affectedClauses2) if (groundedMarkovNetwork.isaMarkedGroundClause(currClause) && !affectedClauses1.contains(currClause))  {
				double deltaCost = currClause.deltaCostIfBlockFlip(block, turnOnIndex, turnOffIndex);
				if      (deltaCost > 0.0) { addToActiveClauses(     currClause, markedClauses); }
				else if (deltaCost < 0.0) { removeFromActiveClauses(currClause, markedClauses); }
			}
		}
		if (checkForBugsExtraHard && !checkStateOfAllClauses(timeStamp)) { Utils.error("Check out the mismatches above."); }
	}
	
	/**
	 * @return Sum of weights of the active clauses.
	 */
	protected double getSumOfActiveClauses(TimeStamp timeStamp) {
		int counter = 0;
		if (checkForBugsExtraHard && !checkStateOfAllClauses( new TimeStamp((timeStamp == null ? "" : timeStamp + " ") + "getSumOfActiveClauses"))) { Utils.error("Check out the mismatches above."); }
		if (debugLevel > 1 && countOfActiveClauses > 0 && useActiveClausesHashSet) for (GroundClause gndClause : activeClauses) if (gndClause.isActive()) {
			if (debugLevel > 0 && counter   <  100) { Utils.println("% Active clause #" + (counter+1) + ": " + gndClause); }
			if (debugLevel > 0 && ++counter == 100) { Utils.println("% ...  Will not print the remainder of the " + Utils.comma(countOfActiveClauses) + " active clauses."); }
			if (counter >= 100) { return activeClausesSum; }
		}		
		return activeClausesSum;
	}
}