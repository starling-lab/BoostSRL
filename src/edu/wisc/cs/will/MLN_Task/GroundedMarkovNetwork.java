package edu.wisc.cs.will.MLN_Task;

import java.util.Collection;
import java.util.List;
import java.util.Set;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.Utils.Utils;

public class GroundedMarkovNetwork extends GroundThisMarkovNetwork {
	

	/* 
	 *     Public Members 
	 */
	

	/* 
	 *     Private Members 
	 */

	/* 
	 *     Public Methods 
	 */
	
	/**
	 * Default Constructor
	 * @param task
	 * @param allClauses
	 */
	public GroundedMarkovNetwork(MLN_Task task, Collection<Clause> allClauses) {
		super(task, allClauses);
		// TODO Auto-generated constructor stub
	}


    @Deprecated
	public boolean prepareForInference(TimeStamp timeStamp) { // Return TRUE if LAZY inference needed.
		if (debugLevel > -110) { Utils.println("\n% Create all the query literals."); }
		task.createAllQueryLiterals();  // Need all of these to be expanded (TODO - keep statistics in a sparse array), since we're assuming inference will be done soon.
	//	task.createAllHiddenLiterals(); // TODO do we need to create these, or can we simply assume any non-query that has survived is a hidden?  seems so ...
		if (debugLevel > -110) { Utils.println("\n% There are " + Utils.comma(task.getQueryLiterals()) + " query literals: " + Utils.limitLengthOfPrintedList(task.getQueryLiterals(), 25)); }
		collectAllRemainingGroundings(timeStamp);
		if (debugLevel > -110 && Utils.getSizeSafely(stillTooLargeAfterReduction) < 1) { Utils.println("\n% Because there are only " + Utils.truncate(totalNumberOfGroundingsRemaining, 0) + " clause groundings remaining, will perform standard inference."); }
		else if (debugLevel > -110)                                                    { Utils.println("\n% Due to the large number of groundings they have remaining, " + Utils.comma(stillTooLargeAfterReduction) + " clauses need to be handled lazily."); }
		return (Utils.getSizeSafely(stillTooLargeAfterReduction) > 0);
	}
	
    @Deprecated
	public void clearAllMarkers() {
		setAllMarkers(null);
		//freezeAllGroundLiterals(false);// TODO - combine with setAllMarker to save some cycles?
	}

    @Deprecated
	public void setAllMarkers(Object marker) {
		setAllClauseMarkers( marker);
		setAllLiteralMarkers(marker);
		markerInUse = marker;
	}

    @Deprecated
	public void setAllClauseMarkers(Object marker) {
		if (!haveCollectedAllGroundClauses) {
			Utils.error("Cannot set all the  markers until all the gound clauses have been collected.");
		}
		GroundClause gndClause = getFirstGroundClause();
		while (gndClause != null) {
			gndClause.setMarker(marker);
			gndClause = getNextGroundClause();
		}
		markerInUse = marker;
	}

    @Deprecated
	public void setAllLiteralMarkers(Object marker) {
		if (!haveCollectedAllGroundLiterals) {
			Utils.error("Cannot set all the markers until all the gound literals have been collected.");
		}
		GroundLiteral gLit = getFirstGroundLiteral();
		while (gLit != null) {
			gLit.setMarker(marker);
			gLit = getNextGroundLiteral();
		}
		markerInUse = marker;
	}

    @Deprecated
	public void clearMarkedClauses() {
		GroundClause gndClause = getFirstMarkedGroundClause();
		while (gndClause != null) { 
			gndClause.setMarker(null);
			gndClause = getNextMarkedGroundClause();
		}
	}
	
	@Deprecated
	public long getCountOfUniqueGroundClauses() {
		int counter  = 0;
		int counter2 = 0;
		int max      = 0;
		Integer indexOfMax = 0;
		for (Integer index : hashOfGroundClauses.keySet()) {
			int size = hashOfGroundClauses.get(index).size();
			counter += size;
			if (size > max) { max = size; indexOfMax = index; }
			if (size > 1)   { counter2++; }
		}
		Utils.println("\n% There are " + Utils.comma(countofUniqueGroundClauses) + " unique ground clauses; "
				+ Utils.comma(countOfMergedGroundClauses) + " have had their weights merged.");
		Utils.println("%  |canonical ground-clause hash codes| = " + Utils.comma(hashOfGroundClauses.keySet().size()) + 
					   ", |hash of ground clauses| = "             + Utils.comma(counter)  +
					   ", |with collisions| = "                    + Utils.comma(counter2) +
					   ", max # of collisions = "                  + Utils.comma(max));
		Utils.println("%    max collisions: " + Utils.limitLengthOfPrintedList(hashOfGroundClauses.get(indexOfMax), 25));
		return countofUniqueGroundClauses;
	}
	
    /**
     * Prints literals and clauses in this GroundedMarkovNetwork
     * TVK:GMN Copied from GroundThisMarkovNetwork.
     *
     */
    @Deprecated
	public void printLiteralsAndClauses() {
		List<GroundLiteral> gndLiterals = getAllGroundLiterals_ExpensiveVersion();
		for(GroundLiteral gndL : gndLiterals) {
			Utils.println("Literal: " + gndL.toPrettyString());
			Set<GroundClause> gndClauses = gndL.getGndClauseSet();
			for(GroundClause gndC : gndClauses) {
				Utils.println("Clause: " + gndC.toPrettyString());
			}
		}
	}
	
	/* 
	 *     Private Methods 
	 */
}
