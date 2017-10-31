package edu.wisc.cs.will.MLN_Inference;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.MLN_Task.GroundClause;
import edu.wisc.cs.will.MLN_Task.GroundLiteral;
import edu.wisc.cs.will.MLN_Task.GroundedMarkovNetwork;
import edu.wisc.cs.will.MLN_Task.TimeStamp;
import edu.wisc.cs.will.Utils.Utils;

/**
 * This is the MCSAT inference class.  MCSAT computes marginal probabilities of each query literal in the presence of hard-to-satisfy clauses (?).
 * 
 *   Poon, Hoifung and Domingos, Pedro (2006).
 *   Sound and Efficient Inference with Probabilistic and Deterministic Dependencies. 
 *   Proceedings of the Twenty-First National Conference on Artificial Intelligence (pp. 458-463), 2006. Boston, MA: AAAI Press. 
 *   http://www.cs.washington.edu/homes/pedrod/papers/aaai06a.pdf 
 *   
 * Note: in the above paper's MC-SAT algorithm, it says that the initial state
 *       should satisfy all of the hard clauses.  This is NOT explicitly done.
 *       What is done is that the initial state is set by MCMCInference's calls to MaxWalkSAT.
 *       In the default settings of parameters, these calls to MaxWalkSAT do not use many cycles, 
 *       and so it might make sense to run MaxWalkSAT longer initially, in order to cover
 *       most, if not all, of the high-weight clauses.  (Alternative idea: collect
 *       all the hard clauses, or maybe all those with 'very large' positive weight,
 *       and do a lengthy run of MaxWalkSAT on just these clauses; if still cannot
 *       satisfy most/all of these (nearly) 'hard' clauses, throw an error.)   TODO
 *  
 * @author pavan and shavlik
 */
public class MCSAT extends AllOfInference {
	private final static int debugLevel = 0;
	
	protected GroundedMarkovNetwork groundedMarkovNetwork;
	protected int    maxNumberOfStarts_SampleSAT          =     1;   // TODO - do we even want more than 1 start??  Don't need a lot here, since this is called for each sample collected.
	protected int    maxNumberOfFlips_SampleSAT           =  1000;   // The product of these two numbers is the number of flips PER SAMPLE.
	
	protected double prob_WalkSAT                   = SampleSAT.probOfWalkSAT_default;
	protected double temperature_SA                 = SampleSAT.temperatureSA_default;
	protected int    maxNumStepsAfterSoln_sampleSAT = SampleSAT.maxNumStepsAfterSoln_sampleSAT_default;
	
	protected double                          minWgtToBeHardClause = Sentence.maxWeight - 0.1; // Used to flag 'hard' clauses that are not satisfied in the initial state.
	protected int                             samples              = 0; // Count samples produced.
	
	private  SampleSAT theSampleSATsolver = null;	
	private  String    msg = "MCSAT"; // Used in printouts.
	
	private Map<GroundClause,List<GroundClause>> negClauseMap = null;

	
	public MCSAT() {
		// Used by LazyMCSAT.
	}
	public MCSAT(GroundedMarkovNetwork groundedMarkovNetwork, double priorProbOfBeingTrue) {
		this.groundedMarkovNetwork = groundedMarkovNetwork;
		if (debugLevel > 0) { Utils.println("% MCSAT: Number of ground clauses: " + Utils.comma(groundedMarkovNetwork.countOfMarkedGroundClauses()) + "."); }
		//initGndLiteralsWithUnitClause();
	}
	public MCSAT(GroundedMarkovNetwork groundedMarkovNetwork, double priorProbOfBeingTrue, int maxNumberOfStarts_SampleSAT, int maxNumberOfFlips_SampleSAT) {
		this(groundedMarkovNetwork, priorProbOfBeingTrue);
		this.maxNumberOfStarts_SampleSAT    = maxNumberOfStarts_SampleSAT;
		this.maxNumberOfFlips_SampleSAT     = maxNumberOfFlips_SampleSAT;
}
	public MCSAT(GroundedMarkovNetwork groundedMarkovNetwork, double priorProbOfBeingTrue, int maxNumberOfStarts_SampleSAT, int maxNumberOfFlips_SampleSAT,
			     double prob_WalkSAT, double temperature_SA, int maxNumStepsAfterSoln_sampleSAT_sampleSAT) {
		this(groundedMarkovNetwork, priorProbOfBeingTrue);
		this.maxNumberOfStarts_SampleSAT    = maxNumberOfStarts_SampleSAT;
		this.maxNumberOfFlips_SampleSAT     = maxNumberOfFlips_SampleSAT;
		this.prob_WalkSAT                   = prob_WalkSAT;
		this.temperature_SA                 = temperature_SA;
		this.maxNumStepsAfterSoln_sampleSAT = maxNumStepsAfterSoln_sampleSAT_sampleSAT;
	}
	
	public int getStepsPerSample() {
		return maxNumberOfStarts_SampleSAT * maxNumberOfFlips_SampleSAT;
	}
	// Check to see if any 'hard' clauses are not satisfied in the initial state.  (See comments above.)
	protected void checkHardClauses() {
		GroundClause gndClause = groundedMarkovNetwork.getFirstMarkedGroundClause();
		int countMARKED = 0;
		int countUNSAT  = 0;
		int countHARD   = 0;
		if (gndClause == null) { return; } 
		while (gndClause != null) {
			countMARKED++;
			if (gndClause.getWeightOnSentence() > minWgtToBeHardClause) {
				countHARD++;
				if (!gndClause.isSatisfiedCached()) {
					countUNSAT++;
					if (debugLevel > 0 && warningCount < maxWarnings) { Utils.println("% MCSAT WARNING #" + Utils.comma(++warningCount) + " in " + (groundedMarkovNetwork.doingLazyInference ? "Lazy" : "") + "MCSAT: The initial state does not satisfy 'hard' clause: '" + gndClause + "'."); }
				}
			}
			gndClause = groundedMarkovNetwork.getNextMarkedGroundClause();
		}
		if (debugLevel > -10 && countHARD > 0) { Utils.println("% Out of " + Utils.comma(countMARKED) + " clauses, " + Utils.comma(countHARD) + " were hard clauses, and of these " + Utils.comma(countUNSAT) + " were not satisfied in the initial state."); }
	}
	
	List<GroundClause> allNewUnitClausesFromNegWgtClause = null;
	private void invertNegativeWeightClauses() {
		if (negClauseMap == null) {
			negClauseMap = new HashMap<GroundClause,List<GroundClause>>(4);
		} else { negClauseMap.clear(); }
		GroundClause gndClause = groundedMarkovNetwork.getFirstMarkedGroundClause();
        while (gndClause != null) {
        	if (gndClause.getWeightOnSentence() < 0) {
        		if (gndClause.getLength() < 1) { Utils.error("Unit (and empty) clauses should have been fixed before here: " + gndClause); }
        		List<GroundClause> newClauses = new ArrayList<GroundClause>(gndClause.getLength());
        		// Convert a clause with negative weight.
				// Convert "-wgt (p v q v ~r)" to "wgt ~(p v q v ~r)" which equals "[wgt/3 ~p] ^ [wgt/3 ~q] ^ [wgt/3 r]" by DeMorgan's Law.
        		// Distribute the weight equally across all resulting unit clauses.
				// Note: other code makes sure that these, and never the neg-wgt clause are marked.  Also, these are removed after MCSAT is done with its current run.
				double individualWeights = -gndClause.getWeightOnSentence() / gndClause.getLength();						
			//	if (debugLevel > -22) { Utils.print("%     Need to negate '" + gndClause + "' and create unit clauses."); }
				for (int i = 0; i < gndClause.getLength(); i++) {
					GroundClause newClause = new GroundClause(gndClause.getStringHandler(), gndClause.getIthLiteral(i), !gndClause.getSignOfIthLiteral(i), null);
					newClause.setWeightOnSentence(individualWeights);
					newClauses.add(newClause);	
				}
//				if (debugLevel > -22) { Utils.println(Utils.getSizeSafely(newClauses) + " created."); }
				// Utils.println("Inserted entries for "+ gndClause.getInfo());
				negClauseMap.put(gndClause, newClauses);
				if (allNewUnitClausesFromNegWgtClause == null) { allNewUnitClausesFromNegWgtClause = new ArrayList<GroundClause>(gndClause.getLength()); }
				allNewUnitClausesFromNegWgtClause.addAll(newClauses);
        	}
        	gndClause = groundedMarkovNetwork.getNextMarkedGroundClause();
		}
		// Not required.[TVK]
        // if (allNewUnitClausesFromNegWgtClause != null) { groundedMarkovNetwork.addTheseUnitClauseFromNegWgtClauses(allNewUnitClausesFromNegWgtClause); }
	}
	// TODO - might want to CACHE these, but probably safer to recompute.
	public void cleanUpSampleGenerator() {
		// Since we dont insert them anymore, commented out
	    //	if (allNewUnitClausesFromNegWgtClause != null) { groundedMarkovNetwork.removeTheseUnitClauseFromNegWgtClauses(allNewUnitClausesFromNegWgtClause); }
	    // Reset samples count
		samples=0;
		// Cleanup the ground literals
		if (negClauseMap == null || negClauseMap.isEmpty()) return;
		// TVK: Following code deletes the references to the negative clauses from
		// the literals. Commented out as it causes some other bug.
	   	for (GroundClause gndClause : negClauseMap.keySet()) {
			List<GroundClause> newClauses = negClauseMap.get(gndClause);
			for (int i = 0; i < newClauses.size(); i++) {
				// gndClause.getIthLiteral(i).getGndClauseSet().remove(newClauses.get(i));
				GroundClause newGndClause = newClauses.get(i);
				for(int j = 0; j < newGndClause.getLength();j++) {
					newGndClause.getIthLiteral(j).getGndClauseSet().remove(newGndClause);
				}
			}
		}
		negClauseMap.clear();
		allNewUnitClausesFromNegWgtClause.clear();
	}
	
	/**
	 * Find the clauses to be solved at the current step, using a SampleSAT solver.
	 */
	private double totalPrepTime  = 0.0;
	private double totalTimeTaken = 0.0; // Use this to compute the mean time per example.
	private double totalUnitClauseTime = 0.0;
	private long   totalNumberClausesForSampleSAT  = 0;
	private long   totalNumberLiteralsForSampleSAT = 0;
	private long   noSampleSATcalledNeeded         = 0;
	private int    numberOfLiteralsMarked          = 0;
	private int    numberOfMarkedClausesConsidered = 0;
	private LinkedList<GroundLiteral> markedLiterals = new LinkedList<GroundLiteral>();
	public void getNextSample() {
		if (debugLevel > -10 && theSampleSATsolver != null) { theSampleSATsolver.setReportFlag(); }
		reportFlagOn = (theSampleSATsolver == null ? reportFlagOn : theSampleSATsolver.reportFlagOn);
		if (samples < 1) { 
			checkHardClauses();
			invertNegativeWeightClauses();
		}
		samples++;
		endTimer1(); // This also restarts the timer.
		endTimer2();
		endTimer3();
		if (debugLevel > 0 && reportFlagOn) { msg = "MCSAT (sample #" + Utils.comma(samples) + ")"; }
		if (groundedMarkovNetwork.getMarkerInUse() != null) { Utils.error("Should not have a non-null marker: " + groundedMarkovNetwork.getMarkerInUse()); }
		
		//// The following is a cpu-cycle waster.  TODO JWSJWSJWS
		//if (groundedMarkovNetwork.countMarkedClauses() > 0) { Utils.println("***** Have some marked clauses!  Number = " + Utils.comma(groundedMarkovNetwork.countMarkedClauses()) + "."); }
				
		TimeStamp timeStamp = (GroundedMarkovNetwork.doMajorDebug ? new TimeStamp("MCSAT: starting sample #" + samples) : null);
		numberOfLiteralsMarked          = 0;
		numberOfMarkedClausesConsidered = 0;
		markedLiterals.clear();
		// Collect all the clauses to be satisfied.  Also mark all those literals in the clauses to be satisfied.  We'll do a SampleSAT run on this subset (note: we still need to do unit-clause propagation - see below).
		// While doing this, also check age of clauses.
		int numberOfClausesMarked = findClausesToBeSatisfied(timeStamp);
		if (numberOfLiteralsMarked != markedLiterals.size()) { Utils.error("numberOfLiteralsMarked = " + Utils.comma(numberOfLiteralsMarked) + " but |markedLiterals| = " + Utils.comma(markedLiterals)); }
		groundedMarkovNetwork.setMarkerInUse(this); // This will cause only the marked literals and clauses to be used.
		if (debugLevel > -22 && reportFlagOn) {
			endTimer3();
			Utils.println("%     Took " + Utils.truncate(timeTaken3, 3) + " seconds for findClausesToBeSatisfied to collect " +  Utils.comma(numberOfClausesMarked) +  " clauses for SampleSAT in MCSAT sample #" + Utils.comma(samples) + ".");
		}
		timeStamp = (GroundedMarkovNetwork.doMajorDebug ? new TimeStamp("MCSAT: getNextSample(" + samples + ") init unused ground literals") : null);
		
		Set<GroundClause> updatedClauses = new HashSet<GroundClause>();
		// Need to do this before unit-clause propagation, since that will set some markers to null, but those literals have the correct setting.
		int randomized = 0;
		int numbGroundLiterals = groundedMarkovNetwork.getNumberOfGroundLiterals();
		if (numberOfLiteralsMarked < numbGroundLiterals || reportFlagOn || GroundedMarkovNetwork.doMajorDebug) {
			GroundLiteral gLit = groundedMarkovNetwork.getFirstUnMarkedGroundLiteral();
			while (gLit != null) {
				// We maintain a set of clauses which may have been satisfied/unsatisfied after this flip and 
				// compute satisfaction at the end.
				boolean old_value = gLit.getValue();
				boolean new_value = (Utils.random() <= 0.5);
				if (old_value != new_value && gLit.getGndClauseSet() != null)
				 updatedClauses.addAll(gLit.getGndClauseSet());
				
				randomized++;                                                // Do a random assignment to ground literals not present in the list of clauses to be satisfied.
				gLit.setValue(new_value, null, timeStamp);        // We do this because in the MCSAT algorithm, one uniformly samples from all states that satisfy clausesToBeSatisfied.
				gLit = groundedMarkovNetwork.getNextUnMarkedGroundLiteral(); // Note: we might not be able to satisfy clausesToBeSatisfied, but we do the best we can via calling SampleSAT below. 
			}                                                                // We assume that SampleSAT uniformly chooses from those states that (nearly)satisfy clausesToBeSatisfied 
		}                                                                    // (because we want to uniformly sample from all states that satisfy clausesToBeSatisfied).
		                                                                     // Since SampleSAT is designed to be a (nearly) uniform sampler (see cite in SampleSAT.java), we're good there.
		
		if (randomized + numberOfLiteralsMarked != groundedMarkovNetwork.getNumberOfGroundLiterals()) {
			Utils.error("|randomizedLiterals| + |numberOfLiteralsMarked| [" + Utils.comma(randomized) + " + " + Utils.comma(numberOfLiteralsMarked) + "] does not match |allGroundLiterals| = " +  Utils.comma(groundedMarkovNetwork.getNumberOfGroundLiterals()) + ".");
		}
		
		// Now do unit-clause propagation.  All the marked clauses had been satisfied, and our goal is to
		// again satisfy them, but sampling (nearly) uniformly from all solutions that satisfy all the marked clauses.
		// All those literals NOT in the selected set get random truth values (since we want to sample from all solutions).
		int  clausesRemovedDueToUnitClausePropagation = 0;
		int literalsRemovedDueToUnitClausePropagation = 0;
		int numberLiteralsForcedToBeTrue              = 0;
		int numberLiteralsForcedToBeFalse             = 0;
		int unitClausePropagationCounter              = 0;
		Set<GroundLiteral> markedLiteralsRemaining = new HashSet<GroundLiteral>(markedLiterals);
		while (!markedLiterals.isEmpty()) { // Need to keep looking until no more unit clauses remain.  Why are repeated loops necessary?  Because lit7 might get set to false, which means clause {lit1 v lit7} should now cause lit1 to be set to true.  TODO - use recursion?
			GroundLiteral gLit = markedLiterals.pop(); // Set truth value and count at most once.
			gLit.inLinkedList = false;  // Need multiple iterations: e.g., unit clause 3 might cause lit1 to be true, and now we can finalize clause 2 which is (lit1 v lit7).
			if (++unitClausePropagationCounter % 100000 == 0) { Utils.println("% Have processed " + Utils.comma(unitClausePropagationCounter) + " literals during unit-clause propagation."); }
			for (GroundClause gndClause : gLit.getGndClauseSet()) if (gndClause.getMarker() == this) {
				if (gndClause.allOtherLiteralsAreUnmarked(gLit)) { // Have essentially a unit clause that is not yet satisfied.  Setting this gLit will do so (or else it is an error).
					// If reached here, there is only ONE 'free' literal left and this clause is NOT yet known to be satisfied.
					if (gLit.getMarker() == this) { // The first unit clause encountered will set this, and we only want to do this once.
						// Since this is still an 'unset' literal, it should satisfy this clause (due to the nature of how MCSAT selects clauses).
						if (GroundedMarkovNetwork.doMajorDebug && gLit.getValue() != gndClause.isaPosLiteral(gLit)) {
							gndClause.writeMarkedLiteralsOnly(  groundedMarkovNetwork);
							gndClause.writeUnMarkedLiteralsOnly(groundedMarkovNetwork);
							Utils.error("Have the wrong truth value for '" + gLit + " in {" + gndClause.groundClauseSettingToString(groundedMarkovNetwork) + "}");
						}
						if (GroundedMarkovNetwork.doMajorDebug && !gndClause.isaPosLiteral(gLit) && !gndClause.isaNegLiteral(gLit)) {
							Utils.error("This literal ("+ gLit + ") is not in this clause: " + gndClause.groundClauseSettingToString());
						}
						if (debugLevel > -22 && reportFlagOn) { if (gLit.getValue()) { numberLiteralsForcedToBeTrue++; } else { numberLiteralsForcedToBeFalse++; } }
						literalsRemovedDueToUnitClausePropagation++;
						gLit.setMarker(null);
						if (!markedLiteralsRemaining.remove(gLit)) { Utils.error("Should not happen."); }
						// Since this gLit was set, see which marked clauses are now satisfied. 
						// We also need to make sure all other literals that share clauses with this literal get checked again.
						for (GroundClause gndClause2 : gLit.getGndClauseSet()) if (gndClause2.getMarker() == this) {
							if (gndClause2.isSatisfiedViaUnmarkedFeatures()) {
								clausesRemovedDueToUnitClausePropagation++;  
								gndClause2.setMarker(null);
							} else for (int i = 0; i < gndClause2.getLength(); i++) {
								GroundLiteral gLit2 = gndClause2.getIthLiteral(i);
								if (!gLit2.inLinkedList && gLit2.getMarker() == this) { markedLiterals.push(gLit2); }
							}
						}
						break; // No need to continue the outer FOR loop, since the inner FOR loop took care of all clauses in which this literal appears.
					}
				}
			}
		}
		if (literalsRemovedDueToUnitClausePropagation > numberOfLiteralsMarked) {
			Utils.error("|literalsRemovedDueToUnitClausePropagation| = " + Utils.comma(literalsRemovedDueToUnitClausePropagation) + " should not exceed |numberOfLiteralsMarked| = " + Utils.comma(numberOfLiteralsMarked));
		}
		if (debugLevel > -22 && reportFlagOn && numberOfLiteralsMarked > 0) { Utils.println("%       Unit-clause propagation: " + Utils.comma(clausesRemovedDueToUnitClausePropagation) + " clauses (out of " + Utils.comma(numberOfClausesMarked) + ") and " + Utils.comma(literalsRemovedDueToUnitClausePropagation) + " literals (out of of " + Utils.comma(numbGroundLiterals) + ") were set due to unit-clause propagation."); }
				
		if (debugLevel > -22 && reportFlagOn) {
			endTimer3();
			totalUnitClauseTime += timeTaken3;
			if (numberOfLiteralsMarked > 0) { 
				Utils.println("%     Took " + Utils.truncate(timeTaken3, 3) + " seconds to do unit-clause propagation (" + Utils.comma(numberLiteralsForcedToBeTrue) + " literals were set to TRUE and " + Utils.comma(numberLiteralsForcedToBeFalse) + " to FALSE)." + (randomized > 0 ? "  Also set the truth values of the " + Utils.comma(randomized) + " remaining initially unselected literals (out of " + Utils.comma(numbGroundLiterals) + ") were randomly set." : "") + " [Overall ave = " + Utils.truncate(totalUnitClauseTime / samples, 3) + " sec.]");
			} else {				
				Utils.println("%     Took " + Utils.truncate(timeTaken3, 3) + " seconds to set the truth values of the " + Utils.comma(randomized) + " remaining initially unselected literals (out of " + Utils.comma(numbGroundLiterals) + ") were randomly set." + " [Overall ave = " + Utils.truncate(totalUnitClauseTime / samples, 3) + " sec.]");
			}
		 }
		if (debugLevel > 0) {
			endTimer2();
			endTimer3();
			totalPrepTime += timeTaken2;
			if (reportFlagOn) { Utils.println("%   Took " + Utils.truncate(timeTaken2, 3) + " seconds to prepare for SampleSAT in MCSAT sample #" + Utils.comma(samples) + " [Overall ave = " + Utils.truncate(totalPrepTime / samples, 3) + " sec.]"); }
		}
		int stepsTakenThisTime = 0;
		if (numberOfClausesMarked - clausesRemovedDueToUnitClausePropagation > 0) {  // It is acceptable for there to be NO selected clauses, especially after unit-clause propagation.
			int numbClauses  = numberOfClausesMarked  -  clausesRemovedDueToUnitClausePropagation;
			int numbLiterals = numberOfLiteralsMarked - literalsRemovedDueToUnitClausePropagation;
			totalNumberClausesForSampleSAT  += numbClauses;
			totalNumberLiteralsForSampleSAT += numbLiterals;
			if (theSampleSATsolver == null) {
				theSampleSATsolver = new SampleSAT(groundedMarkovNetwork, MCMCInference.prior_for_being_true_default,
					               						 maxNumberOfStarts_SampleSAT, maxNumberOfFlips_SampleSAT,
					               						 prob_WalkSAT, temperature_SA, maxNumStepsAfterSoln_sampleSAT);
			}
			if (debugLevel > -10 && reportFlagOn) {
				Utils.println("% MCSAT is calling SampleSAT: Using " + Utils.comma(numbClauses)  + " ground clauses (out of "  + Utils.comma(groundedMarkovNetwork.getNumberOfGroundClauses())  + ") and " +
								                   				       Utils.comma(numbLiterals) + " ground literals (out of " + Utils.comma(groundedMarkovNetwork.getNumberOfGroundLiterals()) + ").  " +
								                   				       "Mean values: " + Utils.truncate(numbClauses / samples, 1) + " clauses and " + Utils.truncate(numbLiterals / samples, 1) + " literals.");
			}
			useGreedyInitialStates =  (totalNumberLiteralsForSampleSAT > theSampleSATsolver.maxNumberOfFlips); // If we have more literals to consider then flips to be done, use a 'smarter' initial state.
			Collection<GroundClause> markedClauses = null;
			if (numbClauses < 1000) {
				markedClauses = new ArrayList<GroundClause>(numbClauses);
				GroundClause gndClause = groundedMarkovNetwork.getFirstMarkedGroundClause();
				while (gndClause != null) { 
					markedClauses.add(gndClause);
					gndClause = groundedMarkovNetwork.getNextMarkedGroundClause();
				}
			}
			stepsTakenThisTime = theSampleSATsolver.solve(markedLiteralsRemaining, markedClauses, reportFlagOn);
			if (!markedLiteralsRemaining.isEmpty())	for (GroundLiteral gLit : markedLiteralsRemaining)  { gLit.setMarker(null); }
			if (debugLevel > -10 && reportFlagOn) { 
				endTimer3();
				Utils.println("%    Took " + Utils.truncate(timeTaken3, 3) + " seconds for SampleSAT to solve its task (|marked literals|=" + Utils.comma(markedLiteralsRemaining) + ")."); 
			}
		} else {
			// When no need to call SampleSAT, need to randomly set all the still-marked literals since we want to uniformly sample all solutions.
			if (!markedLiteralsRemaining.isEmpty()) for (GroundLiteral gLit : markedLiteralsRemaining) {
				// We maintain a set of clauses which may have been satisfied/unsatisfied after this flip and 
				// compute satisfaction at the end.
				boolean old_value = gLit.getValue();
				boolean new_value = (Utils.random() < 0.5);
				if (old_value != new_value && gLit.getGndClauseSet() != null)
				 updatedClauses.addAll(gLit.getGndClauseSet());

				gLit.setValue(new_value, null, timeStamp); 
				gLit.setMarker(null);
			}
			noSampleSATcalledNeeded++;
			if (debugLevel > -10 && reportFlagOn) { 
				endTimer3();
				Utils.println("% MCSAT need not call SampleSAT since no collected clauses (possibly due to unit-clause propagation).  Took " + Utils.truncate(timeTaken3, 3) + " seconds to randomly set the still-marked literals.  [" + Utils.comma(noSampleSATcalledNeeded) + " out of " + Utils.comma(samples) + " samples]"); 
			}
		}		
		
		// Update isSatisfiedCached for these clauses.
		for(GroundClause gndClause : updatedClauses) {
			gndClause.checkIfSatisfied(timeStamp);
		}
		// TODO would be nice to count fraction of gLits that are true in each sample ...		
		if (samples % 10 == 0 && groundedMarkovNetwork.doingLazyInference) { groundedMarkovNetwork.removeOldLazyClauses((short) 1); }  // Garbage collect any lazy clauses not used over the last N samples.  I.e., all those used this time will now have age=0 (incremented to age=1), and those not reset to zero since last check, will get age incremented to 2.
		groundedMarkovNetwork.setMarkerInUse(null);
		endTimer3();
		if (reportFlagOn) { Utils.println("%    Took " + Utils.truncate(timeTaken3, 3) + " seconds to do final clean up."); }
		if (debugLevel > -10) {
			if (debugLevel > 2 && reportFlagOn) { groundedMarkovNetwork.reportGroundLiteralState(25); }
			endTimer1();
			totalTimeTaken += timeTaken1;
			if (reportFlagOn) { Utils.println("%   Took " + Utils.truncate(timeTaken1, 3) + " seconds for MCSAT sample #" + Utils.comma(samples) + 
												 " [Overall ave = "  + Utils.truncate(totalTimeTaken / samples,    3) + " sec.]  Took " + Utils.comma(stepsTakenThisTime) + " steps." + (theSampleSATsolver == null ? "" : "  Final number of active clauses = " + Utils.comma(theSampleSATsolver.last_countOfActiveClauses) +  
												 " and best cost = " + Utils.truncate(theSampleSATsolver.bestCost, 3) + ".")); }
		}
	}	
	
	/**
	 * Determine the clauses that have to be satisfied in the next step.
	 */ 
	private int findClausesToBeSatisfied(TimeStamp timeStamp) {
		if (debugLevel > 0 && reportFlagOn) { Utils.println("\n% " + msg + ": Calling findClausesToBeSatisfied()."); }
		int selected   = 0;
		int inverts    = 0;
		int candidates = 0;
        GroundClause gndClause = groundedMarkovNetwork.getFirstGroundClause(); // Need to look at all the clauses.
        while (gndClause != null) {
			double weight = gndClause.getWeightOnSentence();			
			if (weight > 0) { 
				double probHasToBeSatisfied = 1 - Math.exp(-weight); // Don't bother to check if satisfied until we decide it will be kept.
				if (Utils.random() < probHasToBeSatisfied && gndClause.checkIfSatisfied(timeStamp)) { // If already satisfied, keep in clausesToBeSatisfied with probability: 1 - e^(-weight).		
					candidates++;						
					if (debugLevel > 3 && reportFlagOn) { Utils.println("% CANDIDATE: " + gndClause.getInfo()); }						
					if (gndClause.getMarker() != null) { // TODO stop doing this check unless debugging?  Probably good to watch for errors.
						Utils.error("selected=" + Utils.comma(selected) + "  candidates=" + Utils.comma(candidates) + "  inverts=" + Utils.comma(inverts) + "  Already marked: " + gndClause.groundClauseSettingToString(groundedMarkovNetwork));
					}
					gndClause.setMarker(this); // Will also set age=0.
					selected++;
					processThisSelectedGroundClause(gndClause);
					if (debugLevel > 3 && reportFlagOn) {
						Utils.println("%   Marked! " + gndClause);
					}	
				}
			} else if (weight < 0) {
				double probHasToBeUnSatisfied = 1 - Math.exp(weight);
				if (Utils.random() < probHasToBeUnSatisfied && !gndClause.checkIfSatisfied(timeStamp)) { // If already unsatisfied, keep its negation in clausesToBeSatisfied with probability: 1 - e^(weight).		
					candidates++;						
					if (debugLevel > 3 && reportFlagOn) { Utils.println("% CANDIDATE with negative weight: " + gndClause.getInfo()); }
					if (negClauseMap == null) { Utils.error("negClauseMap not initialized"); }
					if (negClauseMap.get(gndClause) == null) { Utils.error("No entry mapped in negClauseMap for " + gndClause.getInfo());}
					for (GroundClause inverted : negClauseMap.get(gndClause)) { 
						if (gndClause.getMarker() != null) {
							Utils.error("selected=" + Utils.comma(selected) + "  candidates=" + Utils.comma(candidates) + "  inverts=" + Utils.comma(inverts) + "  Already marked: " + gndClause.groundClauseSettingToString(groundedMarkovNetwork));
						}
						selected++;	inverts++; inverted.setMarker(this);
					}
					processThisSelectedGroundClause(gndClause);
					if (debugLevel > 3 && reportFlagOn) {
						Utils.println("%   Marked! " + gndClause);
					}	
				}
			}
            gndClause = groundedMarkovNetwork.getNextGroundClause();
		}
		if (debugLevel > -110 && reportFlagOn) { 
			Utils.println("% " + msg + ":   Selected " + Utils.comma(selected) + " clauses " + 
															(inverts > 0 ? "(including " + Utils.comma(inverts) + " from negative-weight clauses) " : "") + "from " + 
														    Utils.comma(groundedMarkovNetwork.getNumberOfGroundClauses()) + " candidates.");
		 }
		return selected;
	}
	
	private void processThisSelectedGroundClause(GroundClause gndClause) {		
		int numberLits = gndClause.getLength();
		for (int i = 0; i < numberLits; i++) { // NOTE: we need to look at ALL here and should NOT YET check the marker (other than to see if another clause marked it).
			GroundLiteral gLit = gndClause.getIthLiteral(i);
			if (debugLevel > 3 && reportFlagOn) { Utils.println("%   Ground Literal in Marked Clause: " + gLit); }
			if (gLit.getMarker() == null) {
				gLit.setMarker(this);
				numberOfLiteralsMarked++;
				if (gLit.inLinkedList) { Utils.error("Should not happen ..."); }
				markedLiterals.push(gLit);
				gLit.inLinkedList = true; // Used to quickly see if already in this list.
				// See if the use of this literal means that some lazy clauses need to be made explicit.
				if (groundedMarkovNetwork.doingLazyInference) { groundedMarkovNetwork.makeSureAllGroundClausesAreMaterialized(gLit); }
				else if (debugLevel > 3 && reportFlagOn) { Utils.println("%   already marked ..."); }
			}
		}
	}
}