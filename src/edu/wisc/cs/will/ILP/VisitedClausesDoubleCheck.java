/**
 * 
 */
package edu.wisc.cs.will.ILP;

import java.util.List;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;

/**
 * @author shavlik
 *
 * Due to the (presumably) NP-complete nature of computing variants on clauses, a greedy algorithm is used to sort the literals.
 * If one wants to also compare the UNSORTED version when computing variants, this class should be used.
 *
 */
public class VisitedClausesDoubleCheck {
	VisitedClauses sorted;
	VisitedClauses unsorted;

	/**
	 * 
	 */
	public VisitedClausesDoubleCheck() {
		sorted   = new VisitedClauses(true);
		unsorted = new VisitedClauses(false);
	}

	/**
	 * @param maxSize
	 */
	public VisitedClausesDoubleCheck(int maxSize) {
		sorted   = new VisitedClauses(maxSize, true);
		unsorted = new VisitedClauses(maxSize, false);
	}

	public boolean alreadyInClosedListAfterSorting(List<Literal> literalsInAndBodyAsStandAlone) {
		List<Literal> result = sorted.alreadyInClosedListAfterSorting(literalsInAndBodyAsStandAlone);
		if (result != null) { return true; }
		return unsorted.alreadyInClosedListAfterSorting(literalsInAndBodyAsStandAlone) != null;
	}
	public List<Literal> alreadyInSortedClosedList(List<Literal> literalsInAndBodyAsStandAlone) {
		return sorted.alreadyInClosedListAfterSorting(literalsInAndBodyAsStandAlone);
	}
	public List<Literal> alreadyInUnsortedClosedList(List<Literal> literalsInAndBodyAsStandAlone) {
		return unsorted.alreadyInClosedListAfterSorting(literalsInAndBodyAsStandAlone);
	}
 
	public void addListOfUnsortedLiteralsToClosed(HandleFOPCstrings stringHandler, List<Literal> literalsInAndBodyAsStandAlone) {
		unsorted.addListOfUnsortedLiteralsToClosed(stringHandler, literalsInAndBodyAsStandAlone);
		sorted.addListOfUnsortedLiteralsToClosed(  stringHandler, literalsInAndBodyAsStandAlone);
	}
	public List<Literal> addListOfUnsortedLiteralsToSortedClosed(  HandleFOPCstrings stringHandler, List<Literal> literalsInAndBodyAsStandAlone) {
		return sorted.addListOfUnsortedLiteralsToClosed(  stringHandler, literalsInAndBodyAsStandAlone);
	}
	public List<Literal> addListOfUnsortedLiteralsToUnsortedClosed(HandleFOPCstrings stringHandler, List<Literal> literalsInAndBodyAsStandAlone) {
		return unsorted.addListOfUnsortedLiteralsToClosed(stringHandler, literalsInAndBodyAsStandAlone);
	}

	public void addClauseToClosed(HandleFOPCstrings stringHandler, Clause c) {
		unsorted.addClauseToClosed(stringHandler, c); 
		sorted.addClauseToClosed(  stringHandler, c); 
	}

	public List<Literal> alreadyInClosedList(HandleFOPCstrings stringHandler, Clause c) {
		List<Literal> result = sorted.alreadyInClosedList(stringHandler, c);
		if (result != null) { return result; }
		return unsorted.alreadyInClosedList(stringHandler, c);
	}
	public List<Literal> alreadyInSortedClosedList(  HandleFOPCstrings stringHandler, Clause c) {
		return sorted.alreadyInClosedList(  stringHandler, c);
	}
	public List<Literal> alreadyInUnsortedClosedList(HandleFOPCstrings stringHandler, Clause c) {
		return unsorted.alreadyInClosedList(stringHandler, c);
	}
}
