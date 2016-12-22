package edu.wisc.cs.will.MLN_Task;

import java.util.*;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.Utils.*;

/**
 * This is the Block class. Exactly or at most k of the literals within a block
 * can be true. All the ground literals in a block are groundings of the same literal.
 * 
 * @author pavan and shavlik
 */
public class Block {
	private static final int debugLevel = 0;
	
	public  static final int maxNumCombinations_default = 10000; // We stop execution if numCombinations is more than maxNumBlockCombinations.
	private              int maxNumCombinations = maxNumCombinations_default;
	
	private List<GroundLiteral> gndLiterals;      // The ground literals in this block.
	private Literal                literal;       // All ground literals in block are groundings of this literal.
	
	// The truth assignments of the ground literals may be immutable, for example,
	// when k of the ground literals are evidence literals, and they are true.
	private boolean valuesFixed;  
	
	private int[] truthCounts;  
	private Set<GroundClause> gndClauses;  // Set of all ground clauses in which the ground literals of this block appear.
	
	// The indices of 'currNumTrueLiterals' true ground literals are contained in
	// the first 'currNumTrueLiterals' locations of currTrueIndices.
	private int[] currTrueIndices;  
	
	// Exactly or at-most k of the ground literals in the block must be true.
	private int     k;
	private boolean exactly;
	
	private int     numCombinations;  // Number of combinations of truth assignments this block can take.
	private boolean valuesInited;	
	private int     currNumTrueLiterals;
	private boolean groundClausesComputed;
		
	/**
	 * @param literal All ground literals in the block are groundings of this literal.
	 * @param gndLiterals The ground literals in the block. Assumes that it doesn't contain any evidence literals.
	 */
	public Block(Literal literal, List<GroundLiteral> gndLiterals, TimeStamp timeStamp) {
		this(literal, gndLiterals, 0, timeStamp);
	}
	
	/**
	 * The constructor. All the gndLiterals and evidence information need not be supplied
	 * at the point of constructing the object. This information can be supplied later with
	 * addGndLiteral and addEvidence methods. However, all this information must be supplied
	 * before the initialization of truth values is done using initValues or setRandomValues 
	 * method. Either initValues or setRandomValues has to be explicitly called to bring the
	 * truth assignments in the block to a consistent state.
	 * 
	 * @param literal All ground literals in the block are groundings of this literal.
	 * @param gndLiterals The ground literals in the block. Assumes that it doesn't contain any evidence literals.
	 * @param numTrueEvidenceLiterals The number of positive evidence literals belonging to this block.
	 */
	public Block(Literal literal, List<GroundLiteral> gndLiterals, int numTrueEvidenceLiterals, TimeStamp timeStamp) {
		this.gndLiterals = gndLiterals;
		valuesFixed = false;
		this.literal = literal;
		truthCounts = new int[literal.numberArgs()];
		int index = 0;
		boolean isABlock = false;
		exactly = true;
		List<TypeSpec> typeSpecList = literal.predicateName.getTypeOnlyList(literal.numberArgs()).get(0).getTypeSpecList();
		for (TypeSpec typeSpec : typeSpecList) {
			truthCounts[index++] = typeSpec.truthCounts;
			if (typeSpec.truthCounts != 0) {
				isABlock = true;
				k = typeSpec.truthCounts;
				if (k < 0) {
					exactly = false;
					k = -k;
				}
			}
		}
		if (!isABlock) {
			Utils.printlnErr("Literal " + literal + " should not be used to instantiate a block object.");
		}				
		valuesInited = false;
		groundClausesComputed = false;
		reduceK(numTrueEvidenceLiterals, timeStamp);
	}	
	
	private void initGndClauses() {
		if (debugLevel > 0) { Utils.println("*** Initializing list of ground clauses in " + literal + "'s block"); }
		gndClauses = new HashSet<GroundClause>();
		for (GroundLiteral gndLiteral : gndLiterals) {			
			for (GroundClause gndClause : gndLiteral.getGndClauseSet()) {
				gndClauses.add(gndClause);
				if (debugLevel > 0) { Utils.println(gndClause.toString()); }
			}
		}
		if (debugLevel > 0) { Utils.println(""); }
	}	
	
	/**
	 * Brings the truth value assignments to a consistent state.
	 * 
	 * Calling this method also signals that all the ground literals and evidence information has been supplied.
	 * So this method also calls computeNumBlockCombinations.
	 */
	public void initValues(TimeStamp timeStamp) {
		if (!groundClausesComputed) {
			initGndClauses();
			groundClausesComputed = true;
		}
		if (!valuesInited) {
			
			if (valuesFixed) {
				numCombinations = 1;
				valuesInited = true;
				return;
			}
			if (k >= gndLiterals.size()) { k = gndLiterals.size(); }
			computeNumBlockCombinations();
			currTrueIndices = new int[k];
		}		
		
		if (exactly) { currNumTrueLiterals = k;	}		
		else         { currNumTrueLiterals = 0; }			
		
		startPosition(currNumTrueLiterals, timeStamp);
		valuesInited = true;
	}
	
	public void init() {
		if (!groundClausesComputed) {
			initGndClauses();
			groundClausesComputed = true;
		}
	}
	
	/**
	 * Computes the number of block combinations.
	 * The execution stops if the number of block combinations is more than maxNumBlockCombinations. 
	 */
	private void computeNumBlockCombinations() {
		if (exactly) { // Exactly k are true.
			numCombinations = numCombinations(gndLiterals.size(), k);			
			if (numCombinations == -1)                { numCombinationError1(); }
			if (numCombinations > maxNumCombinations) { numCombinationError2(); }
		} else { // At most k are true.
			numCombinations = 0;			
			for (int i = 0; i <= k; i++) {
				int temp = numCombinations(gndLiterals.size(), i);
				if (temp == -1)                                    { numCombinationError1(); }
				if (temp > (maxNumCombinations - numCombinations)) { numCombinationError2();}
				numCombinations += temp; 				
			}			
		}
		if (numCombinations == 1) { valuesFixed = true; }
	}	
	
	private void startPosition(int numTrueLiterals, TimeStamp timeStamp) {
		for (int i = 0; i < numTrueLiterals; i++) {
			gndLiterals.get(i).setValueOnly(true,  timeStamp);
			currTrueIndices[i] = i;
		}
		for (int i = numTrueLiterals; i < gndLiterals.size(); i++) {
			gndLiterals.get(i).setValueOnly(false, timeStamp);
		}
	}
	
	/**
	 * Selects one of the "numCombinations" truth value combinations uniformly at random.
	 * The user must either call this method or initValues to get the truth assignments to a consistent state.
	 */
	public void setRandomValues(TimeStamp timeStamp) {
		if (!valuesInited) { initValues(timeStamp); }
		setState(Utils.random0toNminus1(numCombinations), timeStamp); // Randomly (uniformly) choose a state to set.
	}
	
	/**
	 * The user must call initValues and then he can call this method repeatedly to iterate
	 * over all the truth-value combinations the block can be in.
	 * 
	 * @return false if we have iterated over all the "numCombinations" combinations.
	 */
	public boolean moveToNextState(TimeStamp timeStamp) {
		if (valuesFixed) { return false; }
		int size = gndLiterals.size();
		int indexToMoveForward = currNumTrueLiterals - 1;
		while (indexToMoveForward >= 0) {
			if (currTrueIndices[indexToMoveForward] == size - (currNumTrueLiterals - indexToMoveForward)) { 
				indexToMoveForward--;
			} else { break; }
		}
		if (indexToMoveForward == -1) {
			if (currNumTrueLiterals == k) { return false; }
			currNumTrueLiterals++;
			startPosition(currNumTrueLiterals, timeStamp);
			return true;
		}
		for (int i = indexToMoveForward; i < currNumTrueLiterals; i++) {
			gndLiterals.get(currTrueIndices[i]).setValueOnly(false, timeStamp);
		}
		int currLoc = currTrueIndices[indexToMoveForward];
		for (int i = indexToMoveForward; i < currNumTrueLiterals; i++) {
			currTrueIndices[i] = currLoc + (i - indexToMoveForward) + 1;
			gndLiterals.get(currTrueIndices[i]).setValueOnly(true,  timeStamp);
		}		
		return true;
	}
	
	/**
	 * Turn the gndLiteral at index indexTurnOn on (true) and the gndLiteral
	 * at index indexTurnOff off (false), provided it results in a consistent truth-value state. 
	 * 
	 * @param indexTurnOn
	 * @param indexTurnOff
	 */
	public void flipFinal(int indexTurnOn, int indexTurnOff, GroundedMarkovNetwork groundedMarkovNetwork, TimeStamp timeStamp) {
		if (isTrue(indexTurnOn) && !isTrue(indexTurnOff)) { return; }
		if (indexTurnOn == indexTurnOff) { // If they are equal, then the convention is that the 'off' wins out.
			gndLiterals.get(indexTurnOff).setValue(false, groundedMarkovNetwork, timeStamp);
		} else {
			gndLiterals.get(indexTurnOn ).setValue(true,  groundedMarkovNetwork, timeStamp);
			gndLiterals.get(indexTurnOff).setValue(false, groundedMarkovNetwork, timeStamp);
		}
		helpFlip(indexTurnOn, indexTurnOff);
	}
	public void helpFlip(int indexTurnOn, int indexTurnOff) { // The Lazy version needs to call this.
		boolean foundIt = false;
		for (int i = 0; i < k; i++) { // Update this list of literals turned on.
			if (currTrueIndices[i] == indexTurnOff) {
				currTrueIndices[i] = indexTurnOn;
				foundIt = true;
				break;
			}
		}
		if (!foundIt) { Utils.error("Did not find " + indexTurnOn + " in " + currTrueIndices); }
	}
	
	/**
	 *
	 * @param index
	 * @return  Is this literal at this index currently set to true?
	 */
	public boolean isTrue(int index) {
		return gndLiterals.get(index).getValue();
	}
	
	/**
	 * Returns the gndLiterals in the block which currently have a true truth value.
	 * 
	 * @return
	 */
	public List<GroundLiteral> getCurrentTrueLiterals() {
		List<GroundLiteral> trueLiterals = new ArrayList<GroundLiteral>();
		for (int i = 0; i < currNumTrueLiterals; i++) {
			trueLiterals.add(gndLiterals.get(currTrueIndices[i]));
		}
		return trueLiterals;
	}
	
	/**
	 * Given a value between 0 and (numCombinations - 1), it sets the block truth values
	 * to the corresponding assignment.
	 * 
	 * Say number of ground literals n = 5, and the block can have atmost 1 true ground literal,
	 * we have 6 possible combinations.
	 * 0 corresponds to fffff, 1,2,3,4,5 correspond to tffff, ftfff, fftff, ffftf, and
	 * fffft, respectively.
	 * 
	 * @param indexInOrderingOfPossibleStates A value between 0 and (numCombintions - 1)
	 */
	public void setState(int indexInOrderingOfPossibleStates, TimeStamp timeStamp) {
		int numTrueLiterals = k;
		if (!exactly) {
			// Find how many true literals will be there in the resulting truth value assignment.
			for (int i = 0; i < k; i++) {
				int numCombinations = numCombinations(gndLiterals.size(), i);
				if (numCombinations > indexInOrderingOfPossibleStates) {
					numTrueLiterals = i;
					break;
				}
				indexInOrderingOfPossibleStates -= numCombinations;
			}
		}
		for (int i = 0; i < currNumTrueLiterals; i++) {
			gndLiterals.get(currTrueIndices[i]).setValueOnly(false, timeStamp);
		}
		if (numTrueLiterals == 1) {
			// just to speed up the common case.
			currTrueIndices[0] = indexInOrderingOfPossibleStates;
		} else {
			int currIndex = 0;
			int currLoc = 0;
			while (currIndex < numTrueLiterals) {
				int N = gndLiterals.size() - 1 - currLoc;
				int K = numTrueLiterals - 1 - currIndex;
				int combinations = numCombinations(N, K);
				if (combinations > indexInOrderingOfPossibleStates) {
					currTrueIndices[currIndex] = currLoc;
					currIndex++;
					currLoc++;
				} else {
					currLoc++;
					indexInOrderingOfPossibleStates -= combinations;
				}
			}
		}		
		for (int i = 0; i < numTrueLiterals; i++) {
			gndLiterals.get(currTrueIndices[i]).setValueOnly(true, timeStamp);
		}
		if (!exactly) {	currNumTrueLiterals = numTrueLiterals; }
	}
	
	/**
	 * @return The number of ground literals in the block.
	 */
	public int getSize() {
		return gndLiterals.size();
	}
	
	/**
	 * The size of the returned array is equal to the number of currently true literals,
	 * and not the maximum possible value of k (in the at-most case).
	 * 
	 * @return An array containing the indices of the ground literals which are currently true. 
	 */
	public int[] getCurrentTrueIndices() {
		if (exactly) { return currTrueIndices; }
		int[] result = new int[currNumTrueLiterals];
		for (int i = 0; i < currNumTrueLiterals; i++) {
			result[i] = currTrueIndices[i];
		}
		return result;
	}
	
	// A faster version for specialized use, i.e., when the programmer is sure to not walk too far into this list.
	public int[] getCurrentTrueIndicesUnsafe() {
		return currTrueIndices; 
	}
	
	/**
	 * @return The number of truth value combinations the block can be in.
	 */
	public int getNumCombinations() {
		return numCombinations;
	}
	
	public Set<GroundLiteral> getNeighbors() {
		Utils.error("need to fix this code"); return null;
		/*
		Set<GroundLiteral> neighbors = new HashSet<GroundLiteral>(4);
		if (!valuesInited) { initValues(); }
		for (GroundClause gndClause : gndClauses) {
			for (GroundLiteral gndLiteral : gndClause.getLiterals()) if (!neighbors.contains(gndLiteral)) {
				neighbors.add(gndLiteral);
			}
		}
		return neighbors;
		*/
	}
	
	/**
	 * @return All the ground clauses which the ground literals of this block appear in.
	 */
	public Set<GroundClause> getGndClauses() {
		return gndClauses;
	}
	
	/**
	 * Set the truth value of the ground literal at index 'index' true.
	 * 
	 * @param index
	 * @return false if the groundLiteral cannot be set to true.
	 */
	public boolean turnOn(int index, TimeStamp timeStamp) {
		GroundLiteral literal = gndLiterals.get(index);
		if (literal.getValue()) return true;
		if (exactly) return false;
		if (currNumTrueLiterals == k) return false;		
		literal.setValueOnly(true, timeStamp);
		currNumTrueLiterals++;
		currTrueIndices[currNumTrueLiterals-1] = index;
		return true;
	}
	
	/**
	 * Set the truth value of the ground literal at index 'index' false.
	 * 
	 * @param index
	 * @return false if the groundLiteral cannot be set to false.
	 */
	public boolean turnOff(int index, TimeStamp timeStamp) {
		GroundLiteral literal = gndLiterals.get(index);
		if (!literal.getValue()) return true;
		if (exactly) return false;
		literal.setValueOnly(false, timeStamp);
		int currIndex = 0;
		for (int i = 0; i < currNumTrueLiterals; i++) {
			if (currTrueIndices[i] == index) {
				currIndex = i;
				break;
			}
		}
		for (int i = currIndex + 1; i < currNumTrueLiterals; i++) {
			currTrueIndices[i-1] = currTrueIndices[i];
		}
		currNumTrueLiterals--;
		return true;
	}
	
	/**
	 * @param gndLiteral
	 * @return The index of gndLiteral in list of ground literals in this block.
	 */
	public int indexOf(GroundLiteral gndLiteral) {
		return gndLiterals.indexOf(gndLiteral);
	}
	
	/**
	 * @return The sum of weights of satisfied clauses which have at least one ground
	 * literal in this block.
	 */
	public double sumSatisfiedClauses() {
		double sum = 0;
		for (GroundClause gndClause : gndClauses) {
			if (gndClause.isSatisfiedCached()) { sum += gndClause.getWeightOnSentence(); }
		}
		return sum;
	}
	
	/**
	 * @return true if this block is an 'exactly k true' type, and false if it is an 'atmost k true' type.
	 */
	public boolean isExactly() {
		return exactly;
	}
	
	/**
	 * @return Number of current true literals in the block.
	 */
	public int getNumTrueLiterals() {
		return currNumTrueLiterals;
	}
	
	/**
	 * @return The value of k in 'exactly/at-most k true literals'
	 */
	public int getK() {
		return k;
	}
	
	/**
	 * @return All the ground literals in the block.
	 */
	public List<GroundLiteral> getGndLiterals() {
		return gndLiterals;
	}	
	
	/**
	 * Each time a new true evidence literal belonging to this block is seen,
	 * this method can be called. Do not call this method twice for the same ground literal.
	 * Likewise, do not call this method for ground literals which were accounted for by 
	 * numTrueEvidenceLiterals argument in the constructor call.
	 */
	public void addEvidence(TimeStamp timeStamp) {
		reduceK(1, timeStamp);
	}
	
	private void reduceK(int value, TimeStamp timeStamp) {
		if (value <= 0) return;
		k -= value;
		if (k <= 0) {
			valuesFixed = true;
			for (GroundLiteral gndLiteral : gndLiterals) {
				gndLiteral.setValueOnly(false, timeStamp);
			}
			k = 0;
		}
	}
	
	/**
	 * @return true if the ground literal truth values are fixed for this block.
	 */
	public boolean valuesFixed() {
		return valuesFixed;
	}
	
	/**
	 * Tries to add the gndLiteral to the block.
	 * 
	 * @param gndLiteral
	 * @return true if the gndLiteral was added to the block.
	 */
	public boolean addGndLiteral(GroundLiteral gndLiteral) {
		if (!canAddGndLiteral(gndLiteral)) return false;
		if (gndLiterals == null) {
			gndLiterals = new ArrayList<GroundLiteral>();			
		}		
		gndLiterals.add(gndLiteral);
		return true;
	}
	
	/**
	 * A gndLiteral can be added to the block if it is a grounding of the same literal,
	 * and has the same constants (for those arguments with truthCounts = 0) as the current
	 * ground literals in the block.
	 * 
	 * @param gndLiteral
	 * @return true/false indicating whether this gndLiteral must be added to this block or not.
	 */
	public boolean canAddGndLiteral(GroundLiteral gndLiteral) {
		Utils.error("need to fix this code"); return false;
		/*
		String predName = literal.predicateName.name;
		if (!gndLiteral.getParentLiteral().predicateName.name.equals(predName)) return false;
		if (gndLiterals == null) {			
			return true;
		}
		List<Constant> oldGndTerms = gndLiterals.get(0).getGndTerms();
		List<Constant> gndTerms    = gndLiteral.getGndTerms();
		for (int i = 0; i < truthCounts.length; i++) {
			if (truthCounts[i] == 0 && !oldGndTerms.get(i).equals(gndTerms.get(i))) {
				return false;
			}
		}		
		return true;
		*/
	}
	
	/**
	 * Compute N choose K.
	 * Returns -1 if the value is more than Integer.MAX_VALUE
	 * 
	 * @param N
	 * @param K
	 * @return
	 */
	private int numCombinations(int N, int K) {
		if (K > N / 2) K = N - K;
		double result = 1;
		for (int i = 0; i < K; i++) {
			result *= ((double)(N - i)/(K - i));
			if (result > Integer.MAX_VALUE) { return -1; }
		}
		return (int)Math.round(result);
	}
	
	private void numCombinationError1() {
		Utils.printlnErr("Number of combinations in " + literal.toString() +
				   " block is more than " + Integer.MAX_VALUE + ".\nExiting ...");					
		System.exit(0);		
	}
	
	private void numCombinationError2() {
		Utils.printlnErr("Number of combinations in " + literal.toString() +
				   		   " block is more than the current maxNumBlockCombinations value of " + maxNumCombinations + ".");
		System.out.println("Try increasing the value with -maxNumBlockCombinations option.");
		System.out.println("Exiting ...");					
		System.exit(0);
	}
}