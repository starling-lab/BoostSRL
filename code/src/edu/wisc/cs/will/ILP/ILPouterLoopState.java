/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ILP;

import java.io.Serializable;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Theory;
import edu.wisc.cs.will.FOPC.TreeStructuredTheory;
import edu.wisc.cs.will.FOPC.TreeStructuredTheoryInteriorNode;
import edu.wisc.cs.will.Utils.Utils;

/**
 *
 * @author twalker
 */
@SuppressWarnings("serial")
public class ILPouterLoopState implements Serializable, Cloneable {

    protected int            numberOfCycles;
    protected int            numberOfLearnedClauses;     // Could easily count this, but keep it around for simplicity.
    protected int            numberOfPosExamples;        // This is the UNWEIGHTED count.  Note, this value is only used a check during deserializaion.  innerTask.getNumberOfPosExamples() should be used to get the current value.
    protected int            numberOfNegExamples;        // Ditto.
    protected int            numberOfPosExamplesCovered; // Ditto.
    protected int            numberOfNegExamplesCovered; // Ditto.
    protected int            total_nodesExpanded;        // Sum over all outer-loop iterations.
    protected int            total_nodesCreated;
    protected int            total_nodesNotAddedToOPENsinceMaxScoreTooLow;
    protected int            total_nodesRemovedFromOPENsinceMaxScoreNowTooLow;
    protected int            total_countOfPruningDueToVariantChildren;

    protected double         fractionOfPosCovered;
    protected double         fractionOfNegCovered;

    protected int            indexIntoPosSeedArray;  // When the provided list runs out, seeds are randomly chosen from the not-yet-covered positive examples.
    protected Theory         stdILPtheory;           // The standard ILP theory, i.e. the best clause from each seed.
    protected int[]          posSeedIndicesToUse = null;    // This can be overridden with setSequenceOfSeedsToUse().  These three variables help to allow users to specific which examples are the seeds.
    protected int            lengthPosSeedArray;

    protected Collection<Example> coveredPosExamples; // Collect positive examples covered by at least ONE 'best clause' produced by the ILP inner loop.
    protected Collection<Example> coveredNegExamples; // Also see which negative examples are covered by some clause.

    private int              currentFold   = -1;

    private String           prefix;
    private boolean          RRR;
    private boolean          flipFlopPosAndNegExamples = false; // BUGGY? Can be used to flip-flop the positive and negative examples before training.

    private Set<Example>     seedPosExamplesUsed;
    private Set<Example>     seedNegExamplesUsed;
    // private Set<Example>     negExamplesUsedAsSeeds;

    private   List<TreeStructuredLearningTask>  queueOfTreeStructuredLearningTasks; 
	private   TreeStructuredTheory              treeBasedTheory;  // Used when learning tree-structured theories.
    private   TreeStructuredLearningTask        currentTreeLearningTask;
    private   double                            overallMinPosWeight = -1; // When doing trees and we use smaller training sets upon recursion, this specifies the minimum (weighted) size of positive examples in a recursive call.
    protected double                            maxAcceptableNodeScoreToStop = Double.POSITIVE_INFINITY; // If score <= this, can create a leaf node in a tree-structured theory.

    private long             clockTimeUsedInMillisec;
    private long             maximumClockTimeInMillisec = Long.MAX_VALUE;
    
   /** Empty constructor for ILPouterLoopState.
    *
    * It is assumed that the ILPOuterLoop will setup all of these variables during
    * initialization or re-constitution of the checkpoint file.
    */
    protected ILPouterLoopState() {
    }

    /** Checks to make sure that the two state objects belong to the same search.
     *
     * When loading checkpoint information, we need to make sure that the state
     * information saved to disk belongs to the same ILP run as the one currently
     * being performed.
     *
     * If this method returns false, this state is probably from a different search
     * the checkpoint information should be ignored.  If it is true, you can replace
     * <code>otherState</code> with this state and the search should resume properly
     * from the last checkpoint.
     *
     * This code resembled equals code and performs approximately the same function.
     * However, I renamed it to make it explicit what it is doing.
     *
     * @param otherState The state of a new search after it has been completely
     *        initialized.
     * @return true if the two states are from the same search with high likelihood.
     */
    protected void checkStateCongruency(ILPouterLoopState otherState) throws IncongruentSavedStateException {
        // Check that we have the same number of positive examples...
        if ( this.numberOfPosExamples != otherState.numberOfPosExamples ) {
             throw new IncongruentSavedStateException("The number of positive examples does not match. Expected = " + otherState.numberOfPosExamples + ".  Found = " + this.numberOfPosExamples);

        }

        // Check that we have the same number of negative examples...
        if ( this.numberOfNegExamples != otherState.numberOfNegExamples ) {
            throw new IncongruentSavedStateException("The number of negative examples does not match. Expected = " + otherState.numberOfNegExamples + ".  Found = " + this.numberOfNegExamples);
        }

        // Dataset name check?
        if ( this.prefix != otherState.prefix && (this.prefix == null || this.prefix.equals(otherState.prefix) == false) ) {
            throw new IncongruentSavedStateException("The dataset prefix not match. Expected = " + otherState.prefix + ".  Found = " + this.prefix);
        }

        // Make sure we are working on the same fold...
        if ( this.currentFold != otherState.currentFold ) {
            throw new IncongruentSavedStateException("Current fold does not match. Expected = " + otherState.currentFold + ".  Found = " + this.currentFold);
        }

        // Search Strategy
        if ( this.RRR != otherState.RRR ) {
            throw new IncongruentSavedStateException("Search strategy does not match. Expected RRR = " + otherState.RRR + ".  Found RRR = " + this.RRR);
        }

        // Rule length
        
    }

    public ILPouterLoopState clone() {
        try {
            return (ILPouterLoopState) super.clone();
        } catch(CloneNotSupportedException e) {
            return null;
        }
    }

    protected Collection<Example> getCoveredNegExamples() {
        return coveredNegExamples;
    }

    protected void setCoveredNegExamples(Collection<Example> coveredNegExamples) {
        this.coveredNegExamples = coveredNegExamples;
    }

    protected Collection<Example> getCoveredPosExamples() {
        return coveredPosExamples;
    }

    protected void setCoveredPosExamples(Collection<Example> coveredPosExamples) {
        this.coveredPosExamples = coveredPosExamples;
    }

    protected double getFractionOfNegCovered() {
        return fractionOfNegCovered;
    }

    protected void setFractionOfNegCovered(double fractionOfNegCovered) {
        this.fractionOfNegCovered = fractionOfNegCovered;
    }

    protected double getFractionOfPosCovered() {
        return fractionOfPosCovered;
    }

    protected void setFractionOfPosCovered(double fractionOfPosCovered) {
        this.fractionOfPosCovered = fractionOfPosCovered;
    }

    protected int getIndexIntoPosSeedArray() {
        return indexIntoPosSeedArray;
    }

    protected void setIndexIntoPosSeedArray(int indexIntoPosSeedArray) {
        this.indexIntoPosSeedArray = indexIntoPosSeedArray;
    }

    protected int getLengthPosSeedArray() {
        return lengthPosSeedArray;
    }

    protected void setLengthPosSeedArray(int lengthPosSeedArray) {
        this.lengthPosSeedArray = lengthPosSeedArray;
    }

    protected int getNumberOfCycles() {
        return numberOfCycles;
    }

    protected void setNumberOfCycles(int numberOfCycles) {
        this.numberOfCycles = numberOfCycles;
    }

    protected int getNumberOfLearnedClauses() {
        return numberOfLearnedClauses;
    }

    protected void setNumberOfLearnedClauses(int numberOfLearnedClauses) {
        this.numberOfLearnedClauses = numberOfLearnedClauses;
    }

    protected int getNumberOfNegExamples() {
        return numberOfNegExamples;
    }

    protected void setNumberOfNegExamples(int numberOfNegExamples) {
        this.numberOfNegExamples = numberOfNegExamples;
    }

    protected int getNumberOfNegExamplesCovered() {
        return numberOfNegExamplesCovered;
    }

    protected void setNumberOfNegExamplesCovered(int numberOfNegExamplesCovered) {
        this.numberOfNegExamplesCovered = numberOfNegExamplesCovered;
    }

    protected int getNumberOfPosExamples() {
        return numberOfPosExamples;
    }

    protected void setNumberOfPosExamples(int numberOfPosExamples) {
        this.numberOfPosExamples = numberOfPosExamples;
    }

    protected int getNumberOfPosExamplesCovered() {
        return numberOfPosExamplesCovered;
    }

    protected void setNumberOfPosExamplesCovered(int numberOfPosExamplesCovered) {
        this.numberOfPosExamplesCovered = numberOfPosExamplesCovered;
    }

    protected int[] getPosSeedIndicesToUse() {
        return posSeedIndicesToUse;
    }

    protected void setPosSeedIndicesToUse(int[] posSeedIndicesToUse) {
        this.posSeedIndicesToUse = posSeedIndicesToUse;
    }

    protected Theory getStdILPtheory() {
        return stdILPtheory;
    }

    protected void setStdILPtheory(Theory stdILPtheory) {
        this.stdILPtheory = stdILPtheory;
    }

    protected int getTotal_countOfPruningDueToVariantChildren() {
        return total_countOfPruningDueToVariantChildren;
    }

    protected void setTotal_countOfPruningDueToVariantChildren(int total_countOfPruningDueToVariantChildren) {
        this.total_countOfPruningDueToVariantChildren = total_countOfPruningDueToVariantChildren;
    }

    protected int getTotal_nodesExpanded() {
        return total_nodesExpanded;
    }
	/**
	 * @param total_nodesExpanded
	 */
	public void setTotal_nodesExpanded(int total_nodesExpanded) {
		this.total_nodesExpanded = total_nodesExpanded;
	}

    protected void setTotal_nodesConsidered(int total_nodesConsidered) {
        this.total_nodesExpanded = total_nodesConsidered;
    }

    protected int getTotal_nodesCreated() {
        return total_nodesCreated;
    }

    protected void setTotal_nodesCreated(int total_nodesCreated) {
        this.total_nodesCreated = total_nodesCreated;
    }

    protected int getTotal_nodesNotAddedToOPENsinceMaxScoreTooLow() {
        return total_nodesNotAddedToOPENsinceMaxScoreTooLow;
    }

    protected void setTotal_nodesNotAddedToOPENsinceMaxScoreTooLow(int total_nodesNotAddedToOPENsinceMaxScoreTooLow) {
        this.total_nodesNotAddedToOPENsinceMaxScoreTooLow = total_nodesNotAddedToOPENsinceMaxScoreTooLow;
    }

    protected int getTotal_nodesRemovedFromOPENsinceMaxScoreNowTooLow() {
        return total_nodesRemovedFromOPENsinceMaxScoreNowTooLow;
    }

    protected void setTotal_nodesRemovedFromOPENsinceMaxScoreNowTooLow(int total_nodesRemovedFromOPENsinceMaxScoreNowTooLow) {
        this.total_nodesRemovedFromOPENsinceMaxScoreNowTooLow = total_nodesRemovedFromOPENsinceMaxScoreNowTooLow;
    }

    /**
     * @return the currentFold
     */
    protected int getCurrentFold() {
        return currentFold;
    }

    /**
     * @param currentFold the currentFold to set
     */
    protected void setCurrentFold(int currentFold) {
        this.currentFold = currentFold;
    }

    /**
     * @return the prefix
     */
    protected String getPrefix() {
        return prefix;
    }

    /**
     * @param prefix the prefix to set
     */
    protected void setPrefix(String prefix) {
        this.prefix = prefix;
    }

    /**
     * @return the useRRR
     */
    protected boolean isRRR() {
        return RRR;
    }

    /**
     * @param useRRR the useRRR to set
     */
    protected void setRRR(boolean useRRR) {
        this.RRR = useRRR;
    }

    /**
     * @return the flipFlopPosAndNegExamples
     */
    protected boolean isFlipFlopPosAndNegExamples() {
        return flipFlopPosAndNegExamples;
    }

    /**
     * @param flipFlopPosAndNegExamples the flipFlopPosAndNegExamples to set
     */
    protected void setFlipFlopPosAndNegExamples(boolean flipFlopPosAndNegExamples) {
    //	Utils.println("% ILPouterLoopState.setFlipFlopPosAndNegExamples from " + this.flipFlopPosAndNegExamples + " to " + flipFlopPosAndNegExamples + ".");
        this.flipFlopPosAndNegExamples = flipFlopPosAndNegExamples;
    }

    /**
     * @return the negExamplesUsedAsSeeds
     */
    protected Set<Example> getNegExamplesUsedAsSeeds() {
        return seedNegExamplesUsed;
    }

    /**
     * @param negExamplesUsedAsSeeds the posExamplesUsedAsSeeds to set
     */
    protected void setPosExamplesUsedAsSeeds(Set<Example> posExamplesUsedAsSeeds) {
        this.seedPosExamplesUsed = posExamplesUsedAsSeeds;
    }

    /**
     * @param negExamplesUsedAsSeeds the negExamplesUsedAsSeeds to set
     */
    protected void setNegExamplesUsedAsSeeds(Set<Example> negExamplesUsedAsSeeds) {
        this.seedNegExamplesUsed = negExamplesUsedAsSeeds;
    }

        /**
     * @return the seedPosExamplesUsed
     */
    protected Set<Example> getSeedPosExamplesUsed() {
        if ( seedPosExamplesUsed == null ) seedPosExamplesUsed = new HashSet<Example>();

        return seedPosExamplesUsed;
    }

    /**
     * @param seedPosExamplesUsed the seedPosExamplesUsed to set
     */
    protected void setSeedPosExamplesUsed(Set<Example> seedPosExamplesUsed) {
        this.seedPosExamplesUsed = seedPosExamplesUsed;
    }

    /**
     * @return the seedNegExamplesUsed
     */
    protected Set<Example> getSeedNegExamplesUsed() {
        if ( seedNegExamplesUsed == null ) seedNegExamplesUsed = new HashSet<Example>();

        return seedNegExamplesUsed;
    }
    
    protected void clearSeedPosExamplesUsed() {
    	if ( seedPosExamplesUsed == null ) { seedPosExamplesUsed = new HashSet<Example>(4); return; }
    	seedPosExamplesUsed.clear();
    }
    
    protected void clearSeedNegExamplesUsed() {
    	if ( seedNegExamplesUsed == null ) { seedNegExamplesUsed = new HashSet<Example>(4);return; }
    	seedNegExamplesUsed.clear();
    }

    /**
     * @param seedNegExamplesUsed the seedNegExamplesUsed to set
     */
    protected void setSeedNegExamplesUsed(Set<Example> seedNegExamplesUsed) {
        this.seedNegExamplesUsed = seedNegExamplesUsed;
    }

    /**
     * @return the clockTimeUsed
     */
    public long getClockTimeUsedInMillisec() {
        return clockTimeUsedInMillisec;
    }

    /**
     * @param clockTimeUsed the clockTimeUsed to set
     */
    public void setClockTimeUsedInMillisec(long clockTimeUsed) {
        this.clockTimeUsedInMillisec = clockTimeUsed;
    }

    /**
     * @return the maximumClockTime
     */
    public long getMaximumClockTimeInMillisec() {
        return maximumClockTimeInMillisec;
    }

    /**
     * @param maximumClockTime the maximumClockTime to set
     */
    public void setMaximumClockTimeInMillisec(long maximumClockTime) {
        this.maximumClockTimeInMillisec = maximumClockTime;
    }
	
	public TreeStructuredLearningTask popQueueOfTreeStructuredLearningTasks() {
		if (queueOfTreeStructuredLearningTasksIsEmpty()) { return null; }
		return queueOfTreeStructuredLearningTasks.remove(0);
	}	
	
	// This method assumes LOWER scores are better.
	public void addToQueueOfTreeStructuredLearningTasks(TreeStructuredLearningTask task, TreeStructuredTheoryInteriorNode treeNode, SingleClauseNode creatingSearchNode, double score) {
		if (true) { Utils.println("%      addToQueueOfTreeStructuredLearningTasks (level=" + Utils.comma(treeNode == null ? -1 : treeNode.getLevel()) 
					+ "; score=" + Utils.truncate(score, 6) + ")\n%         ILP node to extend: "	+  creatingSearchNode);
		}
		task.setCreatingNode(creatingSearchNode);
		task.setScore(score);
		insertIntoQueueOfLearningTasks(task, (treeNode == null ? -1 : treeNode.getLevel()), score);
	}
	
	// This method assumes LOWER scores are better.
	private void insertIntoQueueOfLearningTasks(TreeStructuredLearningTask task, int level, double score) {
		if (queueOfTreeStructuredLearningTasks == null) { queueOfTreeStructuredLearningTasks = new LinkedList<TreeStructuredLearningTask>(); }
		int counter = 0;
		int size    = Utils.getSizeSafely(queueOfTreeStructuredLearningTasks);
		for (TreeStructuredLearningTask item : queueOfTreeStructuredLearningTasks) {
			if (score < item.getScore()) { // See if the new node's score belongs BEFORE this item.  (Ties go AFTER old entries.)
				queueOfTreeStructuredLearningTasks.add(counter, task);
				if (true) { Utils.println("%      Insert tree-structured search node (@ level = " + Utils.comma(level) + " and with score = " + Utils.truncate(score, 6) + ") into position #" + Utils.comma(counter + 1) + " in the search queue (new size=" + Utils.comma(size + 1)+  ")."); }
				return;
			}
			counter++;
		}
		if (true) { Utils.println("%      Insert tree-structured search node (@ level = " + Utils.comma(level) + " and with score = " + Utils.truncate(score, 6) + ") into the LAST position (#" + Utils.comma(counter + 1) + ") in the search queue."); }
		queueOfTreeStructuredLearningTasks.add(task);
	}

	public boolean queueOfTreeStructuredLearningTasksIsEmpty() {
		return (queueOfTreeStructuredLearningTasks == null || queueOfTreeStructuredLearningTasks.isEmpty()) ;
	}

	/**
	 * @return the current tree-based theory
	 */
	public TreeStructuredTheory getTreeBasedTheory() {
		return treeBasedTheory;
	}

	/**
	 * @param treeBasedTheory
	 */
	public void setTreeBasedTheory(TreeStructuredTheory treeBasedTheory) {
		this.treeBasedTheory = treeBasedTheory;
	}

	/**
	 * @return the current tree-learning task.
	 */
	public TreeStructuredLearningTask getCurrentTreeLearningTask() {
		return currentTreeLearningTask;
	}

	/**
	 * @param currentTreeLearningTask
	 */
	public void setCurrentTreeLearningTask(TreeStructuredLearningTask currentTreeLearningTask) {
		this.currentTreeLearningTask = currentTreeLearningTask;
	}

	public double getOverallMinPosWeight() {
		return overallMinPosWeight;
	}

	public void setOverallMinPosWeight(double wgt) {
	//	Utils.waitHere("setOverallMinPosWeight: " + wgt);
		this.overallMinPosWeight = wgt;
	}
    
    public void clearAll() {
    	if (coveredPosExamples     != null) { coveredPosExamples.clear(); }
    	if (coveredNegExamples     != null) { coveredNegExamples.clear(); }
    	if (seedPosExamplesUsed    != null) { seedPosExamplesUsed.clear(); }
    	if (seedNegExamplesUsed    != null) { seedNegExamplesUsed.clear(); }
    	if (queueOfTreeStructuredLearningTasks != null) { queueOfTreeStructuredLearningTasks.clear(); }
    	stdILPtheory = null;
    }

}
