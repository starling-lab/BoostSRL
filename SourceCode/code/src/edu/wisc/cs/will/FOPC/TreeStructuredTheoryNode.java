package edu.wisc.cs.will.FOPC;

import java.util.Collection;
import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.Utils.Utils;

public abstract class TreeStructuredTheoryNode extends AllOfFOPC {
	
	protected double weightedCountOfPositiveExamples = 0;
	protected double weightedCountOfNegativeExamples = 0;
	protected double mEstimatePos = 0.1; // Be careful if the example weight is normalized to 1.
	protected double mEstimateNeg = 0.1;	
	protected TreeStructuredTheoryInteriorNode parent = null;     // Need this in case tree-surgery is needed.
	protected int level = -1; // Level in the tree. Root=0.  I.e., this counts number of ancestor nodes.
	// Used for creating a graph in DOT format.
	protected int nodeNumber = 0;
	
	public TreeStructuredTheoryInteriorNode getParent() {
		return parent;
	}

	public void setParent(TreeStructuredTheoryInteriorNode parent) {
		this.parent = parent;
		level = (parent == null ? 0 : parent.level + 1);
	}
	
	public double estimatedProbOfPositiveExample() {
		// Could cache this calculation, but probably fast enough to not bother.
		// For CLASSIFICATION trees, should this BE the leafValue?
		return (weightedCountOfPositiveExamples + mEstimatePos) / (weightedCountOfPositiveExamples + mEstimatePos + weightedCountOfNegativeExamples + mEstimateNeg);
	}

	public double getWeightedCountOfPositiveExamples() {
		return weightedCountOfPositiveExamples;
	}

	public void setWeightedCountOfPositiveExamples(double weightedCountOfPositiveExamples) {
		this.weightedCountOfPositiveExamples = weightedCountOfPositiveExamples;
	}

	public double getWeightedCountOfNegativeExamples() {
		return weightedCountOfNegativeExamples;
	}

	public void setWeightedCountOfNegativeExamples(double weightedCountOfNegativeExamples) {
		this.weightedCountOfNegativeExamples = weightedCountOfNegativeExamples;
	}

	public double getMEstimatePos() {
		return mEstimatePos;
	}

	public void setMEstimatePos(double estimatePos) {
		mEstimatePos = estimatePos;
	}

	public double getMEstimateNeg() {
		return mEstimateNeg;
	}

	public void setMEstimateNeg(double estimateNeg) {
		mEstimateNeg = estimateNeg;
	}

	public abstract String                   printRelationalTree(String newLineStarter, int precedenceOfCaller, int depth, BindingList bindingList);
	public abstract List<Clause>             collectPathsToRoots(TreeStructuredTheory treeTheory);
	public abstract TreeStructuredTheoryNode applyTheta(Map<Variable,Term> bindings);	
	public abstract Collection<Variable>     collectFreeVariables(Collection<Variable> boundVariables); 
	public abstract Collection<Variable>     collectAllVariables();

	protected static int counter=0;
	public abstract String writeDotFormat();

	/**
	 * @return the level
	 */
	public int getLevel() {
		return level;
	}

	/**
	 * @param level the level to set
	 */
	public void setLevel(int level) {
		if (this.level >= 0 && this.level != level) { Utils.waitHere("Setting to level = " + level + " but level currently equals = " + this.level + ":\n  " + this); }
		this.level = Math.max(0, level);
	}
	

}
