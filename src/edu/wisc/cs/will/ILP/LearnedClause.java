/**
 * 
 */
package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

/**
 * @author shavlik
 * 
 * This is a clause with some extra information concerning how it was learned.
 *
 */
@SuppressWarnings("serial")
public class LearnedClause extends Clause {
	private LearnOneClause   task;
	private SingleClauseNode node;
	private int outerLoopCycle; 
	private int totalNumberOfPosExamplesCovered; 
	private int numberOfPosExamplesCovered; 
	private int newlyCoveredPosExamples;
	private int numberOfPosExamples;
	private int totalNumberOfNegExamplesCovered; 
	private int numberOfNegExamplesCovered; 
	private int newlyCoveredNegExamples;
	private int numberOfNegExamples;
	
	public LearnedClause(LearnOneClause task, SingleClauseNode node, int outerLoopCycle,
						 int totalNumberOfPosExamplesCovered, int numberOfPosExamplesCovered, int newlyCoveredPosExamples, int numberOfPosExamples, 
						 int totalNumberOfNegExamplesCovered, int numberOfNegExamplesCovered, int newlyCoveredNegExamples, int numberOfNegExamples) {
		super(task.getStringHandler(), node.getClause()); // TODO (I no longer recall why we) need to rename this learned clause, but since 'node' is a property, have not yet done so, because node and all its parents would then not match the clause.
		this.task                       = task;
		this.node                       = node;
		this.outerLoopCycle             = outerLoopCycle; 
		this.numberOfPosExamplesCovered = numberOfPosExamplesCovered; 
		this.newlyCoveredPosExamples    = newlyCoveredPosExamples;
		this.numberOfPosExamples        = numberOfPosExamples;
		this.numberOfNegExamplesCovered = numberOfNegExamplesCovered; 
		this.newlyCoveredNegExamples    = newlyCoveredNegExamples;
		this.numberOfNegExamples        = numberOfNegExamples;
		this.totalNumberOfPosExamplesCovered = totalNumberOfPosExamplesCovered;
		this.totalNumberOfNegExamplesCovered = totalNumberOfNegExamplesCovered;
	}
	
	public String reportStats() throws SearchInterrupted {
		double percentPos      = 100 * (double)numberOfPosExamplesCovered      / numberOfPosExamples;
		double precentNeg      = 100 * (double)numberOfNegExamplesCovered      / numberOfNegExamples;
		double percentTotalPos = 100 * (double)totalNumberOfPosExamplesCovered / numberOfPosExamples;
		double percentTotalNeg = 100 * (double)totalNumberOfNegExamplesCovered / numberOfNegExamples;
		
		String result = "\n // Learned this clause on outer loop cycle #" + outerLoopCycle + ".  It scores=" 
						+ Utils.truncate(node.score, 2) + " and has recall=" + Utils.truncate(node.recall(), 2) + ", precision=" + Utils.truncate(node.precision(), 2) + ", and F1=" + Utils.truncate(node.F(1.0), 2) + " (using m-estimates)."
						+ "\n // It covers " + Utils.truncate(percentPos) + "% of the positive examples, " + numberOfPosExamplesCovered + " of " + numberOfPosExamples
						+ (newlyCoveredPosExamples < numberOfPosExamplesCovered ? " (of which " + newlyCoveredPosExamples + " are newly covered)" : "") + ","
						+ (task.regressionTask ? ""
											   : "\n // and "+ Utils.truncate(precentNeg) + "% of the negative examples, " + numberOfNegExamplesCovered + " of " + numberOfNegExamples
											                 + (newlyCoveredNegExamples < numberOfNegExamplesCovered ? " (of which " + newlyCoveredNegExamples + " are newly covered)" : "") + ".")
						+ (outerLoopCycle > 1 ? "\n // So far " + totalNumberOfPosExamplesCovered + " (" + Utils.truncate(percentTotalPos) + "%) of the positive " 
						                        + (task.regressionTask ? "" : "and " + totalNumberOfNegExamplesCovered +  " (" + Utils.truncate(percentTotalNeg) + "%) of the negative ")
						                        + "examples have been covered." 
						                      : "")	+ "";		
		return result;
	}
	
	public String toPrettyString(boolean useStdLogicNotation) {	
		try {
			return reportStats() + "\n" + super.toPrettyString();
		}
		catch (SearchInterrupted e) {
			Utils.reportStackTrace(e);
			Utils.error("Something went wrong when trying to report statistics on a learned clause.  Error message: " + e.getMessage());
			return null;
		}
	}
	
	public String toString() {	
		try {
			return reportStats() + "\n" + super.toString();
		}
		catch (SearchInterrupted e) {
			Utils.reportStackTrace(e);
			Utils.error("Something went wrong when trying to report statistics on a learned clause.  Error message: " + e.getMessage());
			return null;
		}
	}

}
