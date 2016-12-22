/**
 * 
 */
package edu.wisc.cs.will.DataSetUtils;

import java.util.ArrayList;
import java.util.List;

import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.ResThmProver.HornClauseProver;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

/**
 * @author shavlik
 *
 */
public class ExamplesByFeatures {
	protected final static int debugLevel = 0; // Used to control output from this class (0 = no output, 1=some, 2=much, 3=all).
	
	private double       defaultTolerance = 1e-9;
	private double[][]   matrixA;
	private double[]     outputs;
	private List<Object> features;
	private List<Object> discardedFeatures; // Probably should keep who they matched as well, but this can be a moving target as the indices change.
	
	public ExamplesByFeatures(double[][] matrixA, double[] outputs, List<Object> features) {
		super();
		this.matrixA  = matrixA;
		this.outputs  = outputs;
		this.features = features;
		discardedFeatures = new ArrayList<Object>(4);
	}
	
	// These would be more efficient if written as linked lists, at least when there are a good number of removes.
	public void removeFeature(int i) {
		double[][] new_matrixA = new double[getNumberOfExamples()][getNumberOfFeatures() - 1];
		
		for (int e = 0; e < getNumberOfExamples(); e++) {
			for (int f = 0; f < getNumberOfFeatures() - 1; f++) {
				if (f <  i) { new_matrixA[e][f] = matrixA[e][f]; }
				else        { new_matrixA[e][f] = matrixA[e][f+1]; } // Shift to the right.
			}
		}
		matrixA = new_matrixA;
		// No change to 'outputs'
		features.remove(i);
	}
	public void removeExample(int i) {
		double[][] new_matrixA = new double[getNumberOfExamples() - 1][getNumberOfFeatures()];
		double[]   new_outputs = new double[getNumberOfExamples() - 1];
		
		for (int e = 0; e < getNumberOfExamples() - 1; e++) {
			new_outputs[e] = outputs[e+1]; // Shift up.
			for (int f = 0; f < getNumberOfFeatures(); f++) {
				if (f <  i) { new_matrixA[e][f] = matrixA[e][f]; }
				else        { new_matrixA[e][f] = matrixA[e+1][f]; } // Shift up.
			}
		}
		matrixA = new_matrixA;	
		outputs = new_outputs;
		// No change to 'features'
	}
	

	public int getNumberOfExamples() {
		return outputs.length;
	}
	public int getNumberOfFeatures() {
		return features.size();
	}

	public double[][] getMatrixA() {
		return matrixA;
	}
	public void setMatrixA(double[][] matrixA) {
		this.matrixA = matrixA;
	}

	public double[] getOutputs() {
		return outputs;
	}
	public void setOutputs(double[] outputs) {
		this.outputs = outputs;
	}

	public List<Object> getFeatures() {
		return features;
	}
	public void setFeatures(List<Object> features) {
		this.features = features;
	}
	public List<Object> getDiscardedFeatures() {
		return discardedFeatures;
	}

	public void removeDuplicateColumns() {
		removeDuplicateColumns(defaultTolerance);
	}
	public void removeDuplicateColumns(double toleranceToUse) {
		int currentFeature = 1; // The first time through, compare feature 1 to feature 0 (in general, feature i to features 0 ... i-1).
		
		if (debugLevel > 0) { Utils.print("% Looking for duplicated features (tolerance = " + toleranceToUse + "):"); } 
		while (currentFeature < getNumberOfFeatures()) {
			// See if current feature is equivalent to an earlier feature.  If so, delete current feature and repeat.
			if (debugLevel > 1) { Utils.print(currentFeature + " vs. "); } 
			int  earlierFeatureToConsider = 0;
			while (earlierFeatureToConsider < currentFeature && currentFeature < getNumberOfFeatures()) { // Need this extra check in case duplications being removed.
				if (equivalentFeatures(earlierFeatureToConsider, currentFeature, toleranceToUse)) { 
					if (debugLevel > 0) { Utils.println("\n% *** Remove:   " + features.get(currentFeature)); }
					if (debugLevel > 0) { Utils.println(  "% ***  it dups: " + features.get(earlierFeatureToConsider)); }
					if (debugLevel > 0) { Utils.println(  "% ***  curr=" + currentFeature + " earlier=" + earlierFeatureToConsider + " #" + getNumberOfFeatures()); }
					discardedFeatures.add(features.get(currentFeature));
					removeFeature(currentFeature);
					if (getNumberOfFeatures() < 2) { return; } // Have deleted all but the first feature.
				}
				else { 
					if (debugLevel > 1) { Utils.print(" " + earlierFeatureToConsider); }
					earlierFeatureToConsider++; // Advance to the next feature, stopping when up to the feature under consideration.
				}
			}
			if (debugLevel > 1) { Utils.println(""); } 
			currentFeature++;
		}	
	}

	public void fillAandY(Literal query, int locOfNumericVar, List<Example> examples, Unifier unifier, HornClauseProver prover) throws SearchInterrupted {
		if (outputs.length != examples.size()) {
			Utils.error("Need to have #outputs (= " + outputs.length + ") = #examples (= " + examples.size() + ")");
		}
		if (features.size() != matrixA[0].length)  {
			Utils.error("Need to have #features (= " + features.size() + ") = #columns of A (= " + matrixA[0].length + ")");
		}
		int i = 0;
		for (Example ex : examples) {
			List<Term> arguments2 = query.getArguments();// Do things this way in case the arguments are named.
			arguments2.clear();
			arguments2.addAll(ex.getArguments());
			query.setArguments(arguments2);
	        outputs[i] = ((NumericConstant) ex.getArgument(locOfNumericVar)).value.doubleValue();
			//Utils.println("// " + ex + "   y = " + y[i]);
			int j = 0;
			for (Object obj : features) {
				Clause         c    = (Clause) obj;
				Literal        head = c.posLiterals.get(0);
				List<Literal>  body = c.negLiterals;
				Variable   queryVar = (Variable) head.getArgument(locOfNumericVar); // This should really be the same variable in all features, but play it safe and pull it out each time.
				//Utils.print(" " + c + " = ");
				arguments2 = query.getArguments(); // Do this so named arguments can be checked. 
				arguments2.set(locOfNumericVar, queryVar); // Don't want any matching at this position by the unifier, so use the same variable in the head and the query.
				query.setArguments(arguments2);
				//Utils.println("\n unify(" + head + "," + query + ")");
				BindingList theta = unifier.unify(query, head); // Pull out the example and time-step fields of this example.
				BindingList result = null;
				if (body.size() < 2) {
					Literal newBody = body.get(0).copy(false);
					newBody = newBody.applyTheta(theta.theta); // Apply the binding list to a COPY of the body (since applyTheta works 'in place').
					//Utils.println("  prove(" + newBody +")");
					result = prover.proveSimpleQueryAndReturnBindings(newBody); // Evaluate this body.
				}
				else {
					List<Literal> newBody = new ArrayList<Literal>(body.size());
					for (Literal lit : body) {
						Literal newLit = lit.copy(false);
						newLit = newLit.applyTheta(theta.theta); // Apply the binding list to a COPY of the body (since applyTheta works 'in place').
						newBody.add(newLit);
					}
					//Utils.println("  prove(" + newBody +")");
					result = prover.proveConjunctiveQueryAndReturnBindings(newBody); // Evaluate this body.
				}
				// Utils.println("  result=" + result);
				Term         answer = (result == null ? null : result.lookup(queryVar)); // Pull out the value.
				//Utils.println(" " + answer + ": "+ c);
				// Use zero for the value if not true.
				matrixA[i][j] = (answer == null ? 0.0 : ((NumericConstant) answer).value.doubleValue());
				j++;																	
			}
			i++;
			// Utils.println("");
		}
	}
	
	public void reportMatrixA(boolean alsoPrintOutput) { // Print the A matrix to the screen.
		if (alsoPrintOutput) { Utils.println("\nThe Dataset:"); } else { Utils.println("\nThe Features (columns) for Each Example (rows):"); }
		for (int e = 0; e < getNumberOfExamples(); e++) {
			Utils.print(" " + matrixA[e][0]);
			for (int f = 1; f < getNumberOfFeatures(); f++) {
				Utils.print(", " + matrixA[e][f]);
			}
			if (alsoPrintOutput) { Utils.print("  --->  " + outputs[e]); }
			Utils.println("");
		}
	}
			
	private boolean equivalentFeatures(int f1, int f2, double toleranceToUse) {	
		for (int e = 0; e < getNumberOfExamples(); e++) {
				if (Math.abs(matrixA[e][f1] - matrixA[e][f2]) > toleranceToUse) { return false; }
		}
		return true;		
	}	

}
