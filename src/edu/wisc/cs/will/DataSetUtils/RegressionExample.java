package edu.wisc.cs.will.DataSetUtils;

import java.io.Serializable;
import java.util.HashMap;
import java.util.Map;

import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.ILP.SingleClauseNode;
import edu.wisc.cs.will.Utils.Utils;

public class RegressionExample extends Example  implements Serializable {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	// The regression value that the trees should match
	private double outputValue = 0.0;

	// The expected regression value that we want to match (not used for RFGB but only if pos.txt contains regression examples)
	// This is the regression value mentioned in pos.txt
	public double originalRegressionOrProbValue = 0.0;
	
	// Does this example have a regression vector to fit instead of value ?
	// TODO(TVK): Should always be a vector ?
	private boolean hasRegressionVector = false;
	
	private double[] outputVector = null;
	
	public String leafId = "";
	
	public RegressionExample(HandleFOPCstrings stringHandler, Literal literal, double outputValue, String provenance, String extraLabel) {
		this(stringHandler, literal, outputValue, provenance, extraLabel, null);
	}
	public RegressionExample(HandleFOPCstrings stringHandler, Literal literal, double outputValue, String provenance, String extraLabel, Term annotationTerm) {
		super(stringHandler, literal, provenance, extraLabel, annotationTerm);
		this.setOutputValue(outputValue);
	}

	public RegressionExample(HandleFOPCstrings stringHandler, Literal literal, String provenance) {
		super(stringHandler, literal, provenance);
		this.setOutputValue(literal.getWeightOnSentence());
		this.setWeightOnSentence(); // In this and the next call, the weight on the literal is being used to temporarily hold the output value for this example. 
	}
	public RegressionExample(HandleFOPCstrings stringHandler, Literal literal, String provenance, String extraLabel, Term annotationTerm) {
		super(stringHandler, literal, provenance, extraLabel, annotationTerm);
		this.setOutputValue(literal.getWeightOnSentence());
		this.setWeightOnSentence();		
	}
	public RegressionExample(RegressionExample copy) {
		super(copy.getStringHandler(), copy, copy.provenance, copy.extraLabel, copy.getAnnotationTerm());
		this.hasRegressionVector = copy.hasRegressionVector;
		this.originalRegressionOrProbValue = copy.originalRegressionOrProbValue;
		if (copy.isHasRegressionVector()) {
			setOutputVector(copy.getOutputVector());
		} else {
			setOutputValue(copy.getOutputValue());
		}
		leafId = copy.leafId;
	}
	private Map<SingleClauseNode, Long> cachedNumberOfGroundings = null;
	
	public void cacheNumGroundings(SingleClauseNode key, long num) {
		if (cachedNumberOfGroundings == null) cachedNumberOfGroundings = new HashMap<SingleClauseNode, Long>();
		cachedNumberOfGroundings.put(key, num);
	}
	
	public long lookupCachedGroundings(SingleClauseNode key) {
		if (cachedNumberOfGroundings == null ||
			!cachedNumberOfGroundings.containsKey(key)) { return -1; }
		return cachedNumberOfGroundings.get(key);
	}

	public void clearCache() {
		cachedNumberOfGroundings = null;
	}
	/**
	 * @return the outputValue
	 */
	public double getOutputValue() {
		if (hasRegressionVector) {
			Utils.error("Retrieving scalar output value for " + this.toString() + "\n but has regression vector: " + getOutputVector());
		}
		return outputValue;
	}
	/**
	 * @param outputValue the outputValue to set
	 */
	public void setOutputValue(double outputValue) {
		this.outputValue = outputValue;
	}
	/**
	 * @return the outputVector
	 */
	public double[] getOutputVector() {
		if (!hasRegressionVector) {
			Utils.error("Retrieving regression vector for " + this.toString() + "\n but has scalar output value: " + getOutputValue());
		}
		return outputVector;
	}
	/**
	 * @param outputVector the outputVector to set
	 */
	public void setOutputVector(double[] outputVector) {
		setHasRegressionVector(true);
		this.outputVector = outputVector;
	}
	/**
	 * @return the hasRegressionVector
	 */
	public boolean isHasRegressionVector() {
		return hasRegressionVector;
	}
	/**
	 * @param hasRegressionVector the hasRegressionVector to set
	 */
	public void setHasRegressionVector(boolean hasRegressionVector) {
		this.hasRegressionVector = hasRegressionVector;
	}
	
	
	
}
