package edu.wisc.cs.will.Boosting.RDN;

import java.io.Serializable;
import java.util.Arrays;

import edu.wisc.cs.will.Boosting.EM.HiddenLiteralState;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.DataSetUtils.RegressionExample;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.Utils;

/**
 * Regression Example used for learning RDNs
 * TODO move to DataSetUtils, maybe?
 * @author Tushar Khot
 *
 */
public class RegressionRDNExample extends RegressionExample  implements Serializable  {
	
	/**
	 *  This is used to indicate the original truth value of an example
	 *  Should not be changed once set
	 */
	@Deprecated
	private boolean originalTruthValue = false;
	
	/**
	 * Rather than using a boolean value, use integer for original value
	 * for single class problem, 0==false, 1==true
	 * for multi  class problem, the originalValue is an index to a constant value stored in MultiClassExampleHandler
	 */
	private int originalValue = 0;
	
	/**
	 *  This indicates whether this is a hidden literal. Original truth value wouldn't be useful if this is
	 *  set to true. 
	 *  
	 */
	private boolean hiddenLiteral = false;
	
	/**
	 * Only set if hiddenLiteral is set to true. 
	 */
	private int originalHiddenLiteralVal = 0;
	
	/**
	 *  This is to be only used while sampling.
	 */
	@Deprecated
	private boolean sampledTruthValue=(Utils.random() > 0.8);
	
	/**
	 * Rather than using a boolean value, use integer for sampled value
	 * for single class problem, 0==false, 1==true
	 * for multi class problem, the sampledValue is an index to a constant value stored in MultiClassExampleHandler
	 */
	private int sampledValue= (Utils.random() > 0.8) ? 1 : 0;
	
	
	/**
	 * Examples may have an associated state assignment to the hidden literals for the corresponding 
	 * output value.
	 */
	private HiddenLiteralState stateAssociatedWithOutput = null;
	
	
	
	/**
	 * The probability of this example being true. Generally set by sampling procedure
	 * Hence  has Nan default value.
	 */
	private ProbDistribution probOfExample = null;
	
	public RegressionRDNExample(HandleFOPCstrings stringHandler, Literal literal, double outputValue, String provenance, String extraLabel) {
		super(stringHandler, literal, outputValue, provenance, extraLabel);
	}

	public RegressionRDNExample(HandleFOPCstrings stringHandler, Literal literal, double outputValue, String provenance, String extraLabel, boolean truthValue) {
		super(stringHandler, literal, outputValue, provenance, extraLabel);
		originalTruthValue = truthValue;
		originalValue = truthValue ? 1:0;
	}
	public RegressionRDNExample(RegressionRDNExample copy) {
		super(copy);
		originalTruthValue = copy.originalTruthValue;
		probOfExample = new ProbDistribution(copy.probOfExample);
		sampledTruthValue = copy.sampledTruthValue;
		hiddenLiteral = copy.hiddenLiteral;
		originalValue = copy.originalValue;
		sampledValue  = copy.sampledValue;
		stateAssociatedWithOutput = copy.stateAssociatedWithOutput;
	}
	public RegressionRDNExample(Example ex, boolean truthValue) {
		super(ex.getStringHandler(), ex, (truthValue ? 1 : 0), ex.provenance, ex.extraLabel);
		originalTruthValue = truthValue;
		originalValue = truthValue ? 1:0;
	}
	public RegressionRDNExample(Literal lit, boolean truthValue, String provenance) {
		this(lit.getStringHandler(), lit, (truthValue ? 1 : 0), provenance, null);
	}
	/*
	public RegressionRDNExample(HandleFOPCstrings stringHandler, Example ex) {
		super(stringHandler, ex);
		originalTruthValue = truthValue;
	}
*/
	/**
	 * 
	 */
	private static final long serialVersionUID = 5438994291636517166L;
	/**
	 * @return the originalTruthValue
	 */
	public boolean isOriginalTruthValue() {
		if (isHiddenLiteral()) {
			Utils.waitHere("Can't trust original truth value here");
		}
		if (getOriginalValue() > 1) {
			Utils.error("Checking for truth value for multi-class example.");
		}
		return getOriginalValue() == 1;
		//return originalTruthValue;
	}

	/**
	 * @param originalTruthValue the originalTruthValue to set
	 */
	public void setOriginalTruthValue(boolean originalTruthValue) {
		// this.originalTruthValue = originalTruthValue;
		setOriginalValue(originalTruthValue?1:0);
	}

	
	
	/**
	 * @return the hiddenLiteral
	 */
	public boolean isHiddenLiteral() {
		return hiddenLiteral;
	}

	/**
	 * @param hiddenLiteral the hiddenLiteral to set
	 */
	public void setHiddenLiteral(boolean hiddenLiteral) {
		this.hiddenLiteral = hiddenLiteral;
	}

	/**
	 * @return the originalHiddenLiteralVal
	 */
	public int getOriginalHiddenLiteralVal() {
		if (!isHiddenLiteral()) {
			Utils.error("Not hidden literal!");
		}
		return originalHiddenLiteralVal;
	}

	/**
	 * @param originalHiddenLiteralVal the originalHiddenLiteralVal to set
	 */
	public void setOriginalHiddenLiteralVal(int originalHiddenLiteralVal) {
		if (!isHiddenLiteral()) {
			Utils.error("Not hidden literal!");
		}
		this.originalHiddenLiteralVal = originalHiddenLiteralVal;
	}

	/**
	 * @return the probOfExample
	 */
	public ProbDistribution getProbOfExample() {
		if (probOfExample == null) {
			Utils.error("Probability was not set");
			return null;
		}
		
		return probOfExample;
	}

	/**
	 * @param probOfExample the probOfExample to set
	 */
	public void setProbOfExample(ProbDistribution probOfExample) {
	//	System.out.println("Probability set:" + probOfExample);
		this.probOfExample = probOfExample;
	}
	
	public String toString() {
		String result= super.toString();
		return result; // + " Actual Bool=" + originalTruthValue +" Prob=" + probOfExample + " Output=" + outputValue;
	}

	public String toPrettyString() {
		String result= super.toString();
		result += " Actual Bool=" + originalTruthValue +" Prob=" + probOfExample + " Output=";
		if (isHasRegressionVector()) {
			result += Arrays.toString(getOutputVector());
		} else {
			result += getOutputValue();
		}
		return result;
	}
	
/*	*//**
	 * @param sampledTruthValue the sampledTruthValue to set
	 *//*
	public void setSampledTruthValue(boolean sampledTruthValue) {
		this.sampledTruthValue = sampledTruthValue;
	}

	*//**
	 * @return the sampledTruthValue
	 *//*
	public boolean getSampledTruthValue() {
		return sampledTruthValue;
	}
*/
	/**
	 * @return the originalValue
	 */
	public int getOriginalValue() {
		if (isHiddenLiteral()) {
			Utils.waitHere("Can't trust original value here");
		}
		return originalValue;
	}

	/**
	 * @param originalValue the originalValue to set
	 */
	public void setOriginalValue(int originalValue) {
		this.originalValue = originalValue;
	}

	/**
	 * @return the sampledValue
	 */
	public int getSampledValue() {
		return sampledValue;
	}

	/**
	 * @param sampledValue the sampledValue to set
	 */
	public void setSampledValue(int sampledValue) {
		this.sampledValue = sampledValue;
	}

	/**
	 * @return the stateAssociatedWithOutput
	 */
	public HiddenLiteralState getStateAssociatedWithOutput() {
		return stateAssociatedWithOutput;
	}

	/**
	 * @param stateAssociatedWithOutput the stateAssociatedWithOutput to set
	 */
	public void setStateAssociatedWithOutput(HiddenLiteralState stateAssociatedWithOutput) {
		this.stateAssociatedWithOutput = stateAssociatedWithOutput;
	}

}
