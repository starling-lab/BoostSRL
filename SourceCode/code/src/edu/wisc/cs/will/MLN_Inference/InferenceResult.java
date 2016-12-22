package edu.wisc.cs.will.MLN_Inference;

import edu.wisc.cs.will.MLN_Task.GroundLiteral;
import edu.wisc.cs.will.Utils.Utils;

public class InferenceResult {
	public GroundLiteral groundLiteral;
	public double        probability;
	public String        documentation;
	
	public InferenceResult(GroundLiteral groundLiteral, double probability, String documentation) {
		this.groundLiteral = groundLiteral;
		this.probability   = probability;
		this.documentation = documentation;
	}
	
	public String toStringProbAndLiteralOnly() { // Write "backwards" so better alignment when literal names are of varying length.
		return toStringProbAndLiteralOnly("% ");
	}
	public String toStringProbAndLiteralOnly(String preface) { // Write "backwards" so better alignment when literal names are of varying length.
		return preface + "Prob = " + Utils.truncate(probability, 6) + " for '" + groundLiteral.toStringLiteralOnly() + "'. " + documentation;
	}
	public String toString() {
		return toString("% ");
	}	
	public String toString(String preface) { // Write "backwards" so better alignment when literal names are of varying length.
		return preface + "Prob = " + Utils.truncate(probability, 6) + " for '" + groundLiteral.toString() + "'. " + documentation;
	}
}