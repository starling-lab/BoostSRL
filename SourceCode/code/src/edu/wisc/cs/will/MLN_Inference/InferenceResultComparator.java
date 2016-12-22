package edu.wisc.cs.will.MLN_Inference;

import java.util.Comparator;

public class InferenceResultComparator implements Comparator<InferenceResult>{

	/**
	 * 
	 */
	public InferenceResultComparator() {
	}

	/* (non-Javadoc)
	 * @see java.util.Comparator#compare(java.lang.Object, java.lang.Object)
	 */
	public int compare(InferenceResult result0, InferenceResult result1) {
		if (result0.probability < result1.probability) { return -1; }
		if (result0.probability > result1.probability) { return  1; }
		return 0; 
	}

}
