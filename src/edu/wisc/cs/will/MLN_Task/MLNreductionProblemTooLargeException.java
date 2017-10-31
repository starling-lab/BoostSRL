/**
 * 
 */
package edu.wisc.cs.will.MLN_Task;

import edu.wisc.cs.will.Utils.Utils;

/** The MLN reducer exceeded its time and/or space limitations.
 * 
 * @author shavlik
 *
 */
public class MLNreductionProblemTooLargeException extends Exception {

	/**
	 * 
	 */
	private static final long serialVersionUID = 5767896698846546439L;

	/**
	 * 
	 */
	public MLNreductionProblemTooLargeException() {
	}

	/**
	 * @param message
	 */
	public MLNreductionProblemTooLargeException(String message) {
		if (message != null) { Utils.println("% MLNreductionProblemTooLargeException: " + message); }
	}

}
