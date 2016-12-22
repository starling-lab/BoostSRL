/**
 * 
 */
package edu.wisc.cs.will.stdAIsearch;

/**
 * @author shavlik
 *
 */
public class SearchInterrupted extends Exception {
	/**
	 * If some code wishes to interrupt a search in the middle, it should throw a new instance of this class.
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * 
	 */
	public SearchInterrupted() {
	}

	/**
	 * @param message
	 */
	public SearchInterrupted(String message) {
		super(message);
	}

	/**
	 * @param cause
	 */
	public SearchInterrupted(Throwable cause) {
		super(cause);
	}

	/**
	 * @param message
	 * @param cause
	 */
	public SearchInterrupted(String message, Throwable cause) {
		super(message, cause);
	}

}
