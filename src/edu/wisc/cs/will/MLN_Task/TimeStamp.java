/**
 * 
 */
package edu.wisc.cs.will.MLN_Task;

/**
 * @author shavlik
 *
 */
public class TimeStamp {
	private String timeStamp;

	/**
	 * 
	 */
	public TimeStamp(String theTimeStamp) {
		timeStamp = theTimeStamp;
	}
	
	public String getTimeStamp() {
		return timeStamp;
	}
	
	public String toString() {
		return "[" + timeStamp + "]";
	}

}
