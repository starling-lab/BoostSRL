package edu.wisc.cs.will.Utils;

@SuppressWarnings("serial")
public class WILLinterruption extends RuntimeException {

	// Allow interruption of WILL.
	public WILLinterruption() {
	   	super();
	   }
	public WILLinterruption(String msg) {
	   super(msg);
	}	   
}
