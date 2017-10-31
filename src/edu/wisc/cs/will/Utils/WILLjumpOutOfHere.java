package edu.wisc.cs.will.Utils;

@SuppressWarnings("serial")
public class WILLjumpOutOfHere extends RuntimeException {

	// Allow jumping out of here, where some other code will presumably catch..
	public WILLjumpOutOfHere() {
	   	super();
	   }
	public WILLjumpOutOfHere(String msg) {
	   super(msg);
	}	   
}
