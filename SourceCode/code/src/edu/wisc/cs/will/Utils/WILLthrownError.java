package edu.wisc.cs.will.Utils;

// Allow catching of WILL Errors.

@SuppressWarnings("serial")
public class WILLthrownError extends RuntimeException { // Should this extend Error instead?
    public WILLthrownError() {
    	super();
    }
    public WILLthrownError(String msg) {
        super(msg);
    }
}
