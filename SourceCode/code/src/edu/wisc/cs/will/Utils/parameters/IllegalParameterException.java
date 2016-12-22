/*
 * IllegalParameterException.java
 *
 * Created on August 27, 2007, 12:31 PM
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package edu.wisc.cs.will.Utils.parameters;

/**
 *
 * @author twalker
 */
public class IllegalParameterException extends java.lang.RuntimeException {
    
    /**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
     * Creates a new instance of <code>IllegalParameterException</code> without detail message.
     */
    public IllegalParameterException() {
    }
    
    
    /**
     * Constructs an instance of <code>IllegalParameterException</code> with the specified detail message.
     * @param msg the detail message.
     */
    public IllegalParameterException(String msg) {
        super(msg);
    }

    public IllegalParameterException(Throwable cause) {
        super(cause);
    }

    public IllegalParameterException(String message, Throwable cause) {
        super(message, cause);
    }

    
}
