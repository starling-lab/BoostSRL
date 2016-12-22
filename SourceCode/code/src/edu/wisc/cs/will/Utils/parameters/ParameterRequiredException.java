/*
 * ParameterRequiredException.java
 *
 * Created on August 27, 2007, 11:44 AM
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package edu.wisc.cs.will.Utils.parameters;

/**
 *
 * @author twalker
 */
public class ParameterRequiredException extends java.lang.RuntimeException {

    /**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
     * Constructs an instance of <code>ParameterRequiredException</code> with the specified detail message.
     * 
     * @param msg the detail message.
     */
    public ParameterRequiredException(String parameterName) {
        super("The " + parameterName + " parameter is require but not set");
    }
}
