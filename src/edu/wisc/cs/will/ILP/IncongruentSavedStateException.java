/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ILP;

/**
 *
 * @author twalker
 */
@SuppressWarnings("serial")
public class IncongruentSavedStateException extends Exception {

    /**
     * Creates a new instance of <code>IncongruentCheckpointException</code> without detail message.
     */
    public IncongruentSavedStateException() {
    }


    /**
     * Constructs an instance of <code>IncongruentCheckpointException</code> with the specified detail message.
     * @param msg the detail message.
     */
    public IncongruentSavedStateException(String msg) {
        super(msg);
    }
}
