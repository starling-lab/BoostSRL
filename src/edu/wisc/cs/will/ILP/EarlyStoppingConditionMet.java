/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

/**
 *
 * @author twalker
 */
@SuppressWarnings("serial")
public class EarlyStoppingConditionMet extends SearchInterrupted {

    /**
     * Creates a new instance of <code>CVEarlyStoppingException</code> without detail message.
     */
    public EarlyStoppingConditionMet() {
    }


    /**
     * Constructs an instance of <code>CVEarlyStoppingException</code> with the specified detail message.
     * @param msg the detail message.
     */
    public EarlyStoppingConditionMet(String msg) {
        super(msg);
    }
}
