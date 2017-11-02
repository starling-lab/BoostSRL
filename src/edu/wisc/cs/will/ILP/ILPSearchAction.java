/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ILP;

/**
 *
 * @author twalker
 */
public enum ILPSearchAction {
    PERFORM_LOOP, // Continues search normally
    SKIP_ITERATION, // Skips all inner loops for a set of parameters, but continues this loop
    TERMINATE_LOOP; // Terminates this loop completely, returning to outer loop immediate

    public static ILPSearchAction getHigherPrecedenceAction(ILPSearchAction action1, ILPSearchAction action2) {
        return ILPSearchAction.values()[Math.max(action1.ordinal(), action2.ordinal())];
    }
}
