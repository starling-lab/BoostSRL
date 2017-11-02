/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.BindingList;

/**
 *
 * @author twalker
 */
public interface Proof {

    /** Returns true if the most recent prove through the proof succeeded.
     *
     * @return
     */
    public boolean isTrue();

    /** Returns true if there are remaining choice points that could be evaluated.
     *
     * @return
     */
    public boolean isProofComplete();

    /** Returns the binding list for the most recent prove through the proof.
     *
     * If the most recent proof failed, this will return null.
     *
     * @return
     */
    public BindingList getBindings();

    /** Attempts to prove the query, backtracking through remaining choice points if necessary.
     *
     * @return BindingList if prove is successful, or null.
     */
    public BindingList prove();

    public HornClauseProver getProver();
}
