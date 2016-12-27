/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ILP;

/** Generic stopping condition interface for a search process.
 *
 * @param <L> The type of object that is executing the search.
 * @author twalker
 */
public interface StoppingCondition<L> {
    /** Determines if a search process should be terminated early.
     *
     * @param search The search being executed.
     * @return True indicates that the stopping conditions have been met and
     * whatever is evaluating this condition should stop executing.  False
     * indicates that the stopping conditions were not met.
     */
    public boolean isStoppingConditionMet(L search);
}
