/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import java.util.Set;

/**
 *
 * @author twalker
 */
public interface ModeConstraint {

    /** Applies the mode constraint to the set of possible expansion modes.
     *
     * This method should remove modes that are currently ineligible for expansion
     * from the eligibleExpansionModes.  If the set changed, it should be returned,
     * otherwise the method should return null.
     *
     * For efficiency purposes, the isMutable parameter indicates whether the
     * eligibleExpansionModes is mutable.  If isMutable is false and the eligible
     * modes needs to be modified, a new set must be created.  If isMutable is
     * true, the current set can (and should) be modified directly.
     *
     * @param nodeBeingExpanded Node currently being expanded.
     * @param possibleExpansionModes Set of currently eligible expansion modes.
     * @return returns the new set of eligible expansion modes, or null if the current set did not change.
     */
    public Set<PredicateNameAndArity> applyConstraint(SingleClauseNode nodeBeingExpanded, Set<PredicateNameAndArity> eligibleExpansionModes, boolean isMutable);
}
