/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.Literal;

/**
 *
 * @author twalker
 */
public interface ILPPruningRule {
    /** Prunes the definiteClause given a new element.
     *
     */
    public boolean pruneLastElement(DefiniteClause definiteClause, Literal addedLiteral);

}
