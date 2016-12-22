/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.DefiniteClause;

/**
 *
 * @author twalker
 */
public interface AssertRetractListener {
    public void clauseAsserted(HornClausebase context, DefiniteClause clause);
    public void clauseRetracted(HornClausebase context, DefiniteClause clause);
}
