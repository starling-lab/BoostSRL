/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import java.util.Collection;
import java.util.List;

/** Interface for an indexer of a horn clause fact base.
 *
 * @param <T> Type of the indexed object.  This is just for convenience if you
 * know that only Clauses or Literals are being indexed.
 *
 * @author twalker
 */
public interface HornClausebaseIndexer<T extends DefiniteClause> {

    /** Clears the index.
     *
     */
    public void resetIndex();

    /** Indicates that the index is built.
     *
     * After being reset, an index will not be built.  Prior to using
     * an index, it must be built via buildIndex.
     *
     * @return True if the index is built.
     */
    public boolean isBuilt();

    /** Builds the index for the indicated collection of DefiniteClauses.
     *
     * After a reset, the index will not be built.  buildIndex(Collection)
     * must be called prior to the index being used.
     *
     * @param clauses Clauses to build the index from.  May be null if the
     * index should be started from scratch.
     */
    public void buildIndex(Collection<? extends T> clauses);

    /** Indexes the definite clause rule.
     *
     * This should be called by the HornClauseFactBase every time a definite
     * clause rule is added to the fact base.
     *
     * @param clause Clause (guaranteed to be definite) that was added to the fact base.
     * The clause may have no body, in case it should be considered a facts.
     */
    public void indexAssertion(T clause);

    /** Retracts the specified definiteClause.
     *
     * The definite clause in the index.  The definite clause
     * should be the exact one that is in the clausebase.
     *
     * @param definiteClause Definite clause to retract.
     */
    public void removeAssertion(T definiteClause);

    /** Returns a Collection of definite clauses whose head might match the specified clauseHead.
     *
     * The Sentence return can be either a Literal (representing a definite clause with no body) or a
     * Clause (representing a definite clause with a body).  This can be restricted by specifying a Generics
     * type T.
     *
     * There is no guarantee that head of the clauses in the returned set will match the clauseHead requested.
     * The predicateName and arity will be the same, but the arguments may not unify.  However,
     * it is guaranteed that all clauses in the factbase whose head does match will be returned.
     * 
     * @param clauseHead Literal to match against head of clauses in factbase.
     * @param currentBinding Bindings currently applied to clauseHead.
     * @return Collection of Sentences that may match predicateName/arity, possible null.
     */
    public List<T> getPossibleMatchingAssertions(Literal clauseHead, BindingList currentBinding);
    
    /** Returns a Collection of definite clauses whose head might match the specified clauseHead.
     *
     * The Sentence return can be either a Literal (representing a definite clause with no body) or a
     * Clause (representing a definite clause with a body).  This can be restricted by specifying a Generics
     * type T.
     *
     * There is no guarantee that head of the clauses in the returned set will match the clauseHead requested.
     * Depending on the indexing method, other predicateNames or arities might be returned.  However,
     * it is guaranteed that all clauses in the factbase whose head does match will be returned.
     *
     * @param predicateName PredicateName to match.
     * @param arity Arity to match.
     * @return Collection of Sentences that may match predicateName/arity, possible null.
     */
    public List<T> getPossibleMatchingAssertions(PredicateName predicateName, int arity);


}
