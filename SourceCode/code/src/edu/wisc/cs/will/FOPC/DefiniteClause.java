/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC;

import java.util.List;

/** This is just an interface to mark Literals and Clauses as definite clauses.
 *
 * This is actually a pretty odd-ball class that is necessary because we store
 * facts as bare Literals and rules as Clauses.
 *
 * Note, that just because a class supports this does not mean that it is a definite
 * clause.  The method isDefiniteClause() should still be called to determine if
 * this in a definite clause.
 *
 *
 * @author twalker
 */
public interface DefiniteClause {

    /** Indicates that this is in fact a definite clause
     * (A disjunctive clause with one positive literal and zero or more negative
     * literals).
     *
     * @return True if this is a definite clause.
     *
     */
    public boolean isDefiniteClause();

    /** Indicates that this is a definite clause with no body.
     *
     * @return True if this is a rule (definite clause with no body).
     */
    public boolean isDefiniteClauseFact();

    /** Indicates that this is a definite clause with a body.
     *
     * @return True if this is a rule (definite clause with a body).
     */
    public boolean isDefiniteClauseRule();

    /** Returns the head to this definite clause.
     *
     * Note: If this object is not a definite clause (as indicated by isDefiniteClause())
     * then a IllegalStateException will be thrown.
     *
     * @return Literal representing the head to this definite clause.
     * @throws IllegalStateException Indicates that the original object was not a definite clause.
     */
    public Literal getDefiniteClauseHead() throws IllegalStateException;

    /** Returns the body of this definite clause, possibly null.
     *
     * @return Literals in the body of the definite clause, possibly null.
     */
    public List<Literal> getDefiniteClauseBody();

    /** Returns the DefiniteClause fact as a Literal.
     *
     * This method will return a literal representing a fact.  If the
     * definite clause is not a fact (as indicated by isDefiniteClauseFact())
     * then an IllegalStateException will be thrown.
     *
     * @return Literal representing fact.
     * @throws IllegalStateException Indicates that the original object was not a fact.
     */
    public Literal getDefiniteClauseFactAsLiteral() throws IllegalStateException;

    /** Returns the DefiniteClause as a Clause.
     *
     * This method will return a clause representing the definite clause.  This will
     * work for both bare Literals and clauses.
     *
     * If the DefiniteClause isn't a definite clause (as indicated by isDefiniteClause())
     * then a IllegalStateException will be thrown.
     *
     * @param stringHandler String handler used to lookup the canonicalized clause.
     * @return Clause representing fact.
     * @throws IllegalStateException Indicates that the original object was not a definite clause.
     */
    public abstract Clause getDefiniteClauseAsClause() throws IllegalStateException;

    /** Indicates that free variables exist after substitution of the binding list.
     *
     * @param theta BindingList.
     * @return True if free variables still exist after substitution.
     */
    public boolean containsFreeVariablesAfterSubstitution(BindingList theta);

    /** Returns whether the otherClause is a variant of this clause.
     * 
     * @param otherClause
     * @return
     */
    public boolean isDefiniteClauseVariant(DefiniteClause otherClause);

    /** Attempts to unify this clause with otherClause.
     *
     * @param otherClause
     * @param bindingList If non-null, the binding list to populate.
     * @return If the two clauses unify, returns a unifying BindingList; otherwise returns null.
     */
    public BindingList unifyDefiniteClause(DefiniteClause otherClause, BindingList bindingList);

    /** Returns the arity of the head of the clause.
     *
     * @return
     */
    public int getArity();

    /** Returns the type of the nth argument of the head of the clause.
     * 
     * @param argument
     * @return
     */
    public Type getType(int argument);
}
