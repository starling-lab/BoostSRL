/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.ProcedurallyDefinedPredicateHandler;
import edu.wisc.cs.will.FOPC.Sentence;
import java.util.Collection;
import java.util.List;
import java.util.Map;

/**
 *
 * @author twalker
 */
public interface HornClausebase {

//    /** Resets the fact base and asserts the definite clauses from rules and facts.
//     *
//     * @param stringHandler String handler for this fact base.
//     * @param rules Rules to initially assert.
//     * @param facts Facts to initially assert.
//     * @param userProcHandler Handler for special user defined predicates.
//     */
//    public void initializeClausebase(HandleFOPCstrings stringHandler, Collection<? extends Sentence> rules, Collection<? extends Sentence> facts, ProcedurallyDefinedPredicateHandler userProcHandler);
    /** Returns the String handler for this fact base.
     * 
     * @return String handler for this fact base.
     */
    public HandleFOPCstrings getStringHandler();

    public MapOfDefiniteClauseLists getAssertionsMap();

    /** Returns the set of all asserted sentences.
     *
     * To maintain prolog semantics, we need to have all assertions in order,
     * independent of whether they are facts or background knowledge.
     *
     * Facts will be returned as Literals while background knowledge will be
     * returned as Clauses.  The DefiniteClause interface can be used to determine
     * which is which and how to handle it.
     *
     * The returned collection should be considered immutable.  Changing the
     * collection directly would be bad.
     *
     * @return Set of all asserted definite clauses, in their assertion order.
     */
    public Iterable<DefiniteClause> getAssertions();

    /** Returns the set of all asserted facts.
     *
     * The returned collection should be considered immutable.  Changing the
     * collection directly would be bad.
     *
     * @return Set of all asserted definite clauses facts.
     */
    public Iterable<Literal> getFacts();

    /** Returns the set of all asserted background knowledge.
     * 
     * The returned collection should be considered immutable.  Changing the
     * collection directly would be bad.
     *
     * @return Set of all asserted definite clauses background knowledge.
     */
    public Iterable<Clause> getBackgroundKnowledge();

    /** Asserts a definite clause into the background knowledge.
     *
     * @param head Clause to assert into the background knowledge.
     * @throws IllegalArgumentException Throws an IllegalArgumentException if the
     * sentence is not a definite clause.
     */
    public void assertBackgroundKnowledge(DefiniteClause definiteClause) throws IllegalArgumentException;

    /** Asserts a list of definite clauses into the background knowledge.
     *
     * The sentences in the list must be either clause which are definite or Literals.
     *
     * @param definiteClauses Clauses to assert into the background knowledge.
     * @throws IllegalArgumentException Throws an IllegalArgumentException if any of the
     * sentences are not single definite clauses and can not be converted to definite clauses.
     */
    public void assertBackgroundKnowledge(Collection<? extends Sentence> definiteClauses) throws IllegalArgumentException;

    /** Asserts a fact into the clause base.
     *
     * @param fact Fact to assert into the facts.
     */
    public void assertFact(Literal fact);

    /** Asserts a fact into the clause base.
     *
     * @param facts Facts to assert into the clause base.
     * @throws IllegalArgumentException Throws a IllegalArgumentException if any of the Sentences
     * in facts collection is not a single definite clause with no body and can't be converted
     * into one.
     */
    public void assertFacts(Collection<? extends Sentence> facts) throws IllegalArgumentException;

    /**
     * Retracts the first occurrence of the specified definiteClause.
     *
     * The first definite clause in the clausebase which matches definiteClause via
     * unification will be retracted.
     *
     * Use the retractAllClausesWithUnifyingBody or retractAllClauseWithHead method
     * if you need to retract multiple matches beyond just the first unifying clause.
     *
     * @param definiteClause Definite clause to retract.
     * @param bindingList If bindingList is non-null, it will be populated with any variable bindings from the unification.
     * @return True if a clause was retracted.
     */
    public boolean retract(DefiniteClause definiteClause, BindingList bindingList);

    /** Retracts all of the matching clauses contained in clauses.
     *
     * This method retracts all clauses that exactly match the sentences in
     * the clauses collections.  Essentially, it repeatedly calls retract(Clause)
     * for all the sentences.<p>
     *
     * Although the collection contains sentences for convenience, all of the
     * sentences much conform to the DefiniteClause interface.<p>
     *
     * If a clause does not exist in the clause base, it will be ignored.
     *
     * @param clauses Clauses to be retracted.
     * @throws IllegalArgumentException An IllegalArgumentException will be thrown if any
     * of the sentences are not definite clauses.  If this occurs, none of the sentences
     * will be retracted.
     */
    public void retract(Collection<? extends Sentence> clauses) throws IllegalArgumentException;

    /**
     * Retract all the clauses which unify with definiteClause.
     *
     * Retracts all clauses from the clausebase which unify with definiteClause.
     * This version requires the full body of the clause to unify.  @See  retractAllClauseWithHead(Literal)
     * if you want to retract all clauses matching a given head literal.
     *
     * @param definiteClause Pattern of definite clauses to retract.
     * @return True if one or more clauses were retracted.
     */
    public boolean retractAllClausesWithUnifyingBody(DefiniteClause definiteClause);

    /**
     * Retract all the clauses whose head literal unifies with literal.
     *
     * Retracts all clauses from the clausebase where the head of the
     * definite clause unifies with clauseHead.
     * @See  retractAllClausesWithUnifyingBody(DefiniteClause)
     * if you want to retract all clauses matching a given head and body.
     *
     * @param clauseHead Pattern of definite clauses to retract.
     * @return True if one or more clauses were retracted.
     */
    public boolean retractAllClauseWithHead(DefiniteClause clauseHead);

    public boolean retractAllClausesForPredicate(PredicateNameAndArity predicateNameAndArity);

    /** Checks to see if there are any possible matching definite clauses in either the background knowledge or the facts.
     * 
     * This method check both facts and background knowledge.
     * 
     * @param predName Predicate name to lookup.
     * @param arity Arity of predicate.
     * @return True if the background knowledge or facts contains possible matching facts or rules.
     */
    public boolean checkForPossibleMatchingAssertions(PredicateName predName, int arity);

    /** Returns a Collection of definite clauses whose head might match the specified clauseHead.
     *
     * The DefiniteClause returned can be either a Literal or a Clause from either the background
     * knowledge or the facts.
     *
     * There is no guarantee that head of the clauses in the returned set will match the clauseHead requested.
     * Depending on the indexing method, other predicateNames or arities might be returned.  However,
     * it is guaranteed that all clauses in the background knowledge and/or facts whose head does match
     * will be returned.
     *
     * The iteration order of the collection returned is guaranteed to match the
     * order in which the clauses were oridinally asserted.
     *
     * @param clauseHead Literal to match against head of clauses in fact base.
     * @param currentBinding Bindings currently applied to clauseHead.  If non-null, the binding
     * list will be applied against the head prior to lookup in the fact base.
     * @return Collection of Sentences that may match predicateName/arity, possible null.
     */
    public List<DefiniteClause> getPossibleMatchingAssertions(Literal clauseHead, BindingList currentBinding);

    /** Returns a Collection of definite clauses from both the background knowledge and the facts whose head matches the predicateName and arity.
     *
     * This is guaranteed to be the complete list and to only contain definite clauses with
     * a head that matches the predName and arity.
     *
     * The DefiniteClause returned can be either a Literal (representing a fact) or a
     * Clause (representing a definite clause from the background knowledge).
     *
     * The iteration order of the collection returned is guaranteed to match the
     * order in which the clauses were ordinally asserted.
     *
     * @param predName Predicate name of head.
     * @param arity Arity of head.
     * @return Collection of Definite clauses matching the predName and arity.
     */
    public List<DefiniteClause> getAssertions(PredicateName predName, int arity);

    /** Returns a Collection of definite clauses from both the background knowledge and the facts whose head matches the predicateName and arity.
     *
     * This is guaranteed to be the complete list and to only contain definite clauses with
     * a head that matches the predName and arity.
     *
     * The DefiniteClause returned can be either a Literal (representing a fact) or a
     * Clause (representing a definite clause from the background knowledge).
     *
     * The iteration order of the collection returned is guaranteed to match the
     * order in which the clauses were ordinally asserted.
     *
     * @param predName Predicate name of head.
     * @param arity Arity of head.
     * @return Collection of Definite clauses matching the predName and arity.
     */
    public List<DefiniteClause> getAssertions(PredicateNameAndArity predicateNameAndArity);

    /** Checks to see if there are any possible matching clauses in the background knowledge.
     *
     * @param predName Predicate name to lookup.
     * @param arity Arity of predicate.
     * @return True if the fact base contains possible matching rules.
     */
    public boolean checkForPossibleMatchingBackgroundKnowledge(PredicateName predName, int arity);

    /** Returns a Collection of background knowledge whose head might match the specified clauseHead.
     *
     * There is no guarantee that head of the clauses in the returned set will match the clauseHead requested.
     * Depending on the indexing method, other predicateNames or arities might be returned.  However,
     * it is guaranteed that all clauses in the fact base whose head does match will be returned.
     *
     * @param clauseHead Literal to match against head of clauses.
     * @param currentBinding Bindings currently applied to clauseHead.  If non-null, the binding
     * list will be applied against the head prior to lookup in the fact base.
     * @return Collection of Rules that may match predicateName/arity, possible null.
     */
    public Iterable<Clause> getPossibleMatchingBackgroundKnowledge(Literal clauseHead, BindingList currentBinding);

//    /** Returns a Collection of definite clauses background knowledge whose head matches the predicateName and arity.
//     *
//     * This is guaranteed to be the complete list and to only contain definite clauses with
//     * a head that matches the predName and arity.
//     *
//     * The DefiniteClause will all be Clauses (representing a definite clause with a body).
//     *
//     * @param predName Predicate name of head.
//     * @param arity Arity of head.
//     * @return Collection of Definite clauses matching the predName and arity.
//     */
//    public List<Clause> getBackgroundKnowledge(PredicateName predName, int arity);
//
//    /** Returns a Collection of definite clauses background knowledge whose head matches the predicateName and arity.
//     *
//     * This is guaranteed to be the complete list and to only contain definite clauses with
//     * a head that matches the predName and arity.
//     *
//     * The DefiniteClause will all be Clauses (representing a definite clause with a body).
//     *
//     * @param predName Predicate name of head.
//     * @param arity Arity of head.
//     * @return Collection of Definite clauses matching the predName and arity.
//     */
//    public List<Clause> getBackgroundKnowledge(PredicateNameAndArity predicateNameAndArity);

    /** Checks to see if there are any possible matching facts in the factbase.
     * 
     * @param predName Predicate name to lookup.
     * @param arity Arity of predicate.
     * @return True if the fact base contains possible matching facts.
     */
    public boolean checkForPossibleMatchingFacts(PredicateName predName, int arity);

    /** Returns a Collection of facts which might match the specified clauseHead.
     *
     * There is no guarantee that head of the clauses in the returned set will match the clauseHead requested.
     * Depending on the indexing method, other predicateNames or arities might be returned.  However,
     * it is guaranteed that all clauses in the fact base whose head does match will be returned.
     *
     * @param clauseHead Literal to match against head of clauses.
     * @param currentBinding Bindings currently applied to clauseHead.
     * @return Collection of Sentences that may match predicateName/arity, possible null.
     */
    public Iterable<Literal> getPossibleMatchingFacts(Literal clauseHead, BindingList currentBinding);
    
    /**
     * Removes the clause from facts and assertions. Does not find possible matching assertions or facts.
     * @param clauseToRemove
     */
    public void removeClause(DefiniteClause clauseToRemove);

//    /** Returns a Collection of definite clauses facts whose head matches the predicateName and arity.
//     *
//     * This is guaranteed to be the complete list and to only contain definite clauses with
//     * a head that matches the predName and arity.
//     *
//     * The DefiniteClause will all be Literal (representing a definite clause with a no body).
//     *
//     * @param predName Predicate name of head.
//     * @param arity Arity of head.
//     * @return Collection of Definite clauses matching the predName and arity.
//     */
//    public List<Literal> getFacts(PredicateName predName, int arity);
//
//    /** Returns a Collection of definite clauses facts whose head matches the predicateName and arity.
//     *
//     * This is guaranteed to be the complete list and to only contain definite clauses with
//     * a head that matches the predName and arity.
//     *
//     * The DefiniteClause will all be Literal (representing a definite clause with a no body).
//     *
//     * @param predName Predicate name of head.
//     * @param arity Arity of head.
//     * @return Collection of Definite clauses matching the predName and arity.
//     */
//    public List<Literal> getFacts(PredicateNameAndArity predicateNameAndArity);

    public boolean recorded(DefiniteClause definiteClause);

    //public Collection<Literal> collectAllFactsOfThisName(PredicateName actionPname);
    public ProcedurallyDefinedPredicateHandler getBuiltinProcedurallyDefinedPredicateHandler();

    public ProcedurallyDefinedPredicateHandler getUserProcedurallyDefinedPredicateHandler();

    public void setUserProcedurallyDefinedPredicateHandler(ProcedurallyDefinedPredicateHandler userDefinedPredicateHandler);

    public boolean isOnlyInFacts(PredicateName predName, int arity);

    public void addAssertRetractListener(AssertRetractListener assertRetractListener, PredicateNameAndArity predicate);

    public void removeAssertRetractListener(AssertRetractListener assertRetractListener, PredicateNameAndArity predicate);

    /** Returns whether the predicate currently has a definition.
     *
     * @param pnaa
     * @return
     */
    public boolean isDefined(PredicateNameAndArity pnaa);
}
