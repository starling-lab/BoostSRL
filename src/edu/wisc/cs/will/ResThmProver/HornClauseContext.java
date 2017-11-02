/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.SLDQuery;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;

/**
 *
 * @author twalker
 */
public interface HornClauseContext {

    public HandleFOPCstrings getStringHandler();
    public FileParser        getFileParser();
    public HornClausebase    getClausebase();
    public Unifier           getUnifier();

    /** Asserts a set of definite clauses represented by <code>clauses</code>.
     *
     * @param clauses A string containing a list of clauses to be parsed and asserted.
     * The clauses must be definite.
     *
     * @throws java.lang.IllegalArgumentException If any of the clauses in <code>clauses</code>
     * is not definite, an IllegalArgumentException will be thrown.  One is also thrown
     * if the parser is not able to correctly parse the clauses.
     */
    public void assertDefiniteClause(String clauses) throws IllegalArgumentException;

    /** Asserts the definite clause in the fact base of the prover.
     *
     * @param definiteClause A definite clause to be asserted in the fact base.
     * @throws IllegalArgumentException Throws an illegal argument exceptions if
     * the clause is not definite.
     */
    public void assertDefiniteClause(Clause definiteClause) throws IllegalArgumentException;

    /** Asserts the definite clauses from the iterable into the clausebase.
     *
     * The sentences must definite clauses.  If any of the sentences are not
     * definite clauses, this method will throw an IllegalArgumentException
     * and none of the clauses will be asserted.
     *
     * @param sentences An iterator over a set of definite clauses.
     * @throws IllegalArgumentException Throws an illegal argument exceptions if
     * any of the clauses to be asserted are not definite clauses.
     */
    public void assertSentences(Iterable<? extends Sentence> sentences) throws IllegalArgumentException;

    /**
     * Attempts to prove the clause <code>goal</code>.
     *
     * The goal should a single line string containing the a conjunct of literals
     * to prove.
     *
     * The theorem prover will attempt to prove the statement, given the currently
     * asserted fact base.
     *
     * @param goal A single line string containing a conjunct of literals to prove, given the
     * current asserted fact base.
     *
     * @return If the goal is successful, returns the BindingList for the first
     * sucessful proof found.
     *
     * @throws IllegalArgumentException Throws an IllegalArgumentException if the goal is
     * not parsable or if the
     */
    public BindingList prove(String goal) throws IllegalArgumentException;

    /**
     * Attempts to prove the SLDQuery <code>goal</code>.
     *
     * The SLDQuery should be a legal SLD query.  This includes sentences which evaluate
     * to a single clause with no positive literals and one or more negative literals,
     * bare literals, and functions of terms.
     *
     * The theorem prover will attempt to prove the query, given the currently
     * asserted fact base.
     *
     * @param goal A legal SLD query.
     *
     * @return If the goal is successful, returns the BindingList for the first
     * successful proof found.
     *
     * @throws IllegalArgumentException Throws an IllegalArgumentException if the goal
     * can not be converted into a legal SLD query.
     */
    public BindingList prove(SLDQuery goal) throws IllegalArgumentException;

    /**
     * Attempts to prove the clause <code>goal</code>.
     *
     * The goal should a single line string containing a conjunct of literals
     * to prove.
     *
     * The theorem prover will attempt to prove the statement, given the currently
     * asserted fact base.
     *
     * @param goal A single line string containing a conjunct of literals to prove, given the
     * current asserted fact base.
     *
     * @return A Proof object is returned whether the proof is successful or not.  This can
     * be used to determine if the proof succeeded and to backtrack for more solutions.
     *
     * @throws IllegalArgumentException Throws an IllegalArgumentException if the goal is
     * not parsable.
     */
    public Proof getProof(String goal) throws IllegalArgumentException;

    /**
     * Attempts to prove the SLDQuery <code>goal</code>.
     *
     * The goal should a single line string containing a conjunct of literals
     * to prove.
     *
     * The theorem prover will attempt to prove the statement, given the currently
     * asserted fact base.
     *
     * @param goal A legal SLD query.
     *
     * @return A Proof object is returned whether the proof is successful or not.  This can
     * be used to determine if the proof succeeded and to backtrack for more solutions.
     *
     * @throws IllegalArgumentException Throws an IllegalArgumentException if the goal is
     * not parsable.
     */
    public Proof getProof(SLDQuery goal) throws IllegalArgumentException;

    public void addProofListener(ProofListener proofListener);

    public void removeProofListener(ProofListener proofListener);

    public void loadLibrary(String libraryName);

}
