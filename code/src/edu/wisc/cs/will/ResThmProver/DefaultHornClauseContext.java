/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.SLDQuery;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.Utils.Utils;
import java.util.ArrayList;
import java.util.List;

/** This is a self contained Horn clause prover.
 *
 * This provides an easily usable API for performing proofs.
 *
 * @author twalker
 */
public class DefaultHornClauseContext implements HornClauseContext {

    private final HandleFOPCstrings stringHandler;

    private FileParser parser;

    private HornClausebase clausebase;

    private Unifier unifier;

    private List<ProofListener> proofListenerList = null;


    public DefaultHornClauseContext() {
        this.stringHandler = new HandleFOPCstrings();
    }
    
    public DefaultHornClauseContext(boolean okToBeSecondStringHandler) {
        this.stringHandler = new HandleFOPCstrings(okToBeSecondStringHandler);
    }
    
    public DefaultHornClauseContext(String workingDir) {
        this.stringHandler = new HandleFOPCstrings();
        parser = new FileParser(stringHandler, workingDir);
    }
    
    public DefaultHornClauseContext(String workingDir, boolean okToBeSecondStringHandler) {
        this.stringHandler = new HandleFOPCstrings(okToBeSecondStringHandler);
        parser = new FileParser(stringHandler, workingDir);
    }

    public DefaultHornClauseContext(HandleFOPCstrings stringHandler) {
    	this.stringHandler = (stringHandler != null ? stringHandler : new HandleFOPCstrings());  // Make sure we have one.
    }

    public DefaultHornClauseContext(HandleFOPCstrings stringHandler, FileParser parser) {
        this.stringHandler = (stringHandler != null ? stringHandler : new HandleFOPCstrings());
        this.parser        = parser;

        checkSetup();
    }

    public DefaultHornClauseContext(HornClausebase clausebase) {
        if (clausebase == null) {
            throw new IllegalStateException("Clausebase must be non-null.");
        }

        this.clausebase    = clausebase;
        this.stringHandler = clausebase.getStringHandler();

        checkSetup();
    }

    public DefaultHornClauseContext(HornClausebase clausebase, FileParser parser) {
        if (clausebase == null) {
            throw new IllegalStateException("Clausebase must be non-null.");
        }

        this.clausebase    = clausebase;
        this.stringHandler = clausebase.getStringHandler();
        this.parser        = parser;
        

        checkSetup();
    }

    private void checkSetup() {
        if (clausebase != null && clausebase.getStringHandler() != stringHandler) {
            throw new IllegalStateException("Clausebase stringHandler does not match Context string handler.");
        }
        if (parser != null && parser.stringHandler != stringHandler) {
            throw new IllegalStateException("Parser stringHandler does not match Context string handler.");
        }
    }

    /** Asserts a set of definite clauses represented by <code>clauses</code>.
     *
     * @param clauses A string containing a list of clauses to be parsed and asserted.
     * The clauses must be definite.
     *
     * @throws java.lang.IllegalArgumentException If any of the clauses in <code>clauses</code>
     * is not definite, an IllegalArgumentException will be thrown.  One is also thrown
     * if the parser is not able to correctly parse the clauses.
     */
    @Override
    public void assertDefiniteClause(String clauses) throws IllegalArgumentException {

        try {
            List<Sentence> sentences = getFileParser().readFOPCstream(clauses);
            assertSentences(sentences);
        } catch (Exception e) {
            if (e instanceof IllegalArgumentException) {
    			Utils.reportStackTrace(e);
                throw (IllegalArgumentException) e;
            }
            else {
                throw new IllegalArgumentException("Error parsing clauses:\n" + clauses, e);
            }
        }

    }

    /** Asserts the definite clause in the fact base of the prover.
     *
     * @param definiteClause A definite clause to be asserted in the fact base.
     * @throws IllegalArgumentException Throws an illegal argument exceptions if
     * the clause is not definite.
     */
    @Override
    public void assertDefiniteClause(Clause definiteClause) throws IllegalArgumentException {
        if (definiteClause.isDefiniteClause() == false) {
            throw new IllegalArgumentException("Clause '" + definiteClause + "' is not definite.");
        }

        getClausebase().assertBackgroundKnowledge(definiteClause);
    }

    @Override
    public void assertSentences(Iterable<? extends Sentence> sentences) throws IllegalArgumentException {
        if (sentences != null) {
            List<DefiniteClause> clausesToAssert = new ArrayList<DefiniteClause>();

            // First parse the sentences and make sure the all evaluate to
            // definite clauses.
            for (Sentence sentence : sentences) {
                if (sentence instanceof Clause) {
                    Clause clause = (Clause) sentence;
                    if (clause.isDefiniteClause()) {
                        clausesToAssert.add(clause);
                    }
                }
                else if (sentence instanceof Literal) {
                    Literal literal = (Literal) sentence;
                    clausesToAssert.add(literal);
                }
                else {
                    List<Clause> clauses2 = sentence.convertToClausalForm();
                    for (Clause clause : clauses2) {
                        if (clause.isDefiniteClause()) {
                            clausesToAssert.add(clause);
                        }
                        else {
                            throw new IllegalArgumentException("Logic sentence '" + clause + "' is not a definite clause.");
                        }
                    }
                }
            }

            // Next assert the definite clauses into the clausebase.
            for (DefiniteClause clause : clausesToAssert) {
                if (clause instanceof Clause) {
                    Clause clause1 = (Clause) clause;
                    getClausebase().assertBackgroundKnowledge(clause1);
                }
                else if (clause instanceof Literal) {
                    Literal literal = (Literal) clause;
                    getClausebase().assertFact(literal);
                }
            }
        }
    }

    /** Attempts to prove the clause <code>goal</code>.
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
    @Override
    public BindingList prove(String goal) throws IllegalArgumentException {
            SLDQuery sldQuery = parseGoal(goal);

            return prove(sldQuery);
    }

    @Override
    public BindingList prove(SLDQuery goal) throws IllegalArgumentException {
            try {
                HornClauseProver prover = new HornClauseProver(stringHandler, getClausebase());

                fireProving(goal);

                return prover.prove(goal);
            } catch (Throwable t) {
                Utils.warning("Error proving goal '" + goal + "!");
    			Utils.reportStackTrace(t);
                // Just catch everything and return null...
                return null;
            }
    }

    @Override
    public Proof getProof(String goal) throws IllegalArgumentException {
        SLDQuery sldQuery = null;
        try {
            sldQuery = parseGoal(goal);
        } catch (Exception e) {
            throw new IllegalArgumentException("Error parsing goal '" + goal + "':" + e);
        }

        return getProof(sldQuery);
    }

    @Override
    public Proof getProof(SLDQuery goal) throws IllegalArgumentException {
            DefaultProof proof = new DefaultProof(clausebase, goal);
            return proof;
    }

    private SLDQuery parseGoal(String goal) throws IllegalArgumentException {
        if (goal.endsWith(".") == false) {
            goal = goal + ".";
        }

        List<Sentence> sentences = getFileParser().readFOPCstream(goal);

        if ( sentences.isEmpty() ) {
            return getStringHandler().getClause();
        }

        if (sentences.size() != 1) {
            throw new IllegalArgumentException("Goal '" + goal + "' did not parse into a single conjunct of literals.");
        }


        List<Clause> clauses = sentences.get(0).convertToClausalForm();

        List<Literal> literalsToProve = new ArrayList<Literal>();

        for (int i = 0; i < clauses.size(); i++) {
            Clause clause = clauses.get(i);

            if (clause.getNegLiteralCount() != 0) {
                throw new IllegalArgumentException("Negated literal '" + clause + "' found in goal '" + goal + "'.  Goal should be conjunct of positive literals.");
            }

            if (clause.posLiterals != null) {
                literalsToProve.addAll(clause.posLiterals);
            }
        }

        return getStringHandler().getClause(null, literalsToProve);
    }

    @Override
    public HornClausebase getClausebase() {
        if (clausebase == null) {
            this.clausebase = new DefaultHornClausebase(stringHandler);
        }

        return clausebase;
    }

    @Override
    public FileParser getFileParser() {
        if (parser == null) {
            parser = new FileParser(stringHandler);
        }

        return parser;
    }

    @Override
    public Unifier getUnifier() {
        if (unifier == null) {
            unifier = new Unifier();
        }

        return unifier;
    }

    @Override
    public HandleFOPCstrings getStringHandler() {
        return stringHandler;
    }

    @Override
    public void loadLibrary(String libraryName) {


        boolean hold_cleanFunctionAndPredicateNames = getStringHandler().cleanFunctionAndPredicateNames;
        getStringHandler().cleanFunctionAndPredicateNames = false;

        try {
            List<Sentence> librarySentences = getFileParser().loadThisFile(true, libraryName, false);

            assertSentences(librarySentences);
        } catch (Exception e) {
            throw new RuntimeException("Problem encountered reading built-in library: '" + libraryName + "'.", e);
        } finally {
            getStringHandler().cleanFunctionAndPredicateNames = hold_cleanFunctionAndPredicateNames;
        }

    }

    @Override
    public String toString() {
        return "DefaultHornClauseContext [\n" + getClausebase() + "]";
    }

    public void addProofListener(ProofListener proofListener) {
        if ( proofListenerList == null ) {
            proofListenerList = new ArrayList<ProofListener>();
        }
        proofListenerList.add(proofListener);
    }

    public void removeProofListener(ProofListener proofListener) {
        if ( proofListenerList != null ) {
            proofListenerList.remove(proofListener);
        }
    }

    private void fireProving(SLDQuery query) {
        if ( proofListenerList != null ) {
            for (int i = 0; i < proofListenerList.size(); i++) {
                ProofListener proofListener = proofListenerList.get(i);
                proofListener.proving(query);
            }
        }
    }
}
