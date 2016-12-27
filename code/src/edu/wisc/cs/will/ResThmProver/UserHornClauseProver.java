/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.ResThmProver;

import java.util.List;

import edu.wisc.cs.will.FOPC.AbstractUserDefinedBooleanLiteral;
import edu.wisc.cs.will.FOPC.AbstractUserDefinedFunctionAsLiteral;
import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.CallbackRegister;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.SLDQuery;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.FOPC.UserDefinedLiteral;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;

/** This is a self contained Horn clause prover.
 *
 * This provides an easily usable API for performing proofs.
 *
 * @author twalker
 */
public class UserHornClauseProver implements HornClauseContext, CallbackRegister {

    protected HornClauseContext context;

    public UserHornClauseProver() {
        this.context = new DefaultHornClauseContext();
    }

    protected UserHornClauseProver(HandleFOPCstrings stringHandler, FileParser parser) {
        this.context = new DefaultHornClauseContext(stringHandler, parser);
    }

    /** Attempts to prove the willConceptString given the specified parameters.
     *
     * The willConceptString should be one or more Horn clauses.  For each
     * Horn clause, the parameters will be unified against the head, and then
     * the Horn clause will be evaluated, until one of them evaluates to true.
     *
     * The theorem prover will attempt to prove the statement, given the currently
     * asserted fact base.
     *
     * @param willConceptString String containing one or more Horn clauses to be evaluated.
     *
     * @param parameters Parameters to bind against the head of the Horn clauses.
     * Parameters that are null are considered to be variables.  The parameters will
     * be parsed into standard logic and should follow standard syntax for logically
     * terms.
     *
     * @return If a Horn clause is successfully evaluated, returns the BindingList for the first
     * successful proof found.  Otherwise returns null.
     *
     * @throws IllegalArgumentException Throws an IllegalArgumentException if the willConceptString is
     * not parsable.
     */
    public BindingList prove(String willConceptString, String[] parameters) throws IllegalArgumentException {
        List<Sentence> sentences = getFileParser().readFOPCstream(willConceptString);


        StringBuilder sb = new StringBuilder();
        sb.append("lit(");
        for (int i = 0; i < parameters.length; i++) {
            String string = parameters[i];

            if (i > 0) {
                sb.append(", ");
            }

            if (string == null) {
                sb.append("_variable").append(i);
            }
            else {
                sb.append(string);
            }
        }
        sb.append(").");

        List<Term> terms = (getFileParser().readFOPCstream(sb.toString()).get(0).convertToClausalForm().get(0).posLiterals.get(0)).getArguments();


        for (Sentence sentence : sentences) {
            List<Clause> clauses = sentence.convertToClausalForm();

            for (Clause clause : clauses) {

                if (clause.isDefiniteClause() == false) {
                    throw new IllegalArgumentException("Clause obtained from willConceptString contained is not definite: " + sentence.toPrettyString());
                }

                Literal head = clause.posLiterals.get(0);

                if (head.numberArgs() != parameters.length) {
                    throw new IllegalArgumentException("Clause head arity does not match parameter array length: " + sentence.toPrettyString());
                }

                BindingList bindingList = new BindingList();
                bindingList = context.getUnifier().unifyAssumingSameNumberOfArgs(head.getArguments(), terms, bindingList);

                clause = clause.applyTheta(bindingList.theta);

                BindingList bindingList2 = context.prove(clause);
                if (bindingList2 != null) {
                    return bindingList2;
                }

            }
        }

        return null;
    }

    @Override
    public BindingList prove(String goal) throws IllegalArgumentException {
        return context.prove(goal);
    }

    @Override
    public BindingList prove(SLDQuery goal) throws IllegalArgumentException {
        return context.prove(goal);
    }

    @Override
    public Proof getProof(String goal) throws IllegalArgumentException {
        return context.getProof(goal);
    }

    @Override
    public Proof getProof(SLDQuery goal) throws IllegalArgumentException {
        return context.getProof(goal);
    }

    @Override
    public HandleFOPCstrings getStringHandler() {
        return context.getStringHandler();
    }

    @Override
    public FileParser getFileParser() {
        return context.getFileParser();
    }

    @Override
    public HornClausebase getClausebase() {
        return context.getClausebase();
    }

    @Override
    public Unifier getUnifier() {
        return context.getUnifier();
    }

    @Override
    public void assertDefiniteClause(Clause definiteClause) throws IllegalArgumentException {
        context.assertDefiniteClause(definiteClause);
    }

    @Override
    public void assertDefiniteClause(String clauses) throws IllegalArgumentException {
        context.assertDefiniteClause(clauses);
    }

    @Override
    public void assertSentences(Iterable<? extends Sentence> sentences) throws IllegalArgumentException {
        context.assertSentences(sentences);
    }

    /** Asserts a procedurally defined predicate.
     *
     * @param predicateName Name of the predicate.
     *
     * @param literalDefinition UserDefinedLiteral object defining the predicate.
     * The abstract classes {@link AbstractUserDefinedBooleanLiteral} and {@link AbstractUserDefinedFunctionAsLiteral}
     * can be easily extended to create a UserDefinedLiteral by implementing the relevant evaluateMe() methods.
     *
     * @throws IllegalStateException Throws an IllegalStateException if the predicateName/arity is already defined.
     */
    public void assertProcedurallyDefinedLiteral(String predicateName, UserDefinedLiteral literalDefinition) throws IllegalStateException {
        getStringHandler().registerCallback(predicateName, literalDefinition);
    }

    @Override
    public void registerCallback(String predicateName, UserDefinedLiteral literalDefinition) throws IllegalStateException {
        getStringHandler().registerCallback(predicateName, literalDefinition);
    }

    @Override
    public void loadLibrary(String libraryName) {
        context.loadLibrary(libraryName);
    }

    public void loadAllLibraries() throws Exception {
        List<Sentence> sentences = this.getFileParser().loadAllLibraries();
        for (Sentence sentence : sentences) {
            if (sentence instanceof Clause) {
                Clause clause = (Clause) sentence;
                if (clause.isDefiniteClause()) {
                    assertDefiniteClause(clause);
                }
            }
            else if (sentence instanceof Literal) {
                Literal literal = (Literal) sentence;
                getClausebase().assertBackgroundKnowledge(literal);
            }
            else {
                List<Clause> clauses2 = sentence.convertToClausalForm();
                for (Clause clause : clauses2) {
                    if (clause.isDefiniteClause()) {
                        assertDefiniteClause(clause);
                    }
                    else {
                        throw new IllegalArgumentException("Logic sentence '" + sentence + "' is not a definite clause.");
                    }
                }
            }
        }
    }

    public void removeProofListener(ProofListener proofListener) {
        context.removeProofListener(proofListener);
    }

    public void addProofListener(ProofListener proofListener) {
        context.addProofListener(proofListener);
    }

    

    public static void main(String[] args) {
        UserHornClauseProver prover = new UserHornClauseProver();

        prover.assertDefiniteClause("p(X,Y) :- \\+q(X,Y).");
        prover.assertDefiniteClause("okIfUnknown: q/2.");
        prover.assertDefiniteClause("q(a,b).");

        String goal;
        BindingList result;
        @SuppressWarnings("unused")
		String[] arr = {"c", "b"};
        
        goal = "p(c,b)";
        result = prover.prove(goal);
        System.out.println(goal + " = " + (result == null ? "fail." : "true. " + result));


        goal = "p(a,b)";
        result = prover.prove(goal);
        System.out.println(goal + " = " + (result == null ? "fail." : "true. " + result));


        System.out.println("-----------");

// Replace p :- !q by p:- q
        prover.getClausebase().retractAllClauseWithHead(prover.getFileParser().parseLiteral("p(_,_)"));
        prover.assertDefiniteClause("p(X,Y) :- q(X,Y).");

        goal = "p(c,b)";
        result = prover.prove(goal);
        System.out.println(goal + " = " + (result == null ? "fail." : "true. " + result));


        goal = "p(a,b)";
        result = prover.prove(goal);
        System.out.println(goal + " = " + (result == null ? "fail." : "true. " + result));
    }
}
