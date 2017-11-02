///*
// * To change this template, choose Tools | Templates
// * and open the template in the editor.
// */
package edu.wisc.cs.will.ResThmProver;
//
//import edu.wisc.cs.will.FOPC.BindingList;
//import edu.wisc.cs.will.FOPC.BuiltinProcedurallyDefinedPredicateHandler;
//import edu.wisc.cs.will.FOPC.Clause;
//import edu.wisc.cs.will.FOPC.DefiniteClause;
//import edu.wisc.cs.will.FOPC.Function;
//import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
//import edu.wisc.cs.will.FOPC.Literal;
//import edu.wisc.cs.will.FOPC.NumericConstant;
//import edu.wisc.cs.will.FOPC.PredicateName;
//import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
//import edu.wisc.cs.will.FOPC.ProcedurallyDefinedPredicateHandler;
//import edu.wisc.cs.will.FOPC.Sentence;
//import edu.wisc.cs.will.FOPC.StringConstant;
//import edu.wisc.cs.will.FOPC.Term;
//import edu.wisc.cs.will.FOPC.Unifier;
//import edu.wisc.cs.will.Utils.MapOfLists;
//import edu.wisc.cs.will.Utils.Utils;
//import java.util.ArrayList;
//import java.util.Collection;
//import java.util.HashMap;
//import java.util.Iterator;
//import java.util.List;
//import java.util.Map;
//
///**
// *
// * @author twalker
// */
public class ImprovedHornClausebase  { // Seems something must be here to make a JAR.  JWS 8/19/10

}
//public class ImprovedHornClausebase implements HornClausebase {
//
//    /** Set of all asserted sentences.
//     *
//     * To maintain prolog semantics, we need to have all assertions in order,
//     * independent of whether they are facts (definite clauses with no body, stored
//     * as bare Literals) or rules (definite clauses with one or more Literals in
//     * the body, stored as DefiniteClauses).
//     */
//    protected MapOfLists<PredicateNameAndArity, DefiniteClause> assertions;
//
//    private HandleFOPCstrings stringHandler;
//
//    private Map<PredicateNameAndArity, List<AssertRetractListener>> listenerMap = null;
//
//    /** Index for all assertions.
//     *
//     * This should never be used directly.  Always use the accessor method since
//     * indices are build lazily and the index may not yet be built if you use this
//     * directly.
//     *
//     * Guaranteed to be non-null.
//     */
//    private HornClausebaseIndexer<DefiniteClause> indexerForAllAssertions;
//
//    /** Index for all facts.
//     *
//     * This should never be used directly.  Always use the accessor method since
//     * indices are build lazily and the index may not yet be built if you use this
//     * directly.
//     *
//     * Guaranteed to be non-null.
//     */
//    private HornClausebaseIndexer<Literal> indexerForFacts;
//
//    /** Index for all background knowledge.
//     *
//     * This should never be used directly.  Always use the accessor method since
//     * indeces are build lazily and the index may not yet be built if you use this
//     * directly.
//     *
//     * Guaranteed to be non-null.
//     */
//    private HornClausebaseIndexer<Clause> indexerForBackgroundKnowledge;
//
//    private ProcedurallyDefinedPredicateHandler builtinProcedurallyDefinedPredicateHandler;
//
//    private ProcedurallyDefinedPredicateHandler userProcedurallyDefinedPredicateHandler;
//
//    protected boolean reportFactsWithVariables = false; // Report facts with variables in them.
//
//    private int duplicateFactCount = 0;
//
//    private int duplicateRuleCount = 0;
//
//    public ImprovedHornClausebase() {
//        initializeClausebase(new HandleFOPCstrings(), null, null, null);
//    }
//
//    public ImprovedHornClausebase(HandleFOPCstrings stringHandler, Collection<? extends Sentence> rules, Collection<? extends Sentence> facts) {
//        initializeClausebase(stringHandler, rules, facts, null);
//    }
//
//    public ImprovedHornClausebase(HandleFOPCstrings stringHandler) {
//        initializeClausebase(stringHandler, null, null, null);
//    }
//
//    public ImprovedHornClausebase(HandleFOPCstrings stringHandler, Collection<? extends Sentence> rules, Collection<? extends Sentence> facts, ProcedurallyDefinedPredicateHandler userProcedurallyDefinedPredicateHandler) {
//        initializeClausebase(stringHandler, rules, facts, userProcedurallyDefinedPredicateHandler);
//    }
//
//    private void initializeClausebase(HandleFOPCstrings stringHandler, Collection<? extends Sentence> rules, Collection<? extends Sentence> facts, ProcedurallyDefinedPredicateHandler userProcHandler) {
//        this.stringHandler = stringHandler;
//        this.userProcedurallyDefinedPredicateHandler = userProcHandler;
//
//        this.builtinProcedurallyDefinedPredicateHandler = new BuiltinProcedurallyDefinedPredicateHandler(stringHandler);
//
//        addAssertRetractListener(new SpyAssertRetractListener(), stringHandler.getPredicate(stringHandler.standardPredicateNames.spy, 1));
//
//        setupDataStructures();
//
//        if (rules != null) {
//            assertBackgroundKnowledge(rules);
//        }
//
//        if (facts != null) {
//            assertFacts(facts);
//        }
//    }
//
//    /** Initializes the clausebase.
//     *
//     */
//    private void setupDataStructures() {
//
//        assertions = new MapOfLists<PredicateNameAndArity, DefiniteClause>();
//
//        // Check to see if the indexers are null, since someone might have tried to use other indexing class
//        // if they knew something specific about their data.
//        if (indexerForAllAssertions == null) {
//            indexerForAllAssertions = new DefaultHornClausebaseIndexer<DefiniteClause>();
//        }
//        if (indexerForFacts == null) {
//            indexerForFacts = new DefaultHornClausebaseIndexer<Literal>();
//        }
//        if (indexerForBackgroundKnowledge == null) {
//            indexerForBackgroundKnowledge = new DefaultHornClausebaseIndexer<Clause>();
//        }
//
//        resetIndexes();
//    }
//
//    @Override
//    public void assertBackgroundKnowledge(DefiniteClause definiteClause) throws IllegalArgumentException {
//        if (definiteClause.isDefiniteClause()) {
//            Clause clause = definiteClause.getDefiniteClauseAsClause(stringHandler);
//
//
//            if (checkRule(clause)) {
//                Literal head = definiteClause.getDefiniteClauseHead();
//                PredicateNameAndArity pnaa = head.getPredicateNameAndArity();
//
//                assertions.add(pnaa, clause);
//
//                indexBackgroundKnowledge(pnaa, clause);
//
//                fireAssertion(definiteClause);
//            }
//
//        }
//        else {
//            throw new IllegalArgumentException("Attempted to assert non-definite clause into the HornClauseFactBase: " + definiteClause);
//        }
//    }
//
//    @Override
//    public void assertBackgroundKnowledge(Collection<? extends Sentence> sentences) {
//        for (Sentence sentence : sentences) {
//            if (sentence instanceof DefiniteClause) {
//                DefiniteClause definiteClause = (DefiniteClause) sentence;
//                assertBackgroundKnowledge(definiteClause);
//            }
//            else {
//                List<Clause> clauses = sentence.convertToClausalForm();
//                if (clauses.size() != 1 || clauses.get(0).isDefiniteClause() == false) {
//                    throw new IllegalArgumentException("Sentence '" + sentence + "' is not a definite clause.");
//                }
//                assertBackgroundKnowledge(clauses.get(0));
//            }
//        }
//    }
//
//    @Override
//    public void assertFact(Literal literal) {
//        if (checkFact(literal)) {
//            PredicateNameAndArity pnaa = literal.getPredicateNameAndArity();
//
//            assertions.add(pnaa, literal);
//            indexFact(pnaa, literal);
//
//            fireAssertion(literal);
//        }
//    }
//
//    @Override
//    public void assertFacts(Collection<? extends Sentence> sentences) {
//        for (Sentence sentence : sentences) {
////            if (sentence instanceof DefiniteClause) {
////                DefiniteClause definiteClause = (DefiniteClause) sentence;
////                if ( definiteClause.isDefiniteClauseFact() ) {
////                    assertFact(definiteClause.getDefiniteClauseFactAsLiteral());
////                }
////                else {
////                    throw new IllegalArgumentException("Sentence '" + sentence + "' is not a definite clause fact.");
////                }
////            } else {
//            List<Clause> clauses = sentence.convertToClausalForm();
//            if (clauses.size() != 1 || clauses.get(0).isDefiniteClause() == false) {
//                throw new IllegalArgumentException("Sentence '" + sentence + "' is not a definite clause fact.");
//            }
//            assertFact(clauses.get(0).getDefiniteClauseFactAsLiteral());
////            }
//        }
//    }
//
//    @Override
//    public boolean retract(DefiniteClause definiteClause, BindingList bindingList) {
//
//        Literal clauseHead = definiteClause.getDefiniteClauseHead();
//
//        Collection<DefiniteClause> matchAssertions = getAssertions(clauseHead.predicateName, clauseHead.numberArgs());
//
//        boolean result = false;
//
//        if (matchAssertions != null) {
//
//            DefiniteClause clauseToRemove = null;
//
//            Iterator<DefiniteClause> it = matchAssertions.iterator();
//
//            while (it.hasNext()) {
//                DefiniteClause aClause = it.next();
//
//                if (definiteClause.unifyDefiniteClause(aClause, bindingList) != null) {
//
//                    clauseToRemove = aClause;
//                    result = true;
//                    break;
//                }
//            }
//
//            if ( clauseToRemove != null ) {
//                removeClause(clauseToRemove);
//            }
//        }
//
//        return result;
//    }
//
//    private void removeClauses(Collection<DefiniteClause> clausesToRemove) {
//        if ( clausesToRemove != null ) {
//            for (DefiniteClause definiteClause : clausesToRemove) {
//                removeClause(definiteClause);
//            }
//        }
//    }
//
//    private void removeClause(DefiniteClause clauseToRemove) {
//        PredicateNameAndArity pnaa = clauseToRemove.getDefiniteClauseHead().getPredicateNameAndArity();
//
//        assertions.removeValue(pnaa, clauseToRemove);
//        removeFromIndexes(pnaa, clauseToRemove);
//
//        fireRetraction(clauseToRemove);
//    }
//
//    @Override
//    public boolean retractAllClausesWithUnifyingBody(DefiniteClause definiteClause) {
//        Literal clauseHead = definiteClause.getDefiniteClauseHead();
//
//        Collection<DefiniteClause> matchAssertions = getAssertions(clauseHead.predicateName, clauseHead.numberArgs());
//
//        boolean result = false;
//
//        if (matchAssertions != null) {
//            Iterator<DefiniteClause> it = matchAssertions.iterator();
//
//            List<DefiniteClause> clausesToRemove = null;
//
//            while (it.hasNext()) {
//                DefiniteClause aClause = it.next();
//
//                if (definiteClause.unifyDefiniteClause(aClause, null) != null) {
//                    if ( clausesToRemove == null ) clausesToRemove = new ArrayList<DefiniteClause>();
//                    clausesToRemove.add(aClause);
//                    result = true;
//                }
//            }
//
//            if ( clausesToRemove != null ){
//                removeClauses(clausesToRemove);
//            }
//        }
//
//        return result;
//    }
//
//    @Override
//    public boolean retractAllClauseWithHead(DefiniteClause definiteClause) {
//
//        Literal clauseHead = definiteClause.getDefiniteClauseHead();
//
//        Collection<DefiniteClause> matchAssertions = getAssertions(clauseHead.predicateName, clauseHead.numberArgs());
//
//        List<DefiniteClause> clausesToRemove = null;
//
//        boolean result = false;
//
//        if (matchAssertions != null) {
//            Iterator<DefiniteClause> it = matchAssertions.iterator();
//
//            while (it.hasNext()) {
//                DefiniteClause aClause = it.next();
//
//                if (Unifier.UNIFIER.unify(clauseHead, aClause.getDefiniteClauseHead()) != null) {
//                    if ( clausesToRemove == null ) clausesToRemove = new ArrayList<DefiniteClause>();
//                    clausesToRemove.add(aClause);
//                    result = true;
//                }
//            }
//
//            if ( clausesToRemove != null ){
//                removeClauses(clausesToRemove);
//            }
//        }
//
//        return result;
//    }
//
//    @Override
//    public boolean retractAllClausesForPredicate(PredicateNameAndArity predicateNameAndArity) {
//
//        Collection<DefiniteClause> matchAssertions = getAssertions(predicateNameAndArity.getPredicateName(), predicateNameAndArity.getArity());
//
//        List<DefiniteClause> clausesToRemove = null;
//
//        boolean result = false;
//
//        if (matchAssertions != null) {
//            clausesToRemove = new ArrayList<DefiniteClause>();
//
//            for (DefiniteClause definiteClause : matchAssertions) {
//                clausesToRemove.add(definiteClause);
//                result = true;
//            }
//
//            if ( clausesToRemove != null ){
//                removeClauses(clausesToRemove);
//            }
//        }
//
//        return result;
//    }
//
//    public void retract(Collection<? extends Sentence> sentences) throws IllegalArgumentException {
//
//        for (Sentence sentence : sentences) {
//	        if (sentence instanceof DefiniteClause) {
//	            DefiniteClause definiteClause = (DefiniteClause) sentence;
//	            retract(definiteClause,null);
//	        }
//	        else {
//	            List<Clause> clauses = sentence.convertToClausalForm();
//	            if (clauses.size() != 1 || clauses.get(0).isDefiniteClause() == false) {
//	                throw new IllegalArgumentException("Sentence '" + sentence + "' is not a definite clause.");
//	            }
//	            retract(clauses.get(0),null);
//	        }
//        }
//    }
//
//    /** Checks to fact to make sure we should add it.
//     *
//     * Depending on the settings stringHandler.variantFactHandling settings, various checks will be performed.
//     *
//     * @param newRule Clause to check.
//     * @return True if the fact is okay to add to the fact base.  False otherwise.
//     */
//    private boolean checkFact(Literal newFact) {
//
//        boolean keep = true;
//
//        boolean ground = newFact.isGrounded();
//        if (reportFactsWithVariables && ground == false) {
//            Utils.println("% Fact containing variables: '" + newFact + "'.");
//        }
//
//        VariantClauseAction action = getStringHandler().variantFactHandling;
//
//        boolean duplicate = false;
//
//        if (action.isCheckRequired()) {
//
//            if (ground) {
//                duplicate = isFactAsserted(newFact);
//            }
//            else {
//
//                Collection<Literal> matching = getPossibleMatchingFacts(newFact, null);
//                if (matching != null) {
//                    for (Literal literal : matching) {
//                        if (literal.isVariant(newFact)) {
//                            duplicate = true;
//                            break;
//                        }
//                    }
//                }
//            }
//        }
//
//        if (duplicate) {
//            duplicateFactCount++;
//
//            if (action.isWarnEnabled()) {
//                // Utils.println("% Duplicate grounded fact #" + Utils.comma(++duplicateFactCount) + ": '" + newFact + (action.isRemoveEnabled() ? "'  It will be deleted." : "'  (It will be kept.  Manually delete if you wish it removed.)"));
//            }
//
//            if (action.isRemoveEnabled()) {
//                keep = false;
//            }
//        }
//
//        return keep;
//    }
//
//    /** Checks to fact to make sure we should add it.
//     *
//     * Depending on the settings stringHandler.variantFactHandling settings, various checks will be performed.
//     *
//     * @param newRule Literal to check.
//     * @return True if the fact is okay to add to the fact base.  False otherwise.
//     */
//    private boolean checkRule(Clause newRule) {
//
//        boolean keep = true;
//
//        VariantClauseAction action = getStringHandler().variantRuleHandling;
//
//        boolean duplicate = false;
//
//        if (action.isCheckRequired()) {
//            Collection<Clause> matching = getPossibleMatchingBackgroundKnowledge(newRule.getDefiniteClauseHead(), null);
//            if (matching != null) {
//                for (Clause clause : matching) {
//                    if (clause.isVariant(newRule)) {
//                        duplicate = true;
//                        break;
//                    }
//                }
//            }
//        }
//
//        if (duplicate) {
//            duplicateRuleCount++;
//
//            if (action.isWarnEnabled()) {
//                Utils.println("% Duplicate rule #" + Utils.comma(++duplicateRuleCount) + ": '" + newRule + (action.isRemoveEnabled() ? "'  It will be deleted." : "'  (It will be kept.  Manually delete if you wish it removed.)"));
//            }
//
//            if (action.isRemoveEnabled()) {
//                keep = false;
//            }
//        }
//
//        return keep;
//    }
//
//    /** Resets the indexes.
//     *
//     * The indexes are built lazily, as needed.
//     */
//    public void resetIndexes() {
//        indexerForAllAssertions.resetIndex();
//        indexerForFacts.resetIndex();
//        indexerForBackgroundKnowledge.resetIndex();
//    }
//
//    private void indexBackgroundKnowledge(PredicateNameAndArity predicateNameAndArity,DefiniteClause definiteClause) {
//        if (indexerForAllAssertions.isBuilt()) {
//            indexerForAllAssertions.indexAssertion(definiteClause);
//        }
//
//        if (indexerForBackgroundKnowledge.isBuilt()) {
//            indexerForBackgroundKnowledge.indexAssertion(definiteClause.getDefiniteClauseAsClause(stringHandler));
//        }
//    }
//
//    private void indexFact(PredicateNameAndArity par1,Literal literal) {
//        if (indexerForAllAssertions.isBuilt()) {
//            indexerForAllAssertions.indexAssertion(literal);
//        }
//
//        if (indexerForFacts.isBuilt()) {
//            indexerForFacts.indexAssertion(literal);
//        }
//    }
//
//    private void removeFromIndexes(PredicateNameAndArity predicateNameAndArity,DefiniteClause definiteClause) {
//        if (indexerForAllAssertions.isBuilt()) {
//            indexerForAllAssertions.removeAssertion(definiteClause);
//        }
//
//        if (indexerForBackgroundKnowledge.isBuilt()) {
//            indexerForBackgroundKnowledge.removeAssertion(definiteClause.getDefiniteClauseAsClause(stringHandler));
//        }
//
//        if (indexerForFacts.isBuilt() && definiteClause.isDefiniteClauseFact()) {
//            indexerForFacts.removeAssertion(definiteClause.getDefiniteClauseFactAsLiteral());
//        }
//    }
//
//    /** Builds the AllAssertions index, if necessary.
//     *
//     */
//    private void buildAllAssertionsIndex() {
//        if (indexerForAllAssertions.isBuilt() == false) {
//            //Utils.println("%  Building the all-assertions index with " + Utils.comma(assertions) + " assertions.");
//            indexerForAllAssertions.buildIndex(assertions);
//            //Utils.println("%  Done building the all-assertions index.");
//        }
//    }
//
//    /** Builds the background knowledge index, if necessary.
//     *
//     */
//    private void buildBackgroundKnowledgeIndex() {
//        if (indexerForBackgroundKnowledge.isBuilt() == false) {
//            //Utils.println("%  Building background knowledge index with " + backgroundKnowledge.size() + " clauses.");
//            indexerForBackgroundKnowledge.buildIndex(backgroundKnowledge);
//            //Utils.println("%  Done building background knowledge index.");
//        }
//    }
//
//    /** Builds the facts index, if necessary.
//     *
//     */
//    private void buildFactsIndex() {
//        if (indexerForFacts.isBuilt() == false) {
//            //Utils.println("%  Building facts index with " + facts.size() + " facts.");
//            indexerForFacts.buildIndex(facts);
//        }
//    }
//
//    @Override
//    public Collection<DefiniteClause> getPossibleMatchingAssertions(Literal clauseHead, BindingList currentBinding) {
//        return getIndexerForAllAssertions().getPossibleMatchingAssertions(clauseHead, currentBinding);
//    }
//
//    @Override
//    public Collection<Clause> getPossibleMatchingBackgroundKnowledge(Literal clauseHead, BindingList currentBinding) {
//        return getIndexerForBackgroundKnowledge().getPossibleMatchingAssertions(clauseHead, currentBinding);
//    }
//
//    @Override
//    public Collection<Literal> getPossibleMatchingFacts(Literal clauseHead, BindingList currentBinding) {
//        return getIndexerForFacts().getPossibleMatchingAssertions(clauseHead, currentBinding);
//    }
//
//    @Override
//    public boolean checkForPossibleMatchingAssertions(PredicateName predName, int arity) {
//        Collection<DefiniteClause> possibleMatches = getIndexerForAllAssertions().getPossibleMatchingAssertions(predName, arity);
//        return (possibleMatches != null && possibleMatches.size() > 0);
//    }
//
//    @Override
//    public Collection<DefiniteClause> getAssertions(PredicateName predName, int arity) {
//        return getIndexerForAllAssertions().getPossibleMatchingAssertions(predName, arity);
//    }
//
//    @Override
//    public boolean checkForPossibleMatchingFacts(PredicateName predName, int arity) {
//        Collection<Literal> possibleMatches = getIndexerForFacts().getPossibleMatchingAssertions(predName, arity);
//        return (possibleMatches != null && possibleMatches.size() > 0);
//    }
//
//    @Override
//    public Collection<Literal> getFacts(PredicateName predName, int arity) {
//        return getIndexerForFacts().getPossibleMatchingAssertions(predName, arity);
//    }
//
//    @Override
//    public boolean checkForPossibleMatchingBackgroundKnowledge(PredicateName predName, int arity) {
//        Collection<Clause> possibleMatches = getIndexerForBackgroundKnowledge().getPossibleMatchingAssertions(predName, arity);
//        return (possibleMatches != null && possibleMatches.size() > 0);
//    }
//
//    @Override
//    public Collection<Clause> getBackgroundKnowledge(PredicateName predName, int arity) {
//        return getIndexerForBackgroundKnowledge().getPossibleMatchingAssertions(predName, arity);
//    }
//
//    @Override
//    public Collection<DefiniteClause> getAssertions() {
//        throw new UnsupportedOperationException("This is a bad method.  Instead we need to write an iterator for all assertions.");
//    }
//
//    @Override
//    public Collection<Literal> getFacts() {
//        throw new UnsupportedOperationException("This is a bad method.  Instead we need to write an iterator for all assertions.");
//        //return facts;
//    }
//
//    @Override
//    public Collection<Clause> getBackgroundKnowledge() {
//        throw new UnsupportedOperationException("This is a bad method.  Instead we need to write an iterator for all assertions.");
//        //return backgroundKnowledge;
//    }
//
//    @Override
//    public boolean isOnlyInFacts(PredicateName predName, int arity) {
//        // This is really expensive!  Without maintain a completely separate data structure for
//        return getIndexerForFacts().getPossibleMatchingAssertions(predName, arity) != null && getIndexerForBackgroundKnowledge().getPossibleMatchingAssertions(predName, arity) == null;
//    }
//
//    /**
//     * @return the stringHandler
//     */
//    @Override
//    public HandleFOPCstrings getStringHandler() {
//        return stringHandler;
//    }
//
//    /**
//     * @return the builtinProcedurallyDefinedPredicateHandler
//     */
//    @Override
//    public ProcedurallyDefinedPredicateHandler getBuiltinProcedurallyDefinedPredicateHandler() {
//        return builtinProcedurallyDefinedPredicateHandler;
//    }
//
//    /**
//     * @param builtinProcedurallyDefinedPredicateHandler the builtinProcedurallyDefinedPredicateHandler to set
//     */
//    public void setBuiltinProcedurallyDefinedPredicateHandler(ProcedurallyDefinedPredicateHandler builtinProcedurallyDefinedPredicateHandler) {
//        this.builtinProcedurallyDefinedPredicateHandler = builtinProcedurallyDefinedPredicateHandler;
//    }
//
//    /**
//     * @return the userProcedurallyDefinedPredicateHandler
//     */
//    @Override
//    public ProcedurallyDefinedPredicateHandler getUserProcedurallyDefinedPredicateHandler() {
//        return userProcedurallyDefinedPredicateHandler;
//    }
//
//    /**
//     * @param userProcedurallyDefinedPredicateHandler the userProcedurallyDefinedPredicateHandler to set
//     */
//    @Override
//    public void setUserProcedurallyDefinedPredicateHandler(ProcedurallyDefinedPredicateHandler userProcedurallyDefinedPredicateHandler) {
//        this.userProcedurallyDefinedPredicateHandler = userProcedurallyDefinedPredicateHandler;
//    }
//
//    @Override
//    public String toString() {
//        StringBuilder sb = new StringBuilder();
//
//        sb.append("DefaultHornClauseFactbase:\n");
//        sb.append("\nAll assertions indexer:\n");
//        sb.append(indexerForAllAssertions);
//        sb.append("\nRules indexer:\n");
//        sb.append(indexerForBackgroundKnowledge);
//        sb.append("\nFacts indexer:\n");
//        sb.append(indexerForFacts);
//
//        return sb.toString();
//    }
//
//    public String toLongString() {
//        StringBuilder sb = new StringBuilder();
//
//        sb.append("DefaultHornClauseFactbase:\n");
//        sb.append("\nAssertions:\n");
//        for (DefiniteClause definiteClause : assertions) {
//            sb.append("  ").append(definiteClause).append(".\n");
//        }
//        sb.append("\nAll assertions indexer:\n");
//        sb.append(getIndexerForAllAssertions());
//        sb.append("\nRules indexer:\n");
//        sb.append(getIndexerForBackgroundKnowledge());
//        sb.append("\nFacts indexer:\n");
//        sb.append(getIndexerForFacts());
//
//        return sb.toString();
//    }
//
//    @Override
//    public boolean recorded(DefiniteClause definiteClause) {
//        Clause definiteClauseAsClause = definiteClause.getDefiniteClauseAsClause(stringHandler);
//        Literal clauseHead = definiteClause.getDefiniteClauseHead();
//        Collection<DefiniteClause> possibleMatchingClauses = getIndexerForAllAssertions().getPossibleMatchingAssertions(clauseHead, null);
//        if (possibleMatchingClauses != null) {
//            BindingList bl = new BindingList();
//            for (DefiniteClause anotherClause : possibleMatchingClauses) {
//                // Variants will check for duplication without performing unification.
//                bl.theta.clear();
//                if (definiteClauseAsClause.variants(anotherClause.getDefiniteClauseAsClause(stringHandler), bl) != null) {
//                    return true;
//                }
//            }
//        }
//        return false;
//    }
//
//    private boolean isFactAsserted(Literal literal) {
//        Collection<Literal> possibleMatchingFacts = getIndexerForFacts().getPossibleMatchingAssertions(literal, null);
//        if (possibleMatchingFacts != null) {
//            BindingList bl = new BindingList();
//            for (Literal anotherFact : possibleMatchingFacts) {
//                // Variants will check for duplication without performing unification.
//                bl.theta.clear();
//                if (literal.variants(anotherFact, bl) != null) {
//                    return true;
//                }
//            }
//        }
//        return false;
//    }
//
//    /** Returns the index for all assertions.
//     *
//     * If the index is not built yet, this method will build it.
//     *
//     * @return the indexerForAllAssertions
//     */
//    private HornClausebaseIndexer<DefiniteClause> getIndexerForAllAssertions() {
//        buildAllAssertionsIndex();
//        return indexerForAllAssertions;
//    }
//
//    /** Returns the index for all facts.
//     *
//     * If the index is not built yet, this method will build it.
//     *
//     * @return the indexerForFacts
//     */
//    private HornClausebaseIndexer<Literal> getIndexerForFacts() {
//        buildFactsIndex();
//        return indexerForFacts;
//    }
//
//    /** Returns the index for all background knowledge.
//     *
//     * If the index is not built yet, this method will build it.
//     *
//     * @return the indexerForBackgroundKnowledge
//     */
//    private HornClausebaseIndexer<Clause> getIndexerForBackgroundKnowledge() {
//        buildBackgroundKnowledgeIndex();
//        return indexerForBackgroundKnowledge;
//    }
//
//    /** Sets the indexer for all assertions.
//     *
//     * This will set the indexer to be used for all assertions.  As a side effect,
//     * the index will be reset and lazily rebuilt when necessary.
//     *
//     * @param indexerForAllAssertions the indexerForAllAssertions to set, must be non-null.
//     */
//    public void setIndexerForAllAssertions(HornClausebaseIndexer<DefiniteClause> indexerForAllAssertions) {
//        if (indexerForAllAssertions == null) {
//            throw new IllegalArgumentException("Indexer must be non-null");
//        }
//
//        this.indexerForAllAssertions = indexerForAllAssertions;
//    }
//
//    /** Sets the indexer for facts.
//     *
//     * This will set the indexer to be used for all assertions.  As a side effect,
//     * the index will be reset and lazily rebuilt when necessary.
//     *
//     * @param indexerForFacts the indexerForFacts to set
//     */
//    public void setIndexerForFacts(HornClausebaseIndexer<Literal> indexerForFacts) {
//        if (indexerForFacts == null) {
//            throw new IllegalArgumentException("Indexer must be non-null");
//        }
//
//        this.indexerForFacts = indexerForFacts;
//    }
//
//    /** Sets the indexer for background knowledge.
//     *
//     * This will set the indexer to be used for all assertions.  As a side effect,
//     * the index will be reset and lazily rebuilt when necessary.
//     *
//     *
//     * @param indexerForBackgroundKnowledge the indexerForBackgroundKnowledge to set
//     */
//    public void setIndexerForBackgroundKnowledge(HornClausebaseIndexer<Clause> indexerForBackgroundKnowledge) {
//        if (indexerForBackgroundKnowledge == null) {
//            throw new IllegalArgumentException("Indexer must be non-null.");
//        }
//
//        this.indexerForBackgroundKnowledge = indexerForBackgroundKnowledge;
//    }
//
//    public void reportStats() {
//    	Utils.println("% Stats about the HornClausebase:");
//    	Utils.println("%   |backgroundKnowledge| = " + Utils.comma(backgroundKnowledge));
//    	Utils.println("%   |facts|               = " + Utils.comma(facts));
//    	Utils.println("%   |assertions|          = " + Utils.comma(assertions));
//    }
//
//    public void addAssertRetractListener(AssertRetractListener assertRetractListener, PredicateNameAndArity predicate) {
//        if (listenerMap == null) {
//            listenerMap = new HashMap<PredicateNameAndArity, List<AssertRetractListener>>();
//        }
//
//        List<AssertRetractListener> list = listenerMap.get(predicate);
//        if ( list == null ) {
//            list = new ArrayList<AssertRetractListener>();
//            listenerMap.put(predicate, list);
//        }
//
//        if ( list.contains(assertRetractListener) == false ) {
//            list.add(assertRetractListener);
//        }
//    }
//
//    public void removeAssertRetractListener(AssertRetractListener assertRetractListener, PredicateNameAndArity predicate) {
//        if (listenerMap != null) {
//            List<AssertRetractListener> list = listenerMap.get(predicate);
//            if ( list != null ) {
//                list.remove(assertRetractListener);
//
//                if ( list.isEmpty() ) {
//                    listenerMap.remove(predicate);
//
//                    if ( listenerMap.isEmpty() ) {
//                        listenerMap = null;
//                    }
//                }
//            }
//        }
//    }
//
//    private void fireAssertion(DefiniteClause clause) {
//        if ( listenerMap != null ) {
//            PredicateNameAndArity pnaa = new PredicateNameAndArity(clause);
//
//            List<AssertRetractListener> list = listenerMap.get(pnaa);
//
//            if ( list != null ) {
//                for (AssertRetractListener assertRetractListener : list) {
//                    assertRetractListener.clauseAsserted(this, clause);
//                }
//            }
//        }
//    }
//
//    private void fireRetraction(DefiniteClause clause) {
//        if ( listenerMap != null ) {
//            PredicateNameAndArity pnaa = new PredicateNameAndArity(clause);
//
//            List<AssertRetractListener> list = listenerMap.get(pnaa);
//
//            if ( list != null ) {
//                for (AssertRetractListener assertRetractListener : list) {
//                    assertRetractListener.clauseRetracted(this, clause);
//                }
//            }
//        }
//    }
//
//    public class SpyAssertRetractListener implements AssertRetractListener{
//
//        public void clauseAsserted(HornClausebase context, DefiniteClause clause) {
//            if ( clause.isDefiniteClauseFact() ) {
//                Literal fact = clause.getDefiniteClauseFactAsLiteral();
//                if ( fact.predicateName == context.getStringHandler().standardPredicateNames.spy && fact.getArity() == 1) {
//                    try {
//                        Term term = fact.getArgument(0);
//                        Function function = (Function) term;
//                        String predName = ((StringConstant)function.getArgument(0)).name;
//                        int predArity = ((NumericConstant)function.getArgument(1)).value.intValue();
//
//                        getStringHandler().spyEntries.addLiteral(predName, predArity);
//                    } catch( Exception e) {
//                        Utils.warning("Encountered spy/1 statement.  Expected argument 1 to be function of form pred/arity.  Found: " + fact + ".");
//                    }
//                }
//            }
//        }
//
//        public void clauseRetracted(HornClausebase context, DefiniteClause clause) {
//            throw new UnsupportedOperationException("Not supported yet.");
//        }
//    }
//}
