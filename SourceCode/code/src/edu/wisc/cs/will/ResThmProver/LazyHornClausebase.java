/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.BuiltinProcedurallyDefinedPredicateHandler;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.ProcedurallyDefinedPredicateHandler;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.StringConstant;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.Utils.Utils;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

/**
 *
 * @author twalker
 */
public class LazyHornClausebase implements HornClausebase {

    /** Set of all asserted sentences.
     *
     * To maintain prolog semantics, we need to have all assertions in order,
     * independent of whether they are facts (definite clauses with no body, stored
     * as bare Literals) or rules (definite clauses with one or more Literals in
     * the body, stored as DefiniteClauses).
     */
    protected MapOfDefiniteClauseLists assertions = null;

    private HandleFOPCstrings stringHandler;

    private Map<PredicateNameAndArity, List<AssertRetractListener>> listenerMap = null;
    
    protected static final int DEBUG = 0;

    /** Index for all assertions.
     *
     * This should never be used directly.  Always use the accessor method since
     * indices are build lazily and the index may not yet be built if you use this
     * directly.
     *
     * Guaranteed to be non-null.
     */
    private LazyHornClausebaseIndexer indexerForAllAssertions; 

//    /** Index for all facts.
//     *
//     * This should never be used directly.  Always use the accessor method since
//     * indices are build lazily and the index may not yet be built if you use this
//     * directly.
//     *
//     * Guaranteed to be non-null.
//     */
//    private LazyHornClausebaseIndexer<Literal> indexerForFacts;
    private ProcedurallyDefinedPredicateHandler builtinProcedurallyDefinedPredicateHandler;

    private ProcedurallyDefinedPredicateHandler userProcedurallyDefinedPredicateHandler;

    protected boolean reportFactsWithVariables = false; // Report facts with variables in them.

    private int duplicateFactCount = 0;

    private int duplicateRuleCount = 0;

    public LazyHornClausebase() {
        initializeClausebase(new HandleFOPCstrings(), null, null, null);
    }

    public LazyHornClausebase(HandleFOPCstrings stringHandler, Collection<? extends Sentence> rules, Collection<? extends Sentence> facts) {
        initializeClausebase(stringHandler, rules, facts, null);
    }

    public LazyHornClausebase(HandleFOPCstrings stringHandler) {
        initializeClausebase(stringHandler, null, null, null);
    }

    public LazyHornClausebase(HandleFOPCstrings stringHandler, Collection<? extends Sentence> rules, Collection<? extends Sentence> facts, ProcedurallyDefinedPredicateHandler userProcedurallyDefinedPredicateHandler) {
        initializeClausebase(stringHandler, rules, facts, userProcedurallyDefinedPredicateHandler);
    }

    private void initializeClausebase(HandleFOPCstrings stringHandler, Collection<? extends Sentence> rules, Collection<? extends Sentence> facts, ProcedurallyDefinedPredicateHandler userProcHandler) {
        this.stringHandler = stringHandler;
        this.userProcedurallyDefinedPredicateHandler = userProcHandler;

        this.builtinProcedurallyDefinedPredicateHandler = new BuiltinProcedurallyDefinedPredicateHandler(stringHandler);

        addAssertRetractListener(new SpyAssertRetractListener(), stringHandler.getPredicate(stringHandler.standardPredicateNames.spy, 1));

        setupDataStructures();

        if (rules != null) {
            assertBackgroundKnowledge(rules);
        }

        if (facts != null) {
            assertFacts(facts);
        }
    }

    /** Initializes the clausebase.
     *
     */
    private void setupDataStructures() {
        assertions = new MapOfDefiniteClauseLists();

        // Check to see if the indexers are null, since someone might have tried to use other indexing class
        // if they knew something specific about their data.
        if (indexerForAllAssertions == null) {
            indexerForAllAssertions = new LazyHornClausebaseIndexer(this);
        }
//        if (indexerForFacts == null) {
//            indexerForFacts = new LazyHornClausebaseIndexer<Literal>(this, Literal.class);
//        }

        resetIndexes();
    }

    @Override
    public void assertBackgroundKnowledge(DefiniteClause definiteClause) throws IllegalArgumentException {
        if (definiteClause.isDefiniteClause()) {
            Clause clause = definiteClause.getDefiniteClauseAsClause();

            if (checkRule(clause)) {
                assertions.add(clause.getDefiniteClauseHead().getPredicateNameAndArity(), definiteClause);

                indexerForAllAssertions.indexAssertion(clause);

                fireAssertion(definiteClause);
            }

        }
        else {
            throw new IllegalArgumentException("Attempted to assert non-definite clause into the HornClauseFactBase: " + definiteClause);
        }
    }

    @Override
    public void assertBackgroundKnowledge(Collection<? extends Sentence> sentences) {
        for (Sentence sentence : sentences) {
            if (sentence instanceof DefiniteClause) {
                DefiniteClause definiteClause = (DefiniteClause) sentence;
                assertBackgroundKnowledge(definiteClause);
            }
            else {
                List<Clause> clauses = sentence.convertToClausalForm();
                if (clauses.size() != 1 || clauses.get(0).isDefiniteClause() == false) {
                    throw new IllegalArgumentException("Sentence '" + sentence + "' is not a definite clause.");
                }
                assertBackgroundKnowledge(clauses.get(0));
            }
        }
    }

    @Override
    public void assertFact(Literal literal) {
        if (checkFact(literal)) {
            
            if ( DEBUG >= 2 ) Utils.println("% [ LazyHornClausebase ]  Asserting fact " + literal + ".");
            
            assertions.add(literal.getPredicateNameAndArity(), literal);

            indexerForAllAssertions.indexAssertion(literal);

            fireAssertion(literal);
        }
    }

    @Override
    public void assertFacts(Collection<? extends Sentence> sentences) {
        for (Sentence sentence : sentences) {
            List<Clause> clauses = sentence.convertToClausalForm();
            if (clauses.size() != 1 || clauses.get(0).isDefiniteClause() == false) {
                throw new IllegalArgumentException("Sentence '" + sentence + "' is not a definite clause fact.");
            }
            assertFact(clauses.get(0).getDefiniteClauseFactAsLiteral());
        }
    }

    @Override
    public boolean retract(DefiniteClause definiteClause, BindingList bindingList) {

        Literal clauseHead = definiteClause.getDefiniteClauseHead();

        Collection<DefiniteClause> matchAssertions = getAssertions(clauseHead.predicateName, clauseHead.numberArgs());

        boolean result = false;

        if (matchAssertions != null) {

            DefiniteClause clauseToRemove = null;

            Iterator<DefiniteClause> it = matchAssertions.iterator();

            while (it.hasNext()) {
                DefiniteClause aClause = it.next();

                if (definiteClause.unifyDefiniteClause(aClause, bindingList) != null) {

                    clauseToRemove = aClause;
                    result = true;
                    break;
                }
            }

            if (clauseToRemove != null) {
                removeClause(clauseToRemove);
            }
        }

        return result;
    }

    private void removeClauses(Collection<DefiniteClause> clausesToRemove) {

        if (clausesToRemove != null) {
            for (DefiniteClause definiteClause : clausesToRemove) {
                removeClause(definiteClause);
            }
        }
    }

    /** Remove the first exact clause.
     * 
     * @param clauseToRemove
     */
    public void removeClause(DefiniteClause clauseToRemove) {

        PredicateNameAndArity pnaa = clauseToRemove.getDefiniteClauseHead().getPredicateNameAndArity();

        assertions.removeValue(pnaa, clauseToRemove);
        //backgroundKnowledge.remove(clauseToRemove.getDefiniteClauseAsClause(stringHandler));
//        if (clauseToRemove.isDefiniteClauseFact()) {
//            facts.remove(clauseToRemove.getDefiniteClauseFactAsLiteral());
//        }
        removeFromIndexes(clauseToRemove);

        fireRetraction(clauseToRemove);
    }

    @Override
    public boolean retractAllClausesWithUnifyingBody(DefiniteClause definiteClause) {

        Literal clauseHead = definiteClause.getDefiniteClauseHead();

        Collection<DefiniteClause> matchAssertions = getAssertions(clauseHead.predicateName, clauseHead.numberArgs());

        boolean result = false;

        if (matchAssertions != null) {
            Iterator<DefiniteClause> it = matchAssertions.iterator();

            DefiniteClauseList clausesToRemove = null;

            while (it.hasNext()) {
                DefiniteClause aClause = it.next();

                if (definiteClause.unifyDefiniteClause(aClause, null) != null) {
                    if (clausesToRemove == null) {
                        clausesToRemove = new DefiniteClauseList();
                    }
                    clausesToRemove.add(aClause);
                    result = true;
                }
            }

            if (clausesToRemove != null) {
                removeClauses(clausesToRemove);
            }
        }

        return result;
    }

    @Override
    public boolean retractAllClauseWithHead(DefiniteClause definiteClause) {

        Literal clauseHead = definiteClause.getDefiniteClauseHead();

        Collection<DefiniteClause> matchAssertions = getAssertions(clauseHead.predicateName, clauseHead.numberArgs());

        DefiniteClauseList clausesToRemove = null;

        boolean result = false;

        if (matchAssertions != null) {
            Iterator<DefiniteClause> it = matchAssertions.iterator();

            while (it.hasNext()) {
                DefiniteClause aClause = it.next();

                if (Unifier.UNIFIER.unify(clauseHead, aClause.getDefiniteClauseHead()) != null) {
                    if (clausesToRemove == null) {
                        clausesToRemove = new DefiniteClauseList();
                    }
                    clausesToRemove.add(aClause);
                    result = true;
                }
            }

            if (clausesToRemove != null) {
                removeClauses(clausesToRemove);
            }
        }

        return result;
    }

    @Override
    public boolean retractAllClausesForPredicate(PredicateNameAndArity predicateNameAndArity) {

        DefiniteClauseList matchAssertions = getAssertions(predicateNameAndArity.getPredicateName(), predicateNameAndArity.getArity());

        DefiniteClauseList clausesToRemove = null;

        boolean result = false;

        if (matchAssertions != null) {
            clausesToRemove = new DefiniteClauseList();

            for (DefiniteClause definiteClause : matchAssertions) {
                clausesToRemove.add(definiteClause);
                result = true;
            }

            if (clausesToRemove != null) {
                removeClauses(clausesToRemove);
            }
        }

        return result;
    }

    public void retract(Collection<? extends Sentence> sentences) throws IllegalArgumentException {

        for (Sentence sentence : sentences) {
            if (sentence instanceof DefiniteClause) {
                DefiniteClause definiteClause = (DefiniteClause) sentence;
                retract(definiteClause, null);
            }
            else {
                List<Clause> clauses = sentence.convertToClausalForm();
                if (clauses.size() != 1 || clauses.get(0).isDefiniteClause() == false) {
                    throw new IllegalArgumentException("Sentence '" + sentence + "' is not a definite clause.");
                }
                retract(clauses.get(0), null);
            }
        }
    }

    /** Checks to fact to make sure we should add it.
     *
     * Depending on the settings stringHandler.variantFactHandling settings, various checks will be performed.
     *
     * @param newRule Clause to check.
     * @return True if the fact is okay to add to the fact base.  False otherwise.
     */
    private boolean checkFact(Literal newFact) {

        boolean keep = true;

        boolean ground = newFact.isGrounded();
        if (reportFactsWithVariables && ground == false) {
            Utils.println("% Fact containing variables: '" + newFact + "'.");
        }

        VariantClauseAction action = getStringHandler().variantFactHandling;

        boolean duplicate = false;

        if (action.isCheckRequired()) {

            if (ground) {
                duplicate = isFactAsserted(newFact);
            }
            else {

                Iterable<Literal> matching = getPossibleMatchingFacts(newFact, null);
                if (matching != null) {
                    for (Literal literal : matching) {
                        if (literal.isVariant(newFact)) {
                            duplicate = true;
                            break;
                        }
                    }
                }
            }
        }

        if (duplicate) {
            duplicateFactCount++;

            if (action.isWarnEnabled()) {
                // Utils.println("% Duplicate grounded fact #" + Utils.comma(++duplicateFactCount) + ": '" + newFact + (action.isRemoveEnabled() ? "'  It will be deleted." : "'  (It will be kept.  Manually delete if you wish it removed.)"));
            }

            if (action.isRemoveEnabled()) {
                keep = false;
            }
        }

        return keep;
    }

    /** Checks to fact to make sure we should add it.
     *
     * Depending on the settings stringHandler.variantFactHandling settings, various checks will be performed.
     *
     * @param newRule Literal to check.
     * @return True if the fact is okay to add to the fact base.  False otherwise.
     */
    private boolean checkRule(Clause newRule) {

        boolean keep = true;

        VariantClauseAction action = getStringHandler().variantRuleHandling;

        boolean duplicate = false;

        if (action.isCheckRequired()) {
            Iterable<Clause> matching = getPossibleMatchingBackgroundKnowledge(newRule.getDefiniteClauseHead(), null);
            if (matching != null) {
                for (Clause clause : matching) {
                    if (clause.isVariant(newRule)) {
                        duplicate = true;
                        break;
                    }
                }
            }
        }

        if (duplicate) {
            duplicateRuleCount++;

            if (action.isWarnEnabled()) {
                Utils.println("% Duplicate rule #" + Utils.comma(++duplicateRuleCount) + ": '" + newRule + (action.isRemoveEnabled() ? "'  It will be deleted." : "'  (It will be kept.  Manually delete if you wish it removed.)"));
            }

            if (action.isRemoveEnabled()) {
                keep = false;
            }
        }

        return keep;
    }

    /** Resets the indexes.
     *
     * The indexes are built lazily, as needed.
     */
    public void resetIndexes() {
        indexerForAllAssertions.resetIndex();
    }

    private void removeFromIndexes(DefiniteClause definiteClause) {
        if (indexerForAllAssertions.isBuilt()) {
            indexerForAllAssertions.removeAssertion(definiteClause);
        }
    }

    /** Builds the AllAssertions index, if necessary.
     *
     */
    private void buildAllAssertionsIndex() {
        // Lazy indices don't need to be built.
//        if (indexerForAllAssertions.isBuilt() == false) {
//            //Utils.println("%  Building the all-assertions index with " + Utils.comma(assertions) + " assertions.");
//            indexerForAllAssertions.buildIndex(assertions);
//            //Utils.println("%  Done building the all-assertions index.");
//        }
    }

    @Override
    public DefiniteClauseList getPossibleMatchingAssertions(Literal clauseHead, BindingList currentBinding) {
        return getIndexerForAllAssertions().getPossibleMatchingAssertions(clauseHead, currentBinding);
    }

    @Override
    public Iterable<Clause> getPossibleMatchingBackgroundKnowledge(Literal clauseHead, BindingList currentBinding) {
        DefiniteClauseList list = getIndexerForAllAssertions().getPossibleMatchingAssertions(clauseHead, currentBinding);
        return list == null ? null : list.getClauseIterable();
    }

    @Override
    public Iterable<Literal> getPossibleMatchingFacts(Literal clauseHead, BindingList currentBinding) {
        DefiniteClauseList list = getIndexerForAllAssertions().getPossibleMatchingAssertions(clauseHead, currentBinding);
        return list == null ? null : list.getFactIterable();
    }

    @Override
    public boolean checkForPossibleMatchingAssertions(PredicateName predName, int arity) {
//        DefiniteClauseList possibleMatches = getIndexerForAllAssertions().getPossibleMatchingAssertions(predName, arity);
//        return (possibleMatches != null && possibleMatches.size() > 0);
        return assertions.containsKey( new PredicateNameAndArity(predName, arity));
    }

    public MapOfDefiniteClauseLists getAssertionsMap() {
        return assertions;
    }

    @Override
    public DefiniteClauseList getAssertions(PredicateName predName, int arity) {
        return getIndexerForAllAssertions().getPossibleMatchingAssertions(predName, arity);
    }

    @Override
    public boolean checkForPossibleMatchingFacts(PredicateName predName, int arity) {
        DefiniteClauseList possibleMatches = getIndexerForAllAssertions().getPossibleMatchingAssertions(predName, arity);
        return (possibleMatches != null && possibleMatches.size() > 0);
    }
//
//    @Override
//    public List<Literal> getFacts(PredicateName predName, int arity) {
//        throw new UnsupportedOperationException("Not implemented");
////        return getIndexerForFacts().getPossibleMatchingAssertions(predName, arity);
//    }

    @Override
    public boolean checkForPossibleMatchingBackgroundKnowledge(PredicateName predName, int arity) {
        //DefiniteClauseList possibleMatches = getIndexerForAllAssertions().getPossibleMatchingAssertions(predName, arity);
        //return (possibleMatches != null && possibleMatches.size() > 0);
        return assertions.containsKey( new PredicateNameAndArity(predName, arity));
    }

//    @Override
//    public List<Clause> getBackgroundKnowledge(PredicateName predName, int arity) {
//        throw new UnsupportedOperationException("Not implemented");
//
////        return getIndexerForBackgroundKnowledge().getPossibleMatchingAssertions(predName, arity);
//    }
    @Override
    public Iterable<DefiniteClause> getAssertions() {
        return assertions;
    }

    @Override
    public Iterable<Literal> getFacts() {
        return new DefiniteClauseToLiteralIterable(assertions);
    }

    @Override
    public Iterable<Clause> getBackgroundKnowledge() {
        return new DefiniteClauseToClauseIterable(assertions);
    }

    /**
     * @return the stringHandler
     */
    @Override
    public HandleFOPCstrings getStringHandler() {
        return stringHandler;
    }

    /**
     * @return the builtinProcedurallyDefinedPredicateHandler
     */
    @Override
    public ProcedurallyDefinedPredicateHandler getBuiltinProcedurallyDefinedPredicateHandler() {
        return builtinProcedurallyDefinedPredicateHandler;
    }

    /**
     * @param builtinProcedurallyDefinedPredicateHandler the builtinProcedurallyDefinedPredicateHandler to set
     */
    public void setBuiltinProcedurallyDefinedPredicateHandler(ProcedurallyDefinedPredicateHandler builtinProcedurallyDefinedPredicateHandler) {
        this.builtinProcedurallyDefinedPredicateHandler = builtinProcedurallyDefinedPredicateHandler;
    }

    /**
     * @return the userProcedurallyDefinedPredicateHandler
     */
    @Override
    public ProcedurallyDefinedPredicateHandler getUserProcedurallyDefinedPredicateHandler() {
        return userProcedurallyDefinedPredicateHandler;
    }

    /**
     * @param userProcedurallyDefinedPredicateHandler the userProcedurallyDefinedPredicateHandler to set
     */
    @Override
    public void setUserProcedurallyDefinedPredicateHandler(ProcedurallyDefinedPredicateHandler userProcedurallyDefinedPredicateHandler) {
        this.userProcedurallyDefinedPredicateHandler = userProcedurallyDefinedPredicateHandler;
    }

    @Override
    public boolean isOnlyInFacts(PredicateName predName, int arity) {

        DefiniteClauseList list = indexerForAllAssertions.getPossibleMatchingAssertions(predName, arity);

        return list != null && list.containsOnlyFacts();
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append("LazyHornClauseFactbase:\n");
        sb.append("\nAll assertions indexer:\n");
        sb.append(indexerForAllAssertions);
//        sb.append("\nFacts indexer:\n");
//        sb.append(indexerForFacts);

        return sb.toString();
    }

    public String toLongString() {
        StringBuilder sb = new StringBuilder();

        sb.append("LazyHornClauseFactbase:\n");
        sb.append("\nAssertions:\n");

        for (List<DefiniteClause> list : assertions.values()) {
            for (DefiniteClause definiteClause : list) {
                sb.append("  ").append(definiteClause).append(".\n");
            }
        }
        sb.append("\nAll assertions indexer:\n");
        sb.append(getIndexerForAllAssertions());

        return sb.toString();
    }

    @Override
    public boolean recorded(DefiniteClause definiteClause) {
        Clause definiteClauseAsClause = definiteClause.getDefiniteClauseAsClause();
        Literal clauseHead = definiteClause.getDefiniteClauseHead();
        Collection<DefiniteClause> possibleMatchingClauses = getIndexerForAllAssertions().getPossibleMatchingAssertions(clauseHead, null);
        if (possibleMatchingClauses != null) {
            BindingList bl = new BindingList();
            for (DefiniteClause anotherClause : possibleMatchingClauses) {
                // Variants will check for duplication without performing unification.
                bl.theta.clear();
                if (definiteClauseAsClause.variants(anotherClause.getDefiniteClauseAsClause(), bl) != null) {
                    return true;
                }
            }
        }
        return false;
    }

    private boolean isFactAsserted(Literal literal) {
        Iterable<Literal> possibleMatchingFacts = getPossibleMatchingFacts(literal, null);
        if (possibleMatchingFacts != null) {
            for (Literal anotherFact : possibleMatchingFacts) {
                BindingList bl = new BindingList();
                if (literal.variants(anotherFact, bl) != null) {
                    return true;
                }
            }
        }
        return false;
    }

    /** Returns the index for all assertions.
     *
     * If the index is not built yet, this method will build it.
     *
     * @return the indexerForAllAssertions
     */
    private LazyHornClausebaseIndexer getIndexerForAllAssertions() {
        buildAllAssertionsIndex();
        return indexerForAllAssertions;
    }

    /** Returns the index for all facts.
     *
     * If the index is not built yet, this method will build it.
     *
     * @return the indexerForFacts
     */
//    private LazyHornClausebaseIndexer<Literal> getIndexerForFacts() {
//        buildFactsIndex();
//        return indexerForFacts;
//    }
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
    /** Sets the indexer for all assertions.
     *
     * This will set the indexer to be used for all assertions.  As a side effect,
     * the index will be reset and lazily rebuilt when necessary.
     *
     * @param indexerForAllAssertions the indexerForAllAssertions to set, must be non-null.
     */
    public void setIndexerForAllAssertions(LazyHornClausebaseIndexer indexerForAllAssertions) {
        if (indexerForAllAssertions == null) {
            throw new IllegalArgumentException("Indexer must be non-null");
        }

        this.indexerForAllAssertions = indexerForAllAssertions;
    }

//    /** Sets the indexer for facts.
//     *
//     * This will set the indexer to be used for all assertions.  As a side effect,
//     * the index will be reset and lazily rebuilt when necessary.
//     *
//     * @param indexerForFacts the indexerForFacts to set
//     */
//    public void setIndexerForFacts(LazyHornClausebaseIndexer<Literal> indexerForFacts) {
//        if (indexerForFacts == null) {
//            throw new IllegalArgumentException("Indexer must be non-null");
//        }
//
//        this.indexerForFacts = indexerForFacts;
//    }
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
    public void reportStats() {
        Utils.println("% Stats about the HornClausebase:");
        Utils.println("%   |assertions|          = " + Utils.comma(assertions.size()));
    }

    public void addAssertRetractListener(AssertRetractListener assertRetractListener, PredicateNameAndArity predicate) {
        if (listenerMap == null) {
            listenerMap = new HashMap<PredicateNameAndArity, List<AssertRetractListener>>();
        }

        List<AssertRetractListener> list = listenerMap.get(predicate);
        if (list == null) {
            list = new ArrayList<AssertRetractListener>();
            listenerMap.put(predicate, list);
        }

        if (list.contains(assertRetractListener) == false) {
            list.add(assertRetractListener);
        }
    }

    public void removeAssertRetractListener(AssertRetractListener assertRetractListener, PredicateNameAndArity predicate) {
        if (listenerMap != null) {
            List<AssertRetractListener> list = listenerMap.get(predicate);
            if (list != null) {
                list.remove(assertRetractListener);

                if (list.isEmpty()) {
                    listenerMap.remove(predicate);

                    if (listenerMap.isEmpty()) {
                        listenerMap = null;
                    }
                }
            }
        }
    }

    private void fireAssertion(DefiniteClause clause) {
        if (listenerMap != null) {
            PredicateNameAndArity pnaa = new PredicateNameAndArity(clause);

            List<AssertRetractListener> list = listenerMap.get(pnaa);

            if (list != null) {
                for (AssertRetractListener assertRetractListener : list) {
                    assertRetractListener.clauseAsserted(this, clause);
                }
            }
        }
    }

    private void fireRetraction(DefiniteClause clause) {
        if (listenerMap != null) {
            PredicateNameAndArity pnaa = new PredicateNameAndArity(clause);

            List<AssertRetractListener> list = listenerMap.get(pnaa);

            if (list != null) {
                for (AssertRetractListener assertRetractListener : list) {
                    assertRetractListener.clauseRetracted(this, clause);
                }
            }
        }
    }

    public DefiniteClauseList getAssertions(PredicateNameAndArity predicateNameAndArity) {
        return getAssertions(predicateNameAndArity.getPredicateName(), predicateNameAndArity.getArity());
    }

//    public List<Clause> getBackgroundKnowledge(PredicateNameAndArity predicateNameAndArity) {
//        return getBackgroundKnowledge(predicateNameAndArity.getPredicateName(), predicateNameAndArity.getArity());
//    }
//    public List<Literal> getFacts(PredicateNameAndArity predicateNameAndArity) {
//        return getFacts(predicateNameAndArity.getPredicateName(), predicateNameAndArity.getArity());
//    }
    public boolean isDefined(PredicateNameAndArity pnaa) {

        if (getStringHandler().standardPredicateNames.buildinPredicates.contains(pnaa.getPredicateName())) {
            return true;
        }

        if (getUserProcedurallyDefinedPredicateHandler() != null && getUserProcedurallyDefinedPredicateHandler().canHandle(pnaa.getPredicateName(), pnaa.getArity())) {
            return true;
        }
        if (getBuiltinProcedurallyDefinedPredicateHandler() != null && getBuiltinProcedurallyDefinedPredicateHandler().canHandle(pnaa.getPredicateName(), pnaa.getArity())) {
            return true;
        }

        if (checkForPossibleMatchingAssertions(pnaa.getPredicateName(), pnaa.getArity())) {
            return true;
        }

        return false;
    }

    public class SpyAssertRetractListener implements AssertRetractListener {

        public void clauseAsserted(HornClausebase context, DefiniteClause clause) {
            if (clause.isDefiniteClauseFact()) {
                Literal fact = clause.getDefiniteClauseFactAsLiteral();
                if (fact.predicateName == context.getStringHandler().standardPredicateNames.spy && fact.getArity() == 1) {
                    try {
                        Term term = fact.getArgument(0);
                        Function function = (Function) term;
                        String predName = ((StringConstant) function.getArgument(0)).getBareName();
                        int predArity = ((NumericConstant) function.getArgument(1)).value.intValue();

                        getStringHandler().spyEntries.addLiteral(predName, predArity);
                    } catch (Exception e) {
                        Utils.warning("Encountered spy/1 statement.  Expected argument 1 to be function of form pred/arity.  Found: " + fact + ".");
                    }
                }
            }
        }

        public void clauseRetracted(HornClausebase context, DefiniteClause clause) {
            throw new UnsupportedOperationException("Not supported yet.");
        }
    }
}
