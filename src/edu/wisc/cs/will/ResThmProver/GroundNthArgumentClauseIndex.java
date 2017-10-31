/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ResThmProver;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.Term;

/** This is an index of definite clauses (either Clauses or Literal or a mix of both) with ground Nth arguments in the head.
 *
 * @param <T> Type of object to be indexed.  This is either a Sentence, Clause, or Literal.
 * Specifying other types has an undefined result.
 *
 * @author twalker
 */
public class GroundNthArgumentClauseIndex<T extends DefiniteClause> {

    /** Index of clauses which might match a constant arg N.
     *
     */
    private Map<PredicateNameAndArity, Map<Term, List<T>>> definiteClausesByArgNIndex = new HashMap<PredicateNameAndArity, Map<Term, List<T>>>();

    /** Store clauses in which the Nth arg is not ground.
     *
     * This is used to as a starting place for new definiteClause lists indexed by the
     * Nth args.  This is necessary to make sure unseen
     */
    private Map<PredicateNameAndArity, List<T>> definiteClausesWithUngroundNthArg = new HashMap<PredicateNameAndArity, List<T>>();

    private int indexedArgument;
    private int minimumClauseLengthToIndex;

    public GroundNthArgumentClauseIndex(int indexedArgument) {
        setIndexedArgument(indexedArgument);
    }

    public void indexDefiniteClause(PredicateNameAndArity key, T definiteClause) {
        
        Literal literal = definiteClause.getDefiniteClauseHead();

        if (literal.numberArgs() >= minimumClauseLengthToIndex ) {
            if (definiteClausesByArgNIndex == null) {
                definiteClausesByArgNIndex = new HashMap<PredicateNameAndArity, Map<Term, List<T>>>();
            }

            Map<Term, List<T>> mapForKey = definiteClausesByArgNIndex.get(key);
            if (mapForKey == null) {
                mapForKey = new HashMap<Term, List<T>>();
                definiteClausesByArgNIndex.put(key, mapForKey);
            }

            Term key2 = literal.getArgument(indexedArgument);

            if ( key2.isGrounded() ) {

                List<T> definiteClauseList = mapForKey.get(key2);

                if (definiteClauseList == null) {
                    definiteClauseList = new LinkedList<T>(getDefiniteClauseByNthArgSeedList(key));
                    mapForKey.put(key2, definiteClauseList);
                }

                definiteClauseList.add(definiteClause);
            }
            else {
                for (List<T> list : mapForKey.values()) {
                    list.add(definiteClause);
                }

                addDefiniteClauseByNthArgSeedSentence(key, definiteClause);
            }
        }
    }

    public void removeDefiniteClause(PredicateNameAndArity key, T definiteClause) {
        Literal literal = definiteClause.getDefiniteClauseHead();

        if (literal.numberArgs() >= minimumClauseLengthToIndex) {
            if (definiteClausesByArgNIndex != null) {

                Map<Term, List<T>> mapForKey = definiteClausesByArgNIndex.get(key);
                if (mapForKey != null) {

                    Term key2 = literal.getArgument(indexedArgument);

                    if (key2.isGrounded()) {

                        List<T> definiteClauseList = mapForKey.get(key2);

                        if (definiteClauseList != null) {
                            definiteClauseList.remove(definiteClause);
                        }
                    }
                    else {
                        // If key2 isn't grounded, we have a problem.  We have to add
                        // this definiteClause to every single index entry currently existing.
                        // We also must add it to a list of unground Nth arg clauses
                        // that will later be used as a seed for unseed ground Nth args.
                        for (List<T> list : mapForKey.values()) {
                            list.remove(definiteClause);
                        }

                        removeDefiniteClauseByNthArgSeedSentence(key, definiteClause);
                    }
                }
            }
        }
    }

    private List<T> getDefiniteClauseByNthArgSeedList(PredicateNameAndArity key) {

        List<T> definiteClausesForKey = definiteClausesWithUngroundNthArg.get(key);
        if ( definiteClausesForKey != null ) {
            return definiteClausesForKey;
        }
        else {
            List<T> emptyList = Collections.emptyList();
            return emptyList;
        }
    }

    private void addDefiniteClauseByNthArgSeedSentence(PredicateNameAndArity key, T definiteClause) {
        List<T> definiteClausesForKey = definiteClausesWithUngroundNthArg.get(key);

        if ( definiteClausesForKey == null ) {
            definiteClausesForKey = new ArrayList<T>();
            definiteClausesWithUngroundNthArg.put(key, definiteClausesForKey);
        }

        definiteClausesForKey.add(definiteClause);
    }

    private void removeDefiniteClauseByNthArgSeedSentence(PredicateNameAndArity key, T definiteClause) {
        List<T> definiteClausesForKey = definiteClausesWithUngroundNthArg.get(key);

        if ( definiteClausesForKey != null ) {
            definiteClausesForKey.remove(definiteClause);

            if ( definiteClausesForKey.isEmpty() ) {
                definiteClausesWithUngroundNthArg.remove(key);
            }
        }
    }

    /** Return a list of possible matches for <code>literalToLookup</code> based upon the Nth argument.
     *
     * @param literalToLookup Literal to look for possible matches of.
     * @return List of all possible matches to <code>literalToLookup</code>'s nth argument currently in the fact base.
     * This method can return null if the index doesn't contain a complete list of the possible matches.  This happen,
     * for example, if the Nth argument of literalToLookup is unground.
     */
    public List<T> lookupDefiniteClauses(Literal literalToLookup) {
        if (definiteClausesByArgNIndex != null && literalToLookup != null && literalToLookup.numberArgs() >= minimumClauseLengthToIndex && literalToLookup.getArgument(indexedArgument).isGrounded()) {
            PredicateNameAndArity key = new PredicateNameAndArity(literalToLookup.predicateName, literalToLookup.numberArgs());

            Map<Term, List<T>> mapForKey = definiteClausesByArgNIndex.get(key);

            if (mapForKey != null) {
                List<T> definiteClauseList = mapForKey.get(literalToLookup.getArgument(indexedArgument));

                // If we got this far, than we know that the predicate/arity does have entries.
                // So, if definiteClauseList is null, then there must be no completions and we
                // should return an empty list.
                if (definiteClauseList == null) {
                    return getDefiniteClauseByNthArgSeedList(key);
                } else {
                    return definiteClauseList;
                }
            }
        }

        return null;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        for (Map.Entry<PredicateNameAndArity, Map<Term, List<T>>> entry : definiteClausesByArgNIndex.entrySet()) {
            sb.append("  ").append(entry.getKey()).append(":\n");
            for (Map.Entry<Term, List<T>> entry1 : entry.getValue().entrySet()) {
                sb.append("    ").append(entry1.getKey()).append(":\n");

                for (T definiteClause : entry1.getValue()) {
                    sb.append("      ").append(definiteClause).append(".\n");
                }
            }
            sb.append("\n");
        }

        return sb.toString();
    }

    /**
     * @param indexedArgument the indexedArgument to set
     */
    private void setIndexedArgument(int indexedArgument) {
        this.indexedArgument = indexedArgument;
        this.minimumClauseLengthToIndex = Math.max(2, indexedArgument+1);
    }
}
