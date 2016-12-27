/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.Term;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/** This is an index of definite clauses (either Clauses or Literal or a mix of both) with ground heads.
 *
 * @param <T> Type of object to be indexed.
 *
 * @author twalker
 */
public class GroundClauseIndex<T extends DefiniteClause> {

    private Map<PredicateNameAndArity, Map<List<Term>, List<T>>> definiteClausesAllArgsIndex = new HashMap<PredicateNameAndArity, Map<List<Term>, List<T>>>();

    /** Store clauses in which one or more of the args is not ground.
     *
     * This is used to as a starting place for new definiteClause lists indexed by the
     * all args.  This is necessary to make sure unseen term combinations
     * start with the unground clauses in their index.
     */
    private Map<PredicateNameAndArity, List<T>> definiteClausesWithUngroundArgs = new HashMap<PredicateNameAndArity, List<T>>();

    public void indexDefiniteClause(PredicateNameAndArity key, T definiteClause) {
        Literal headLiteral = definiteClause.getDefiniteClauseHead();


        if (definiteClausesAllArgsIndex == null) {
            definiteClausesAllArgsIndex = new HashMap<PredicateNameAndArity, Map<List<Term>, List<T>>>();
        }

        Map<List<Term>, List<T>> mapForKey = definiteClausesAllArgsIndex.get(key);
        if (mapForKey == null) {
            mapForKey = new HashMap<List<Term>, List<T>>();
            definiteClausesAllArgsIndex.put(key, mapForKey);
        }

        if (headLiteral.isGrounded()) {
            List<T> definiteClauseList = mapForKey.get(headLiteral.getArguments());

            if (definiteClauseList == null) {
                definiteClauseList = new ArrayList<T>(getDefiniteClausesSeedList(key));
                mapForKey.put(headLiteral.getArguments(), definiteClauseList);
            }

            definiteClauseList.add(definiteClause);
        }
        else {
            // This is an non-ground literal, so we just need to throw into all of the appropriate
            // places was well as the seed list.
            for (List<T> list : mapForKey.values()) {
                list.add(definiteClause);
            }

            addDefiniteClausesSeedDefiniteClause(key, definiteClause);
        }


    }

    public void removeDefiniteClause(PredicateNameAndArity key, T definiteClause) {
        Literal headLiteral = definiteClause.getDefiniteClauseHead();

        if (definiteClausesAllArgsIndex != null) {
            Map<List<Term>, List<T>> mapForKey = definiteClausesAllArgsIndex.get(key);
            if (mapForKey != null) {

                if (headLiteral.isGrounded()) {
                    List<T> definiteClauseList = mapForKey.get(headLiteral.getArguments());

                    if (definiteClauseList != null) {
                        definiteClauseList.remove(definiteClause);
                    }
                }
                else {
                    // This is an non-ground literal, so we just need to throw into all of the appropriate
                    // places was well as the seed list.
                    for (List<T> list : mapForKey.values()) {
                        list.remove(definiteClause);
                    }

                    removeDefiniteClausesSeedDefiniteClause(key, definiteClause);
                }
            }
        }
    }

    public List<T> lookupDefiniteClauses(Literal lookupLiteral) {
        if (definiteClausesAllArgsIndex != null && lookupLiteral != null && lookupLiteral.isGrounded()) {
            PredicateNameAndArity key = lookupLiteral.getPredicateNameAndArity();
            Map<List<Term>, List<T>> mapForKey = definiteClausesAllArgsIndex.get(key);

            if (mapForKey != null) {
                List<T> definiteClauseList = mapForKey.get(lookupLiteral.getArguments());

                // If we got this far, than we know that the predicate/arity does have entries.
                // So, if definiteClauseList is null, then there must be no completions and we
                // should return an empty list.
                if (definiteClauseList == null) {
                    return getDefiniteClausesSeedList(key);
                }
                else {
                    return definiteClauseList;
                }
            }
        }

        return null;
    }

    private List<T> getDefiniteClausesSeedList(PredicateNameAndArity key) {

        List<T> definiteClausesForKey = definiteClausesWithUngroundArgs.get(key);
        if (definiteClausesForKey != null) {
            return definiteClausesForKey;
        }
        else {
            List<T> emptyList = Collections.emptyList();
            return emptyList;
        }
    }

    private void addDefiniteClausesSeedDefiniteClause(PredicateNameAndArity key, T definiteClause) {
        List<T> definiteClausesForKey = definiteClausesWithUngroundArgs.get(key);

        if (definiteClausesForKey == null) {
            definiteClausesForKey = new ArrayList<T>();
            definiteClausesWithUngroundArgs.put(key, definiteClausesForKey);
        }

        definiteClausesForKey.add(definiteClause);
    }

    private void removeDefiniteClausesSeedDefiniteClause(PredicateNameAndArity key, T definiteClause) {
        List<T> definiteClausesForKey = definiteClausesWithUngroundArgs.get(key);

        if (definiteClausesForKey != null) {
            definiteClausesForKey.remove(definiteClause);

            if ( definiteClausesForKey.isEmpty() ) {
                definiteClausesWithUngroundArgs.remove(key);
            }
        }
    }

    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer();

        for (Map.Entry<PredicateNameAndArity, Map<List<Term>, List<T>>> entry : definiteClausesAllArgsIndex.entrySet()) {


            sb.append("  ").append(entry.getKey()).append(":\n");
            for (Map.Entry<List<Term>, List<T>> entry1 : entry.getValue().entrySet()) {
                sb.append("    ").append(entry1.getKey()).append(":\n");

                for (DefiniteClause definiteClause : entry1.getValue()) {
                    sb.append("      ").append(definiteClause).append(".\n");
                }
            }
            sb.append("\n");
        }

        return sb.toString();
    }
}
