/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ResThmProver;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;

/** This is an index of definite clauses (either Clauses or Literal or a mix of both) indexed on the predicateName and arity.
 *
 * @param <T> Type of object to be indexed.
 *
 * @author twalker
 */
public class PredicateIndex<T extends DefiniteClause> {

    private Map<PredicateNameAndArity, List<T>> definiteClausesByPredicateIndex = new HashMap<PredicateNameAndArity, List<T>>();

    public void indexDefiniteClause(PredicateNameAndArity key, T definiteClause) {

        List<T> definiteClausesForKey = definiteClausesByPredicateIndex.get(key);
        if (definiteClausesForKey == null) {
            definiteClausesForKey = new ArrayList<T>();
            definiteClausesByPredicateIndex.put(key, definiteClausesForKey);
        }

        definiteClausesForKey.add(definiteClause);

    }

    public void removeDefiniteClause(PredicateNameAndArity key, T definiteClause) {

        List<T> definiteClausesForKey = definiteClausesByPredicateIndex.get(key);
        if (definiteClausesForKey != null) {
            definiteClausesForKey.remove(definiteClause);

            if ( definiteClausesForKey.isEmpty()) {
                definiteClausesByPredicateIndex.remove(key);
            }
        }

    }

    public List<T> lookupDefiniteClause(PredicateName predicateName, int arity) {
            PredicateNameAndArity key = new PredicateNameAndArity(predicateName, arity);

            List<T> definiteClauseList = definiteClausesByPredicateIndex.get(key);

            return definiteClauseList;
    }

    public List<T> lookupDefiniteClause(PredicateNameAndArity key) {
        if (key != null) {
            List<T> definiteClauseList = definiteClausesByPredicateIndex.get(key);

            return definiteClauseList;
        }

        return null;
    }

    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer();

        for (Map.Entry<PredicateNameAndArity, List<T>> entry : definiteClausesByPredicateIndex.entrySet()) {
            sb.append("  ").append(entry.getKey()).append(":\n");
            for (T definiteClause : entry.getValue()) {
                sb.append("    ").append(definiteClause).append(".\n");
            }
            sb.append("\n");
        }

        return sb.toString();
    }


}
