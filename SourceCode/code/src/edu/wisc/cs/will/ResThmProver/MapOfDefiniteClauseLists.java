/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.Utils.MapOfLists;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

/**
 *
 * @author twalker
 */
public class MapOfDefiniteClauseLists extends MapOfLists<PredicateNameAndArity, DefiniteClause> implements Iterable<DefiniteClause> {

    @Override
    protected List<DefiniteClause> createValueList() {
        return new DefiniteClauseList();
    }

    @Override
    public DefiniteClauseList getValues(PredicateNameAndArity key) {
        return (DefiniteClauseList) super.getValues(key);
    }
//
//    @Override
//    protected Map<PredicateNameAndArity, List<DefiniteClause>> createMap() {
//        return new DebuggingHashMap(16, "DefiniteClauseList", 1);
//    }
    
    

    
}
