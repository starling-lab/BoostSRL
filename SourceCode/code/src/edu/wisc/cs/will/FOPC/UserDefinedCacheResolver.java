/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC;

import java.util.List;

/**
 *
 * @author twalker
 */
public interface UserDefinedCacheResolver {
    public Literal resolveCacheEntry(PredicateNameAndArity predicateNameAndArity, List<Term> inputTerms, Object cachedValue);
}
