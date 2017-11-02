/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC;


/** Abstract class for User defined literal.
 *
 * <p>This class provides some basic functionality for User Defined Literals, including
 * caching of answers.</p>
 *
 * <p>Generally users should not subclass this directly.  Instead they should subclass
 * on of the subclass based on their needs.</p>
 *
* <p>See {@link UserDefinedLiteral} for help in choosing the correct abstract class
 * to base your user defined literal on.  Must of the book-keeping and Will types
 * are already handled by these classes.
 *
 */
public abstract class AbstractUserDefinedLiteral implements UserDefinedLiteral {

    

    /** Indicates that the UserDefinedLiteral values may be cached.
     * 
     */
    private boolean cachingEnabled = false;

    /** Constructor for AbstractUserDefinedLiteral.
     *
     * @param cachingEnabled Sets cachingEnabled.  Caching should only be used
     * when the literal is deterministic.
     */
    public AbstractUserDefinedLiteral(boolean cachingEnabled) {
        setCachingEnabled(cachingEnabled);
    }

//    /** If caching is enabled, this will cache the resulting value, assuming terms is ground.
//     *
//     * Note, this is a flexible caching mechanism so the UserDefinedLiteral can determine
//     * how it wants to use it based upon the specific implementation of the user defined literal.
//     * The only requirement is that for any fixed set of terms, the cached value is always the
//     * same.
//     * <p>
//     * Note, the list of terms does not need to match the arity of the literal being evaluated.
//     * However, if a reduction of the number of terms is performed (say by ignoring Variable
//     * terms), it should be a 1-to-1 mapping of the original terms to the new term list.  Just
//     * removing all non-ground terms generally will not result in a 1-to-1 mapping.
//     * <p>
//     * If you wish to cache a failed evaluation result, pass null or UserDefinedLiteralCache.FAILURE_INDICATOR for value.
//     *
//     * @param predicateNameArity Predicate name and arity to lookup.
//     * @param terms List of terms to cache on. Length of list must be the same as the
//     * arity of the predicate.
//     *
//     * @param value Value to cache, null or UserDefinedLiteralCache.FAILURE_INDICATOR if the evaluation of the literal for terms failed.
//     */
//    protected void cache(PredicateNameArity predicateNameArity, List<Term> terms, Object value) {
//
//    }

//    /** Returns the cached value.
//     *
//     * If caching is enabled, this will lookup the cached value for terms.
//     *
//     * Note, this is a flexible caching mechanism so the UserDefinedLiteral can determine
//     * how it wants to use it based upon the specific implementation of the user defined literal.
//     * The only requirement is that for any fixed set of terms, the cached value is always the
//     * same.
//     * <p>
//     * Note, the list of terms does not need to match the arity of the literal being evaluated.
//     * However, if a reduction of the number of terms is performed (say by ignoring Variable
//     * terms), it should be a 1-to-1 mapping of the original terms to the new term list.  Just
//     * removing all non-ground terms generally will not result in a 1-to-1 mapping.
//     *
//     * @param predicateNameArity Predicate name and arity to lookup.
//     * @param terms List of terms to lookup value for.
//     *
//     * @return Either a value, UserDefinedLiteralCache.FAILURE_INDICATOR, or null.  If the lookup is successful, the value
//     * of the literal for terms will be returned, with a return value of
//     * UserDefinedLiteralCache.FAILURE_INDICATOR indicating that the evaulation of the literal previously
//     * failed.  If the lookup is unsuccessful (ie the value for terms isn't currently
//     * cached) then null is returned.
//     */
//    protected Object lookup(PredicateNameArity predicateNameArity, List<Term> terms) {
//        return null;
//    }

    /**
     * @return the cachingEnabled
     */
    public boolean isCachingEnabled() {
        return cachingEnabled;
    }

    /** Enables caching of the results of evaluating the literal.
     *
     * Caching should only be enabled on deterministic user defined literals.
     *
     * @param cachingEnabled the cachingEnabled to set
     */
    public void setCachingEnabled(boolean cachingEnabled) {
        if (this.cachingEnabled != cachingEnabled) {

            this.cachingEnabled = cachingEnabled;

//            if ( this.cachingEnabled ) {
//                createCache();
//            }
//            else {
//                destroyCache();
//            }
        }
    }

//    /** Creates the actual cache.
//     *
//     * This method should create the cacheMap map.  Subclasses could override
//     * this method, along with lookup, cache, and destroyCache if they want
//     * specialized caching.
//     *
//     * This is only called when cachingEnabled switches from false to true.
//     */
//    protected void createCache() {
//
//    }
//
//    /** Destorys the actual cache.
//     *
//     * This method should destroy the cacheMap map and clean up any cached memory.
//     * Subclasses could override this method, along with lookup, cache, and
//     * destroyCache if they want specialized caching.
//     */
//    protected void destroyCache() {
//
//    }

}
