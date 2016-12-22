/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.FOPC.UserDefinedLiteralCache.CacheEntry;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import java.util.ArrayList;
import java.util.List;

import edu.wisc.cs.will.Utils.Utils;

/** A userDefinedLiteral wrapping a traditional logical evaluation.
 *
 * <p>This class implements a UserDefinedLiteral such that the literal is
 * either true or false.  Arguments may be used as input, output, or both.
 *
 * <p>Subclasses only have to implement the evaluateMe(List<Term> arguments) method
 * which returns a binding list if the literal is true, or null if the literal is false
 * not be evaluated.</p>
 *
 * <p>See {@link UserDefinedLiteral} for help in choosing the correct abstract class
 * to base your user defined literal on.  Most of the book-keeping and Will types
 * are already handled by these classes.
 * 
 * @author shavlik
 *
 */
public abstract class AbstractUserDefinedBooleanLiteral extends AbstractUserDefinedLiteral {

    private int arity = 0;

    /** Creates a new AbstractUserDefinedBooleanLiteral with arity <code>arity</code>.
     *
     * @param arity Arity of the literal.
     * @param cachingEnabled If true, caching is enable.  Caching should only be enabled
     * on deterministic literals.
     */
    public AbstractUserDefinedBooleanLiteral(int arity, boolean cachingEnabled) {
        super(cachingEnabled);
        this.arity = arity;
    }

    /** Evaluates the User defined literal by wrapping the value return from evaluateMe().
     *
     * <p>Subclasses should implement evaluateMe(), not handleUserDefinedLiteral().  If you need
     * to change the functionality of handleUserDefinedLiteral(), you should probably be
     * subclassing AbstractUserDefinedLiteral directly.</p>
     *
     * @param caller Literal to be evaluated.  This literal is guaranteed to be
     * of the arity indicated by getArity() method.
     *
     * @param unifier The unifier to use if additional unification is necessary to
     * handle the evaluation of the predicate.
     *
     * @param bindingList Current bindings of variables in <code>called</code>.  The bindingList may
     * be null if no bindings are present.  If the bindingList is non-null, the return value should
     * add binding and return it.
     * 
     * @return If the user defined literal evaluates to true, the bindingList is returned.  If false,
     * null is returned.
     */
    @SuppressWarnings("unchecked")
    public BindingList handleUserDefinedLiteral(Literal caller, Unifier unifier, BindingList bindingList, HornClauseContext context) {

        Utils.waitHere("UserDefinedBooleanLiterals have not been tested thoroughly.  Use with caution.");
        // Arguments to pass to evaluateMe.
        List<Term> arguments = new ArrayList<Term>(getArity());

        boolean unboundInputArguments = false;

        // Collect the arguments, applying the bindings if necessary...
        for (int i = 0; i < getArity(); i++) {
            Term t = caller.getArgument(i).applyTheta(bindingList.theta);
            if (t.isGrounded() == false) {
                unboundInputArguments = true;
                break;
            }
            arguments.add(t);
        }

        if (unboundInputArguments) {
            Utils.warning("An unbound input argument existing in UserDefinedLiteral call: " + caller);
            return null;
        }

        BindingList newBindingList = null;
        PredicateNameAndArity predicateNameArity = null;

        boolean tryCache = isCachingEnabled();
        boolean timingEnabled = false;

        CacheEntry cacheEntry = null;

        long cacheStartTime = 0;
        long evaluationTime = 0;

        List<Term> result = null;

        if (tryCache) {
            UserDefinedLiteralCache cache = context.getStringHandler().getUserDefinedLiteralCache();
            timingEnabled = cache.isCacheTimingEnabled();

            if (timingEnabled) {
                cacheStartTime = System.nanoTime();
            }

            predicateNameArity = new PredicateNameAndArity(caller.predicateName, caller.numberArgs());

            cacheEntry = cache.lookupCacheEntry(predicateNameArity, arguments, null);

            Object cachedValue = cacheEntry.getCachedValue();

            if (cachedValue == UserDefinedLiteralCache.FAILURE_INDICATOR) {
                if (timingEnabled) {
                    long lookupTime = (System.nanoTime() - cacheStartTime) - evaluationTime;
                    cacheEntry.recordLookupTime(lookupTime);
                }

                return null;
            }
            result = (List<Term>) cachedValue;

            if (result != null) {
                // We have a non-null cache result...check to make sure it is legal...
                // And unify the result terms with arguments to generate the
                // new binding list.
                newBindingList = bindingList;

                for (int i = 0; i < arguments.size(); i++) {
                    // Unify each of the resulting terms.
                    newBindingList = unifier.unify(arguments.get(i), result.get(i), newBindingList);
                    if (newBindingList == null) {
                        break;
                    }
                }

                if (newBindingList == null) {
                    // The unification of the arguments did not match the cached value.
                    // This should not happen!
                    Utils.warning("Error in UserDefinedBooleanLiteral for " + caller.predicateName + "/" + getArity() + ": Cached results of evaluateMe and original arguments did not unify.  Failing.");
                }
            }
        }

        if ( newBindingList == null ) {
            long evaluationStartTime = 0;
            if (timingEnabled) {
                evaluationStartTime = System.nanoTime();
            }

            // Didn't find a result in the cache...
            // So calculate it...
            newBindingList = evaluateMe(arguments, unifier, bindingList == null ? new BindingList() : bindingList);

            if (timingEnabled) {
                evaluationTime = System.nanoTime() - evaluationStartTime;
                cacheEntry.recordEvaluationTime(evaluationTime);
            }

            if (tryCache) {
                if (newBindingList != null) {
                    List<Term> cacheValue = new ArrayList<Term>(getArity());
                    // Caching is enabled, so apply the binding list to the arguments
                    // and cache the result...
                    for (int i = 0; i < getArity(); i++) {
                        // Unify each of the resulting terms.
                        cacheValue.set(i, arguments.get(i).applyTheta(newBindingList.theta));
                    }

                    cacheEntry.setCachedValue(cacheValue);
                }
                else {
                    // Binding list was null, so something went wrong.  Cache a failure.
                    cacheEntry.setCachedValue(UserDefinedLiteralCache.FAILURE_INDICATOR);
                }


            }
        }

        if ( timingEnabled ) {
            long lookupTime = (System.nanoTime() - cacheStartTime) - evaluationTime;
            cacheEntry.recordLookupTime(lookupTime);
        }

        return newBindingList;
    }

    /** Evaluates this literal given these arguments.
     *
     * <p>evaluateMe should determine the truth value of the literal.  If the truth
     * value is false, it should return null.  Otherwise, it should return a
     * a binding list containing additional variable bindings performed by the literal.
     * The new binding list should be based on bindingList.  If no changes are made
     * to the bindings of variables, bindingList can be returned unmodified.</p>
     *
     * @param arguments List of terms indicating the original arguments to the literal.
     * The arguments are may not be ground.  This list can be modified as desired.
     *
     * @param unifier The unifier to use if evaluateMe needs to perform unification.
     * 
     * @param bindingList Current binding list, non-null.  This binding list should 
     * be extended (if you change the bindings) and returned if the literal evalutes
     * to true.
     * 
     * @return If literal evaluates to true, the binding list containing any newly
     * bound variables (or bindingList if nothing change).  If literal evaluates to
     * false/fail, this returns null.
     */
    protected abstract BindingList evaluateMe(List<Term> arguments, Unifier unifier, BindingList bindingList);

    /**
     * @return the arity
     */
    public int getArity() {
        return arity;
    }
}
