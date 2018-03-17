/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.FOPC.UserDefinedLiteralCache.CacheEntry;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import java.util.ArrayList;
import java.util.List;

import edu.wisc.cs.will.Utils.Utils;

/** A userDefinedLiteral wrapping a function as a literal.
 *
 * <p>This class implements a UserDefinedLiteral such that the literal is effectively
 * a function with N input arguments and 1 output argument.  The arity of the literal
 * will be N+1.</p>
 *
 * <p>So, the defined literal will be of the form:</p>
 *
 * <p>  litName(input1, ... inputX, output, inputX+1, ... inputN)</p>
 *
 * <p>representing the function:</p>
 *
 * <p>  output = linName(input1, ..., inputN).</p>
 *
 * <p>Subclasses only have to implement the evaluateMe(List&ltTerm&gt inputs, Term output) method
 * which returns the output value, or null if the function could not be evaluated.</p>
 *
 * <p>See {@link UserDefinedLiteral} for help in choosing the correct abstract class
 * to base your user defined literal on.  Most of the book-keeping and Will types
 * are already handled by these classes.
 * 
 * @author twalker and shavlik
 *
 */
public abstract class AbstractUserDefinedFunctionAsLiteral extends AbstractUserDefinedLiteral implements UserDefinedCacheResolver  {
	private int outputArgumentIndex = -1;
    private int inputArgumentCount = 0;
    private boolean evaluateMeChecksOutputArgumentUnification = true;

    /** Creates a new UserDefinedFunctionAsLiteral with arity inputArgumentCount+1 with the output argument at position indexOfOutputArgument of argument list.
     *
     * @param inputArgumentCount Number of input arguments. Arity of the literal will be inputArgumentCount+1.
     * @param indexOfOutputArgument Index of the output argument.
     * @param cachingEnabled If true, caching is enable.  Caching should only be enabled
     * on deterministic literals.
     */
	public AbstractUserDefinedFunctionAsLiteral(int inputArgumentCount, int indexOfOutputArgument, boolean cachingEnabled) {
        super(cachingEnabled);
		this.inputArgumentCount = inputArgumentCount;
        this.outputArgumentIndex = indexOfOutputArgument;
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
    @Override
	public BindingList handleUserDefinedLiteral(Literal caller, Unifier unifier, BindingList bindingList, HornClauseContext context) {
        // Have this user-defined predicate compute an answer.  If the answer is stored in one of the arguments (see locationOfAnswer),
        // then need to add this to bindingList (if a non-variable is in this position, then the answers need to match - if not, return null).
		List<Term> inputArguments = new ArrayList<Term>(getInputArgumentCount());
		Term   outputArgument = null;
		
		// Collect the input and (if any) output arguments, making sure that no input argument is an unbound variable.
        boolean unboundInputArguments = false;

		for (int i = 0; i < getInputArgumentCount()+1; i++) {
            if ( i != getIndexOfOutputArgument() ) {
                Term boundArgument = caller.getArgument(i).applyTheta(bindingList.theta);

                if ( boundArgument.isGrounded() == false ) {
                    unboundInputArguments = true;
                    break;
                }

                inputArguments.add(boundArgument);
            }
            else {
                outputArgument = caller.getArgument(i).applyTheta(bindingList.theta);
            }
		}

        if ( unboundInputArguments ) {
            String skipString = "Unbound input argument " + caller.predicateName.name + "/" + caller.numberArgs();
            Utils.warning("An unbound input argument existing in UserDefinedLiteral call: " + caller, skipString);
            return null;
        }

        boolean tryCache = isCachingEnabled();
        boolean timingEnabled = false;

        CacheEntry cacheEntry = null;

        long cacheStartTime = 0;
        long evaluationTime = 0;

        Term result = null;
        if ( tryCache ) {
            UserDefinedLiteralCache cache = context.getStringHandler().getUserDefinedLiteralCache();
            timingEnabled = cache.isCacheTimingEnabled();

            if ( timingEnabled ) {
                cacheStartTime = System.nanoTime();
            }

            PredicateNameAndArity predicateNameArity = new PredicateNameAndArity(caller.predicateName, caller.numberArgs());

            cacheEntry = cache.lookupCacheEntry(predicateNameArity, inputArguments, this);

            Object cachedValue = cacheEntry.getCachedValue();

            if ( cachedValue == UserDefinedLiteralCache.FAILURE_INDICATOR ) {
                if ( timingEnabled ) {
                    long lookupTime = (System.nanoTime() - cacheStartTime) - evaluationTime;
                    cacheEntry.recordLookupTime(lookupTime);
                }

                return null;
            }
            result = (Term)cachedValue;
        }

        if ( result == null ) {
            long evaluationStartTime = 0;
            if ( timingEnabled ) {
                evaluationStartTime = System.nanoTime();
            }

            // Didn't find a result in the cache...
            result = evaluateMe(inputArguments, outputArgument, context, unifier);

            if ( timingEnabled ) {
                evaluationTime = System.nanoTime() - evaluationStartTime;
                cacheEntry.recordEvaluationTime(evaluationTime);
            }

            // Cache the value
            if ( tryCache ) {
                cacheEntry.setCachedValue(result);
            }
        }

        if ( timingEnabled ) {
            long lookupTime = (System.nanoTime() - cacheStartTime) - evaluationTime;
            cacheEntry.recordLookupTime(lookupTime);
        }

        BindingList newBindingList = null;
        if ( result != null ) {
            // We have a non-null result...check to make sure it is legal...
            // And unify the result with the output argument to generate the
            // new binding list.
            newBindingList = unifier.unify(result, outputArgument, bindingList);

            if ( newBindingList == null ) {
                if ( evaluateMeChecksOutputArgumentUnification ) {
                    Utils.warning("Error in UserDefinedFunctionAsLiteral for " + caller.predicateName + "/" + getArity() + ": Result of evaluateMe and original output term did not unify.  Returning fail.");
                }
                //Utils.waitHere("Error in UserDefinedFunctionAsLiteral for " + caller + ": Result of evaluateMe (" + result + ") and original output term (" + outputArgument + ") did not unify.  Returning fail.");
                result = null;
            }
        }

        if ( newBindingList != null && Boolean.getBoolean("edu.wisc.cs.will.fopc.recordUserDefinedLiteralEvaluations")) {
            Literal resolvedQuery = caller.applyTheta(newBindingList);
            Literal assertIfUnknown = context.getStringHandler().getLiteral("assertifunknown", resolvedQuery.asTerm());
            context.prove(assertIfUnknown);
        }

		return newBindingList;
	}

    public Literal resolveCacheEntry(PredicateNameAndArity predicateNameAndArity, List<Term> inputTerms, Object cachedValue) {

        Literal result = null;
        
        if ( UserDefinedLiteralCache.FAILURE_INDICATOR != cachedValue && cachedValue instanceof Term ) {

            Term outputArgument =  (Term) cachedValue;

            List<Term> allTerms = new ArrayList<Term>();
            int inputTermIndex = 0;
            for (int i = 0; i < predicateNameAndArity.getArity(); i++) {
                if ( i == outputArgumentIndex ) {
                    allTerms.add(outputArgument);
                }
                else {
                    allTerms.add(inputTerms.get(inputTermIndex++));
                }
            }

            result = outputArgument.getStringHandler().getLiteral(predicateNameAndArity.getPredicateName(), allTerms);
        }

        return result;
    }

	/** Evaluates this literal given these input arguments.
     *
     * <p>The output argument, as passed in to the literal, may
     * be a variable or may be set to some value.  The evaluateMe() should check if this
     * is a variable or not and act appropriately.  I.e. If it is a variable, simply
     * calculating the value of output is sufficient.  If it is not a variable, the
     * method should also check to make sure the calculated value, based on the input
     * terms, is semantically equivalent to the output variable.  For most calculations,
     * this can be done via simply unification. However, for some calculations, say
     * equalWithTolerance, it is sufficient that a non-variable outputArgument
     * only be close to the calculated value.</p>
     *
     * <p>The return value should either be null, if the evaluation FAILS, or should
     * be the result of calculating the function.  If evaluation succeeds, the return
     * value should always unify with @param outputArgument.</p>
     *
     * @param inputArguments List of terms indicating the input arguments.  This is
     * the set of complete set of arguments for the literal, except for the output term
     * argument.  The inputArguments may contain variables.
     *
     * @param context
     * @param unifier The unifier to use if evaluateMe needs to perform unification.
     *
     * @param outputArgument The output argument, as passed in to the literal.  This may
     * or may not be a variable.
     * 
     * @return The result of the calculation.  If outputArgument is not a variable,
     * the return value should unify with the outputArgument (otherwise a warning will
     * be posted and we will return fail for the user defined literal).
     */
	protected abstract Term evaluateMe(List<Term> inputArguments, Term outputArgument, HornClauseContext context, Unifier unifier);

	
    /**
     * @return the arity
     */
    @Override
    public int getArity() {
        return getInputArgumentCount()+1;
    }

    /**
     * @return the indexOfOutputArgument
     */
    public int getIndexOfOutputArgument() {
        return outputArgumentIndex;
    }

    /**
     * @param indexOfOutputArgument the indexOfOutputArgument to set
     */
    public void setIndexOfOutputArgument(int indexOfOutputArgument) {
        this.outputArgumentIndex = indexOfOutputArgument;
    }

    /**
     * @return the inputArgumentCount
     */
    public int getInputArgumentCount() {
        return inputArgumentCount;
    }

    /**
     * @param inputArgumentCount the inputArgumentCount to set
     */
    public void setInputArgumentCount(int inputArgumentCount) {
        this.inputArgumentCount = inputArgumentCount;
    }

    public boolean isEvaluateMeChecksOutputArgumentUnification() {
        return evaluateMeChecksOutputArgumentUnification;
    }

    /** Sets the EvaluateMeChecksOutputArgumentUnification value.
     *
     * If evaluateMeChecksOutputArgumentUnification is set to true, it is
     * assumed that evaluateMe performs a unification between the original
     * output argument and the calculated function result, failing if
     * the calculated result doesn't unify with the original output argument.
     * <P>
     * The handleUserDefinedLiteral method also performs this unification
     * based on the return value of evaluateMe.   If the unification fails,
     * an error is reported and the correct, failing, result is returned
     * from the user literal.
     * <P>
     * If evaluateMeChecksOutputArgumentUnification is set to false, the
     * evaluateMe method can ignore the output argument and does not have to
     * worry about verifying the unification.  handleUserDefinedLiteral will
     * perform the unification and return value if there is a mismatch.
     * However, no error is reported in fail case.
     *
     * @param evaluateMeChecksOutputArgumentUnification
     */
    public void setEvaluateMeChecksOutputArgumentUnification(boolean evaluateMeChecksOutputArgumentUnification) {
        this.evaluateMeChecksOutputArgumentUnification = evaluateMeChecksOutputArgumentUnification;
    }

   


}
