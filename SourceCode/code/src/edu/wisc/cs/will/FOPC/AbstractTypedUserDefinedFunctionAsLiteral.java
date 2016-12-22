/**
 * 
 */
package edu.wisc.cs.will.FOPC;


import edu.wisc.cs.will.ResThmProver.HornClauseContext;

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
 * <p>Subclasses only have to implement the evaluateMe(List&ltObject&gt inputs, Object output) method
 * which returns the output value, or null if the function could not be evaluated.</p>
 *
 * <p>See {@link UserDefinedLiteral} for help in choosing the correct abstract class
 * to base your user defined literal on.  Most of the book-keeping and Will types
 * are already handled by these classes.
 * 
 * @author twalker and shavlik
 *
 */
public abstract class AbstractTypedUserDefinedFunctionAsLiteral extends AbstractTypedUserDefinedLiteral {

    private int indexOfOutputArgument = -1;

    @SuppressWarnings("unchecked")
    private Class[] inputArgumentTypes = null;

    @SuppressWarnings("unchecked")
    private Class outputArgumentType = null;

    /** Creates a new UserDefinedFunctionAsLiteral with arity |inputArgumentTypes|+1 with the output argument of type outputArgumentType at position indexOfOutputArgument of argument list.
     *
     * @param inputArgumentTypes Array contain the types of the input arguments.
     * @param outputArgumentType The type of the output argument.
     * @param indexOfOutputArgument Index of the output argument in the full array list.
     * @param cachingEnabled If true, caching is enable.  Caching should only be enabled
     * on deterministic literals.
     * @throws IllegalArgumentException An IllegalArgumentException is thrown if any of the types
     * specified in inputArgumentTypes does not have a typeConverter.
     */
    @SuppressWarnings("unchecked")
    public AbstractTypedUserDefinedFunctionAsLiteral(Class[] inputArgumentTypes, Class outputArgumentType, int indexOfOutputArgument, boolean cachingEnabled) throws IllegalArgumentException {
        this(inputArgumentTypes, outputArgumentType, indexOfOutputArgument, null, cachingEnabled);
    }

    /** Creates a new UserDefinedFunctionAsLiteral with arity |inputArgumentTypes|+1 with the output argument of type outputArgumentType at position indexOfOutputArgument of argument list.
     *
     * @param inputArgumentTypes Array contain the types of the input arguments.
     * @param outputArgumentType The type of the output argument.
     * @param indexOfOutputArgument Index of the output argument in the full array list.
     * @param additionalConverters Additional type converters.
     * @param cachingEnabled If true, caching is enable.  Caching should only be enabled
     * on deterministic literals.
     * @throws IllegalArgumentException An IllegalArgumentException is thrown if any of the types
     * specified in inputArgumentTypes does not have a typeConverter.
     */
    @SuppressWarnings("unchecked")
    public AbstractTypedUserDefinedFunctionAsLiteral(Class[] inputArgumentTypes, Class outputArgumentType, int indexOfOutputArgument, TermToJavaTypeConverter[] additionalConverters, boolean cachingEnabled) throws IllegalArgumentException {
        super(additionalConverters, cachingEnabled);

        this.inputArgumentTypes = inputArgumentTypes;
        this.outputArgumentType = outputArgumentType;
        this.indexOfOutputArgument = indexOfOutputArgument;

        checkTypes(inputArgumentTypes);
        checkTypes(outputArgumentType);
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
//        // Have this user-defined predicate compute an answer.  If the answer is stored in one of the arguments (see locationOfAnswer),
//        // then need to add this to bindingList (if a non-variable is in this position, then the answers need to match - if not, return null).
//        List<Term> inputArguments = new ArrayList<Term>(getInputArgumentCount());
//        Term outputArgument = null;
//
//        Object[] typedInputArgments = new Object[getArity()];
//        Object typedOutputArgument = null;
//
//        boolean unconvertableArgumentsFound = false;
//
//        // Collect the input and (if any) output arguments, making sure that no input argument is an unbound variable.
//
//        for (int i = 0, j = 0; i < getArity(); i++) {
//            Term t = caller.getArgument(i).applyTheta(bindingList.theta);
//            Object typedArgument = convert(inputArgumentTypes[i], t);
//
//            if (i != getIndexOfOutputArgument()) {
//                if (typedArgument == null) {
//                    unconvertableArgumentsFound = true;
//                    break;
//                }
//
//                inputArguments.add(t);
//                typedInputArgments[j++] = typedArgument;
//            }
//            else {
//                outputArgument = t;
//                typedOutputArgument = typedArgument;
//            }
//        }
//
//        if (unconvertableArgumentsFound) {
//            return null;
//        }
//
//        boolean tryCache = isCachingEnabled() && outputArgument instanceof Variable;
//
//        PredicateNameArity predicateNameArity = null;
//
//        Object typedResult = null;
//        if (tryCache) {
//            predicateNameArity = new PredicateNameArity(caller.predicateName, caller.numberArgs());
//
//            Object cachedValue = stringHandler.getUserDefinedLiteralCache().lookup(this, predicateNameArity, inputArguments);
//            if (cachedValue == UserDefinedLiteralCache.FAILURE_INDICATOR) {
//                return null;
//            }
//            typedResult = cachedValue;
//            // set tryCache to false here so that
//            // we don't attempt to recache the result...
//            tryCache = false;
//        }
//
//        if (typedResult == null) {
//            // Didn't find a result in the cache...
//            typedResult = evaluateMe(typedInputArgments, typedOutputArgument);
//        }
//
//        BindingList newBindingList = null;
//        if (typedResult != null) {
//            // We have a non-null result...check to make sure it is legal...
//            // And unify the result with the output argument to generate the
//            // new binding list.
//            Term resultAsTerm = convert(outputArgumentType, typedResult, stringHandler);
//
//
//            newBindingList = unifier.unify(resultAsTerm, outputArgument, bindingList);
//
//            if (newBindingList == null) {
//                // The unification of the output argument did not match the
//                // result.  This should not happen!
//            	Utils.warning( "Error in UserDefinedFunctionAsLiteral for " + caller.predicateName + "/" + getArity() + ": Result of evaluateMe and original output term did not unify.  Returning fail.");
//                //Utils.waitHere("Error in UserDefinedFunctionAsLiteral for " + caller + ": Result of evaluateMe (" + resultAsTerm + ") and original output term (" + outputArgument + ") did not unify.  Returning fail.");
//                typedResult = null;
//            }
//        }
//
//        if (tryCache) {
//            // Go ahead and cache if possible...
//            // We only cache when the output is a variable since semantic equality
//            // calculating functions may evaluate to true even when the result
//            // is not the exact function value...
//            stringHandler.getUserDefinedLiteralCache().cache(this, predicateNameArity, inputArguments, typedResult == null ? UserDefinedLiteralCache.FAILURE_INDICATOR : typedResult);
//        }
//
//        return newBindingList;
        // The code above does not work properly with caching and has note been updates to the most recent
        // caching changes.  It needs to be rewritten, with the AbstractUserDefinedFunctionAsLiteral as a
        // source template with the Typed object stuff integrated as necessary.
        throw new UnsupportedOperationException("TypedUserDefinedFunctionAsLiterals are currently not working.");
    }

    /** Evaluates this literal given these input arguments.
     *
     * <p>The output argument, as passed in to the literal, may
     * be a variable or may be set to some value.  If the outputArgument passed
     * into the literal is a variable, the outputArgument passed to evaluateMe
     * will be null and calculating the value of output is sufficient.
     * 
     * <p>However, If outputArgument is not a variable, then the outputArgument
     * passed to evaluateMe will be non-null and evaluateMe method should also check
     * to make sure the calculated value, based on the input arguments,
     * is semantically equivalent to the outputArgument.  For most calculations,
     * this can be done via simply equality. However, for some calculations, say
     * equalWithTolerance, it is sufficient that a non-variable outputArgument
     * only be close to the calculated value.</p>
     *
     * <p>The return value should either be null, if the evaluation FAILS, or should
     * be the result of calculating the function and must be of type outputArgumentType.
     * Additionally, if outputArgument was non-null and evaluation succeeds,
     * the return value must unify with outputArgument after they are both converted
     * back to term form.</p>
     *
     * <p>The inputArguments are guaranteed to be non-null and of the type specified in
     * inputArgumentTypes, respectively.  If any of the arguments passed to the literal
     * originally were not ground, the literal will fail prior to calling evaluateMe.
     *
     * <p>Other than the return value, additional output is not supported by this class.
     * Modifying the input argument array has no effect.
     *
     * @param inputArguments List of Object indicating the input arguments, guaranteed
     * to be non-null.
     *
     * @param outputArgument The output argument, as passed in to the literal and
     * converted to the appropriate type according to outputArgumentType.  This may
     * be null if it was a variable.
     * 
     * @return The result of the calculation, an object of type outputArgumentType.
     * If outputArgument is not null, the return value should unify with the outputArgument
     * after they are both converted back to terms.
     */
    protected abstract Object evaluateMe(Object[] inputArguments, Object outputArgument);

    /**
     * @return the arity
     */
    public int getArity() {
        return getInputArgumentCount() + 1;
    }

    /**
     * @return the indexOfOutputArgument
     */
    public int getIndexOfOutputArgument() {
        return indexOfOutputArgument;
    }

    /**
     * @return the inputArgumentCount
     */
    public int getInputArgumentCount() {
        return inputArgumentTypes == null ? 0 : inputArgumentTypes.length;
    }

    @SuppressWarnings("unchecked")
    public Class[] getInputArgumentTypes() {
        return inputArgumentTypes;
    }

    @SuppressWarnings("unchecked")
    public Class getOutputArgumentType() {
        return outputArgumentType;
    }
}
