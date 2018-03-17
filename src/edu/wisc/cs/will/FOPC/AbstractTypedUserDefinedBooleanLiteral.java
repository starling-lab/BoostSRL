/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.ResThmProver.HornClauseContext;

/** A userDefinedLiteral wrapping a traditional logical evaluation with Java typing enforced.
 *
 * <p>This class implements a UserDefinedLiteral such that the literal is
 * either true or false.  Arguments can only be used as inputs, must be ground,
 * and are of a specified Java type.
 *
 * <p>Subclasses only have to implement the evaluateMe(List<Term> arguments) method
 * which returns either true or false depending on whether the evaluation is successful.
 * When the literal is evaluated, the Will logical types will be converted in the
 * types specified by inputArgumentTypes so evaluateMe only needs to handle Java types,
 * not Will types.
 *
 * <p>See {@link UserDefinedLiteral} for help in choosing the correct abstract class
 * to base your user defined literal on.  Most of the book-keeping and Will types
 * are already handled by these classes.
 * 
 * @author shavlik
 *
 */
public abstract class AbstractTypedUserDefinedBooleanLiteral extends AbstractTypedUserDefinedLiteral {

    @SuppressWarnings("unchecked")
	private Class[] inputArgumentTypes;

    /** Creates a new AbstractUserDefinedBooleanLiteral with inputArgumentTypes.
     *
     * @param inputArgumentTypes An array of the input argument types for this user defined literal.
     * By default, the only supported Java types are String, Integer, Double, and Boolean.  Use
     * AbstractTypedUserDefinedBooleanLiteral(Class[], TermToJavaTypeConverter[], boolean) should
     * be used.
     * @param cachingEnabled If true, caching is enable.  Caching should only be enabled
     * on deterministic literals.
     * @throws IllegalArgumentException An IllegalArgumentException is thrown if any of the types
     * specified in inputArgumentTypes does not have a typeConverter.
     */
    @SuppressWarnings("unchecked")
	public AbstractTypedUserDefinedBooleanLiteral(Class[] inputArgumentTypes, boolean cachingEnabled) throws IllegalArgumentException {
        this(inputArgumentTypes, null, cachingEnabled);
    }

    /** Creates a new AbstractUserDefinedBooleanLiteral with inputArgumentTypes and additional custom type converters.
     *
     * @param inputArgumentTypes An array of the input argument types for this user defined literal.
     * By default, the only supported Java types are String, Integer, Double, and Boolean.
     * @param additionalConverters Array of additional type converts to use for converting types.
     * @param cachingEnabled If true, caching is enable.  Caching should only be enabled
     * on deterministic literals.
     * @throws IllegalArgumentException An IllegalArgumentException is thrown if any of the types
     * specified in inputArgumentTypes does not have a typeConverter.
     */
    @SuppressWarnings("unchecked")
	public AbstractTypedUserDefinedBooleanLiteral(Class[] inputArgumentTypes, TermToJavaTypeConverter[] additionalConverters, boolean cachingEnabled) throws IllegalArgumentException{
        super(additionalConverters, cachingEnabled);

        this.inputArgumentTypes = inputArgumentTypes;

        checkTypes(inputArgumentTypes);
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

//        // Arguments to pass to evaluateMe.
//        List<Term> arguments = new ArrayList<Term>(getArity());
//        Object[] typedArguments = new Object[getArity()];
//
//        boolean unconvertableArgumentsFound = false;
//
//        // Collect the arguments, applying the bindings if necessary...
//        for (int i = 0; i < getArity(); i++) {
//            Term t = caller.getArgument(i).applyTheta(bindingList.theta);
//            Object typedArgument = convert(inputArgumentTypes[i], t);
//
//            if ( typedArgument == null ) {
//                unconvertableArgumentsFound = true;
//                break;
//            }
//            arguments.add(t);
//            typedArguments[i] = typedArgument;
//        }
//
//        if ( unconvertableArgumentsFound ) return null;
//
//        Boolean result = null;
//        PredicateNameArity predicateNameArity = null;
//
//        if ( isCachingEnabled() ) {
//
//            predicateNameArity = new PredicateNameArity(caller.predicateName, caller.numberArgs());
//
//            Object cachedValue = stringHandler.getUserDefinedLiteralCache().lookup(this, predicateNameArity,arguments);
//            if (cachedValue == UserDefinedLiteralCache.FAILURE_INDICATOR) {
//                return null;
//            }
//            result = (Boolean) cachedValue;
//
//            if ( result != null ) {
//                return result ? bindingList : null;
//            }
//        }
//
//        // Didn't find a result in the cache...
//        // So calculate it...
//        result = evaluateMe(typedArguments);
//
//        if( isCachingEnabled() ) {
//            stringHandler.getUserDefinedLiteralCache().cache(this, predicateNameArity, arguments, result);
//        }
//
//        return result ? bindingList : null;

        // The code above does not work properly with caching and has note been updates to the most recent
        // caching changes.  It needs to be rewritten, with the AbstractUserDefinedBooleanLiteral as a
        // source template with the Typed object stuff integrated as necessary.
        throw new UnsupportedOperationException("TypedUserDefinedFunctionAsLiterals are currently not working.");
    }

    /** Evaluates this literal given these arguments.
     *
     * The inputArguments are gauranteed to be non-null and of the type specified in
     * inputArgumentTypes, respectively.  If any of the arguments passed to the literal
     * originally were not ground, the literal will fail prior to calling evaluateMe.
     * Other than the truth value, output arguments is not supported by the class.
     * Modifying the input argument array has no effect.
     *
     * <p>evaluateMe should determine the truth value of the literal and return
     * true or false appropriately.
     *
     * @param inputArguments Array of objects containing the arguments to literal.
     *
     * @return Truth value of literal given the input arguments.
     */
    protected abstract boolean evaluateMe(Object[] inputArguments);

    /**
     * @return the arity
     */
    public int getArity() {
        return inputArgumentTypes == null ? 0 : inputArgumentTypes.length;
    }

    @SuppressWarnings("unchecked")
	public Class[] getInputArgumentTypes() {
        return inputArgumentTypes;
    }

    

    

}
