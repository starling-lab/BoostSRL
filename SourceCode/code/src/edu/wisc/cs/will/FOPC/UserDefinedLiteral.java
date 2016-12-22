/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.ResThmProver.HornClauseContext;

/** User Defined Literal interface.
 *
 * A User defined literal allows arbitrary code to be embedded in Will
 * concepts and evaluated transparently.
 *
 * <p>Generally users should not implements this directly.  Instead they should subclass
 * on of the abstract classes already implementing this, based on their needs.</p>
 *
 * <p>If the concept being evaluated is boolean and all arguments are inputs
 * arguments with known Java types, then the AbstractTypedUserDefinedBooleanLiteral
 * should be used.</p>
 *
 * <p>If the user defined literal implements a function x = f(y,z,...) and the
 * Java type of both input arguments and the return value is fixed, the
 * AbstractTypedUserDefinedFunctionAsLiteral literal should be used.</p>
 *
 * <p>If a more traditional logic programming approach is desired, where terms
 * can be treated as either inputs or outputs depending on their bindings, then
 * the AbstractUserDefinedBooleanLiteral interface should be used.  This is
 * more flixible than the AbstractTypedUserDefinedBooleanLiteral but serves the
 * same purpose.</p>
 *
 * <p>If the user defined literal implements a function x = f(y,z,...) where
 * arguments may or may not be bound, then the AbstractUserDefinedFunctionAsLiteral
 * literal should be used.  This is more flexible than the
 * AbstractTypedUserDefinedFunctionAsLiteral but serves the same purpose.</p>
 *
 * <p>If even more flexibility is desired, users can subclass the AbstractUserDefinedLiteral
 * directly (or even UserDefinedLiteral).  This approach has the most flixibility, but
 * all requirements the most bookkeeping and in-depth knowledge.</p>
 *
 * @author twalker
 */
public interface UserDefinedLiteral {


    /** Returns the arity of the predicate this object defines.
     *
     * @return Arity of defined predicate.
     */
    int getArity();

    /** Handles the processing of the procedurally defined predicate.
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
     * @param context Context the user defined literal is being evaluated in.
     *
     * @return If the user defined literal evaluates to true, the bindingList is returned.  If false,
     * null is returned.
     */
    public BindingList handleUserDefinedLiteral(Literal caller, Unifier unifier, BindingList bindingList, HornClauseContext context);

}
