/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC;

/** Interface defining objects capable of registering callbacks.
 *
 * @author twalker
 */
public interface CallbackRegister {
    
    /** Registers a callback from WILL to external code for predicateName.
     *
     * Note, a callback is actually registered for a specific predicateName & arity combination.
     * The arity is obtained from the UserDefinedLiteral.
     *
     * @param predicateName Name of the predicate.
     *
     * @param literalDefinition UserDefinedLiteral evaluated when the callback occurs.
     * The abstract classes {@link AbstractUserDefinedBooleanLiteral} and {@link AbstractUserDefinedFunctionAsLiteral}
     * can be easily extended to create a UserDefinedLiteral by implementing the relevant evaluateMe() methods.
     *
     * @throws IllegalStateException Throws an IllegalStateException if the predicateName/arity is already defined.
     */
    public void registerCallback(String predicateName, UserDefinedLiteral literalDefinition) throws IllegalStateException;
}
