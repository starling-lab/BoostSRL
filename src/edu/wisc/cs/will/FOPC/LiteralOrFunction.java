/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC;

import java.util.List;

/** Interface describing the operations commmon between literals and terms.
 *
 * Literal and terms often play a similar role.  Literals are the arguments
 * of Clauses while Terms are the arguments of Functions.  Literals are easily
 * representable as Term via a Function.  Terms are representable as Literals
 * via either the TermAsSentence class or as a more direct translation from
 * a Function to a Literal.
 *
 * @author twalker
 */
public interface LiteralOrFunction {

    public Function asFunction();

    public Literal asLiteral();

    public PredicateName getPredicateName();

    public FunctionName getFunctionName();

    public int getArity();

    PredicateNameAndArity getPredicateNameAndArity();

    public List<Term> getArguments();

    public Term getArgument(int index);

    public HandleFOPCstrings getStringHandler();
}
