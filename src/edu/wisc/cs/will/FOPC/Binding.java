/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import java.util.Map;

import edu.wisc.cs.will.Utils.Utils;

/**
 * @author shavlik
 *
 */
public class Binding extends AllOfFOPC {
	public Variable var;
	public Term     term;

	public Binding(Variable var, Term term) {
		this.var  = var;
		this.term = term;
	}
	
	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return var + " = " + term;
	}
	
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return var + "/" + term;
	}



	@Override
	public Binding applyTheta(Map<Variable,Term> bindings) {
		Utils.error("Should not call applyTheta on a Bindings.");
		return this;
	}

	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return (var == v ? 1 : 0);
	}

}
