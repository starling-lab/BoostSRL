/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.Utils.Utils;

/**
 * @author shavlik
 *
 *  All functions with the same name map to the same instance. 
 */
public class FunctionName extends AllOfFOPC {
	public  String  name;
	public  boolean isaSkolem = false; // Mark if this is a Skolem. 
	private Map<List<Constant>,Constant> extensionalSemantics;
	public  boolean printUsingInFixNotation = false;
	private Map<Integer,List<String>> namedArgumentOrdering = null;  // When getting rid of named arguments, this is the order argument should be placed (if null, then use alphabetic ordering).
	
	/**
	 * 
	 */
	protected FunctionName(String name) { // This is protected because getFunctionName(String name) should be used instead.
		this.name = name;
	}

	public void addExtensionalDefinition(List<Constant> inputs, Constant output) throws IllegalArgumentException {
		if (extensionalSemantics == null) { extensionalSemantics = new HashMap<List<Constant>,Constant>(8); }
		
		Constant current = extensionalSemantics.get(inputs);
		if (current != null) {
			if (current == output) { return; } // OK if redefined.
			throw new IllegalArgumentException("Cannot set " + name + inputs + " = '" + output + "' because it is currently = '" + current + "'");
		}
		extensionalSemantics.put(inputs,output);
	}
	
	public void addNamedArgOrdering(List<String> order) {
		int arity = Utils.getSizeSafely(order);
		if (namedArgumentOrdering == null) {
			namedArgumentOrdering = new HashMap<Integer,List<String>>(4);
		}
		List<String> lookup = namedArgumentOrdering.get(arity);
		if (lookup == null) { // Not currently specified.
			namedArgumentOrdering.put(arity, order);
		}
		else { Utils.println("% WARNING: Duplicate addNamedrgOrdering of '" + name + "/" + arity + "'.  Already have: " + lookup + ".  Will ignore: " + order); }		
	}
	public List<String> getNamedArgOrdering(int arity) {
		if (namedArgumentOrdering == null) { return null; }
		return namedArgumentOrdering.get(arity);
	}

	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return name;
	}
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return name;
	}

	@Override
	public FunctionName applyTheta(Map<Variable, Term> bindings) {
		return this;
	}

	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return 0;
	}

}
