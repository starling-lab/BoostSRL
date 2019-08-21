/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import java.util.ArrayList;
import java.util.List;

/**
 * @author shavlik
 *
 */
@SuppressWarnings("serial")
public class ConstructedLiteral extends Literal {

	public List<AllOfFOPC> definition;
	/**
	 * 
	 */
	public ConstructedLiteral(HandleFOPCstrings stringHandler, PredicateName pName, AllOfFOPC constructor) {
		super(stringHandler, pName);
		createDefinition(constructor);
	}
	public ConstructedLiteral(HandleFOPCstrings stringHandler, PredicateName pName, List<Term> arguments, AllOfFOPC constructor) {
		super(stringHandler, pName, arguments);
		createDefinition(constructor);
	}
	public ConstructedLiteral(HandleFOPCstrings stringHandler,PredicateName pName, Term argument, AllOfFOPC constructor) {
		super(stringHandler, pName);
		List<Term> arguments2 = new ArrayList<Term>(1);
		arguments2.add(argument);
		setArguments(arguments2);
		createDefinition(constructor);
	}
	
	private void createDefinition(AllOfFOPC constructor) {
		definition = ((constructor instanceof ConstructedLiteral) 
						? AllOfFOPC.makeList(constructor, ((ConstructedLiteral) constructor).definition)
						: AllOfFOPC.makeList(constructor));
	}
	
	public String toString() {
		String basic = super.toString();
		
		return basic + " % " + definition.size() + " constructors: " + definition;
	}

}
