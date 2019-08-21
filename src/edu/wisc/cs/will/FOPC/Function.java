/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.wisc.cs.will.FOPC.visitors.TermVisitor;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author shavlik
 *
 */
@SuppressWarnings("serial")
public class Function extends Term implements LiteralOrFunction {
	public  FunctionName functionName;
	protected List<Term>   arguments;    // Note: should not directly manipulate.  Instead use addArgument(), removeArgument(), and setArguments().
	protected List<String> argumentNames; // (Optional) names of the arguments.
	protected int        cached_arity      = -1;
	protected int        cachedVariableCount = -1; // Only set to false if CHECKED.  (Key: -1 = unknown, 0 = false, 1 = true.)  TODO protect against changes to 'arguments'
	
	/**
	 * 
	 */
	public    Function() { // This one is only used in special circumstances, e.g. by WeightedSumModel.		
	}
	protected Function(HandleFOPCstrings stringHandler, FunctionName functionName, List<Term> arguments, TypeSpec typeSpec) {
		this.stringHandler = stringHandler;
		this.functionName  = functionName;
		this.arguments     = arguments;
		this.setTypeSpec(typeSpec);
		if (functionName == null) {         Utils.error("You have not provided a function name!"); }
		if (functionName.name.equals("")) { Utils.error("You have not provided a function name that is the empty string!"); }
	}
	protected Function(HandleFOPCstrings stringHandler, FunctionName functionName, TypeSpec typeSpec) {
		this(stringHandler, functionName, null, typeSpec);
	}
	protected Function(HandleFOPCstrings stringHandler, FunctionName functionName, List<Term> arguments, List<String> argumentNames, TypeSpec typeSpec) {
		this(stringHandler, functionName, arguments, typeSpec);
		this.argumentNames = argumentNames;
		sortArgumentsByName();
		// Allow either to be null (e.g., a 'bare copy' might be being made).
		if (arguments != null && argumentNames != null && Utils.getSizeSafely(arguments) !=  Utils.getSizeSafely(argumentNames)) {
			Utils.error("Have " + arguments + " and " + argumentNames + " - number of arguments and number of names must match.");
		}
	}
	
	// Access values by name if argument names have been stored.
	public String getArgumentName(int index) {
		if (argumentNames == null) { return null; } //Utils.error("Asked for arg #" + index + " but no argument names are stored."); }
		if (argumentNames.size() <= index) { Utils.error("Asked for arg #" + index + " but only have: " + argumentNames); }
		return argumentNames.get(index);
	}

	public Function copyAndClearArgumentNames() {
		return copy(true).clearArgumentNamesInPlace(); // Need to recur in case functions in the terms.
	}
	public Function copyAndClearArgumentNames(boolean removeNameArg) {
		return copy(true).clearArgumentNamesInPlace(true);
	}
	public Function clearArgumentNamesInPlace() {
		return clearArgumentNamesInPlace(true);
	}
	public Function clearArgumentNamesInPlace(boolean removeNameArg) {	
		if (numberArgs() < 1) { return this; }		
		if (argumentNames != null) {
			List<String> argOrdering = functionName.getNamedArgOrdering(numberArgs());
			
			if (removeNameArg) {
				if (argumentNames.get(0).equalsIgnoreCase("name")) {
					removeArgument(arguments.get(0), argumentNames.get(0));
				}
			}			

			if (argOrdering == null) { } // Utils.waitHere("No arg ordering for: " + this); }
			else {
				List<Term> newArgs = new ArrayList<Term>(numberArgs());
				for (String argName : argOrdering) { newArgs.add(getArgumentByName(argName, true)); }
				arguments = newArgs;
			}
		}
		argumentNames = null;
		if (arguments == null) { return this; }
		for (Term term : arguments) if (term instanceof Function) {
			((Function) term).clearArgumentNamesInPlace();
		}
		return this;
	}
	
	// Access a value by name, rather than by position.
	public Term getArgumentByName(String name) {
		return getArgumentByName(name, true);
	}
	public Term getArgumentByName(String name, boolean complainIfNotFound) {
		if (argumentNames == null)    { 
			if (complainIfNotFound) { Utils.error("Cannot find '" + name + "' in " + argumentNames + " of " + this); }
			return null; } 
		if (argumentNames.size() < 1) { 
			if (complainIfNotFound) { Utils.error("Cannot find '" + name + "' in " + argumentNames); }
			return null; }
		for (int i = 0; i < numberArgs(); i++) {
			if (argumentNames.get(i).equalsIgnoreCase(name)) { return arguments.get(i); }
		}
		if (complainIfNotFound) { Utils.error("Cannot find '" + name + "' in " + argumentNames + " of " + this); }
		return null;
	}
	
	public int numberArgs() {
		if (cached_arity < 0) { setNumberArgs(); }
		return cached_arity;
	}
	private void setNumberArgs() {
		if (arguments == null) { cached_arity = 0; }
		else                   { cached_arity =  arguments.size(); }
	}
	
	public void addArgument(Term term) {
		if (argumentNames != null) { Utils.error("Current arguments are named, so you need to pass in term and name for '" + this + "'."); }
		arguments.add(term);
		setNumberArgs();
	}	
	public void addArgument(Term term, String name) {
		addArgument(term, name, true);
	}
	public void addArgument(Term term, String name, boolean sort) {
		arguments.add(term);
		argumentNames.add(name);
		setNumberArgs();
		if (sort) { sortArgumentsByName(); }
	}
	public void addArgument(int position, Term term, String name) {
		addArgument(position, term, name, true);
	}
	public void addArgument(int position, Term term, String name, boolean sort) {
		arguments.add(    position, term);
		argumentNames.add(position, name);
		setNumberArgs();
		if (sort) { sortArgumentsByName(); }
	}
	
	public void removeArgument(Term term) {
		if (argumentNames != null) { Utils.error("Current arguments are named, so you need to pass in term and name for '" + this + "'."); }
		if (!arguments.remove(term)) { Utils.error("Could not remove '" + term + "' from '" + this + "'."); }
		setNumberArgs();
	}	
	public void removeArgument(Term term, String name) {
		if (!arguments.remove(term))     { Utils.error("Could not remove '" + term + "' from '" + this + "'."); }
		if (!argumentNames.remove(name)) { Utils.error("Could not remove '" + name + "' from '" + this + "'."); }
		setNumberArgs();
		sortArgumentsByName();
	}
	
	// Cache this calculation to save time.
	public boolean containsVariables() {
		if (cachedVariableCount < 0) {
			if (arguments == null) { cachedVariableCount = 0; return false; }
			for (Term term : arguments) { 
				if ( term instanceof Variable)                                           { cachedVariableCount = 1; return true; }
				if ((term instanceof Function) && ((Function) term).containsVariables()) { cachedVariableCount = 1; return true; }
			}
			if (cachedVariableCount < 0) { cachedVariableCount = 0; }
		}
		return (cachedVariableCount > 0);
	}

    @Override
    public BindingList isEquivalentUptoVariableRenaming(Term that, BindingList bindings) {
        if (that instanceof Function == false) return null;

        Function function = (Function) that;

        if ( this.functionName.equals(function.functionName) == false ) return null;
        if ( this.numberArgs() != function.numberArgs() ) return null;

        for (int i = 0; i < numberArgs(); i++) {
            bindings = this.getArgument(i).isEquivalentUptoVariableRenaming(function.getArgument(i), bindings);
            if ( bindings == null ) return null;
        }

        return bindings;
    }



	/** Would any variables in this function remain UNBOUND if this binding list were to be applied?	
	 * @param theta
	 * @return
	 */
    @Override
	public boolean freeVariablesAfterSubstitution(BindingList theta) {
		if (!containsVariables()) { return false; }
		if (theta == null || arguments == null) { return false; }
		for (Term term : arguments) if (term.freeVariablesAfterSubstitution(theta)) { return true; }
		return false;
	}

    static int depth = 0; // NOTE: this is risky if we every want to allow parallel WILLs ... JWS 7/24/10
    @Override
	public Function applyTheta(Map<Variable,Term> theta) { // Utils.println("applyTheta to " + this);
        depth++;
        // This should be essentially the same code as in Literal.applyTheta
        boolean needNewFunction = false; // See if there is a chance this might need to change (only do a one-level deep evaluation).
        if (arguments != null) {
            for (Term term : arguments) {
                if (!((term instanceof Variable && theta.get((Variable)term) == null) || term instanceof Constant)) {
                    needNewFunction = true;
                    break;
                }
            }
        }

        if (!needNewFunction) {
            depth--;
            return this;
        }
        
    //    if (depth > 1000) {
    //    	Utils.waitHere(toString());
    //   }

        int numbArgs = numberArgs();
        List<Term> newArguments = (numbArgs == 0 ? null : new ArrayList<Term>(numberArgs()));
        if (numbArgs > 0) {
            for (int i = 0; i < numbArgs; i++) {
                Term arg = arguments.get(i);
                if (arg == null) {
                    Utils.error("Has an arg=null: " + this);
                }
               // Utils.println(" Function.applyTheta arg(" + i + ") = " + arg + "    this = " + this + " theta: " + theta);
                newArguments.add(arg == null ? null : arg.applyTheta(theta));
            }
        }
        depth--;
        return getBareCopy(newArguments);
	}

    public Function applyTheta(BindingList bindings) {
        return (Function) super.applyTheta(bindings);
    }
	
	// Need for proper copying (e.g., ConsCell reused applyTheta for Function).
	public Function getBareCopy() {
		return stringHandler.getFunction(functionName, arguments, argumentNames, typeSpec);
	}
	public Function getBareCopy(List<Term> newArguments) {
		return stringHandler.getFunction(functionName, newArguments, argumentNames, typeSpec);
	}
	public Function getBareCopy(List<Term> newArguments, List<String> newArgumentNames) {
		return stringHandler.getFunction(functionName, newArguments, newArgumentNames, typeSpec);
	}
	public Function getBareCopy(FunctionName functionName, List<Term> newArguments, TypeSpec typeSpec) {
		return stringHandler.getFunction(functionName, newArguments, argumentNames, typeSpec);
	}
	public Function getBareCopy(List<Term> newArguments, List<String> newArgumentNames, TypeSpec typeSpec) {
		return stringHandler.getFunction(functionName, newArguments, newArgumentNames, typeSpec);
	}
	
    @Override
	public Function copy(boolean recursiveCopy) { // recursiveCopy=true means that the copying recurs down to the leaves.
		List<Term>   newArguments = (arguments     != null ? new ArrayList<Term>(  numberArgs()) : null);
		List<String> newArgNames  = (argumentNames != null ? new ArrayList<String>(numberArgs()) : null);
		if (argumentNames != null) { newArgNames.addAll(argumentNames); }
		if (recursiveCopy) {
			if (arguments != null) {				
				for (Term term : arguments) {	
					newArguments.add(term == null ? null : term.copy(recursiveCopy));
				}
			}
			return getBareCopy(newArguments, newArgNames);
		}
		if (arguments!= null) { newArguments.addAll(arguments);    }
		if (typeSpec != null && recursiveCopy) {
			return getBareCopy(newArguments, newArgNames, typeSpec.copy(recursiveCopy));
		}
		return getBareCopy(newArguments, newArgNames);
	}

    @Override
	public Function copy2(boolean recursiveCopy, BindingList bindingList) { // recursiveCopy=true means that the copying recurs down to the leaves.
		List<Term>   newArguments = (arguments     != null ? new ArrayList<Term>(  numberArgs()) : null);
		List<String> newArgNames  = (argumentNames != null ? new ArrayList<String>(numberArgs()) : null);
		if (argumentNames != null) { newArgNames.addAll(argumentNames); }
		if (recursiveCopy) {
			if (arguments != null) {
				for (Term term : arguments) {
					newArguments.add(term == null ? null : term.copy2(recursiveCopy, bindingList));
				}
			}
			return getBareCopy(newArguments, newArgNames);
		}
		if (arguments!= null) { newArguments.addAll(arguments);    }
		if (typeSpec != null && recursiveCopy) {
			return getBareCopy(newArguments, newArgNames, typeSpec.copy(recursiveCopy));
		}
		return getBareCopy(newArguments, newArgNames);
	}

    @Override
    public Sentence asSentence() {
        return stringHandler.getLiteral(stringHandler.getPredicateName(functionName.name), arguments);
    }

    public Clause asClause() {
        return stringHandler.getClause( stringHandler.getLiteral(stringHandler.getPredicateName(functionName.name), arguments), true);
    }

    public Literal asLiteral() {
        return stringHandler.getLiteral(stringHandler.getPredicateName(functionName.name), arguments, argumentNames);
    }
	
    @Override
	public Collection<Variable> collectFreeVariables(Collection<Variable> boundVariables) {
		List<Variable> result = new ArrayList<Variable>(numberArgs());
		
		if (arguments != null) for (Term term : arguments) if (term != null) {	
			Collection<Variable> tempVarList = term.collectFreeVariables(boundVariables);
			
			if (tempVarList != null) { for (Variable var : tempVarList) if (!result.contains(var)) { result.add(var); }}
		}
		return result;
	}
	
	@Override
	public int hashCode() { // Need to have equal objects produce the same hash code.
		final int prime = 31;
		int result = 1;
		result = prime * result + ((functionName == null) ? 0 : functionName.hashCode());
		result = prime * result + ((arguments    == null) ? 0 : arguments.hashCode());
		return result;
	}	
	// Are these two literals identical even if not the same instance?  Can be overridden by stringHandler.useStrictEqualsForLiterals
    @Override
	public boolean equals(Object other) {
		return equals(other, true);
	}
	public boolean equals(Object other, boolean considerUseStrictEqualsForFunctions) {
		if (this == other) { return true; }
		if (considerUseStrictEqualsForFunctions && stringHandler.usingStrictEqualsForFunctions()) { return false; }
		if (!(other instanceof Function)) { return false; }
		
		Function otherAsFunction = (Function) other;
		if (functionName != otherAsFunction.functionName) { return false; }
		int thisNumberOfArgs  =                 numberArgs();
		int otherNumberOfArgs = otherAsFunction.numberArgs();
		if (thisNumberOfArgs != otherNumberOfArgs)       { return false; }
		for (int i = 0; i < thisNumberOfArgs; i++) { // Should do a double walk of the two lists, but I don't recall the syntax (TODO).
			if (!arguments.get(i).equals(otherAsFunction.arguments.get(i))) { return false; }
		}
		if (argumentNames == null && otherAsFunction.argumentNames == null) { return true;  }
		if (argumentNames == null || otherAsFunction.argumentNames == null) { return false; }
		for (int i = 0; i < thisNumberOfArgs; i++) { // Should do a double walk of the two lists, but I don't recall the syntax (TODO).
			if (!argumentNames.get(i).equalsIgnoreCase(otherAsFunction.argumentNames.get(i))) { return false; }
		}
		return true;
	}

	   // Are these two equivalent POSSIBLY AFTER SOME VARIABLE RENAMING.
    @Override
    public BindingList variants(Term other, BindingList bindings) {
        // if (this == other) { return bindings; }	// Need to collect the matched variables (so they don't get matched to another variable elsewhere).
        if (!(other instanceof Function)) {
            return null;
        }
        
        Function otherAsFunction = (Function) other;
        if (functionName != otherAsFunction.functionName) {
            return null;
        }
        
        int thisNumberOfArgs = numberArgs();
        int otherNumberOfArgs = otherAsFunction.numberArgs();
        
        if (thisNumberOfArgs != otherNumberOfArgs) {
            return null;
        }
        
        if (arguments != null) {
            int i = 0;
            for (Term arg : arguments) { // Should do a double walk of the two lists, but I don't recall the syntax (to do).
                bindings = arg.variants(otherAsFunction.arguments.get(i++), bindings);
                if (bindings == null) {
                    return null;
                }
            }
        }
        
        if (argumentNames == null && otherAsFunction.argumentNames == null) {
            return bindings;
        }
        
        if (argumentNames == null || otherAsFunction.argumentNames == null) {
            return null;
        }
        
        for (int j = 0; j < thisNumberOfArgs; j++) { // Should do a double walk of the two lists, but I don't recall the syntax (TODO).
            if (!argumentNames.get(j).equalsIgnoreCase(otherAsFunction.argumentNames.get(j))) {
                return null;
            }
        }
        return bindings;
    }

	public Literal convertToLiteral(HandleFOPCstrings stringHandler) {
		PredicateName predicateName = stringHandler.getPredicateName(functionName.name);
		Literal       result        = stringHandler.getLiteral(predicateName, arguments, argumentNames);
		return result;
	}
	
    @Override
	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		if (functionName.name.equalsIgnoreCase("conscell")) {
			return stringHandler.getConsCell(this).toPrettyString(newLineStarter, precedenceOfCaller, bindingList);
		}
		String  fNameStr = (typeSpec != null ? typeSpec.getModeString() + typeSpec.isaType.typeName + ":" : "") + functionName;
		String  end      = (typeSpec != null ? typeSpec.getCountString() : "");
		boolean firstOne = true;
		boolean hasArgNames = (argumentNames != null);
		
		if (functionName.printUsingInFixNotation && numberArgs() == 1) {
			int precedence = HandleFOPCstrings.getOperatorPrecedence_static(functionName.name);
			if (precedenceOfCaller < precedence) { return "(" + fNameStr + (hasArgNames ? argumentNames.get(0) + "=": "") + arguments.get(0).toPrettyString(newLineStarter, precedence, bindingList) + ")" + end; }
			return fNameStr + (hasArgNames ? argumentNames.get(0) + "=": "") + arguments.get(0).toPrettyString(newLineStarter, precedence, bindingList) + end;
	    }
		if (functionName.printUsingInFixNotation && numberArgs() == 2) {
			int precedence =  HandleFOPCstrings.getOperatorPrecedence_static(functionName.name);
			if (precedenceOfCaller < precedence) { return "(" + (hasArgNames ? argumentNames.get(0) + "=": "") + arguments.get(0).toPrettyString(newLineStarter, precedence, bindingList) + " " + fNameStr + " " + (hasArgNames ? argumentNames.get(1) + "=": "") + arguments.get(1).toPrettyString(newLineStarter, precedence, bindingList) + ")" + end; }
			return                                              (hasArgNames ? argumentNames.get(0) + "=": "") + arguments.get(0).toPrettyString(newLineStarter, precedence, bindingList) + " " + fNameStr + " " + (hasArgNames ? argumentNames.get(1) + "=": "") + arguments.get(1).toPrettyString(newLineStarter, precedence, bindingList)       + end;
	    }
		String result = fNameStr + "(";
		for (int i = 0; i < numberArgs(); i++) {
			Term arg = arguments.get(i);
			if (firstOne) { firstOne = false; } else {result += ", "; }
			result += (hasArgNames ? argumentNames.get(i) + "=": "") + arg.toPrettyString(newLineStarter, Integer.MAX_VALUE, bindingList); // No need for extra parentheses in an argument list.
		}		
		return result + ")" + end;
	}
    @Override
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		if (functionName.name.equalsIgnoreCase("consCell")) {
			return stringHandler.getConsCell(this).toString(precedenceOfCaller, bindingList);
		}
		boolean useTypes = stringHandler.printTypedStrings;
		String  fNameStr = (typeSpec != null && useTypes ? typeSpec.getModeString() + typeSpec.isaType.typeName + ":" : "") + functionName;
		String  end      = (typeSpec != null && useTypes ? typeSpec.getCountString() : "");
		boolean firstOne = true;
		boolean hasArgNames = (argumentNames != null);
		
		if (functionName.printUsingInFixNotation && numberArgs() == 1) {
			int precedence = (stringHandler.alwaysUseParensForInfixFunctions ? Integer.MAX_VALUE : HandleFOPCstrings.getOperatorPrecedence_static(functionName.name));
			if (precedenceOfCaller <= precedence) { return "(" + fNameStr + (hasArgNames ? argumentNames.get(0) + "=" : "") + arguments.get(0).toString(precedence, bindingList) + ")" + end; }
			return                                               fNameStr + (hasArgNames ? argumentNames.get(0) + "=" : "") + arguments.get(0).toString(precedence, bindingList)       + end;
	    }
		if (functionName.printUsingInFixNotation && numberArgs() == 2) {
			int precedence = (stringHandler.alwaysUseParensForInfixFunctions ? Integer.MAX_VALUE : HandleFOPCstrings.getOperatorPrecedence_static(functionName.name));
			if (precedenceOfCaller <= precedence) { return "(" + (hasArgNames ? argumentNames.get(0) + "=" : "") + arguments.get(0).toString(precedence, bindingList) + " " + fNameStr + " " + (hasArgNames ? argumentNames.get(1) + "=": "") + arguments.get(1).toString(precedence, bindingList) + ")" + end; }
			return                                               (hasArgNames ? argumentNames.get(0) + "=" : "") + arguments.get(0).toString(precedence, bindingList) + " " + fNameStr + " " + (hasArgNames ? argumentNames.get(1) + "=": "") + arguments.get(1).toString(precedence, bindingList)       + end;
	    }
		//if (functionName.name.equalsIgnoreCase("consCell")) {
			//return ((ConsCell) this).toString(precedenceOfCaller);
		//}
		String result = fNameStr + "(";
		for (int i = 0; i < numberArgs(); i++) {
			Term arg = arguments.get(i);	
			if (firstOne) { firstOne = false; } else {result += ", "; }
			result += (hasArgNames && i < argumentNames.size() ? argumentNames.get(i) + "=": "") + arg.toString(Integer.MAX_VALUE, bindingList); // No need for extra parentheses in an argument list.
		}		
		return result + ")" + end;
	}
	
	public int countLeaves() {
		if (numberArgs() < 1) { return 0;}
		int total = 0;
		for (Term term : arguments) {
			if (term instanceof Function) { total +=  ((Function) term).countLeaves(); }
			else { total++; }
		}
		return total;
	}
	
	public List<Term> getArguments() {
		return arguments == null ? Collections.EMPTY_LIST : arguments;
	}	
	public Term getArgument(int i) {
		return arguments.get(i);
	}
	public void setArguments(List<Term> arguments) {
		this.arguments = arguments;
		sortArgumentsByName();
	}
	public List<String> getArgumentNames() {
		return argumentNames;
	}
	public void setArgumentNames(List<String> argumentNames) {
		this.argumentNames = argumentNames;
		sortArgumentsByName();
	}
	private void sortArgumentsByName() {
		if (argumentNames == null) { return; }
		int numbArgs = numberArgs();
		if (Utils.getSizeSafely(argumentNames) != numbArgs) { 
			Utils.error("# of arguments (" + numbArgs                           + ") does not equal number of argument names ("
										   + Utils.getSizeSafely(argumentNames) + "):\n   args = " + arguments + "\n  names = " + argumentNames + "\n    lit = " + this);
		}
		if (numbArgs < 2) { return; }
		List<NamedTerm> namedTerms = new ArrayList<NamedTerm>(numbArgs);
		Set<String> namesSeen = new HashSet<String>(4);
		for (int i = 0; i < numbArgs; i++) {
			String argName = argumentNames.get(i);
			if (namesSeen.contains(argName)) { Utils.error("Cannot have duplicate names (" + argName + "): " + argumentNames); }
			if ( argName != null ) namesSeen.add(argName);
            namedTerms.add(new NamedTerm(arguments.get(i), argName));
		}
		Collections.sort(namedTerms, NamedTerm.comparator);
		arguments.clear();
		argumentNames.clear();
		for (NamedTerm nt : namedTerms) { 
			arguments.add(    nt.term);
			argumentNames.add(nt.name);
		}
	}

    // Sometimes what should be ConsCell instances are Function instances instead.
	// This provides a way to check for that case.
	public static boolean isaConsCell(Term expression) {  // This and the above look to be identical (JWS, 7/25/10). So I (JWS) deleted checkIfReallyIsaConsCell.
		if (expression instanceof ConsCell) { return true; }
		if (expression instanceof Function) {
			Function     f     = (Function) expression;
			FunctionName fName = f.functionName;
			return fName.name.equalsIgnoreCase("conscell");
		}
		return false;
	}


    protected void appendToString(StringBuilder sb, int precedenceOfCaller, BindingList bindingList) {

        Term arg0 = getArgument(0);

        sb.append( arg0.toString(precedenceOfCaller, bindingList) );


        Term arg1 = getArgument(1);

        // Be robust to ConsCell's masquerading as Function's.
        boolean arg2isNil = (isaConsCell(arg1) && ((Function) arg1).numberArgs() == 0);
        if (arg2isNil == false  ) {
            if (isaConsCell(arg1)) {
                sb.append(", ");
                ((Function) arg1).appendToString(sb, precedenceOfCaller, bindingList);
            }
            else {
                sb.append(" | ").append(getArgument(1).toString(precedenceOfCaller, bindingList));
            }
        }
    }

    @Override
    public <Return,Data> Return accept(TermVisitor<Return,Data> visitor, Data data) {
        return visitor.visitFunction(this, data);
    }
	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		int total = 0;
		if (arguments != null) { for (Term arg : arguments) { total += arg.countVarOccurrencesInFOPC(v); } }
		return total;
	}

    /** Returns the function name as predicate and arity.
     *
     * Technically, a function doesn't have predicate name, but
     * we convert of the function to the a predicate of the same
     * name.
     *
     * @return
     */
    public PredicateNameAndArity getPredicateNameAndArity() {
        return stringHandler.getPredicate(stringHandler.getPredicateName(functionName.name), getArity());
    }

    public int getArity() {
        return numberArgs();
    }

    public Function asFunction() {
        return this;
    }

    public FunctionName getFunctionName() {
        return functionName;
    }

    public PredicateName getPredicateName() {
        return getStringHandler().getPredicateName( functionName.name );
    }



}

