/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.wisc.cs.will.Utils.Utils;

/**
 * @author shavlik
 *
 */
public class DoBuiltInListProcessing extends AllOfFOPC {
	protected DoBuiltInMath mathHandler = null;

	private FunctionName conscell; // Should really have ConsCell instances, but check for this as a function name as well.
	private FunctionName first;
	private FunctionName rest;
	private FunctionName remove;
	private FunctionName push;
	private FunctionName nth;
	private FunctionName nthPlus1;
	private FunctionName length; // Do numeric-valued here.
	private FunctionName position;
	private FunctionName convertListToString;
	
 //	private FunctionName member; // Don't do Booleans here.
 //	private FunctionName listsEquivalent;
	
	// Use 'fast' to indicate that we convert to lists and manipulate the lists; other than the initial call, no unification is done (ie, for union and intersection).
    // Ie, there are used like this:
    //                 ?X is append(?A, ?B)
    // The FOPC library supports Prolog-based versions, eg
    //                 append(?A, ?B, ?X)
	private FunctionName fastAppend, fastIntersection, fastUnion;

	private HandleFOPCstrings stringHandler;
	private Map<FunctionName,Set<Integer>> canHandle = new HashMap<FunctionName,Set<Integer>>(16);
	
	/**
	 * 
	 */
	public DoBuiltInListProcessing(HandleFOPCstrings stringHandler) {
		this.stringHandler = stringHandler;
		boolean hold = stringHandler.cleanFunctionAndPredicateNames;
		stringHandler.cleanFunctionAndPredicateNames = false;
		
		conscell = addFunctionName("conscell", 1);
		first    = addFunctionName("first",  1);
		rest     = addFunctionName("rest",   1);
		remove   = addFunctionName("remove", 2);
		push     = addFunctionName("push",   2);
		nth      = addFunctionName("nth",    2);
		nthPlus1 = addFunctionName("nthPlus1", 2);
		length   = addFunctionName("length",   1);
		position = addFunctionName("position", 2);
		
		fastAppend       = addFunctionName("append",       2); // Use names w/o 'Fast' here.
		fastIntersection = addFunctionName("intersection", 2);
		fastUnion        = addFunctionName("union",        2);
		
		convertListToString  = addFunctionName("convertListToString", 1);
		
		stringHandler.cleanFunctionAndPredicateNames = hold;
	}
	
	private FunctionName addFunctionName(String fNameString, int arity) {
		FunctionName fName = stringHandler.getFunctionName(fNameString);
		Set<Integer> lookup = canHandle.get(fName);
		if (lookup == null) {
			lookup = new HashSet<Integer>(4);
			canHandle.put(fName, lookup);
		}
		lookup.add(arity);
		return fName;
	}

	public boolean canHandle(FunctionName fName, int arity) {
		Set<Integer> lookup = canHandle.get(fName);
		if (lookup == null) { return false; }
		return lookup.contains(arity);
	}
	public boolean canHandle(Term expression) {
		if (expression instanceof Function) {	
			FunctionName fName = ((Function) expression).functionName;
			
			return canHandle(fName, ((Function) expression).numberArgs());
		}
		return false;
	}
	
	/** 
	 * Simplify expressions involving lists.  Complain if this can't be done.
	 * @param expression
	 * @return The simplification of the given expression.
	 */
	public Term simplify(Term expression) {
		if (Function.isaConsCell(expression)) {
			return expression;
		}
		if (expression instanceof Function) {	
			FunctionName name = ((Function) expression).functionName;
			List<Term>   args = ((Function) expression).getArguments();
			
			if (name == conscell) {
				return ConsCell.ensureIsaConsCell(stringHandler, expression);
			}
			
			if (name == fastAppend) {
				if (args.size() != 2) { Utils.error("Must have TWO arguments here: " + expression); }
				ConsCell arg1 = ConsCell.ensureIsaConsCell(stringHandler, simplify(args.get(0)));
				ConsCell arg2 = ConsCell.ensureIsaConsCell(stringHandler, simplify(args.get(1)));
				return ConsCell.append(arg1, arg2);
			} else if (name == fastUnion) {
				if (args.size() != 2) { Utils.error("Must have TWO arguments here: " + expression); }
				ConsCell arg1 = ConsCell.ensureIsaConsCell(stringHandler, simplify(args.get(0)));
				ConsCell arg2 = ConsCell.ensureIsaConsCell(stringHandler, simplify(args.get(1)));
				return ConsCell.union(arg1, arg2);
			} else if (name == fastIntersection) {
				if (args.size() != 2) { Utils.error("Must have TWO arguments here: " + expression); }
				ConsCell arg1 = ConsCell.ensureIsaConsCell(stringHandler, simplify(args.get(0)));
				ConsCell arg2 = ConsCell.ensureIsaConsCell(stringHandler, simplify(args.get(1)));
				return ConsCell.intersection(arg1, arg2);
			} 
			else if (name == first) { 
				if (args.size() != 1) { Utils.error("Must have ONE argument here: " + expression); }
				ConsCell arg1 = ConsCell.ensureIsaConsCell(stringHandler, simplify(args.get(0)));
				return arg1.first();
			}
			else if (name == rest) { 
				if (args.size() != 1) { Utils.error("Must have ONE argument here: " + expression); }
				ConsCell arg1 = ConsCell.ensureIsaConsCell(stringHandler, simplify(args.get(0)));
				return arg1.rest();
			}
			else if (name == push) { 
				if (args.size() != 2) { Utils.error("Must have TWO arguments here: " + expression); }
				Term     arg1 = stringHandler.simplify(args.get(0));
				ConsCell arg2 = ConsCell.ensureIsaConsCell(stringHandler, simplify(args.get(1)));
				return arg2.push(arg1);
			}
			else if (name == remove) { 
				if (args.size() != 2) { Utils.error("Must have TWO arguments here: " + expression); }
				Term     arg1 = stringHandler.simplify(args.get(0));
				ConsCell arg2 = ConsCell.ensureIsaConsCell(stringHandler, simplify(args.get(1)));
				return arg2.remove(arg1);
			}
			else if (name == nth) { 
				if (args.size() != 2) { Utils.error("Must have TWO arguments here: " + expression); }
				Term     arg1 = stringHandler.simplify(args.get(0));
				ConsCell arg2 = ConsCell.ensureIsaConsCell(stringHandler, simplify(args.get(1)));
				int      n    = ((NumericConstant) arg1).value.intValue();
				try {
                    return arg2.nth(n);
                }
                catch(Exception e) {
                    return null;
                }
			}
			else if (name == nthPlus1) { 
				if (args.size() != 2) { Utils.error("Must have TWO arguments here: " + expression); }
				Term     arg1 = stringHandler.simplify(args.get(0));
				ConsCell arg2 = ConsCell.ensureIsaConsCell(stringHandler, simplify(args.get(1)));
				int      n    = ((NumericConstant) arg1).value.intValue();
				return arg2.nth(n + 1);
			}
			else if (name == length) { 
				if (args.size() != 1) { Utils.error("Must have ONE argument here: " + expression); }

                Term simplifiedArg0 = simplify(args.get(0));

                if (simplifiedArg0 instanceof ConsCell) {
                    ConsCell consCell = (ConsCell) simplifiedArg0;
                    return stringHandler.getNumericConstant(consCell.length());
                }
                else {
                    return null;
                }
			}
			else if (name == position) { 
				if (args.size() != 2) { Utils.error("Must have TWO arguments here: " + expression); }
				Term     arg1 = stringHandler.simplify(args.get(0));
				ConsCell arg2 = ConsCell.ensureIsaConsCell(stringHandler, simplify(args.get(1)));
				return stringHandler.getNumericConstant(arg2.position(arg1));
			}
			else if (name == convertListToString) { 
				if (args.size() != 1) { Utils.error("Must have ONE argument here: " + expression); }
				ConsCell arg1 = ConsCell.ensureIsaConsCell(stringHandler, simplify(args.get(0)));
				return stringHandler.getStringConstant(arg1.toString(), false);
			}
            else {
                Utils.error("Cannot simplify, unknown name '" + name + "' in\n  " + expression);
                return null;
            }
		}
        else {
            return expression;
        }
	}

	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return "<this is an instance of the DoBuiltInListProcessing class>";
	}
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return "<this is an instance of the DoBuiltInListProcessing class>";
	}

	@Override
	public DoBuiltInMath applyTheta(Map<Variable, Term> bindings) {
		Utils.error("Should not call applyTheta on a DoBuiltInListProcessing.");
		return null;
	}

	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return 0;
	}

}
