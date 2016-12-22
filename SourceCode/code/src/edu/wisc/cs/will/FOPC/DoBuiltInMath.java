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
 * Differences from ISO Prolog (as per YAP's documentation 12/07: http://www.ncc.up.pt/~vsc/Yap/documentation.html)
 * 
 *   /@ is integer division instead of // (since that is a comment to us)
 *   several items from Java's Math class ARE included (e.g., toDegreesFunction)
 *   
 *   These are NOT implemented:
 *   	float(X)
 *		float_fractional_part(X)
 *		float_integer_part(X)
 *		X /\ Y  [Integer bitwise conjunction]
 *		X \/ Y  [Integer bitwise disjunction]
 *		X #  Y  [Integer bitwise exclusive disjunction]
 *		X >> Y  [Integer bitwise right logical shift of X by Y places]
 *		\ X     [Integer bitwise negation]
 *
 *		
 *	This generally produces DOUBLES, which isn't ideal, but we'll live with it for now.
 *  The use of the built-in function 'int' can override this.  (TODO if all args are int's keep as an int?)
 *  
 *  To EXTEND this class, "cut-and-paste" from what is done here.
 *  ALSO (a) before to call super() when creating instances of the new class and 
 *       (b) call this class's simplify() method if the new class encounters an unknown function name.
 *       
 *  TODO Build a simpler-to-use mechanism for allowing users to extend the set of built-in math functions.
 *  TODO this code is a memory hog and needs to be cleaned up (eg, this design keeps all calculations encountered, including intermediate ones, as strings.
 *        
 */
public class DoBuiltInMath extends AllOfFOPC {

    protected DoBuiltInListProcessing listHandler = null;

    private HandleFOPCstrings stringHandler;

    private Map<FunctionName, Set<Integer>> canHandle = new HashMap<FunctionName, Set<Integer>>(16);

    /**
     *
     * Reduce an arithmetic expression, producing a NumericConstant node.   Throw an error if any variables encountered where a number is needed.
     * Can NOT use statics since the function names will be different instances for each string handler.
     *
     */
    public DoBuiltInMath(HandleFOPCstrings stringHandler) {
        this.stringHandler = stringHandler;

        addFunctionName("integer", 1); // Allow the user to force integer results.
        addFunctionName("mod", 2); // Use Java's definition of mod.  Don't use a single-character symbol due to confusion between Java and Prolog.
        addFunctionName("min", 2);
        addFunctionName("max", 2);
        addFunctionName("abs", 1);
        addFunctionName("sin", 1);
        addFunctionName("cos", 1);
        addFunctionName("tan", 1);
        addFunctionName("sinh", 1);
        addFunctionName("cosh", 1);
        addFunctionName("tanh", 1);
        addFunctionName("asin", 1);
        addFunctionName("acos", 1);
        addFunctionName("atan", 1);
        addFunctionName("atan2", 1);
        addFunctionName("log", 1);
        addFunctionName("log", 2); // With TWO arguments, the second is the BASE.
        addFunctionName("exp", 1);
        addFunctionName("exp", 2); // With TWO arguments, is 'pow' (ie, X^Y).
        addFunctionName("pow", 2);
        addFunctionName("sqrt", 1);
        addFunctionName("sqrtSafe", 1);
        addFunctionName("sqrtAbs", 1);
        addFunctionName("random", 0);
        addFunctionName("ceiling", 1); // Also use 'ceil' since that is Java's name.
        addFunctionName("floor", 1);
        addFunctionName("round", 1);
        addFunctionName("sign", 1);
        addFunctionName("hypot", 1);
        addFunctionName("toDegrees", 1);
        addFunctionName("toRadians", 1);
        addFunctionName("length", 1); // Explicitly list those list-processing functions that return numbers.
        addFunctionName("position", 2);
    }

    public final void addFunctionName(String fNameString, int arity) {
        FunctionName fName = stringHandler.getFunctionName(fNameString);

        Set<Integer> lookup = canHandle.get(fName);
        if (lookup == null) {
            lookup = new HashSet<Integer>(4);
            canHandle.put(fName, lookup);
        }
        lookup.add(arity);
    }

    public boolean canHandle(FunctionName fName, int arity) {

        // Handle the odd ones...
        if (fName == stringHandler.standardPredicateNames.minFunction) {
            return true; // These are for all arities...
        }
        if (fName == stringHandler.standardPredicateNames.maxFunction) {
            return true;
        }
        if (fName == stringHandler.standardPredicateNames.plusFunction) {
            return true;
        }
        if (fName == stringHandler.standardPredicateNames.minusFunction) {
            return true;
        }
        if (fName == stringHandler.standardPredicateNames.timesFunction) {
            return true;
        }
        if (fName == stringHandler.standardPredicateNames.divideFunction) {
            return true;
        }
        if (fName == stringHandler.standardPredicateNames.intDivFunction) {
            return true;
        }

        Set<Integer> lookup = canHandle.get(fName);
        if (lookup == null) {
            return false;
        }
        return lookup.contains(arity);
    }

    public boolean canHandle(Term expression) {
        if (expression instanceof NumericConstant) {
            return true;
        }
        if (expression instanceof Function) {
            FunctionName fName = ((Function) expression).functionName;
            return canHandle(fName, ((Function) expression).numberArgs());
        }
        return false;
    }

    /**
     * Simplify a logical Term into a numeric constant.  Complain if this can't be done.
     * @param expression
     * @return The numeric constant that is the simplification of the given expression.
     */
    public NumericConstant simplify(Term expression) {
        if (expression instanceof NumericConstant) {
            return (NumericConstant) expression;
        }
        if (expression instanceof Function) {
            double result = simplifyAsDouble(expression);
            FunctionName fName = ((Function) expression).functionName;
            if (       fName == stringHandler.standardPredicateNames.intFunction 
            		|| fName == stringHandler.standardPredicateNames.signFunction
                    || fName == stringHandler.standardPredicateNames.intDivFunction
                    || fName == stringHandler.standardPredicateNames.roundFunction) {
                NumericConstant resultInt = stringHandler.getNumericConstant((int) result); // If the top-level request was to create an integer, then do so.
                //	Utils.println("  Simplifying as an int '" + expression + "' produces: " + Utils.comma((int) result) + "  " + resultInt);
                return resultInt;
            }
            NumericConstant result2 = stringHandler.getNumericConstant(result);
            //	Utils.println("  Simplifying '" + expression + "' produces: " + result2);
            return result2;
        }
		Utils.error("Cannot simplify: " + expression);
		return null;
    }

    /**
     * Do all the intermediate calculations using doubles.  The method above converts into a FOPC data structure at the end.
     * @param expression
     * @return A double, the result of computing the given expression.
     */
    private double simplifyAsDouble(Term expression) {
    	
        if (expression instanceof NumericConstant) {
            return ((NumericConstant) expression).value.doubleValue();
        }
        if (expression instanceof Function) {
            FunctionName name = ((Function) expression).functionName;
            List<Term>   args = ((Function) expression).getArguments();

            if (name == stringHandler.standardPredicateNames.intFunction) { // Can this be a big switch?
                if (args.size() > 1) {
                    Utils.error("Can only have ONE argument here: " + expression);
                }
                return ((int) simplifyAsDouble(args.get(0)));
            }
            else if (name == stringHandler.standardPredicateNames.plusFunction) {
                double total = 0.0;
                for (Term arg : args) {
                    total += simplifyAsDouble(arg);
                }
                return total;
            }
            else if ((name == stringHandler.standardPredicateNames.minusFunction || name == stringHandler.standardPredicateNames.minus2Function) && args.size() == 1) { // If only one argument, interpret as negation.
                return -simplify(args.get(0)).value.doubleValue();
            }
            else if (name == stringHandler.standardPredicateNames.minusFunction || name == stringHandler.standardPredicateNames.minus2Function) { // If a list of arguments, SUBTRACT all but the first from the first.	I.e. -(16, 4, 2) = (16 - 4) - 2 = 10.
                double  total    = 0.0;
                boolean firstArg = true;
                //Utils.println("%  MINUS args: " + args);
                for (Term arg : args) {
                    if (firstArg) {
                        firstArg = false;
                        total = simplifyAsDouble(arg);
                    }
                    else {
                        total -= simplifyAsDouble(arg);
                    }
                }
                return total;
            }
            else if (name == stringHandler.standardPredicateNames.timesFunction) {
                double total = 1.0;
                for (Term arg : args) {
                    total *= simplifyAsDouble(arg);
                }
                return total;
            }
            else if (name == stringHandler.standardPredicateNames.divideFunction) {	 // If a list of arguments, DIVIDE the first by all the rest.  I.e. /(16, 4, 2) = (16 / 4) / 2 = 2.
                double  total    = 1.0;
                boolean firstArg = true;
                for (Term arg : args) {
                    if (firstArg) {
                        firstArg = false;
                        total = simplifyAsDouble(arg);
                    }
                    else {
                        total /= simplifyAsDouble(arg);
                    }
                }
                return total;
            }
            else if (name == stringHandler.standardPredicateNames.intDivFunction) {	 // Integer division, though converted to double at end.
                int total = 1;
                boolean firstArg = true;
                for (Term arg : args) {
                    if (firstArg) {
                        firstArg = false;
                        total = (int) simplifyAsDouble(arg);
                    }
                    else {
                        total /= (int) simplifyAsDouble(arg);
                    }
                }
                return total;
            }
            else if (name == stringHandler.standardPredicateNames.modFunction) {
                if (args.size() > 2) {
                    Utils.error("Can only have TWO arguments here: " + expression);
                }
                double arg0 = simplifyAsDouble(args.get(0));
                double arg1 = simplifyAsDouble(args.get(1));

                return arg0 % arg1; // Java's mod.
            }
            else if (name == stringHandler.standardPredicateNames.maxFunction) { // Handle ANY number of arguments.
                double maxValue = Double.NEGATIVE_INFINITY;
                for (Term arg : args) {
                    double temp = simplifyAsDouble(arg);
                    if (temp > maxValue) {
                        maxValue = temp;
                    }
                }
                return maxValue;
            }
            else if (name == stringHandler.standardPredicateNames.minFunction) {
                double minValue = Double.POSITIVE_INFINITY;
                for (Term arg : args) { // Handle ANY number of arguments.
                    double temp = simplifyAsDouble(arg);
                    if (temp < minValue) {
                        minValue = temp;
                    }
                }
                return minValue;
            }
            else if (name == stringHandler.standardPredicateNames.absFunction) {
                if (args.size() != 1) {
                    Utils.error("Can only have ONE argument here: " + expression);
                }
                return Math.abs(simplifyAsDouble(args.get(0)));
            }
            else if (name == stringHandler.standardPredicateNames.sinFunction) {
                if (args.size() != 1) {
                    Utils.error("Can only have ONE argument here: " + expression);
                }
                return Math.sin(simplifyAsDouble(args.get(0)));
            }
            else if (name == stringHandler.standardPredicateNames.cosFunction) {
                if (args.size() != 1) {
                    Utils.error("Can only have ONE argument here: " + expression);
                }
                return Math.cos(simplifyAsDouble(args.get(0)));
            }
            else if (name == stringHandler.standardPredicateNames.tanFunction) {
                if (args.size() != 1) {
                    Utils.error("Can only have ONE argument here: " + expression);
                }
                return Math.tan(simplifyAsDouble(args.get(0)));
            }
            else if (name == stringHandler.standardPredicateNames.sinhFunction) {
                if (args.size() != 1) {
                    Utils.error("Can only have ONE argument here: " + expression);
                }
                return Math.sinh(simplifyAsDouble(args.get(0)));
            }
            else if (name == stringHandler.standardPredicateNames.coshFunction) {
                if (args.size() != 1) {
                    Utils.error("Can only have ONE argument here: " + expression);
                }
                return Math.cosh(simplifyAsDouble(args.get(0)));
            }
            else if (name == stringHandler.standardPredicateNames.tanhFunction) {
                if (args.size() != 1) {
                    Utils.error("Can only have ONE argument here: " + expression);
                }
                return Math.tanh(simplifyAsDouble(args.get(0)));
            }
            else if (name == stringHandler.standardPredicateNames.asinFunction) {
                if (args.size() != 1) {
                    Utils.error("Can only have ONE argument here: " + expression);
                }
                return Math.asin(simplifyAsDouble(args.get(0)));
            }
            else if (name == stringHandler.standardPredicateNames.acosFunction) {
                if (args.size() != 1) {
                    Utils.error("Can only have ONE argument here: " + expression);
                }
                return Math.acos(simplifyAsDouble(args.get(0)));
            }
            else if (name == stringHandler.standardPredicateNames.atanFunction) {
                if (args.size() != 1) {
                    Utils.error("Can only have ONE argument here: " + expression);
                }
                return Math.atan(simplifyAsDouble(args.get(0)));
            }
            else if (name == stringHandler.standardPredicateNames.atan2Function) {
                if (args.size() != 2) {
                    Utils.error("Can only have TWO arguments here: " + expression);
                }
                return Math.atan2(simplifyAsDouble(args.get(0)), simplifyAsDouble(args.get(1)));
            }
            else if (name == stringHandler.standardPredicateNames.logFunction) {
                if (args.size() == 1) {
                    return Math.log(simplifyAsDouble(args.get(0)));
                }
                if (args.size() != 2) {
                    Utils.error("Can only have ONE or TWO arguments here: " + expression);
                } // Arg 2 is the base.
                // log_base(X) = log_k(X) / log_k(base) for any k.
                return Math.log(simplifyAsDouble(args.get(0))) / Math.log(simplifyAsDouble(args.get(1)));
            }
            else if (name == stringHandler.standardPredicateNames.expFunction) {
                if (args.size() == 1) {
                    return Math.exp(simplifyAsDouble(args.get(0)));
                }
                if (args.size() != 2) {
                    Utils.error("Can only have ONE or TWO arguments here: " + expression);
                }
                return Math.pow(simplifyAsDouble(args.get(1)), Math.log(simplifyAsDouble(args.get(0)))); // Arg 2 is the base.
            }
            else if (name == stringHandler.standardPredicateNames.sqrtFunction) {
                if (args.size() != 1) {
                    Utils.error("Can only have ONE argument here: " + expression);
                }
                return Math.sqrt(simplifyAsDouble(args.get(0)));
            }
            else if (name == stringHandler.standardPredicateNames.sqrtSafeFunction) {
                if (args.size() != 1) {
                    Utils.error("Can only have ONE argument here: " + expression);
                }
                return Math.sqrt(Math.max(0, simplifyAsDouble(args.get(0))));
            }
            else if (name == stringHandler.standardPredicateNames.sqrtAbsFunction) {
                if (args.size() != 1) {
                    Utils.error("Can only have ONE argument here: " + expression);
                }
                return Math.sqrt(Math.abs(simplifyAsDouble(args.get(0))));
            }
            else if (name == stringHandler.standardPredicateNames.powFunction || name == stringHandler.standardPredicateNames.starStarFunction) {
                if (args.size() != 2) {
                    Utils.error("Can only have TWO arguments here: " + expression);
                }
                return Math.pow(simplifyAsDouble(args.get(0)), simplifyAsDouble(args.get(1)));
            }
            else if (name == stringHandler.standardPredicateNames.randomFunction) {
                if (!args.isEmpty()) {
                    Utils.error("Can only have ZERO arguments here: " + expression);
                }
                return Utils.random();
            }
            else if (name == stringHandler.standardPredicateNames.ceilFunction) {
                if (args.size() != 1) {
                    Utils.error("Can only have ONE argument here: " + expression);
                }
                return Math.ceil(simplifyAsDouble(args.get(0)));
            }
            else if (name == stringHandler.standardPredicateNames.floorFunction) {
                if (args.size() != 1) {
                    Utils.error("Can only have ONE argument here: " + expression);
                }
                return Math.floor(simplifyAsDouble(args.get(0)));
            }
            else if (name == stringHandler.standardPredicateNames.signFunction) {
                if (args.size() != 1) {
                    Utils.error("Can only have ONE argument here: " + expression);
                }
                double result = simplifyAsDouble(args.get(0));
                if (result > 0) {
                    return 1.0;
                }
                if (result < 0) {
                    return -1.0;
                }
                return 0.0;
            }
            else if (name == stringHandler.standardPredicateNames.roundFunction) {
                if (args.size() != 1) {
                    Utils.error("Can only have ONE argument here: " + expression);
                }
                return Math.round(simplifyAsDouble(args.get(0)));
            }
            else if (name == stringHandler.standardPredicateNames.hypotFunction) {
                if (args.size() != 1) {
                    Utils.error("Can only have ONE argument here: " + expression);
                }
                return Math.hypot(simplifyAsDouble(args.get(0)), simplifyAsDouble(args.get(1)));
            }
            else if (name == stringHandler.standardPredicateNames.toDegreesFunction) {
                if (args.size() != 1) {
                    Utils.error("Can only have ONE argument here: " + expression);
                }
                return Math.toDegrees(simplifyAsDouble(args.get(0)));
            }
            else if (name == stringHandler.standardPredicateNames.toRadiansFunction) {
                if (args.size() != 1) {
                    Utils.error("Can only have ONE argument here: " + expression);
                }
                return Math.toRadians(simplifyAsDouble(args.get(0)));
            }
            else if (name == stringHandler.standardPredicateNames.pullOutNthArgFunction) {
                if (args.size() != 2) {
                    Utils.error("Must have two arguments here: " + expression);
                }
                NumericConstant index = (NumericConstant) args.get(0);
                Function arg1 = (Function) args.get(1);
                return simplifyAsDouble(arg1.getArgument(index.value.intValue()));
            }
            else if (name == stringHandler.standardPredicateNames.lengthFunction || name == stringHandler.standardPredicateNames.positionFunction) {
                Term result = listHandler.simplify(expression);

                if (result instanceof NumericConstant) {
                    return ((NumericConstant) result).value.doubleValue();
                }
                Utils.error("Unknown result of processing " + expression + "\n " + result);
            }
            Utils.error("Unknown math operator: " + name);
        } else if (expression instanceof SentenceAsTerm) {
        	Sentence s = ((SentenceAsTerm) expression).sentence;
        	if (s instanceof Clause) {
        		Clause c = (Clause) s;
        		if (c.getLength() == 1 && c.isDefiniteClause()) {
        			Literal lit = c.getPosLiteral(0);
        			Function  f = lit.asFunction();
        			return simplifyAsDouble(f);
        		}
        		Utils.error("Cannot simplify: (class = " + ((SentenceAsTerm) expression).sentence.getClass() + ")\n  clause = " + c);
        	}
        	Utils.error("Cannot simplify: (class = " + ((SentenceAsTerm) expression).sentence.getClass() + ")\n  sentence = " + s);
        } else if (expression instanceof StringConstant) {
        	try {
        		return Double.parseDouble(expression.toString()); // JWS added this June 2011 because the next ELSE had an error, so we might as well try this before throwing that error.
        	} catch (NumberFormatException e) {
        		Utils.error("Cannot simplify: (class = " + expression.getClass() + ")\n  " + expression);
        	}
        }
        else {
            Utils.error("Cannot simplify: (class = " + expression.getClass() + ")\n  " + expression);
        }
        return Double.NaN;
    }

    public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
        return "<this is an instance of the DoBuiltInMath class>";
    }

    public String toString(int precedenceOfCaller, BindingList bindingList) {
        return "<this is an instance of the DoBuiltInMath class>";
    }

    @Override
    public DoBuiltInMath applyTheta(Map<Variable, Term> bindings) {
        Utils.error("Should not call applyTheta on a DoBuiltInMath.");
        return null;
    }

    @Override
    public int countVarOccurrencesInFOPC(Variable v) {
        return 0;
    }
}
