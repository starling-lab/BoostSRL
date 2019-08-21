/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import java.io.BufferedReader;
import java.io.IOException;
import java.text.DateFormat;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashSet;
import java.util.List;
import java.util.StringTokenizer;
import java.util.TimeZone;

import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.StateBasedSearchTask; 

/**
 * @author shavlik 
 * 
 * Many of the ISO predicates are implemented.  Some differences among this code, Java, and ISO Prolog:
 * 
 *  not    is in YAP Prolog (though not in ISO Prolog).  In this code it is treated as the logical NOT (and hence
 *         cannot be used in Horn-clause resolution theorem proving).  The ISO standard for negation-by-failure ('\+(p)') is supported, even though this is quite ugly syntax.
 *         
 *  !      means Prolog's 'cut' and not Java's negation ('~' and 'not' can be used instead).
 *         
 *  ;      this code uses ';' as end-of-line (EOL).  These can be used for "or" instead: { 'or' 'v' 'else' }
 *         (note that 'v' [and 'V"] cannot be a variable or constant name). 
 *         
 *  P -> Q ; R  since this code uses '->' as implication and ';' as end-of-line (EOL), it instead uses
 *              'P then Q else R' (where the 'else R' is optional, just like '; R' is optional in ISO Prolog). 
 * 
 *  once() can take a full conjunctive sentence as its argument, e.g. 'once(p, q)' whereas Prolog requires there only be one argument, e.g., 'once((p, q))'. 
 *         This code's once() currently can only accept conjunctive sentences (or single literals).
 *         
 * 	mod    is used instead of Java's '%' since '%' is a comment in Prolog (and in this code)      
 * 
 * The flag 'lowercaseMeansVariable' allows one to choose between standard logical syntax and Prolog's syntax (in Prolog, variables are uppercase).
 * 
 * Also see this project's class DoBuiltInMath and DoBuiltInListProcessing.
 * 
 * These ISO predicates in YAP are not implemented (an incomplete list):  See http://www.ncc.up.pt/~vsc/Yap/documentation.html
 * 	initialization
 *  public
 *  P ; Q  ['P or Q' is implemented]
 *  'P -> Q' and 'P -> Q ; R'  [ "P then Q" and "P then Q else R"  since '->' is also used as implication
 *  catch
 *  throw
 *  atom_chars(?A,?L)
 *  atom_codes(?A,?L)
 *  number_codes(?A,?L)
 *  char_code(?A,?I)
 *  sub_atom(+A,?Bef, ?Size, ?After, ?At_out)
 *  arg(+N,+T,A)
 *  unify_with_occurs_check(?T1,?T2) (this is an easy fix if needed, but means there'll be another boolean in unify [which need to be fast], or duplicated code)
 *  X @< Y, X @=< Y, X @> Y, X @>= Y 
 *  
 *  
 * Some more to maybe add:
 * 	catch and throw
 *  if(p,q,r) P -> Q ; R
 *  treat 'bare' X's as call(X)'s (X must be a constant or a function)
 *  
 *  asserta see http://www.ncc.up.pt/~vsc/Yap/documentation.html
 *  assertz
 *  abolish
 *  clause
 *  retract
 *  
 *  ensure_loaded
 *  include
 *  multifile
 *  discontiguous
 *  
 *  in prolog mode ';' should be OR!
 *  
 *  :- p, q. [process these when parsing the file, or right afterwards?]
 *  
 *  
 *  file open, close, read, write, exists  <-- call Java's 
 *  format <-- call Java's
 *  
 *  sort - put in a library with the others in this group
 *  keysort
 *  
 *  check YAP's math and collect allCollector the ISO's
 *  
 *
 */
public class BuiltinProcedurallyDefinedPredicateHandler extends ProcedurallyDefinedPredicateHandler {

    private static final BindingList FAIL = null;

    HandleFOPCstrings stringHandler;


    private DateFormat       dateTimeInstance;
    private DateFormat       dateInstance;
    private SimpleDateFormat simpleDateformat;

	/**
	 * The job of this class is to evaluate procedurally defined (i.e., built-in) predicates.
     *
     * @param stringHandler 
     */
	public BuiltinProcedurallyDefinedPredicateHandler(HandleFOPCstrings stringHandler) {
        this.stringHandler = stringHandler;

        createBuiltins(stringHandler);
	}
	
	/**
         * Create the hash map that contains allCollector of the built-in
         * ("procedurally defined") predicates. If someone extends this class,
         * but sure to call this first, then add the PredicateName's of the new
         * built-ins to the hash map before returning it.
         */
	private void createBuiltins(HandleFOPCstrings stringHandler) {
		boolean hold_cleanFunctionAndPredicateNames = stringHandler.cleanFunctionAndPredicateNames;
		stringHandler.cleanFunctionAndPredicateNames = false;
		hashOfSupportedPredicates = new HashSet<PredicateNameAndArity>(64);

		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.dateToString,      2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.dateToUTCstring,   2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.dateToMRstring,    2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.convertDateToLong, 2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.isa_variable, 1));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.isa_constant, 1));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.isa_numericConstant, 1));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.isa_stringConstant, 1));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.readEvalPrint, 4));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.var,    1));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.nonvar, 1));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.list, 1));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.number, 1));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.isaInteger, 1));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.isaFloat,   1));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.isaDouble,  1));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.atomic, 1));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.atom,   1));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.is,     2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.equal,  2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.equal2, 2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.diff,      2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.notEqual,  2));
//		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.not,       1));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.ground,    1));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.copyTerm,    2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.unify,       2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.unify2,      2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.ununifiable, 2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.ununifiable2,2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.gt,2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.lt,2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.gte,2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.lte,2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.gt2,2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.lt2,2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.lte2,2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.gte2,2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.lte3,2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.equalNumbers,2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.notEqualNumbers,2));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.halt,0));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.halt,1));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.equalDotDot,2));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.findAllCollector,2));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.findAllCollector,3));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.allCollector,2));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.allCollector,3));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.bagOfCollector,3));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.setOfCollector,3));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.countProofsCollector,2));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.countProofsCollector,3));
		hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.countUniqueBindingsCollector,2));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.countUniqueBindingsCollector,3));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.first,2));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.rest,2));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.push,3));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.remove,3));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.reverse,2));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.sort,2));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.length,2));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.nth,3));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.nthPlus1,3));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.appendFast,           3));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.intersectionFast,     3));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.unionFast,            3));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.listsEquivalent,  1));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.addListOfNumbers, 2));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.multListOfNumbers,2));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.assertName, 1));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.assertifnotName, 1));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.assertifunknownName, 1));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.atomConcat, 3));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.atomLength, 2));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.atomChars,  2));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.tokenizeString,  2));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.setCounter,   1));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.setCounterB,  1));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.setCounterC,  1));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.setCounterD,  1));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.setCounterE,  1));
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.incrCounter,  2)); // Value goes into second argument.  Use incrCounter(0, ?X) to read.
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.incrCounterB, 2)); // Value goes into second argument.  Use incrCounter(0, ?X) to read.
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.incrCounterC, 2)); // Value goes into second argument.  Use incrCounter(0, ?X) to read.
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.incrCounterD, 2)); // Value goes into second argument.  Use incrCounter(0, ?X) to read.
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.incrCounterE, 2)); // Value goes into second argument.  Use incrCounter(0, ?X) to read.
        hashOfSupportedPredicates.add(new PredicateNameAndArity(stringHandler.standardPredicateNames.createUniqueStringConstant, 2));

		stringHandler.cleanFunctionAndPredicateNames = hold_cleanFunctionAndPredicateNames;
	}

    @Override
    public boolean canHandle(PredicateName predicateName, int arity) {
        if ( super.canHandle(predicateName, arity) ) return true;

        // Handle the odd ones...
        if ( predicateName == stringHandler.standardPredicateNames.print )    return true; // These are for allCollector arities...
        if ( predicateName == stringHandler.standardPredicateNames.write )    return true;
        if ( predicateName == stringHandler.standardPredicateNames.waitHere ) return true;

        

        if ( stringHandler != null && stringHandler.getUserDefinedLiteral(predicateName, arity) != null) return true;

        return false;
    }
	
	/**
	 *  This handler manages built-in's like equals, diff, <, >, <=, >=, etc.  Note that these return BINDING LISTS and not Booleans.
	 */
	public BindingList handle(HornClauseContext context, Literal literal, Unifier unifier, BindingList bindingList) throws SearchInterrupted {
		PredicateName pred = literal.predicateName;
		List<Term>    args = literal.getArguments();
		int       numbArgs = literal.numberArgs();

        BindingList TRUE = bindingList;
		
		// Utils.println("handle: " + literal + "\n  with bindings = " + bindingList);
		
        UserDefinedLiteral match = context.getStringHandler().getUserDefinedLiteral(pred, numbArgs);
        
        // Trevor: should we set stringHandler=context.getStringHandler() here?  JWS (6/11)
        if ( match != null ) {
        	//Utils.waitHere("User defined literal: " + match);
			return match.handleUserDefinedLiteral(literal, unifier, bindingList, context);
		}
		if ((pred == stringHandler.standardPredicateNames.unify || pred == stringHandler.standardPredicateNames.unify2) && numbArgs == 2) {
			return unifier.unify(args.get(0), args.get(1), bindingList);
		}
		if ((pred == stringHandler.standardPredicateNames.equal || pred == stringHandler.standardPredicateNames.equal2) && numbArgs == 2) {  // This is '==' - must be equal w/o unification.
			if (args.get(0) == args.get(1)) { return bindingList; }
			if (args.get(0) == null)        { return null; }
			return (args.get(0).equals(args.get(1)) ? bindingList : null);
		}
		if ((pred == stringHandler.standardPredicateNames.diff || pred == stringHandler.standardPredicateNames.notEqual) && numbArgs == 2) {
			if (args.get(0) == args.get(1)) { return null; }
			if (args.get(0) == null)        { return bindingList; }
			return (args.get(0).equals(args.get(1)) ? null : bindingList);
		}
		if ((pred == stringHandler.standardPredicateNames.ununifiable || pred == stringHandler.standardPredicateNames.ununifiable2)  && numbArgs == 2) { // Succeeds if arg0 and arg1 do not unify.
			// Cannot allow the bindingList to be modified, so need a copy.  (Might be able to get away without using the oldBindingList, since that should have been applied, but play it safe.)
			BindingList copyOfBindings = bindingList.copy();
			if (unifier.unify(args.get(0), args.get(1), copyOfBindings) == null) { return bindingList; }
			return null;
		}
		if (pred == stringHandler.standardPredicateNames.is && numbArgs == 2) {
			Term result = context.getStringHandler().simplify(args.get(1));
			return result == null ? null : unifier.unify(args.get(0), result, bindingList);
		}
		if ((pred == stringHandler.standardPredicateNames.var || pred == stringHandler.standardPredicateNames.isa_variable) && numbArgs == 1) {
			return (args.get(0) instanceof Variable ? bindingList : null);
		}
		if (pred == stringHandler.standardPredicateNames.nonvar && numbArgs == 1) {
			return (args.get(0) instanceof Variable ? null : bindingList);
		}
		if (pred == stringHandler.standardPredicateNames.list && numbArgs == 1) {
			return (args.get(0) instanceof ConsCell ? bindingList : null);
		}
		if ((pred == stringHandler.standardPredicateNames.atom   || pred == stringHandler.standardPredicateNames.isa_stringConstant) && numbArgs == 1) {
			return (args.get(0) instanceof StringConstant ? bindingList : null);
		}
		if ((pred == stringHandler.standardPredicateNames.atomic || pred == stringHandler.standardPredicateNames.isa_constant) && numbArgs == 1) {
			return (args.get(0) instanceof Constant ? bindingList : null);
		}
		if (pred == stringHandler.standardPredicateNames.compound && numbArgs == 1) {
			return (args.get(0) instanceof Function ? bindingList : null);
		}
		if ((pred == stringHandler.standardPredicateNames.number || pred == stringHandler.standardPredicateNames.isa_numericConstant) && numbArgs == 1) {
			return (args.get(0) instanceof NumericConstant ? bindingList : null);
		}
		if ((pred == stringHandler.standardPredicateNames.isaInteger || pred == stringHandler.standardPredicateNames.isa_numericConstant) && numbArgs == 1) {
			if (args.get(0) instanceof NumericConstant && ((NumericConstant) args.get(0)).isaInteger()) {
				return bindingList;
			}
			return null;
		}
		if ((pred == stringHandler.standardPredicateNames.isaFloat || pred == stringHandler.standardPredicateNames.isa_numericConstant) && numbArgs == 1) {
			if (true) { Utils.error("There are no float's in this code.  Only int's and double's.  You used float() in your Prolog code."); }
			if (args.get(0) instanceof NumericConstant && ((NumericConstant) args.get(0)).isaFloat()) {
				return bindingList;
			}
			return null;
		}
		if ((pred == stringHandler.standardPredicateNames.isaDouble || pred == stringHandler.standardPredicateNames.isa_numericConstant) && numbArgs == 1) {
			if (args.get(0) instanceof NumericConstant && ((NumericConstant) args.get(0)).isaDouble()) {
				return bindingList;
			}
			return null;
		}
		if ((pred == stringHandler.standardPredicateNames.gt || pred == stringHandler.standardPredicateNames.gt2) && numbArgs == 2) {
			confirmAllVarsAreBound("gt: ", args, true);
			if (!(args.get(0) instanceof NumericConstant) || !(args.get(1) instanceof NumericConstant)) { Utils.error("Both args must be numbers: " + literal); }
			double value1 = ((NumericConstant) args.get(0)).value.doubleValue();
			double value2 = ((NumericConstant) args.get(1)).value.doubleValue();
			return (value1 > value2 ? bindingList : null);
		}
		if ((pred == stringHandler.standardPredicateNames.lt || pred == stringHandler.standardPredicateNames.lt2)  && numbArgs == 2) {
			confirmAllVarsAreBound("lt: ", args, true);
			if (!(args.get(0) instanceof NumericConstant) || !(args.get(1) instanceof NumericConstant)) { Utils.error("Both args must be numbers: " + literal); }
			double value1 = ((NumericConstant) args.get(0)).value.doubleValue();
			double value2 = ((NumericConstant) args.get(1)).value.doubleValue();
			return (value1 < value2 ? bindingList : null);
		}
		if ((pred == stringHandler.standardPredicateNames.gte || pred == stringHandler.standardPredicateNames.gte2) && numbArgs == 2) {
			confirmAllVarsAreBound("gte: ", args, true);
			if (!(args.get(0) instanceof NumericConstant) || !(args.get(1) instanceof NumericConstant)) { Utils.error("Both args must be numbers: " + literal); }
			double value1 = ((NumericConstant) args.get(0)).value.doubleValue();
			double value2 = ((NumericConstant) args.get(1)).value.doubleValue();
			return (value1 >= value2 ? bindingList : null);
		}
		if ((pred == stringHandler.standardPredicateNames.lte || pred == stringHandler.standardPredicateNames.lte2 || pred == stringHandler.standardPredicateNames.lte3) && numbArgs == 2) {
			confirmAllVarsAreBound("lte: ", args, true);
			if (!(args.get(0) instanceof NumericConstant) || !(args.get(1) instanceof NumericConstant)) { Utils.error("Both args must be numbers: " + literal); }
			double value1 = ((NumericConstant) args.get(0)).value.doubleValue();
			double value2 = ((NumericConstant) args.get(1)).value.doubleValue();
			return (value1 <= value2 ? bindingList : null);
		}
		if (pred == stringHandler.standardPredicateNames.equalNumbers && numbArgs == 2) {
			confirmAllVarsAreBound("equalNumbers: ", args, true);
			if (!(args.get(0) instanceof NumericConstant) || !(args.get(1) instanceof NumericConstant)) { Utils.error("Both args must be numbers: " + literal); }
			double value1 = ((NumericConstant) args.get(0)).value.doubleValue();
			double value2 = ((NumericConstant) args.get(1)).value.doubleValue();
			return (value1 == value2 ? bindingList : null);
		}
		if (pred == stringHandler.standardPredicateNames.notEqualNumbers && numbArgs == 2) {
			confirmAllVarsAreBound("notEqualNumbers: ", args, true);
			if (!(args.get(0) instanceof NumericConstant) || !(args.get(1) instanceof NumericConstant)) { Utils.error("Both args must be numbers: " + literal); }
			double value1 = ((NumericConstant) args.get(0)).value.doubleValue();
			double value2 = ((NumericConstant) args.get(1)).value.doubleValue();
			return (value1 != value2 ? bindingList : null);
		}
		if (pred == stringHandler.standardPredicateNames.print || pred == stringHandler.standardPredicateNames.write) {
			//Utils.println(args.toString() + ", |bl| = " + (bindingList == null ? "NULL" : Utils.getSizeSafely(bindingList.theta)));
			//if (bindingList != null && Utils.getSizeSafely(bindingList.theta) < 10) {
			//	Utils.println(" bl = " + bindingList.theta);
			//}
			if (args == null) { Utils.println(""); } else { Utils.println(pred.toString() + ":" + args); }
			return bindingList;
		}
		if (pred == stringHandler.standardPredicateNames.waitHere || pred == stringHandler.standardPredicateNames.wait) {
			Utils.waitHere(args.toString()); // Should we FORCE a wait?  Probably not since this would likely be used for debugging.
			return bindingList;
		}
		if (pred == stringHandler.standardPredicateNames.equalDotDot && numbArgs == 2) { // Note: the function name is returned as a StringConstant.
			if (args.get(0) instanceof Function) {
				Function       f     = (Function) args.get(0);
				FunctionName   fName = f.functionName;
				List<Term>     fArgs = f.getArguments();
				StringConstant f2    = context.getStringHandler().getStringConstant(fName.name);
				fArgs.add(0, f2); // Push the function name on the front.
				ConsCell consCell = ConsCell.convertListToConsCell(context.getStringHandler(), fArgs);
				return unifier.unify(consCell, args.get(1), bindingList);
			}
			Utils.error("In a '=..' the first argument must be a function.  You provided: '" + literal);
		}
		if (pred == stringHandler.standardPredicateNames.findAllCollector) {
			if (numbArgs == 2) { // We're collecting allCollector answers in this phase.
				Term         term           =                args.get(0);
				ObjectAsTerm collector      = (ObjectAsTerm) args.get(1);
				ConsCell     termsCollected = (ConsCell)     collector.item; 
				// Collect ALL proofs of goal, which must be a literal or a conjunct - actually, a clause with only negative literals.
				// And for each proof, save 'term' (which presumably shares variables with 'goal') in a list.
				// Unify this list with 'list' as the final step.
				ConsCell consCell = context.getStringHandler().getConsCell(term, termsCollected, null);
				//int len = consCell.length();if (len % 100 == 0) { Utils.println("  |findAll| = " + len); }
				collector.item = consCell;
			//	Utils.println("  @findAll: " + args);
				return null;
			}
			else if (numbArgs == 3) { // We're processing the collection of answers in this phase.
				Term         list      =                args.get(0);
				ObjectAsTerm collector = (ObjectAsTerm) args.get(1);
				ConsCell     answers   = (ConsCell)     collector.item;
				//int len = answers.length();
				//if (true) { Utils.println("  |answers| = " + len); }
				BindingList  result    = unifier.unify(list, (answers == null ? null : answers.reverse()), bindingList); // Need to reverse since collecting pushes.
			//	Utils.println("  @findAllCollector: results = " + result + " answer = " + answers);
				return result;
			}
			Utils.error("Wrong number of arguments (expecting 2 or 3): '" + literal + "'.");
		}
		if (pred == stringHandler.standardPredicateNames.allCollector) {
			if (numbArgs == 2) { // We're collecting allCollector answers in this phase.
				Term         term           =                args.get(0);
				ObjectAsTerm collector      = (ObjectAsTerm) args.get(1);
				ConsCell     termsCollected = (ConsCell)     collector.item;  
				// Collect ALL proofs of goal, which must be a literal or a conjunct - actually, a clause with only negative literals.
				// And for each proof, save 'term' (which presumably shares variables with 'goal') in a list.
				// Unify this list with 'list' as the final step.
				if (termsCollected.memberViaEquals(term)) { // Need to do a equivalent match since term could be complex (e.g., a Function).
					return null; // Remove duplicates.
				}
				collector.item = context.getStringHandler().getConsCell(term, termsCollected, null);
			//	Utils.println("  @allCollector2 [" + (termsCollected.length() + 1) + "]: " + args);
				return null;
			}
			else if (numbArgs == 3) { // We're processing the collection of answers in this phase.
				Term         list      =                args.get(0);
				ObjectAsTerm collector = (ObjectAsTerm) args.get(1);
				ConsCell     answers   = (ConsCell)     collector.item;
				BindingList  result    = unifier.unify(list, (answers == null ? null : answers.reverse()), bindingList); // Need to reverse since collecting pushes.
			//	Utils.println("  @allCollector3 [" + (answers == null ? 0 : answers.length()) + "]: results = " + result + " answer = " + answers);
				return result;
			}
			Utils.error("Wrong number of arguments (expecting 2 or 3): '" + literal + "'.");
		}
		if (pred == stringHandler.standardPredicateNames.bagOfCollector   && numbArgs == 3) {
			Utils.error("'bagof' is not yet implemented");
		}
		if (pred == stringHandler.standardPredicateNames.setOfCollector   && numbArgs == 3) {
			Utils.error("'setof' is not yet implemented");
		}
		if (pred == stringHandler.standardPredicateNames.countProofsCollector) {
			if (numbArgs == 2) { // We're collecting allCollector answers in this phase.
				ObjectAsTerm collector      = (ObjectAsTerm) args.get(1);
				ConsCell     termsCollected = (ConsCell)     collector.item; 
				// COUNT ALL proofs of goal, which must be a literal or a conjunct - actually, a clause with only negative literals.
				// Only need to store a NUMBER here.  (For countUniqueBindingCollector we need to save allCollector the bindings, since we need to look for duplicates.)
				//Utils.println("collector = " + collector);
				if (termsCollected.length() < 1) { collector.item = context.getStringHandler().getConsCell(context.getStringHandler().getNumericConstant(1), null); }
				else {
					int oldCount = ((NumericConstant) termsCollected.getArgument(0)).value.intValue();
					collector.item = context.getStringHandler().getConsCell(context.getStringHandler().getNumericConstant(oldCount + 1), null);
				}
				//Utils.println("    collector = " + collector);
				return null;
			}
			else if (numbArgs == 3) { // We're processing the collection of answers in this phase.
				Term         list      =                args.get(0);
				ObjectAsTerm collector = (ObjectAsTerm) args.get(1);
				ConsCell     answers   = (ConsCell)     collector.item;
				Term         counter   = (answers.length() < 1 ? context.getStringHandler().getNumericConstant(0) : answers.getArgument(0)); // Pull the number out of the cons cell.
				BindingList  result    = unifier.unify(list, counter, bindingList);
				return result;
			}
			Utils.error("Wrong number of arguments (expecting 2 or 3): '" + literal + "'.");
		}
		if (pred == stringHandler.standardPredicateNames.countUniqueBindingsCollector) {
			if (numbArgs == 2) { // We're collecting allCollector answers in this phase.
				Term         queryAsTerm    =                args.get(0);
				ObjectAsTerm collector      = (ObjectAsTerm) args.get(1);
				ConsCell     termsCollected = (ConsCell)     collector.item;  
				// Collect ALL proofs of goal, which must be a literal or a conjunct - actually, a clause with only negative literals.
				// Unify this list with 'list' as the final step.
				// Check for duplicates.
				//Utils.println("LITERAL = " + literal);
				//Utils.println(" termsCollected = " + termsCollected + " and collector = " + collector + " and queryAsTerm = " + queryAsTerm);
				if (termsCollected.memberViaEquals(queryAsTerm)) { // Need to do a equivalent match since term could be complex (e.g., a Function).
					return null;
				}
				//Utils.println("  @countUniqueBindingCollector: " + args);
				collector.item = context.getStringHandler().getConsCell(queryAsTerm, termsCollected, null);
				//Utils.println("  collector = " + collector);
				return null;
			}
			else if (numbArgs == 3) { // We're processing the collection of answers in this phase.
				Term         list      =                args.get(0);
				ObjectAsTerm collector = (ObjectAsTerm) args.get(1);
				ConsCell     answers   = (ConsCell)     collector.item;
				// Instead of returning the LIST of bindings, return the LENGTH of the list.
				BindingList  result    = unifier.unify(list, context.getStringHandler().getNumericConstant(answers.length()), bindingList);
				return result;
			}
			Utils.error("Wrong number of arguments (expecting 2 or 3): '" + literal + "'.");
		}
		if (pred == stringHandler.standardPredicateNames.ground  && numbArgs == 1) {
			return (args.get(0).isGrounded() ? bindingList : null);
		}
		if (pred == stringHandler.standardPredicateNames.copyTerm  && numbArgs == 2) {

            // TAW: I agree that the ISO definition does specify copy_term(?TI,-TF).  However,
            // TAW: this doesn't mean TF has to be a variable.  As with any Prolog call, even
            // TAW: if it is an "output" argument, you can always try to prove the goal with
            // TAW: the argument bound to something.  The - just means that the value will be
            // TAW: generated.
            // TAW: The '+' works a little different.  You must provide a non-free variable at
            // TAW: the time of evaluation.
            // TAW: The '?' basically means that if you provide it, it will be used in the
            // TAW: algorithm (whatever the literal attempts to do), but if you don't then,
            // TAW: it won't.
            // TAW: In allCollector cases, if a non-free variable is passed in, it must unify with
            // TAW: the results.
            
            Term copy = args.get(0).copyAndRenameVariables();
            return unifier.unify(copy, args.get(1), bindingList);
			
//			// return args.get(0).isVariant(args.get(1), bindingList); // YAP's doc says: 'copy_term(?TI,-TF) [ISO]' - I assume that '-' means "cannot be bound at calling time."
//			Utils.error("The second argument to 'copy_term' must be a variable.  You provided: '" + literal);
		}
		if (pred == stringHandler.standardPredicateNames.first  && numbArgs == 2) {
			Term arg0 = args.get(0);
			if (arg0 instanceof Variable) { return null; }
			ConsCell cc     = ConsCell.ensureIsaConsCell(context.getStringHandler(), args.get(0));
			return unifier.unify(cc.first(), args.get(1), bindingList);
		}
		if (pred == stringHandler.standardPredicateNames.rest  && numbArgs == 2) {
			Term arg0 = args.get(0);
			if (arg0 instanceof Variable) { return null; }
			ConsCell cc     = ConsCell.ensureIsaConsCell(context.getStringHandler(), args.get(0));
			return unifier.unify(cc.rest(), args.get(1), bindingList);
		}
		if (pred == stringHandler.standardPredicateNames.push  && numbArgs == 3) {
			Term arg1 = args.get(1);
			if (arg1 instanceof Variable) { Utils.error("Second argument cannot be a variable: " + literal); }
            if (args.get(1) instanceof ConsCell) {
                ConsCell cc = (ConsCell) args.get(1);
                return unifier.unify(cc.push(args.get(0)), args.get(2), bindingList);
            }
            else {
                return null;
            }
		}
		if (pred == stringHandler.standardPredicateNames.remove  && numbArgs == 3) {
			Term arg1 = args.get(1);
			if (arg1 instanceof Variable) { Utils.error("Second argument cannot be a variable: " + literal); }
			ConsCell cc     = ConsCell.ensureIsaConsCell(context.getStringHandler(), args.get(1));
			return unifier.unify(cc.remove(args.get(0)), args.get(2), bindingList);
		}
		if (pred == stringHandler.standardPredicateNames.reverse  && numbArgs == 2) {
			Term arg0 = args.get(0);
			Term arg1 = args.get(1);
			if (arg0 instanceof Variable) { 
				ConsCell cc     = ConsCell.ensureIsaConsCell(context.getStringHandler(), arg1);
				return unifier.unify(cc.reverse(), arg0, bindingList);
			}
			if (arg1 instanceof Variable) {
				ConsCell cc     = ConsCell.ensureIsaConsCell(context.getStringHandler(), arg0);
				return unifier.unify(cc.reverse(), arg1, bindingList);
			}
			Utils.error("One argument must be a variable: " + literal);
		}
		if (pred == stringHandler.standardPredicateNames.sort && numbArgs == 2) {
			Term arg0 = args.get(0);
			Term arg1 = args.get(1);
			if (arg0 instanceof Variable) { 
				ConsCell cc     = ConsCell.ensureIsaConsCell(context.getStringHandler(), arg1);
				return unifier.unify(cc.sort(), arg0, bindingList);
			}
			if (arg1 instanceof Variable) {
				ConsCell cc     = ConsCell.ensureIsaConsCell(context.getStringHandler(), arg0);
				return unifier.unify(cc.sort(), arg1, bindingList);
			}
			Utils.error("One argument must be a variable: " + literal);
		}
		if (pred == stringHandler.standardPredicateNames.appendFast  && numbArgs == 3) {
			Term arg0 = args.get(0);
			if (arg0 instanceof Variable) { Utils.error("First argument cannot be a variable: " + literal); }
			Term arg1 = args.get(1);
			if (arg1 instanceof Variable) { Utils.error("Second argument cannot be a variable: " + literal); }
			ConsCell cc0    = ConsCell.ensureIsaConsCell(context.getStringHandler(), args.get(0));
			ConsCell cc1    = ConsCell.ensureIsaConsCell(context.getStringHandler(), args.get(1));
			return unifier.unify(cc0.append(cc1), args.get(2), bindingList);
		}
		if (pred == stringHandler.standardPredicateNames.unionFast  && numbArgs == 3) {
			Term arg0 = args.get(0);
			if (arg0 instanceof Variable) { Utils.error("First argument cannot be a variable: " + literal); }
			Term arg1 = args.get(1);
			if (arg1 instanceof Variable) { Utils.error("Second argument cannot be a variable: " + literal); }
			ConsCell cc0    = ConsCell.ensureIsaConsCell(context.getStringHandler(), args.get(0));
			ConsCell cc1    = ConsCell.ensureIsaConsCell(context.getStringHandler(), args.get(1));
			return unifier.unify(cc0.union(cc1), args.get(2), bindingList);
		}
		if (pred == stringHandler.standardPredicateNames.intersectionFast  && numbArgs == 3) {
			Term arg0 = args.get(0);
			if (arg0 instanceof Variable) { Utils.error("First argument cannot be a variable: " + literal); }
			Term arg1 = args.get(1);
			if (arg1 instanceof Variable) { Utils.error("Second argument cannot be a variable: " + literal); }
			ConsCell cc0    = ConsCell.ensureIsaConsCell(context.getStringHandler(), args.get(0));
			ConsCell cc1    = ConsCell.ensureIsaConsCell(context.getStringHandler(), args.get(1));
			return unifier.unify(cc0.intersection(cc1), args.get(2), bindingList);
		}
		if (pred == stringHandler.standardPredicateNames.position  && numbArgs == 3) {
			Term arg1 = args.get(1);
			if (arg1 instanceof Variable) { Utils.error("Second argument cannot be a variable: " + literal); }
			ConsCell cc     = ConsCell.ensureIsaConsCell(context.getStringHandler(), args.get(1));
			int   result = cc.position(args.get(0));
			if (result < 0) { return null; }
			return unifier.unify(context.getStringHandler().getNumericConstant(result), args.get(2), bindingList);
		}
		if (pred == stringHandler.standardPredicateNames.nth && numbArgs == 3) {
			Term arg1 = args.get(1);
			if (arg1 instanceof Variable) { Utils.error("Second argument cannot be a variable: " + literal); }
			ConsCell cc     = ConsCell.ensureIsaConsCell(context.getStringHandler(), arg1);
			if (!(args.get(0) instanceof NumericConstant)) { Utils.error("First argument must be a number: " + literal); }
			Term result = cc.nth(((NumericConstant) args.get(0)).value.intValue());
			if (result == null) { return null; }
			return unifier.unify(result, args.get(2), bindingList);
		}
		if (pred == stringHandler.standardPredicateNames.nthPlus1 && numbArgs == 3) {
			Term arg1 = args.get(1);
			if (arg1 instanceof Variable) { Utils.error("Second argument cannot be a variable: " + literal); }
			ConsCell cc     = ConsCell.ensureIsaConsCell(context.getStringHandler(), arg1);
			if (!(args.get(0) instanceof NumericConstant)) { Utils.error("First argument must be a number: " + literal); }
			Term result = cc.nth(((NumericConstant) args.get(0)).value.intValue() + 1);
			if (result == null) { return null; }
			return unifier.unify(result, args.get(2), bindingList);
		}
		if (pred == stringHandler.standardPredicateNames.length && numbArgs == 2) {
			Term arg0 = args.get(0);
			if (arg0 instanceof Variable) { Utils.error("First argument cannot be a variable: " + literal); }
			ConsCell cc     = ConsCell.ensureIsaConsCell(context.getStringHandler(), args.get(0));
			return unifier.unify(context.getStringHandler().getNumericConstant(cc.length()), args.get(1), bindingList);
		}
		if (pred == stringHandler.standardPredicateNames.addListOfNumbers  && numbArgs == 2) {
			Term arg0 = args.get(0);
			if (arg0 instanceof Variable) { Utils.error("First argument cannot be a variable: " + literal); }
			ConsCell cc     = ConsCell.ensureIsaConsCell(context.getStringHandler(), args.get(0));
			double   result = cc.addNumbers();
			return unifier.unify(context.getStringHandler().getNumericConstant(result), args.get(1), bindingList);
		}
		if (pred == stringHandler.standardPredicateNames.multListOfNumbers && numbArgs == 2) {
			Term arg0 = args.get(0);
			if (arg0 instanceof Variable) { Utils.error("First argument cannot be a variable: " + literal); }
			ConsCell cc     = ConsCell.ensureIsaConsCell(context.getStringHandler(), args.get(0));
			double   result = cc.multiplyNumbers();
			return   unifier.unify(context.getStringHandler().getNumericConstant(result), args.get(1), bindingList);
		}
		if (pred == stringHandler.standardPredicateNames.halt   && numbArgs == 0) {
			throw new SearchInterrupted("halted");
		}
		if (pred == stringHandler.standardPredicateNames.halt   && numbArgs == 1) {
			throw new SearchInterrupted(args.get(0).toString());
		}
        if (pred == stringHandler.standardPredicateNames.dateToString && numbArgs == 2) {
			if (!(args.get(0) instanceof NumericConstant)) { Utils.error("First argument must be a number: " + literal); }
			long date = ((NumericConstant) args.get(0)).value.longValue();
			if (dateInstance == null) { 
				dateInstance = DateFormat.getDateInstance(DateFormat.DEFAULT);  // Create when/if needed.
				TimeZone gmtTimeZone = TimeZone.getTimeZone("UTC");
				dateInstance.setTimeZone(gmtTimeZone);
				dateInstance.setLenient(true);
			}
			String str = dateInstance.format(new Date(date)); // new Date(date).toString();
			return   unifier.unify(context.getStringHandler().getUnCleanedStringConstant(str), args.get(1), bindingList);
        }
        if (pred == stringHandler.standardPredicateNames.dateToUTCstring && numbArgs == 2) {
        	long date = 0;
			if (args.get(0) instanceof NumericConstant) {
				date = ((NumericConstant) args.get(0)).value.longValue();
			} else if (args.get(0) instanceof StringConstant) {
				date = Long.parseLong(((StringConstant) args.get(0)).toString());
			} else {
				Utils.error("First argument must be a number: " + literal + "  " + args.get(0).getClass());
			}
			if (dateTimeInstance == null) { 
				dateTimeInstance = DateFormat.getDateTimeInstance(DateFormat.FULL, DateFormat.FULL);  // Create when/if needed.
				TimeZone gmtTimeZone = TimeZone.getTimeZone("UTC");
				dateTimeInstance.setTimeZone(gmtTimeZone);
				dateTimeInstance.setLenient(true);
			}
			String str = dateTimeInstance.format(new Date(date));
			return   unifier.unify(context.getStringHandler().getUnCleanedStringConstant(str), args.get(1), bindingList);
        }
        if (pred == stringHandler.standardPredicateNames.dateToMRstring && numbArgs == 2) {
        	long date = 0;
			if (args.get(0) instanceof NumericConstant) {
				date = ((NumericConstant) args.get(0)).value.longValue();
			} else if (args.get(0) instanceof StringConstant) {
				date = Long.parseLong(((StringConstant) args.get(0)).toString());
			} else {
				Utils.error("First argument must be a number: " + literal + "  " + args.get(0).getClass());
			}
			if (simpleDateformat == null) { 
				simpleDateformat = new SimpleDateFormat("yyyyMMdd");
				TimeZone gmtTimeZone = TimeZone.getTimeZone("UTC");
				simpleDateformat.setTimeZone(gmtTimeZone);
				simpleDateformat.setLenient(true);
			}
			SimpleDateFormat simpleDateformat = new SimpleDateFormat("yyyyMMdd");
			  
			String str = simpleDateformat.format(new Date(date));
			return   unifier.unify(context.getStringHandler().getUnCleanedStringConstant(str), args.get(1), bindingList);
        }
        if (pred == stringHandler.standardPredicateNames.convertDateToLong && numbArgs == 2) {
			if (!(args.get(0) instanceof StringConstant)) { Utils.error("First argument must be a string: " + literal); }
			if (dateInstance == null) { 
				dateInstance = DateFormat.getDateInstance(DateFormat.DEFAULT);  // Create when/if needed.
				TimeZone gmtTimeZone = TimeZone.getTimeZone("UTC");
				dateInstance.setTimeZone(gmtTimeZone);
				dateInstance.setLenient(true);
			}
			String dateStr = ((StringConstant) args.get(0)).getBareName();
			Date   date    = null;
			try {
				date = dateInstance.parse(dateStr);
			} catch (ParseException e) {
				Utils.reportStackTrace(e);
				Utils.waitHere("Cannot parse date string: " + dateStr + "\n  " + e);
				return unifier.unify(context.getStringHandler().getNumericConstant(0), args.get(1), bindingList);
			}
			return   unifier.unify(context.getStringHandler().getNumericConstant(date.getTime()), args.get(1), bindingList);
        }
        if (pred == stringHandler.standardPredicateNames.assertName && numbArgs == 1) {
            Term arg0 = args.get(0);
            DefiniteClause clause = null;

            Sentence termAsSentence = arg0.asSentence();
            if ( termAsSentence != null ) {
                clause = termAsSentence.convertToClause();
            }
            
            if ( clause != null ) {
                context.getClausebase().assertBackgroundKnowledge(clause);
                return bindingList;
            }
			return FAIL;
        }
        if ( (pred == stringHandler.standardPredicateNames.assertifnotName || pred == stringHandler.standardPredicateNames.assertifunknownName) && numbArgs == 1) {
            Term arg0 = args.get(0);
            DefiniteClause clause = null;

            if (arg0 instanceof SentenceAsTerm) {
                SentenceAsTerm sentenceAsTerm = (SentenceAsTerm) arg0;
                clause = sentenceAsTerm.sentence.convertToClause();
            }
            else if (arg0 instanceof Function) {
                Function function = (Function) arg0;
                clause = function.convertToLiteral( context.getStringHandler() );
            }

            if ( clause != null ) {
                if ( context.getClausebase().recorded(clause) == false) {
                    context.getClausebase().assertBackgroundKnowledge(clause);
                }
                    return bindingList;
            }
			return FAIL;
        }
        if (pred == stringHandler.standardPredicateNames.createUniqueStringConstant && numbArgs == 2) {
			Term arg0 = args.get(0);
			if (!(arg0 instanceof StringConstant)) { Utils.error("First argument must be a StringConstant: " + literal); }
			StringConstant result = context.getStringHandler().getUniqueStringConstant(arg0.toString());
		//	Utils.println("createUniqueStringConstant: " + result + "  unify with " + args.get(1));
			return   unifier.unify(result, args.get(1), bindingList);
        }

//        if (pred == retractName && numbArgs == 1) {
//            Term arg0 = args.get(0);
//            DefiniteClause clause = null;
//
//            if (arg0 instanceof SentenceAsTerm) {
//                SentenceAsTerm sentenceAsTerm = (SentenceAsTerm) arg0;
//                clause = sentenceAsTerm.sentence.convertToClause();
//            }
//            else if (arg0 instanceof Function) {
//                Function function = (Function) arg0;
//                clause = function.convertToLiteral( context.getStringHandler() );
//            }
//
//            if ( clause != null ) {
//                context.getClausebase().retractDefiniteClause(clause);
//                return bindingList;
//            }
//            else {
//               return FAIL;
//            }
//        }

        if ( pred == stringHandler.standardPredicateNames.tokenizeString && numbArgs == 2) {
            Term string = args.get(0);
            Term tokens = args.get(1);
            
            if (!(string instanceof StringConstant)) { Utils.error("First argument must be bound: " + literal); }
            StringTokenizer     toker =  new StringTokenizer(((StringConstant) string).getBareName().replace("-", " - ")); // HACK FOR THE MACHINE READING TASK.  IF OTHERS WANT TO USE THIS 'undocumented' Prolog predicate, we'll need to use some mechanism for this).
            List<Constant> listOfTokens =  new ArrayList<Constant>(4);
            while (toker.hasMoreTokens()) { 
            	String str = wrapInQuotesIfNeeded(toker.nextToken());
            	listOfTokens.add(context.getStringHandler().getStringConstantButCheckIfNumber(null, str, false)); // NOTE: this will put quotes around DOUBLES.  TODO fix if needed.
            }
            ConsCell consCell = ConsCell.convertListToConsCell(context.getStringHandler(), listOfTokens);
            
            return unifier.unify(tokens, consCell, bindingList);
        }
        if ( pred == stringHandler.standardPredicateNames.atomLength && numbArgs == 2) {
            Term atom   = args.get(0);
            Term length = args.get(1);

			if (atom instanceof Variable) { Utils.error("First argument must be bound: " + literal); }
			int lengthOfAtom = atom.toString().length();
			return unifier.unify(length, stringHandler.getNumericConstant(lengthOfAtom), bindingList);
        }
        if ( pred == stringHandler.standardPredicateNames.atomChars && numbArgs == 2) { // NOTE: WILL doesn't have a char data type, so we'll put in StringConstants.
            Term atom = args.get(0);
            Term list = args.get(1);  // Could save some time by seeing if this is a Variable or a ConsCell.
            		
			if (atom instanceof Variable) { Utils.error("First argument must be bound: " + literal); } // TODO - if needed, we can write code to take a list and combine.
			
			String str = atom.toString();
			List<StringConstant> charsAsStringConstants = new ArrayList<StringConstant>(str.length());
		//	Utils.println("% atomChars: " + literal);
			for (int i = 0; i < str.length(); i++) { //Utils.println("%    " + str.charAt(i));
				if (str.charAt(i) == '"') { continue; } // If quote marks are needed, skip over it.
				char chr = str.charAt(i);
				if (chr == '?') { 
					Utils.warning("Problem in atomChars: " + str);
					charsAsStringConstants.add(stringHandler.getStringConstant("QuestionMark"));
				} else if (chr == '_') {
					Utils.warning("Problem in atomChars: " + str); 
					charsAsStringConstants.add(stringHandler.getStringConstant("UnderScore"));
				} else {
					charsAsStringConstants.add(stringHandler.getStringConstant(Character.toString(str.charAt(i)))); // Odd things happen with "(" and ")" and no doubt others - they all become "u_" but we'll live with that.
				}
			}
			
			ConsCell consCell = ConsCell.convertListToConsCell(context.getStringHandler(), charsAsStringConstants);
			return unifier.unify(list, consCell, bindingList);
        }
        
        if ( pred == stringHandler.standardPredicateNames.atomConcat && numbArgs == 3) {
            Term prefix = args.get(0);
            Term suffix = args.get(1);

            Term concat = args.get(2);

            boolean prefixIsConstant = prefix instanceof Constant;
            boolean suffixIsConstant = suffix instanceof Constant;
            boolean concatIsConstant = concat instanceof Constant;

            boolean prefixIsVariable = prefix instanceof Variable;
            boolean suffixIsVariable = suffix instanceof Variable;
            boolean concatIsVariable = concat instanceof Variable;

            if ( concatIsConstant || concatIsVariable ) {

                if ( prefixIsConstant ) {
                    if ( suffixIsConstant ) {                    	
                    	String prefixAsString  = prefix.toString(); // NOTE: this reasoning about explicit quotes also needed for the other cases.
                    	String suffixAsString  = suffix.toString();
                    	boolean prefixIsQuoted = prefixAsString.length() > 0 && prefixAsString.charAt(0) == '"' && prefixAsString.charAt(prefixAsString.length() - 1) == '"';
                    	boolean suffixIsQuoted = suffixAsString.length() > 0 && suffixAsString.charAt(0) == '"' && suffixAsString.charAt(suffixAsString.length() - 1) == '"';
                    	if (prefixIsQuoted) { prefixAsString = prefixAsString.substring(1, prefixAsString.length() - 1); }
                    	if (suffixIsQuoted) { suffixAsString = suffixAsString.substring(1, suffixAsString.length() - 1); }
                    	
                    	/*
                    	Utils.println("atomConcat: prefix = " + prefix);
                    	Utils.println("atomConcat: suffix = " + suffix);
                    	Utils.println("atomConcat: prefixIsQuoted = " + prefixIsQuoted);
                    	Utils.println("atomConcat: suffixIsQuoted = " + suffixIsQuoted);
                    	Utils.println("atomConcat: prefixAsString = " + prefixAsString);
                    	Utils.println("atomConcat: suffixAsString = " + suffixAsString); Utils.waitHere();
                    	*/
                    	
                        String newName = prefixAsString + suffixAsString;
                        if ( concatIsConstant ) {
                            // Form: Constant, Constant, Constant
                            return concat.toString().equals(newName) ? TRUE : FAIL;
                        }
						// Form: Constant, Constant, Variable
						bindingList.addBinding((Variable)concat, stringHandler.getStringConstant(newName, false));
						return TRUE;
                    }
                    else if ( suffixIsVariable ) {
                        if ( concatIsConstant ) {
                            // Form: Constant, Variable, Constant
                            String prefixAsString = prefix.toString();
                            String concatAsString = concat.toString();
                            
                        	boolean prefixIsQuoted = prefixAsString.charAt(0) == '"' && prefixAsString.charAt(prefixAsString.length() - 1) == '"';
                        	boolean concatIsQuoted = concatAsString.charAt(0) == '"' && concatAsString.charAt(concatAsString.length() - 1) == '"';
                        	if (prefixIsQuoted) { prefixAsString = prefixAsString.substring(1, prefixAsString.length() - 1); }
                        	if (concatIsQuoted) { concatAsString = concatAsString.substring(1, concatAsString.length() - 1); }

                            if ( concatAsString.startsWith(prefixAsString) == false ) {
                                return FAIL;
                            }
							String suffixAsString = concatAsString.substring(prefixAsString.length());
							bindingList.addBinding((Variable)suffix, stringHandler.getStringConstant(suffixAsString, false));
							return TRUE;
                        }
						// Form: Constant, Variable, Variable
						return FAIL;
                    }
                }
                else if ( prefixIsVariable ) {
                    if ( suffixIsConstant ) {
                        if ( concatIsConstant ) {
                            // Form: Variable, Constant, Constant
                            String suffixAsString = suffix.toString();
                            String concatAsString = concat.toString();
                            
                        	boolean suffixIsQuoted = suffixAsString.charAt(0) == '"' && suffixAsString.charAt(suffixAsString.length() - 1) == '"';
                        	boolean concatIsQuoted = concatAsString.charAt(0) == '"' && concatAsString.charAt(concatAsString.length() - 1) == '"';
                        	if (suffixIsQuoted) { suffixAsString = suffixAsString.substring(1, suffixAsString.length() - 1); }
                        	if (concatIsQuoted) { concatAsString = concatAsString.substring(1, concatAsString.length() - 1); }


                            if ( concatAsString.endsWith(suffixAsString) == false ) {
                                return FAIL;
                            }
							String prefixAsString = concatAsString.substring(0, concatAsString.length() - suffixAsString.length());
							bindingList.addBinding((Variable)prefix, stringHandler.getStringConstant(prefixAsString, false));
							return TRUE;
                        }
						// Form: Variable, Constant, Variable
						return FAIL;
                    }
                    else if ( suffixIsVariable ) {
                        if ( concatIsConstant ) {
                            // Form: Variable, Variable, Constant
                            // This is legal in ISO, but since we don't support backtracking,
                            // we certainly don't support it here!
                            return FAIL;
                        }
						// Form: Variable, Variable, Variable
						return FAIL;
                    }
                }
            }

            // This will catch the case were Prefix and/or suffix are not variables or constants.
            return FAIL;

        }

        if ( pred == stringHandler.standardPredicateNames.setCounter && numbArgs == 1) {
			Term       arg0       = args.get(0);

			if (!(args.get(0) instanceof NumericConstant)) { Utils.error("First argument must be a number: " + literal); }
			stringHandler.prologCounter = ((NumericConstant) arg0).value.intValue();
			return TRUE;
        }
        if ( pred == stringHandler.standardPredicateNames.setCounterB && numbArgs == 1) {
			Term       arg0       = args.get(0);

			if (!(args.get(0) instanceof NumericConstant)) { Utils.error("First argument must be a number: " + literal); }
			stringHandler.prologCounterB = ((NumericConstant) arg0).value.intValue();
			return TRUE;
        }
        if ( pred == stringHandler.standardPredicateNames.setCounterC && numbArgs == 1) {
			Term       arg0       = args.get(0);

			if (!(args.get(0) instanceof NumericConstant)) { Utils.error("First argument must be a number: " + literal); }
			stringHandler.prologCounterC = ((NumericConstant) arg0).value.intValue();
			return TRUE;
        }
        if ( pred == stringHandler.standardPredicateNames.setCounterD && numbArgs == 1) {
			Term       arg0       = args.get(0);

			if (!(args.get(0) instanceof NumericConstant)) { Utils.error("First argument must be a number: " + literal); }
			stringHandler.prologCounterD = ((NumericConstant) arg0).value.intValue();
			return TRUE;
        }
        if ( pred == stringHandler.standardPredicateNames.setCounterE && numbArgs == 1) {
			Term       arg0       = args.get(0);

			if (!(args.get(0) instanceof NumericConstant)) { Utils.error("First argument must be a number: " + literal); }
			stringHandler.prologCounterE= ((NumericConstant) arg0).value.intValue();
			return TRUE;
        }

        if ( pred == stringHandler.standardPredicateNames.incrCounter && numbArgs == 2) {
			Term       arg0       = args.get(0);
			Term       arg1       = args.get(1);

			if (!(args.get(0) instanceof NumericConstant)) { Utils.error("First argument must be a number: " + literal); }
			int result = stringHandler.prologCounter += ((NumericConstant) arg0).value.intValue();
			return unifier.unify(context.getStringHandler().getNumericConstant(result), arg1, bindingList);
        }
        if ( pred == stringHandler.standardPredicateNames.incrCounterB && numbArgs == 2) {
			Term       arg0       = args.get(0);
			Term       arg1       = args.get(1);

			if (!(args.get(0) instanceof NumericConstant)) { Utils.error("First argument must be a number: " + literal); }
			int result = stringHandler.prologCounterB += ((NumericConstant) arg0).value.intValue();
			return unifier.unify(context.getStringHandler().getNumericConstant(result), arg1, bindingList);
        }
        if ( pred == stringHandler.standardPredicateNames.incrCounterC && numbArgs == 2) {
			Term       arg0       = args.get(0);
			Term       arg1       = args.get(1);

			if (!(args.get(0) instanceof NumericConstant)) { Utils.error("First argument must be a number: " + literal); }
			int result = stringHandler.prologCounterC += ((NumericConstant) arg0).value.intValue();
			return unifier.unify(context.getStringHandler().getNumericConstant(result), arg1, bindingList);
        }
        if ( pred == stringHandler.standardPredicateNames.incrCounterD && numbArgs == 2) {
			Term       arg0       = args.get(0);
			Term       arg1       = args.get(1);

			if (!(args.get(0) instanceof NumericConstant)) { Utils.error("First argument must be a number: " + literal); }
			int result = stringHandler.prologCounterD += ((NumericConstant) arg0).value.intValue();
			return unifier.unify(context.getStringHandler().getNumericConstant(result), arg1, bindingList);
        }
        if ( pred == stringHandler.standardPredicateNames.incrCounterE && numbArgs == 2) {
			Term       arg0       = args.get(0);
			Term       arg1       = args.get(1);

			if (!(args.get(0) instanceof NumericConstant)) { Utils.error("First argument must be a number: " + literal); }
			int result = stringHandler.prologCounterE += ((NumericConstant) arg0).value.intValue();
			return unifier.unify(context.getStringHandler().getNumericConstant(result), arg1, bindingList);
        }

        
        if ( pred == stringHandler.standardPredicateNames.setCounter && numbArgs == 1) {
			Term       arg0       = args.get(0);

			if (!(args.get(0) instanceof NumericConstant)) { Utils.error("First argument must be a number: " + literal); }
			stringHandler.prologCounter = ((NumericConstant) arg0).value.intValue();
			return TRUE;
        }        
        if ( pred == stringHandler.standardPredicateNames.setCounterB && numbArgs == 1) {
			Term       arg0       = args.get(0);

			if (!(args.get(0) instanceof NumericConstant)) { Utils.error("First argument must be a number: " + literal); }
			stringHandler.prologCounterB = ((NumericConstant) arg0).value.intValue();
			return TRUE;
        }        
        if ( pred == stringHandler.standardPredicateNames.setCounterC && numbArgs == 1) {
			Term       arg0       = args.get(0);

			if (!(args.get(0) instanceof NumericConstant)) { Utils.error("First argument must be a number: " + literal); }
			stringHandler.prologCounterC = ((NumericConstant) arg0).value.intValue();
			return TRUE;
        }
        if ( pred == stringHandler.standardPredicateNames.setCounterD && numbArgs == 1) {
			Term       arg0       = args.get(0);

			if (!(args.get(0) instanceof NumericConstant)) { Utils.error("First argument must be a number: " + literal); }
			stringHandler.prologCounterD = ((NumericConstant) arg0).value.intValue();
			return TRUE;
        }
        if ( pred == stringHandler.standardPredicateNames.setCounterE && numbArgs == 1) {
			Term       arg0       = args.get(0);

			if (!(args.get(0) instanceof NumericConstant)) { Utils.error("First argument must be a number: " + literal); }
			stringHandler.prologCounterE = ((NumericConstant) arg0).value.intValue();
			return TRUE;
        }
        
        
		if (pred == stringHandler.standardPredicateNames.readEvalPrint) {
			Utils.print("    Answer: ");
			Term       arg0       = args.get(0);
			Term       arg1       = args.get(1);
			Term       arg2       = args.get(2);
			Term       arg3       = args.get(3);
			List<Term> boundVars  = (arg0 == null ? null : ((ListAsTerm) arg0).objects);
			BufferedReader reader = (BufferedReader) ((ObjectAsTerm) arg2).item;
			if (boundVars == null) { Utils.print("true"); } // Interrupt search?  No need to see how many proofs there are?
			else {
				List<Term> originalVars = ((ListAsTerm) arg1).objects;
				int size = boundVars.size();
				boolean firstTime = true;
				for (int i = 0; i < size; i++) {
					// if (firstTime) { firstTime = false; } else { Utils.print(", "); }
					if (originalVars.get(i) == boundVars.get(i)) { /* Utils.print(originalVars.get(i) + " is unbound")*/ }
					else                                         { if (firstTime) { firstTime = false; } else { Utils.print(", "); }
																   Utils.print(originalVars.get(i) + " = " + boundVars.get(i)); }
				}
			}
			StateBasedSearchTask task = (StateBasedSearchTask) ((ObjectAsTerm) arg3).item;
			//Utils.println("\nopen (size=" + open.size() + ") = " + task.open);
			task.cleanOpen();
			//Utils.println(  "open (size=" + open.size() + ") = " + task.open);
			if (task.open.isEmpty()) {
				Utils.println(".");
				throw new SearchInterrupted("open empty");
			}
			Utils.print(".\n    Continue?");
			try {
				String line = reader.readLine();
				if (//  view LF as a yes: line.equalsIgnoreCase("") ||  
					line.equalsIgnoreCase("n" )   || line.equalsIgnoreCase("n;")    || line.equalsIgnoreCase("n.")    ||
					line.equalsIgnoreCase("no")   || line.equalsIgnoreCase("no;")   || line.equalsIgnoreCase("no.")   ||
					line.equalsIgnoreCase("done") || line.equalsIgnoreCase("done;") || line.equalsIgnoreCase("done.") ||
					line.equalsIgnoreCase("quit") || line.equalsIgnoreCase("quit;") || line.equalsIgnoreCase("quit.") ||
					line.equalsIgnoreCase("exit") || line.equalsIgnoreCase("exit;") || line.equalsIgnoreCase("exit.") ||
					line.equalsIgnoreCase("halt") || line.equalsIgnoreCase("halt;") || line.equalsIgnoreCase("halt.")){
					Utils.println("");
					throw new SearchInterrupted("user aborted");
				}
			}
			catch (IOException e) {
				Utils.reportStackTrace(e);
				Utils.error("Something apparently went wrong trying to read input from the user.  Error message: " + e.getMessage());
			}
			return null;
		}
		if (pred == stringHandler.standardPredicateNames.negationByFailure && numbArgs == 1) {
			Utils.error("Negation-by-failure is handled elsewhere (in HornProofStepGenerator) and should not reach here.");
		}
		Utils.error("Unknown procedurally defined predicate: " + literal);
		return null;
	}

	private String wrapInQuotesIfNeeded(String str) {
		if (str.length() > 0 && str.charAt(0) == '"' && str.charAt(str.length() - 1) == '"') { return str; }
    	for (int i = 0; i < str.length(); i++) {
			if (!Character.isLetterOrDigit(str.charAt(i))) { return '"' + str + '"'; } 
		}
		return str;
	}
}
