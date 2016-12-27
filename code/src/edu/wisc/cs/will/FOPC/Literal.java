/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.FOPC.visitors.SentenceVisitor;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

import edu.wisc.cs.will.FOPC.PredicateName.FunctionAsPredType;
import edu.wisc.cs.will.Utils.Utils;
import java.io.Serializable;

/**
 * @author shavlik
 *
 */
@SuppressWarnings("serial")
public class Literal extends Sentence implements Serializable, DefiniteClause, LiteralOrFunction {
	
    public PredicateName predicateName;
    private List<Term>   arguments;     // Note: should not directly manipulate.  Instead use addArgument(), removeArgument(), and setArguments().
    private List<String> argumentNames; // (Optional) names of the arguments.

    private int containsVariables = -1; // Only set to false if CHECKED.  (Key: -1 = unknown, 0 = false, 1 = true.)  TODO protect against changes to 'arguments'
    private int cached_arity      = -1;
    
    public static long instancesCreated = 0;  // PROBABLY SHOULD PUT THESE IN THESE IN THE STRING HANDLER. 


    protected Literal() {
    	instancesCreated++;
    }
    
    public Literal(Literal lit) { // This is used for classes that need to extend Literal.  *** USE WITH CARE. ***
    	this();
        predicateName      = lit.predicateName;
        this.stringHandler = lit.stringHandler;
        this.arguments     = lit.arguments;
        this.argumentNames = lit.argumentNames;
        if (predicateName == null) {
            Utils.error("You have not provided a predicate name!");
        }
        if (predicateName.name.equals("")) {
            Utils.error("You have not provided a predicate name that is the empty string!");
        }
    }

    protected Literal(HandleFOPCstrings stringHandler) {
    	this();
        predicateName      = new PredicateName("thisIsADummyPredicate", stringHandler);
        this.stringHandler = stringHandler;
        this.arguments     = null;
        this.argumentNames = null;
    }

    protected Literal(HandleFOPCstrings stringHandler, PredicateName pred) {
    	this();
        predicateName      = pred;
        this.stringHandler = stringHandler;
        this.arguments     = null;
        this.argumentNames = null;
    }

    protected Literal(HandleFOPCstrings stringHandler, PredicateName pred, List<Term> arguments) {
        predicateName      = pred;
        this.arguments     = arguments;
        this.argumentNames = null;
        this.stringHandler = stringHandler;
    }

    /** Create a Literal given a predicate name and list of terms.
     *
     * TAW: This uses the varargs semantics common in C.  It allows the user to
     * specify a list of terms to be used as arguments without wrapping it in a List
     * or array.  For example, I can do this:
     *
     * 	new Literal(someHandler, "myPredName", Term1, Term2, Term3)
     *
     * Java boxes up the Term1, Term2, Term3 into a Term array.  So arguments will
     * be of type Term[] or null if there were no Terms passed in.
     *
     * @param stringHandler string handler for this predicate
     * @param pred predicate name
     * @param arguments Terms to be arguments of the predicate
     */
    protected Literal(HandleFOPCstrings stringHandler, PredicateName pred, Term... arguments) {
    	this();
        predicateName = pred;

        // Add the arguments to the this.arguments list.
        if (arguments != null) {
            this.arguments = new ArrayList<Term>(arguments.length);
            this.arguments.addAll(Arrays.asList(arguments));
        }
        else {
            this.arguments = null; // new ArrayList<Term>(0);  JWS: other code should handle arguments=null.
        }
        this.argumentNames = null;
        this.stringHandler = stringHandler;
    }

    protected Literal(HandleFOPCstrings stringHandler, PredicateName pred, Term argument) {
    	this();
        predicateName = pred;
        List<Term> args = new ArrayList<Term>(1);
        args.add(argument);
        this.stringHandler = stringHandler;
        this.arguments     = args;
        this.argumentNames = null;
    }

    protected Literal(HandleFOPCstrings stringHandler, PredicateName pred, List<Term> arguments, List<String> argumentNames) {
        this(stringHandler, pred, arguments);
        this.argumentNames = argumentNames;
        sortArgumentsByName();
        this.stringHandler = stringHandler;
        // If one or the other is null, don't check (e.g, this might be a bareCopy call).
        if (arguments != null && argumentNames != null && Utils.getSizeSafely(arguments) != Utils.getSizeSafely(argumentNames)) {
            Utils.error("Have " + arguments + " and " + argumentNames + " - number of arguments and number of names must match.");
        }
    }

    // Access values by name if argument names have been stored.
    public String getArgumentName(int index) {
        if (argumentNames == null) {
            return null;
        } //Utils.error("Asked for arg #" + index + " but no argument names are stored."); }
        if (index >= argumentNames.size()) {
            Utils.error("Asked for arg #" + index + " but only have: " + argumentNames);
        }
        return argumentNames.get(index);
    }

    public Literal copyAndClearArgumentNames() {
        return copy(true).clearArgumentNamesInPlace(); // Need to recur in case functions in the terms.
    }

    public Literal copyAndClearArgumentNames(boolean removeNameArg) {
        return copy(true).clearArgumentNamesInPlace(true);
    }

    public Literal clearArgumentNamesInPlace() {
        return clearArgumentNamesInPlace(true);
    }

    public Literal clearArgumentNamesInPlace(boolean removeNameArg) {
        if (numberArgs() < 1) {
            return this;
        }
        if (argumentNames != null) {
            List<String> argOrdering = predicateName.getNamedArgOrdering(numberArgs());

            if (removeNameArg) {
                if (argumentNames.get(0).equalsIgnoreCase("name")) {
                    removeArgument(arguments.get(0), argumentNames.get(0));
                }
            }

            if (argOrdering == null) {
            } // Utils.waitHere("No arg ordering for: " + this); }
            else {
                List<Term> newArgs = new ArrayList<Term>(numberArgs());
                for (String argName : argOrdering) {
                    newArgs.add(getArgumentByName(argName, true));
                }
                arguments = newArgs;
            }
        }
        argumentNames = null;
        if (arguments == null) {
            return this;
        }
        for (Term term : arguments) {
            if (term instanceof Function) {
                ((Function) term).clearArgumentNamesInPlace();
            }
        }
        return this;
    }

    // Access a value by name, rather than by position.
    public Term getArgumentByName(String name) {
        return getArgumentByName(name, true);
    }

    public Term getArgumentByName(String name, boolean complainIfNotFound) {
        if (argumentNames == null) {
            if (complainIfNotFound) {
                Utils.error("Can not find '" + name + "' in " + argumentNames);
            }
            return null;
        }
        if (argumentNames.size() < 1) {
            if (complainIfNotFound) {
                Utils.error("Can not find '" + name + "' in " + argumentNames);
            }
            return null;
        }
        for (int i = 0; i < numberArgs(); i++) {
            if (argumentNames.get(i).equalsIgnoreCase(name)) {
                return arguments.get(i);
            }
        }
        if (complainIfNotFound) {
            Utils.error("Can not find '" + name + "' in " + argumentNames);
        }
        return null;
    }

    // See if this literal is a determinate.  TODO FOR NOW, JUST CHECK THE PREDICATE NAME AND ARITY, BUT SHOULD REALLY CHECK IT MATCHES THE TYPE IN THE DETERMINATE SPEC. TODO
    public boolean isaDeterminateLiteral() {
        return predicateName.isDeterminatePredicate(arguments);
    }

    public boolean isaNumericFunctionAsPredLiteral() { // TODO need to check allCollector other vars are bound?
        return predicateName.isaNumericFunctionAsPredLiteral(arguments);
    }

    public boolean isaBooleanFunctionAsPredLiteral() { // TODO need to check allCollector other vars are bound?
        return predicateName.isaBooleanFunctionAsPredLiteral(arguments);
    }

    public boolean isaCategoricalFunctionAsPredLiteral() { // TODO need to check allCollector other vars are bound?
        return predicateName.isaCategoricalFunctionAsPredLiteral(arguments);
    }

    public boolean isaStructuredFunctionAsPredLiteral() { // TODO need to check allCollector other vars are bound?
        return predicateName.isaNumericFunctionAsPredLiteral(arguments);
    }

    public boolean isaAnythingFunctionAsPredLiteral() { // TODO need to check allCollector other vars are bound?
        return predicateName.isaAnythingFunctionAsPredLiteral(arguments);
    }

    public boolean isaListOfNumericFunctionAsPredLiteral() { // TODO need to check allCollector other vars are bound?
        return predicateName.isaListOfNumericFunctionAsPredLiteral(arguments);
    }

    public boolean isaListOfBooleanFunctionAsPredLiteral() { // TODO need to check allCollector other vars are bound?
        return predicateName.isaListOfBooleanFunctionAsPredLiteral(arguments);
    }

    public boolean isaListOfCategoricalFunctionAsPredLiteral() { // TODO need to check allCollector other vars are bound?
        return predicateName.isaListOfCategoricalFunctionAsPredLiteral(arguments);
    }

    public boolean isaListOfStructuredFunctionAsPredLiteral() { // TODO need to check allCollector other vars are bound?
        return predicateName.isaListOfStructuredFunctionAsPredLiteral(arguments);
    }

    public boolean isaListOfAnythingFunctionAsPredLiteral() { // TODO need to check allCollector other vars are bound?
        return predicateName.isaListOfAnythingFunctionAsPredLiteral(arguments);
    }

    public boolean isaBridgerLiteral() { // TODO need to check allCollector other vars are bound?
        return predicateName.isaBridgerLiteral(arguments);
    }

    // See Parser.processIsaInterval() for more information.
    public Term getLowerBoundary_1D() {
        int arity = numberArgs();
        if (predicateName.boundariesAtEnd_1D.contains(arity)) {
            return arguments.get(arity - 2);
        }
        if (arity != 3) {
            Utils.println("predicateName = " + predicateName + " predicateName.boundariesAtEnd_1D = " + predicateName.boundariesAtEnd_1D);
            Utils.error("This literal is said to be a 1D interval, but it doesn't have three arguments: " + this);
        }
        return arguments.get(0);
    }

    public Term getUpperBoundary_1D() {
        int arity = numberArgs();
        if (predicateName.boundariesAtEnd_1D.contains(arity)) {
            return arguments.get(arity - 1);
        }
        if (arity != 3) {
            Utils.error("This literal is said to be a 1D interval, but it doesn't have three arguments: " + this);
        }
        return arguments.get(2);
    }

    public Literal createLiteralWithMaskedBoundaries_1D() {
        Literal newVersion = (Literal) copy();
        int arity = numberArgs();
        if (predicateName.boundariesAtEnd_1D.contains(arity)) {
            newVersion.arguments.set(arity - 2, null);
            newVersion.arguments.set(arity - 1, null);
        }
        else if (arity != 3) {
            Utils.println("predicateName = " + predicateName + " predicateName.boundariesAtEnd_1D = " + predicateName.boundariesAtEnd_1D);
            Utils.error("This literal is said to be a 1D interval, but it doesn't have three arguments: " + this);
        }
        else {
            newVersion.arguments.set(0, null);
            newVersion.arguments.set(2, null);
        }
        return newVersion;
    }

    // Need for property copying (e.g., ConsCell reused applyTheta for Function).
    public Literal getBareCopy() {  // Utils.waitHere("bare lit copy " + this);
        return getBareCopy(arguments, argumentNames);
    }

    public Literal getBareCopy(List<Term> newArguments) {
        return getBareCopy(newArguments, argumentNames);
    }

    public Literal getBareCopy(List<Term> newArguments, List<String> newNames) {
        return (Literal) stringHandler.getLiteral(predicateName, newArguments, newNames).setWeightOnSentence(wgtSentence);
    }

    // A ('reverse') variant of contains().
    public boolean member(Collection<Literal> otherLists, boolean useStrictEquality) {  // TODO - add flag 'useVariantAsComparator'
        if (Utils.getSizeSafely(otherLists) < 1) {
            return false;
        }
        for (Literal otherLit : otherLists) {
            if (this.equals(otherLit, useStrictEquality)) {
                return true;
            }
        }
        return false;
    }

    // This code makes changes "in place" and assumes that the caller has made a copy if necessary.  (Note: be very careful if you change this code. For efficiency reasons it tries to save using new memory.)
    @Override
    public Literal applyTheta(Map<Variable, Term> theta) {
        // This should be essentially the same code as in Function.applyTheta
        boolean needNewLiteral = false; // See if there is a chance this might need to change (only do a one-level deep evaluation).
        if (arguments != null) {
            for (Term term : arguments) {
                if (!((term instanceof Variable && theta.get((Variable)term) == null) || term instanceof Constant)) {
                    needNewLiteral = true;
                    break;
                }
            }
        }
        //Utils.println("literal.applyTheta: '" + this + "', needNewLiteral = " + needNewLiteral + ", theta = " + theta);
        if (!needNewLiteral) {
            return this;
        }
        int numbArgs = numberArgs();
        List<Term> newArguments = (numbArgs == 0 ? null : new ArrayList<Term>(numberArgs()));
        if (numbArgs > 0) {
            for (Term arg : arguments) {
                if (arg == null) {
                    Utils.error("Has an arg=null: " + this);
                }
                newArguments.add(arg == null ? null : arg.applyTheta(theta));
            }
        }
        return getBareCopy(newArguments);
    }

    @Override
    public Literal applyTheta(BindingList bindingList) {
        if (bindingList != null) {
            return applyTheta(bindingList.theta);
        }
        else {
            return this;
        }
    }

    @Override
    public Literal copy(boolean recursiveCopy) { // recursiveCopy=true means that the copying recurs down to the leaves.   Also, variables will be created anew if requested.
        List<Term>   newArguments = (arguments     != null ? new ArrayList<Term>(  numberArgs()) : null);
        List<String> newArgNames  = (argumentNames != null ? new ArrayList<String>(numberArgs()) : null);
        if (argumentNames != null) {
            newArgNames.addAll(argumentNames);
        }
        if (recursiveCopy) {
            if (arguments != null) {
                for (Term term : arguments) {
                    newArguments.add(term == null ? null : term.copy(recursiveCopy));
                }
            }
            return getBareCopy(newArguments, newArgNames);
        }
        if (arguments != null) {
            newArguments.addAll(arguments);
        }
        return getBareCopy(newArguments, newArgNames);
    }

    @Override
    public Literal copy2(boolean recursiveCopy, BindingList bindingList) { // recursiveCopy=true means that the copying recurs down to the leaves.   Also, variables will be created anew if requested.
        List<Term> newArguments = (arguments != null ? new ArrayList<Term>(numberArgs()) : null);
        List<String> newArgNames = (argumentNames != null ? new ArrayList<String>(numberArgs()) : null);
        if (argumentNames != null) {
            newArgNames.addAll(argumentNames);
        }
        if (recursiveCopy) {
            if (arguments != null) {
                for (Term term : arguments) {
                    newArguments.add(term == null ? null : term.copy2(recursiveCopy, bindingList));
                }
            }
            return getBareCopy(newArguments, newArgNames);
        }
        if (arguments != null) {
            newArguments.addAll(arguments);
        }
        return getBareCopy(newArguments, newArgNames);
    }

    @Override
    public boolean containsTermAsSentence() {
        return false;
    }

    @Override
    public Collection<Variable> collectAllVariables() {
        return collectFreeVariables(null);
    }

    @Override
    public Collection<Variable> collectFreeVariables(Collection<Variable> boundVariables) {
        List<Variable> result = null; // Don't create until needed.

        if (arguments != null) {
            for (Term term : arguments) {
                Collection<Variable> temp = term.collectFreeVariables(boundVariables);

                if (temp != null) {
                    if (result == null) {
                        result = new ArrayList<Variable>(4);
                    }
                    for (Variable var : temp) {
                        if (!result.contains(var)) {
                            result.add(var);
                        }
                    }
                }
            }
        }
        return result== null ? Collections.EMPTY_LIST : result;
    }

    private String restOfToString(BindingList bindingList) {
        String result = "(";
        boolean firstOne = true;
        boolean hasArgNames = (argumentNames != null);
        int numberOfArgNames = Utils.getSizeSafely(argumentNames);

        if (arguments != null) {
            for (int i = 0; i < numberArgs(); i++) {
            	
                Term arg = arguments.get(i);
                if (firstOne) {
                    firstOne = false;
                }
                else {
                    result += ", ";
                    if (stringHandler.numberOfTermsPerRowInPrintouts == 1 || stringHandler.numberOfTermsPerRowInPrintoutsForLiterals == 1) { result += "\n        "; } // TODO -  write to properly handle stringHandler.numberOfLiteralsPerRowInPrintouts > 1
                }
                if (arg == null) {
                    result += "null";
                }
                else {
                    result += (hasArgNames ? (i >= numberOfArgNames ? "noNameForMe" : argumentNames.get(i)) + "=" : "") + arg.toString(Integer.MAX_VALUE, bindingList);
                } // No need for extra parentheses in an argument list.
            }
        }
        return result + ")";
    }
    
    public String toStringOneLine() {
    	int hold  = stringHandler.numberOfTermsPerRowInPrintouts;
    	int holdL = stringHandler.numberOfTermsPerRowInPrintoutsForLiterals;
    	stringHandler.numberOfTermsPerRowInPrintouts = Integer.MAX_VALUE;
    	String result = toString();
    	stringHandler.numberOfTermsPerRowInPrintouts            = hold;
    	stringHandler.numberOfTermsPerRowInPrintoutsForLiterals = holdL;
    	return result;
    }

    public PredicateName getPredicateName() {
        return predicateName;
    }

    public FunctionName getFunctionName() {
        return getStringHandler().getFunctionName(predicateName.name);
    }

    public Literal asLiteral() {
        return this;
    }

    public Function asFunction() {

        // We need special handling for conCells for some reason...
        if ( this == getStringHandler().getNilAsLiteral() ) {
            return getStringHandler().getNil(); // Make sure we preserve the Nil function for lists.
        }
        else if (predicateName.equals(getStringHandler().standardPredicateNames.consCell)) {
            return getStringHandler().getConsCell(stringHandler.getFunctionName("consCell"), arguments, argumentNames, null);
        }
        else {
            return getStringHandler().getFunction( getFunctionName(),  getArguments(), getArgumentNames(), null);
        }
    }


    public boolean equals(Object obj, boolean considerUseStrictEqualsForLiterals) {
        if ( this == obj) {
            return true;
        }

        if (considerUseStrictEqualsForLiterals && stringHandler.usingStrictEqualsForLiterals()) {
            return false;
        }

        if (obj == null) {
            return false;
        }
        if (obj instanceof Literal == false) {
            return false;
        }
        final Literal other = (Literal) obj;


        if (this.predicateName != other.predicateName && (this.predicateName == null || !this.predicateName.equals(other.predicateName))) {
            return false;
        }
        if (this.arguments != other.arguments && (this.arguments == null || !this.arguments.equals(other.arguments))) {
            return false;
        }
        if (this.argumentNames != other.argumentNames && (this.argumentNames == null || !this.argumentNames.equals(other.argumentNames))) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {

        if (stringHandler.usingStrictEqualsForLiterals()) {
            return super.hashCode();
        }
        else {
            int hash = 7;
            hash = 23 * hash + (this.predicateName != null ? this.predicateName.hashCode() : 0);
            hash = 23 * hash + (this.arguments != null ? this.arguments.hashCode() : 0);
            hash = 23 * hash + (this.argumentNames != null ? this.argumentNames.hashCode() : 0);
            return hash;
        }
    }

//    @Override
//    public int hashCode() {
//        if (stringHandler.useFastHashCodeForLiterals) {
//            return super.hashCode();
//        }
//        final int prime = 59; // http://primes.utm.edu/lists/small/10000.txt
//        int result = 1;
//        result = prime * result + ((predicateName == null) ? 23 : predicateName.hashCode());
//        result = prime * result + ((arguments == null) ? 439 : arguments.hashCode());
//        return result;
//    }
    // Are these two literals identical even if not the same instance?  Can be overridden by stringHandler.useStrictEqualsForLiterals

    @Override
    @SuppressWarnings("EqualsWhichDoesntCheckParameterClass")
    public boolean equals(Object other) {
        return equals(other, true);
    }

//    public boolean equals(Object other, boolean considerUseStrictEqualsForLiterals) {
//        if (this == other) {
//            return true;
//        }
//        if (considerUseStrictEqualsForLiterals && stringHandler.usingStrictEqualsForLiterals()) {
//            return false;
//        }
//        if (!(other instanceof Literal)) {
//            return false;
//        }
//        Literal otherAsLiteral = (Literal) other;
//        if (this == otherAsLiteral) {
//            return true;
//        }
//        if (predicateName != otherAsLiteral.predicateName) {
//            return false;
//        }
//        int thisNumberOfArgs = numberArgs();
//        int otherNumberOfArgs = otherAsLiteral.numberArgs();
//        if (thisNumberOfArgs != otherNumberOfArgs) {
//            return false;
//        }
//        for (int i = 0; i < thisNumberOfArgs; i++) {
//            Term thisTerm = arguments.get(i);
//            Term otherTerm = otherAsLiteral.arguments.get(i);
//            if (thisTerm == null) {
//                if (otherTerm != null) {
//                    return false;
//                }
//            }
//            else if (!thisTerm.equals(otherTerm)) {
//                return false;
//            } // Seems this short version of the test above suffices.
//        }
//        if (argumentNames == null && otherAsLiteral.argumentNames == null) {
//            return true;
//        }
//        if (argumentNames == null || otherAsLiteral.argumentNames == null) {
//            return false;
//        }
//        for (int i = 0; i < thisNumberOfArgs; i++) { // Should do a double walk of the two lists, but I don't recall the syntax (TODO).
//            if (!argumentNames.get(i).equalsIgnoreCase(otherAsLiteral.argumentNames.get(i))) {
//                return false;
//            }
//        }
//        return true;
//    }





    // Are these two equivalent POSSIBLY AFTER SOME VARIABLE RENAMING?
    public BindingList variants(Literal other, BindingList bindings) {
        //if (this == other) { return bindings; }		// Need to collect the matched variables (so they don't get matched to another variable elsewhere).
        if (predicateName != other.predicateName) {
            return null;
        }
        int numbArgs      = numberArgs();
        int otherNumbArgs = other.numberArgs();
        if (numbArgs != otherNumbArgs) {
            return null;
        }
        // Have checked that the lengths are equal, so need only one iterator.
        if (arguments != null) for (ListIterator<Term> terms1 = arguments.listIterator(), terms2 = other.arguments.listIterator(); terms1.hasNext();) {
            Term term1 = terms1.next();
            Term term2 = terms2.next();

            if (term1 == term2) {
                continue;
            }
            if (term1 == null || term2 == null) {
                return null;
            }

            // Utils.print("  term1=" + term1 + " term2=" + term2 + " bindings=" + bindings);
            bindings = term1.variants(term2, bindings);
            // Utils.println(" |  new bindings=" + bindings);
            if (bindings == null) {
                //Utils.println("fail!");
                return null;
            }
        }
        if (argumentNames == null && other.argumentNames == null) {
            return bindings;
        }
        if (argumentNames == null || other.argumentNames == null) { /* Utils.println("argNames fail!"); */ return null;
        }
        for (int i = 0; i < numbArgs; i++) { // Should do a double walk of the two lists, but I don't recall the syntax (TODO).
            if (!argumentNames.get(i).equalsIgnoreCase(other.argumentNames.get(i))) {
                //Utils.println(      "argumentNames.get(i)=" +       argumentNames.get(i));
                //Utils.println("other.argumentNames.get(i)=" + other.argumentNames.get(i));
                return null;
            }
        }
        return bindings;
    }


    @Override
    public BindingList isEquivalentUptoVariableRenaming(Sentence that, BindingList bindings) {
        if (that instanceof Literal == false) return null;

        Literal thatLiteral = (Literal) that;

        if ( this.predicateName != thatLiteral.predicateName ) return null;

        if ( this.numberArgs() != thatLiteral.numberArgs() ) return null;

        for (int i = 0; i < numberArgs(); i++) {
            bindings = this.getArgument(i).isEquivalentUptoVariableRenaming(thatLiteral.getArgument(i), bindings);
            if ( bindings == null ) return null;
        }

        return bindings;
    }




    @Override
    public BindingList variants(Sentence other, BindingList bindings) {
        // if (this == other) { return bindings; } // Need to collect the matched variables (so they don't get matched to another variable elsewhere).
        if (!(other instanceof Literal)) {
            return null;
        }
        return variants((Literal) other, bindings);
    }

    public int getArity() {
        return numberArgs();
    }

    public int numberArgs() {
        if (cached_arity < 0) {
            setNumberArgs();
        }
        return cached_arity;
    }

    private void setNumberArgs() {
        if (arguments == null) {
            cached_arity = 0;
        }
        else {
            cached_arity = arguments.size();
        }
        containsVariables();
    }

    public boolean containsThisVariable(Variable var) {
        if (arguments == null) {
            return false;
        }
        for (Term arg : arguments) {
            if (arg == var) {
                return true;
            }
        }
        return false;
    }
    
    // Cache this calculation to save time.
    public boolean containsVariables() {
        if (containsVariables < 0) {
            if (arguments == null) {
                containsVariables = 0;
                return false;
            }
            for (Term term : arguments) {
                if (term instanceof Variable) {
                    containsVariables = 1;
                    return true;
                }
                if ((term instanceof Function) && ((Function) term).containsVariables()) {
                    containsVariables = 1;
                    return true;
                }
            }
            if (containsVariables < 0) {
                containsVariables = 0;
            }
        }
        return (containsVariables > 0);
    }

    /** Would any variables in this clause remain UNBOUND if this binding list were to be applied?
     * @param theta
     * @return
     */
    @Override
    public boolean containsFreeVariablesAfterSubstitution(BindingList theta) {
        if (!containsVariables()) {
            return false;
        }
        if (theta == null || arguments == null) {
            return false;
        }
        // Utils.println(" LITERAL: freeVariablesAfterSubstitution: " + theta + "  " + this);
        for (Term term : arguments) {
            if (term.freeVariablesAfterSubstitution(theta)) {
                return true;
            }
        }
        return false;
    }

    // Clausal-form converter stuff.
    @Override
    protected boolean containsThisFOPCtype(String marker) {
        return false;
    }

    @Override
    protected Literal convertEquivalenceToImplication() {
        return this;
    }

    @Override
    protected Literal eliminateImplications() {
        return this;
    }

    @Override
    protected Sentence negate() { // In NOTs, the SECOND argument is used.
        return stringHandler.getConnectedSentence(null, stringHandler.getConnectiveName("not"), this).setWeightOnSentence(wgtSentence);
    }

    @Override
    protected Sentence moveNegationInwards() { // Can't go in any further.
        return this;
    }

    @Override
    protected Literal skolemize(List<Variable> outerUniversalVars) {
        return this; // Can't go in any further.
    }

    @Override
    protected Literal distributeDisjunctionOverConjunction() {
        return this; // Can't go in any further.
    }

    @Override
    protected Literal distributeConjunctionOverDisjunction() {
        return this; // Can't go in any further.
    }

    @Override
    protected List<Clause> convertToListOfClauses() {
        List<Clause> result = new ArrayList<Clause>(1);
        result.add(convertToClause(true)); // Convert allCollector of these to unnegated literals.
        return result;
    }

    @Override
    protected Clause convertToClause() {
        return convertToClause(true);
    }

    protected Clause convertToClause(boolean isaPositiveLiteral) {
        double literalWgt = wgtSentence;
        wgtSentence = Sentence.maxWeight; // Move the literal's weight out to the clause that "wraps" it.
        return (Clause) stringHandler.getClause(this, isaPositiveLiteral).setWeightOnSentence(literalWgt);
    }

    public Function convertToFunction(HandleFOPCstrings stringHandler) {
        FunctionName functionName = stringHandler.getFunctionName(predicateName.name);
        Function result = stringHandler.getFunction(functionName, arguments, argumentNames, null);
        //	result.printUsingInFixNotation = printUsingInFixNotation;
        return result;
    }

    // Convert a list of literals into a conjunct.
    public static ConnectedSentence convertListOfLiteralsToConjunct(HandleFOPCstrings stringHandler, List<Literal> literals) {
        if (literals == null || literals.size() < 2) {
            Utils.error("Should not have an empty nor singleton list here.");
        }
        int length = literals.size();
        if (length == 2) {
            return stringHandler.getConnectedSentence(literals.get(0), stringHandler.getConnectiveName("AND"), literals.get(1));
        }
        ConnectedSentence tail = convertListOfLiteralsToConjunct(stringHandler, literals.subList(1, length));
        return stringHandler.getConnectedSentence(literals.get(0), stringHandler.getConnectiveName("AND"), tail);
    }

    // Get the index where a "function value" is stored in this literal. Return -1 if this literal does not store such a value.
    public int getValueIndex() {
        if (predicateName.isDeterminatePredicate(arguments)) {
            return predicateName.getDeterminateArgumentIndex(numberArgs()) - 1; // Convert to ZERO-BASED accounting.
        }
        else if (predicateName.isaNumericFunctionAsPredLiteral(arguments)) {
            return predicateName.returnFunctionAsPredPosition(FunctionAsPredType.numeric, numberArgs()) - 1;
        }
        return -1;
    }

    // See if this literal is holding a value, and if so return that value.  Otherwise return the constant that represents 'true.'
    public Term getValueOfLiteral() {
        int pos = getValueIndex();
        if (pos >= 0) {
            return arguments.get(pos);
        }
        return stringHandler.trueIndicator;
    }

    @Override
    public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
        return toString(precedenceOfCaller, bindingList);   // TODO have this use toPrettyString in the recursive calls.
    }

    @Override
    public String toString(int precedenceOfCaller, BindingList bindingList) {
        String result = returnWeightString();
        boolean hasArgNames = (argumentNames != null);

        String pNameString = predicateName.toString();
        if (debugLevel > 0) {
        	if (predicateName.isaInlined(      numberArgs())) { pNameString += "[inlined]"; }
            if (predicateName.isaTemporaryName(numberArgs())) { pNameString += "[temporary]"; }
        }
        if (predicateName.printUsingInFixNotation && numberArgs() == 2) {
            int precedence = HandleFOPCstrings.getLiteralPrecedence_static(predicateName);
            if (precedenceOfCaller < precedence) {
                return result + "(" + (hasArgNames ? argumentNames.get(0) + "=" : "") + arguments.get(0).toString(precedence, bindingList) + " " + pNameString + " " + (hasArgNames ? argumentNames.get(1) + "=" : "") + arguments.get(1).toString(precedence, bindingList) + ")";
            }
			return result + (hasArgNames ? argumentNames.get(0) + "=" : "") + arguments.get(0).toString(precedence, bindingList) + " " + pNameString + " " + (hasArgNames ? argumentNames.get(1) + "=" : "") + arguments.get(1).toString(precedence, bindingList);
        }
        if (predicateName.printUsingInFixNotation && numberArgs() == 3 && predicateName.name.equalsIgnoreCase("then")) {
            int precedence = HandleFOPCstrings.getLiteralPrecedence_static(predicateName);
            if (precedenceOfCaller < precedence) {
                return result + "(" + (hasArgNames ? argumentNames.get(0) + "=" : "") + arguments.get(0).toString(precedence, bindingList) + " " + pNameString + " " + (hasArgNames ? argumentNames.get(1) + "=" : "") + arguments.get(1).toString(precedence, bindingList) + " else " + (hasArgNames ? argumentNames.get(2) + "=" : "") + arguments.get(2).toString(precedence, bindingList) + ")";
            }
			return result + (hasArgNames ? argumentNames.get(0) + "=" : "") + arguments.get(0).toString(precedence, bindingList) + " " + pNameString + " " + (hasArgNames ? argumentNames.get(1) + "=" : "") + arguments.get(1).toString(precedence, bindingList) + " else " + (hasArgNames ? argumentNames.get(2) + "=" : "") + arguments.get(2).toString(precedence, bindingList);
        }

//        if ( predicateName == stringHandler.standardPredicateNames.implicit_call && numberArgs() == 1 ) {
//            return getArgument(0).toString(precedenceOfCaller);
//        }

        result += pNameString;
        if (arguments == null) {
            return result;
        }
        return result + restOfToString(bindingList);

    }

    public String toModeString() {
        StringBuilder stringBuilder = new StringBuilder();
        stringBuilder.append(predicateName.name);
        if ( getArity() > 0 ) {
            stringBuilder.append("(");

            for (int i = 0; i < getArity(); i++) {
                TypeSpec ts = getArgument(i).getTypeSpec();
                if ( i > 0 ) {
                    stringBuilder.append(", ");
                }
                stringBuilder.append(ts);
            }

            stringBuilder.append(")");
        }

        return stringBuilder.toString();
    }

    @Override
    public boolean isDefiniteClause() {
        return true;
    }

    @Override
    public boolean isDefiniteClauseFact() {
        return true;
    }

    @Override
    public boolean isDefiniteClauseRule() {
        return false;
    }

    @Override
    public Literal getDefiniteClauseHead() {
        return this;
    }

    @Override
    public Literal getDefiniteClauseFactAsLiteral() throws IllegalStateException {
        return this;
    }

    @Override
    public Clause getDefiniteClauseAsClause() throws IllegalStateException {
        return getStringHandler().getClause(this, true);
    }

    @Override
    public List<Literal> getDefiniteClauseBody() {
        return Collections.EMPTY_LIST;
    }

    @Override
    public boolean isDefiniteClauseVariant(DefiniteClause otherClause) {
        if (otherClause.isDefiniteClauseFact() == false) {
            return false;
        }

        Literal otherHead = otherClause.getDefiniteClauseFactAsLiteral();

        if (predicateName != otherHead.predicateName) {
            return false;
        }

        if (numberArgs() != otherHead.numberArgs()) {
            return false;
        }

        for (int i = 0; i < numberArgs(); i++) {
            Term thisTerm = getArgument(i);
            Term thatTerm = otherHead.getArgument(i);

            if (thisTerm.isVariant(thatTerm) == false) {
                return false;
            }
        }

        return true;
    }

    public BindingList unifyDefiniteClause(DefiniteClause otherClause, BindingList bindingList) {
        if (otherClause.isDefiniteClauseFact() == false) {
            return null;
        }

        Literal otherHead = otherClause.getDefiniteClauseFactAsLiteral();

        if (predicateName != otherHead.predicateName) {
            return null;
        }

        if (numberArgs() != otherHead.numberArgs()) {
            return null;
        }

        if (bindingList == null) {
            bindingList = new BindingList();
        }

        return Unifier.UNIFIER.unify(this, otherHead, bindingList);
    }

    public Type getType(int argument) {
        TypeSpec type = getArgument(argument).getTypeSpec();

        return type != null ? type.isaType : null;
    }

    public List<Term> getArguments() {
        return arguments == null ? Collections.EMPTY_LIST : arguments;
    }

    public Term getArgument(int i) {
        return arguments.get(i);
    }

    public void setArguments(List<Term> arguments) {
        this.arguments = arguments;
        setNumberArgs();
        sortArgumentsByName();
    }

    public void setArgument(int i, Term newValue) {
    	arguments.set(i, newValue);
    }

    public List<String> getArgumentNames() {
        return argumentNames;
    }

    public void setArgumentNames(List<String> argumentNames) {
        this.argumentNames = argumentNames;
        sortArgumentsByName();
    }
    
    // Necessary for RuleSetVisualizer, cth
    public void setArgumentNamesNoSort(List<String> argumentNames) {
        this.argumentNames = argumentNames;
    }

    public void setArgumentName(int i, String newValue) {
        argumentNames.set(i, newValue);
        sortArgumentsByName();
    }

    public void addArgument(int position, Term term) {
        if (argumentNames != null) {
            Utils.error("Current arguments are named, so you need to pass in term and name for '" + this + "'.");
        }
        arguments.add(position, term);
        setNumberArgs();
    }

    public void addArgument(Term term) {
        if (argumentNames != null) {
            Utils.error("Current arguments are named, so you need to pass in term and name for '" + this + "'.");
        }
        if (arguments == null) {
        	arguments = new ArrayList<Term>(1);
        }
        arguments.add(term);
        setNumberArgs();
    }

    public void addArgument(Term term, String name) {
        arguments.add(term);
        argumentNames.add(name);
        setNumberArgs();
        sortArgumentsByName();
    }

    public void removeArgument(Term term) {
        if (argumentNames != null) {
            Utils.error("Current arguments are named, so you need to pass in term and name for '" + this + "'.");
        }
        if (!arguments.remove(term)) {
            Utils.error("Could not remove '" + term + "' from '" + this + "'.");
        }
        setNumberArgs();
    }

    public void removeArgument(String name, boolean complainIfNotFound) {
        Term term = getArgumentByName(name, complainIfNotFound);
        if (term == null) {
            return;
        }
        removeArgument(term, name);
    }

    public void removeArgument(Term term, String name) {
        if (!arguments.remove(term)) {
            Utils.error("Could not remove '" + term + "' from '" + this + "'.");
        }
        if (!argumentNames.remove(name)) {
            Utils.error("Could not remove '" + name + "' from '" + this + "'.");
        }
        setNumberArgs();
        sortArgumentsByName();
    }

    private void sortArgumentsByName() {
        if (argumentNames == null) {
            return;
        }
        int numbArgs = numberArgs();
        if (Utils.getSizeSafely(argumentNames) != numbArgs) {
            Utils.error("# of arguments (" + numbArgs + ") does not equal number of argument names ("
                    + Utils.getSizeSafely(argumentNames) + "):\n   args = " + arguments + "\n  names = " + argumentNames + "\n    lit = " + this);
        }
        if (numbArgs < 2) {
            return;
        }
        List<NamedTerm> namedTerms = new ArrayList<NamedTerm>(numbArgs);
        Set<String> namesSeen = new HashSet<String>(4);
        for (int i = 0; i < numbArgs; i++) {
            String argName = argumentNames.get(i);
            if (namesSeen.contains(argName)) {
                Utils.error("Cannot have duplicate names (" + argName + "): " + argumentNames);
            }
            if ( argName != null ) namesSeen.add(argName);
            namedTerms.add(new NamedTerm(arguments.get(i), argName));
        }
        Collections.sort(namedTerms, NamedTerm.comparator);
        arguments.clear();
        argumentNames.clear();
        for (NamedTerm nt : namedTerms) {
            arguments.add(nt.term);
            argumentNames.add(nt.name);
        }
    }

    /** Returns all possible TypeSpecs for this literal.
     *
     * If typeSpec variable is set, only that type
     * @return
     */
    public List<TypeSpec> getTypeSpecs() {

        List<TypeSpec> result = null;

        List<PredicateSpec> predTypeSpec = predicateName.getTypeList();

        if ( Utils.getSizeSafely(predTypeSpec) > 0 ) {
            PredicateSpec ps = predTypeSpec.get(0);
            result = ps.getTypeSpecList();
        }
        else {
            result = new ArrayList<TypeSpec>();
            for (Term term : getArguments()) {
                result.add(term.getTypeSpec());
            }
        }
        
        return result;
    }

    /** Looks up the set type spec on the literal.
     *
     * In many cases, the literal won't actually
     * have the type spec directly attached.  In those cases,
     * getTypeSpecs() can be used to lookup the list of all
     * possible type specs for the literal.
     * 
     * @param index
     * @return
     */
    public TypeSpec getArgumentTypeSpec(int index) {
        return arguments.get(index).getTypeSpec();
    }

    public PredicateNameAndArity getPredicateNameAndArity() {
        return stringHandler.getPredicate(predicateName, getArity());
    }

    @Override
    public <Return, Data> Return accept(SentenceVisitor<Return, Data> visitor, Data data) {
        return visitor.visitLiteral(this, data);
    }

    @Override
    public Clause getNegatedQueryClause() throws IllegalArgumentException {

        Clause result = null;

        result = stringHandler.getClause(null, Collections.singletonList(this));

        return result;
    }

	   @Override
    public int countVarOccurrencesInFOPC(Variable v) {
        int total = 0;
        if (arguments != null) {
            for (Term arg : arguments) {
                total += arg.countVarOccurrencesInFOPC(v);
            }
        }
        return total;
    }

    public Term asTerm() {
        return asFunction();
    }
}
