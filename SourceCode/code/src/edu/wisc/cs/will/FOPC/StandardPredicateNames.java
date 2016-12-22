/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.FOPC;

import java.util.HashSet;
import java.util.Set;

/**
 *
 * @author twalker
 */
public class StandardPredicateNames { // A few FUNCTION names also appear here; for instance, sometimes we need to convert a literal to a function.

    HandleFOPCstrings stringHandler;

    public final PredicateName dateToString;

    public final PredicateName dateToUTCstring;

    public final PredicateName dateToMRstring;
    
    public final PredicateName convertDateToLong;

    public final PredicateName isa_variable; // NOTE: the same stringHandler needs to be used throughout so the same strings get mapped to the same PredicateName instances.

    public final PredicateName var;

    public final PredicateName isa_constant; // Also note: this mapping is case-independent.

    public final PredicateName atomic;

    public final PredicateName isa_numericConstant;

    public final PredicateName number;

    public final PredicateName isaInteger;

    public final PredicateName isaFloat;

    public final PredicateName isaDouble;

    public final PredicateName isa_stringConstant;

    public final PredicateName atom;

    public final PredicateName nonvar;

    public final PredicateName list;

    public final PredicateName compound;

    public final PredicateName is;

    public final PredicateName halt;

    public final PredicateName sort;

    public final FunctionName pullOutNthArgFunction;

    public final FunctionName unifyFunction;

    public final FunctionName unify2Function;

    public final FunctionName ununifiableFunction;

    public final FunctionName ununifiable2Function;

    public final FunctionName equalFunction;

    public final FunctionName equal2Function;

    public final FunctionName notEqualFunction;


    public final FunctionName gtFunction;  // Prefix versions of these comparators haven't been provided.

    public final FunctionName gt2Function;

    public final FunctionName ltFunction;

    public final FunctionName lt2Function;

    public final FunctionName gteFunction;   // gte = greater-than-or-equal

    public final FunctionName gte2Function;

    public final FunctionName lteFunction;   // lte = less-than-or-equal

    public final FunctionName lte2Function;

    public final FunctionName lte3Function;

    public final FunctionName equalNumbersFunction;  // Equal numbers.

    public final FunctionName notEqualNumbersFunction; // Not equal numbers.

    public final FunctionName equalDotDotFunction;

    public final PredicateName print;

    public final PredicateName write; // A synonym for 'print.'

    public final PredicateName waitHere;

    public final PredicateName wait; // A synonym for 'waitHere.'

    public final PredicateName readEvalPrint;

    public final PredicateName findAllCollector;

    public final PredicateName allCollector;

    public final PredicateName bagOfCollector;

    public final PredicateName setOfCollector;

    public final PredicateName first;

    public final PredicateName rest;

    public final PredicateName push;

    public final PredicateName remove;

    public final PredicateName reverse;


    public final PredicateName position;

    public final PredicateName length;

    public final PredicateName nth;

    public final PredicateName nthPlus1;
    
    // These are also defined in a library.  Note can use fast version via functions, eg:  ?X is union(?Y, ?Z).
    // Libraries override (I [JWS] believe).
    public final PredicateName appendFast;
    public final PredicateName intersectionFast;    
    public final PredicateName unionFast;
    
    public final PredicateName listsEquivalent;

    public final PredicateName addListOfNumbers;

    public final PredicateName multListOfNumbers;

    public final PredicateName countProofsCollector;

    public final PredicateName countUniqueBindingsCollector;

    public final PredicateName assertName;

    public final PredicateName assertifnotName;

    public final PredicateName assertifunknownName;

    public final PredicateName atomConcat;
    
    public final PredicateName atomLength;
    
    public final PredicateName atomChars;
    
    public final PredicateName setCounter,  setCounterB,  setCounterC,  setCounterD,  setCounterE;
    public final PredicateName incrCounter, incrCounterB, incrCounterC, incrCounterD, incrCounterE;
    
    public final PredicateName tokenizeString;

    public final PredicateName implicit_call;

    public final PredicateName trueName;

    public final PredicateName falseName;

    public final PredicateName fail;

    public final PredicateName repeat;

    public final PredicateName once;

    public final PredicateName call;

    public final PredicateName cut;

    public final PredicateName cutMarker;

    public final PredicateName findAll;

    public final PredicateName all;

    public final PredicateName setOf;

    public final PredicateName bagOf;

    public final PredicateName countProofs;

    public final PredicateName countUniqueBindings;

    public final PredicateName then;

    public final PredicateName negationByFailure;

    public final FunctionName negationByFailureAsFunction;

    public final PredicateName spy;

    public final PredicateName nospy;

    public final PredicateName nospyall;

    public final PredicateName trace;

    public final PredicateName notrace;

    public final PredicateName retract;

    public final PredicateName retractall;

    public final PredicateName createUniqueStringConstant;

    public final PredicateName consCell;

    public final FunctionName plusFunction;  // TODO build in a hash table of synonyms?

    public final FunctionName minusFunction;

    public final FunctionName timesFunction;

    public final FunctionName divideFunction;

    public final FunctionName intDivFunction;

    public final FunctionName intFunction;

    public final FunctionName modFunction;

    public final FunctionName minFunction;

    public final FunctionName maxFunction;

    public final FunctionName absFunction;

    public final FunctionName sinFunction;

    public final FunctionName cosFunction;

    public final FunctionName tanFunction;

    public final FunctionName sinhFunction;

    public final FunctionName coshFunction;

    public final FunctionName tanhFunction;

    public final FunctionName asinFunction;

    public final FunctionName acosFunction;

    public final FunctionName atanFunction;

    public final FunctionName atan2Function; // From Java: Returns the angle theta from the conversion of rectangular coordinates (x, y) to polar coordinates (r, theta).

    public final FunctionName logFunction;

    public final FunctionName expFunction;

    public final FunctionName sqrtFunction;

    public final FunctionName sqrtSafeFunction;

    public final FunctionName sqrtAbsFunction;

    public final FunctionName powFunction;

    public final FunctionName starStarFunction;

    public final FunctionName randomFunction;  // A number uniformly drawn from [0,1).  Uses the 'random' used elsewhere in this code so that runs can be repeated deterministically.

    public final FunctionName ceilFunction; // From Java: Returns the smallest (closest to negative infinity) double value that is greater than or equal to the argument and is equal to a mathematical integer.

    public final FunctionName floorFunction;

    public final FunctionName roundFunction;

    public final FunctionName signFunction;

    public final FunctionName hypotFunction; // From Java: Returns sqrt(x^2 +y^2) without intermediate overflow or underflow.

    public final FunctionName toDegreesFunction; // Since in Java's Math class, might as well include them.

    public final FunctionName toRadiansFunction;

    public final FunctionName lengthFunction;   // Since this returns a number, do here as well as in DoBuiltInListProcessing.

    public final FunctionName positionFunction; // Since this returns a number, do here as well as in DoBuiltInListProcessing.

    public final FunctionName minus2Function;

    public final FunctionName isFunction;

    public final PredicateName unify2;

    public final PredicateName unify;

    public final PredicateName ununifiable;

    public final PredicateName ununifiable2;

    public final PredicateName equal;

    public final PredicateName equal2;

    public final PredicateName diff;

    public final PredicateName notEqual;
//	public final PredicateName not; // This had been defined as a synonym for negation-by-failure, but that seems dangerous, so I (JWS) have commented it out (8/21/10).

    public final PredicateName ground;

    public final PredicateName copyTerm;

    public final PredicateName gt;  // Prefix versions of these comparators haven't been provided.

    public final PredicateName gt2;

    public final PredicateName lt;

    public final PredicateName lt2;

    public final PredicateName gte;   // gte = greater-than-or-equal

    public final PredicateName gte2;

    public final PredicateName lte;   // lte = less-than-or-equal

    public final PredicateName lte2;

    public final PredicateName lte3;

    public final PredicateName equalNumbers;  // Equal numbers.

    public final PredicateName notEqualNumbers; // Not equal numbers.

    public final PredicateName equalDotDot;

    public final Set<PredicateName> buildinPredicates;

    protected StandardPredicateNames(HandleFOPCstrings stringHandler) {
        this.stringHandler = stringHandler;


        boolean hold = stringHandler.cleanFunctionAndPredicateNames;
        stringHandler.cleanFunctionAndPredicateNames = false;

        dateToString      = stringHandler.getPredicateName("dateToString");
        dateToUTCstring   = stringHandler.getPredicateName("dateToUTCstring");
        dateToMRstring    = stringHandler.getPredicateName("dateToMRstring");
        convertDateToLong = stringHandler.getPredicateName("convertDateToLong");
        isa_variable = stringHandler.getPredicateName("isa_variable"); // NOTE: the same stringHandler needs to be used throughout so the same strings get mapped to the same PredicateName instances.
        var = stringHandler.getPredicateName("var");
        isa_constant = stringHandler.getPredicateName("isa_constant"); // Also note: this mapping is case-independent.
        atomic = stringHandler.getPredicateName("atomic");
        isa_numericConstant = stringHandler.getPredicateName("isa_numericConstant");
        number = stringHandler.getPredicateName("number");
        isaInteger = stringHandler.getPredicateName("integer");
        isaFloat = stringHandler.getPredicateName("float");
        isaDouble = stringHandler.getPredicateName("double");
        isa_stringConstant = stringHandler.getPredicateName("isa_stringConstant");
        atom = stringHandler.getPredicateName("atom");
        nonvar = stringHandler.getPredicateName("nonvar");
        list = stringHandler.getPredicateName("list");
        compound = stringHandler.getPredicateName("compound");
        is = stringHandler.getPredicateName("is");
        halt = stringHandler.getPredicateName("halt");
        unify = stringHandler.getPredicateName("unify");
        unify2 = stringHandler.getPredicateName("=");
        ununifiable = stringHandler.getPredicateName("notUnify");
        ununifiable2 = stringHandler.getPredicateName("\\=");
        equal = stringHandler.getPredicateName("equal");
        equal2 = stringHandler.getPredicateName("==");
        diff = stringHandler.getPredicateName("diff");
        notEqual = stringHandler.getPredicateName("\\==");
        // not                 = stringHandler.getPredicateName("\\+");  // Note that there is also negationByFailure
        ground = stringHandler.getPredicateName("ground");
        copyTerm = stringHandler.getPredicateName("copy_term");
        gt = stringHandler.getPredicateName(">");  // Prefix versions of these comparators haven't been provided.
        gt2 = stringHandler.getPredicateName("gt");
        lt = stringHandler.getPredicateName("<");
        lt2 = stringHandler.getPredicateName("lt");
        gte = stringHandler.getPredicateName(">=");   // gte = greater-than-or-equal
        gte2 = stringHandler.getPredicateName("gte");
        lte = stringHandler.getPredicateName("=<");   // lte = less-than-or-equal
        lte2 = stringHandler.getPredicateName("<=");
        lte3 = stringHandler.getPredicateName("lte");
        equalNumbers = stringHandler.getPredicateName("=:=");  // Equal numbers.
        notEqualNumbers = stringHandler.getPredicateName("=\\="); // Not equal numbers.
        equalDotDot = stringHandler.getPredicateName("=..");
        print = stringHandler.getPredicateName("print");
        write = stringHandler.getPredicateName("write"); // A synonym for 'print.'
        waitHere = stringHandler.getPredicateName("waitHere");
        wait = stringHandler.getPredicateName("wait"); // A synonym for 'waitHere.'
        readEvalPrint = stringHandler.getPredicateName("readEvalPrintCollector");
        findAllCollector = stringHandler.getPredicateName("findAllCollector");
        allCollector = stringHandler.getPredicateName("allCollector");
        bagOfCollector = stringHandler.getPredicateName("bagofCollector");
        setOfCollector = stringHandler.getPredicateName("setofCollector");
        first = stringHandler.getPredicateName("first");
        rest = stringHandler.getPredicateName("rest");
        push = stringHandler.getPredicateName("push");
        remove = stringHandler.getPredicateName("remove");
        reverse = stringHandler.getPredicateName("reverse");
        position = stringHandler.getPredicateName("position");
        length = stringHandler.getPredicateName("length");
        nth = stringHandler.getPredicateName("nth");
        nthPlus1 = stringHandler.getPredicateName("nthPlus1");
        appendFast       = stringHandler.getPredicateName("append"); // Now defined in a Prolog library.  These versions are 'Fast' and don't do full unification (which especially matters for Union and Intersection).
        intersectionFast = stringHandler.getPredicateName("intersection");
        unionFast        = stringHandler.getPredicateName("union");
        listsEquivalent = stringHandler.getPredicateName("listsEquivalent");
        addListOfNumbers = stringHandler.getPredicateName("addListOfNumbers");
        multListOfNumbers = stringHandler.getPredicateName("multiplyListOfNumbers");
        countProofsCollector = stringHandler.getPredicateName("countProofsCollector");
        countUniqueBindingsCollector = stringHandler.getPredicateName("countUniqueBindingsCollector");
        assertName = stringHandler.getPredicateName("assert");
        assertifnotName = stringHandler.getPredicateName("assertifnot");
        assertifunknownName = stringHandler.getPredicateName("assertifunknown");
        atomConcat = stringHandler.getPredicateName("atom_concat"); // This is a standard name in Prolog, hence the underscore.
        atomLength = stringHandler.getPredicateName("atom_length"); // This is a standard name in Prolog, hence the underscore.
        atomChars  = stringHandler.getPredicateName("atom_chars");  // This is a standard name in Prolog, hence the underscore.
        setCounter   = stringHandler.getPredicateName("setCounter");
        setCounterB  = stringHandler.getPredicateName("setCounterB");
        setCounterC  = stringHandler.getPredicateName("setCounterC");
        setCounterD  = stringHandler.getPredicateName("setCounterD");
        setCounterE  = stringHandler.getPredicateName("setCounterE");
        incrCounter  = stringHandler.getPredicateName("incrCounter");
        incrCounterB = stringHandler.getPredicateName("incrCounterB");
        incrCounterC = stringHandler.getPredicateName("incrCounterC");
        incrCounterD = stringHandler.getPredicateName("incrCounterD");
        incrCounterE = stringHandler.getPredicateName("incrCounterE");
        tokenizeString  = stringHandler.getPredicateName("tokenizeString"); 
        implicit_call = stringHandler.getPredicateName("implicit_call");
        trueName = stringHandler.getPredicateName("true");
        falseName = stringHandler.getPredicateName("false");
        fail = stringHandler.getPredicateName("fail");
        repeat = stringHandler.getPredicateName("repeat");
        once = stringHandler.getPredicateName("once");
        call = stringHandler.getPredicateName("call");
        cut = stringHandler.getPredicateName("!");
        cutMarker = stringHandler.getPredicateName("cutMarker");
        findAll = stringHandler.getPredicateName("findAll");
        all = stringHandler.getPredicateName("all");
        setOf = stringHandler.getPredicateName("setOf");
        bagOf = stringHandler.getPredicateName("bagOf");
        countProofs = stringHandler.getPredicateName("countProofs");
        countUniqueBindings = stringHandler.getPredicateName("countUniqueBindings");
        then = stringHandler.getPredicateName("then");
        negationByFailure = stringHandler.getPredicateName("\\+");
        createUniqueStringConstant = stringHandler.getPredicateName("createUniqueStringConstant");
        sort = stringHandler.getPredicateName("sort");

        negationByFailureAsFunction = stringHandler.getFunctionName("\\+");
        plusFunction = stringHandler.getFunctionName("+"); // If another 'in-fix' operator is added to this list, need to edit FileParser.java.
        minusFunction = stringHandler.getFunctionName("-");
        minus2Function = stringHandler.getFunctionName("minus");
        timesFunction = stringHandler.getFunctionName("*");
        divideFunction = stringHandler.getFunctionName("/");   // Note that in essence 'true' division, rather than integer division, is used.
        intDivFunction = stringHandler.getFunctionName("/@"); // In ISO Prolog, this is '//' but that is a comment indicator to us.
        starStarFunction = stringHandler.getFunctionName("**");

        intFunction = stringHandler.getFunctionName("integer"); // Allow the user to force integer results.
        modFunction = stringHandler.getFunctionName("mod"); // Use Java's definition of mod.  Don't use a single-character symbol due to confusion between Java and Prolog.
        minFunction = stringHandler.getFunctionName("min");
        maxFunction = stringHandler.getFunctionName("max");
        absFunction = stringHandler.getFunctionName("abs");
        sinFunction = stringHandler.getFunctionName("sin");
        cosFunction = stringHandler.getFunctionName("cos");
        tanFunction = stringHandler.getFunctionName("tan");
        sinhFunction = stringHandler.getFunctionName("sinh");
        coshFunction = stringHandler.getFunctionName("cosh");
        tanhFunction = stringHandler.getFunctionName("tanh");
        asinFunction = stringHandler.getFunctionName("asin");
        acosFunction = stringHandler.getFunctionName("acos");
        atanFunction = stringHandler.getFunctionName("atan");
        atan2Function = stringHandler.getFunctionName("atan2");
        logFunction = stringHandler.getFunctionName("log");
        expFunction = stringHandler.getFunctionName("exp");
        powFunction = stringHandler.getFunctionName("pow");
        sqrtFunction = stringHandler.getFunctionName("sqrt");
        sqrtSafeFunction = stringHandler.getFunctionName("sqrtSafe");
        sqrtAbsFunction = stringHandler.getFunctionName("sqrtAbs");
        randomFunction = stringHandler.getFunctionName("random");
        ceilFunction = stringHandler.getFunctionName("ceiling"); // Also use 'ceil' since that is Java's name.
        floorFunction = stringHandler.getFunctionName("floor");
        roundFunction = stringHandler.getFunctionName("round");
        signFunction = stringHandler.getFunctionName("sign");
        hypotFunction = stringHandler.getFunctionName("hypot");
        toDegreesFunction = stringHandler.getFunctionName("toDegrees");
        toRadiansFunction = stringHandler.getFunctionName("toRadians");
        lengthFunction = stringHandler.getFunctionName("length"); // Explicitly list those list-processing functions that return numbers.
        positionFunction = stringHandler.getFunctionName("position");
        isFunction = stringHandler.getFunctionName("is");
        unifyFunction = stringHandler.getFunctionName("unify");
        unify2Function = stringHandler.getFunctionName("=");
        ununifiableFunction = stringHandler.getFunctionName("notUnify");
        ununifiable2Function = stringHandler.getFunctionName("\\=");
        equalFunction = stringHandler.getFunctionName("equal");
        equal2Function = stringHandler.getFunctionName("==");
        notEqualFunction = stringHandler.getFunctionName("\\==");
       // notFunction = stringHandler.getFunctionName("\\+");  // Note that there is also negationByFailure
        gtFunction = stringHandler.getFunctionName(">");  // Prefix versions of these comparators haven't been provided.
        gt2Function = stringHandler.getFunctionName("gt");
        ltFunction = stringHandler.getFunctionName("<");
        lt2Function = stringHandler.getFunctionName("lt");
        gteFunction = stringHandler.getFunctionName(">=");   // gte = greater-than-or-equal
        gte2Function = stringHandler.getFunctionName("gte");
        lteFunction = stringHandler.getFunctionName("=<");   // lte = less-than-or-equal
        lte2Function = stringHandler.getFunctionName("<=");
        lte3Function = stringHandler.getFunctionName("lte");
        equalNumbersFunction = stringHandler.getFunctionName("=:=");  // Equal numbers.
        notEqualNumbersFunction = stringHandler.getFunctionName("=\\="); // Not equal numbers.
        equalDotDotFunction = stringHandler.getFunctionName("=..");
        pullOutNthArgFunction = stringHandler.getFunctionName("pullOutNthArg");

        spy = stringHandler.getPredicateName("spy");
        nospy = stringHandler.getPredicateName("nospy");
        nospyall = stringHandler.getPredicateName("nospyall");
        trace = stringHandler.getPredicateName("trace");
        notrace = stringHandler.getPredicateName("notrace");

        retract = stringHandler.getPredicateName("retract");
        retractall = stringHandler.getPredicateName("retractall");

        consCell = stringHandler.getPredicateName("consCell");


        is.printUsingInFixNotation = true;
        unify2.printUsingInFixNotation = true;
        ununifiable2.printUsingInFixNotation = true;
        equal2.printUsingInFixNotation = true;
        notEqual.printUsingInFixNotation = true;
        gt.printUsingInFixNotation = true;
        lt.printUsingInFixNotation = true;
        gte.printUsingInFixNotation = true;
        lte.printUsingInFixNotation = true;
        lte2.printUsingInFixNotation = true;
        equalNumbers.printUsingInFixNotation = true;
        notEqualNumbers.printUsingInFixNotation = true;
        equalDotDot.printUsingInFixNotation = true;

        isFunction.printUsingInFixNotation = true;
        plusFunction.printUsingInFixNotation = true;
        minusFunction.printUsingInFixNotation = true;
        timesFunction.printUsingInFixNotation = true;
        divideFunction.printUsingInFixNotation = true;
        intDivFunction.printUsingInFixNotation = true;
        starStarFunction.printUsingInFixNotation = true;
        isFunction.printUsingInFixNotation = true;
        unify2Function.printUsingInFixNotation = true;
        ununifiable2Function.printUsingInFixNotation = true;
        equal2Function.printUsingInFixNotation = true;
        notEqualFunction.printUsingInFixNotation = true;
        gtFunction.printUsingInFixNotation = true;
        ltFunction.printUsingInFixNotation = true;
        gteFunction.printUsingInFixNotation = true;
        lteFunction.printUsingInFixNotation = true;
        lte2Function.printUsingInFixNotation = true;
        equalNumbersFunction.printUsingInFixNotation = true;
        notEqualNumbersFunction.printUsingInFixNotation = true;
        equalDotDotFunction.printUsingInFixNotation = true;

        call.setContainsCallable(1);
        negationByFailure.setContainsCallable(1);
        once.setContainsCallable(1);

        buildinPredicates = new HashSet<PredicateName>(32);
        buildinPredicates.add(trueName);
        buildinPredicates.add(falseName);
        buildinPredicates.add(fail);
        buildinPredicates.add(repeat);
        buildinPredicates.add(once);
        buildinPredicates.add(call);
        buildinPredicates.add(implicit_call);
        buildinPredicates.add(cut);
        buildinPredicates.add(cutMarker);
        buildinPredicates.add(findAll);
        buildinPredicates.add(all);
        buildinPredicates.add(setOf);
        buildinPredicates.add(bagOf);
        buildinPredicates.add(countProofs);
        buildinPredicates.add(countUniqueBindings);
        buildinPredicates.add(then);
        buildinPredicates.add(negationByFailure);

        buildinPredicates.add(spy);
        buildinPredicates.add(nospy);
        buildinPredicates.add(nospyall);
        buildinPredicates.add(trace);
        buildinPredicates.add(notrace);

        buildinPredicates.add(retract);
        buildinPredicates.add(retractall);

        stringHandler.cleanFunctionAndPredicateNames = hold;
    }
}
