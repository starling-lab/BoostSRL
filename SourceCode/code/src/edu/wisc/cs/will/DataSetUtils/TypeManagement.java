/**
 * 
 */
package edu.wisc.cs.will.DataSetUtils;

import java.io.File;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import java.io.FileNotFoundException;
import edu.wisc.cs.will.Utils.condor.CondorFileOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.PredicateSpec;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Type;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.Utils.MessageType;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author shavlik
 *
 */
public class TypeManagement {

    protected final static int debugLevel = 0; // Used to control output from this class (0 = no output, 1=some, 2=much, 3=all).

    private HandleFOPCstrings stringHandler;

    private Map<PredicateName, Set<Type>> beenWarnedHashMap;

    private Map<Term, Map<Type, Literal>> addedConstantHashMap;

    public TypeManagement(HandleFOPCstrings stringHandler) {
        this.stringHandler = stringHandler;
    }

    // Collect as many types as possible from the data read in.
    // The Boolean return indicates whether or not addToFactsFile should be called.
    public Boolean collectTypedConstants(boolean createCacheFiles, boolean useCachedFiles, String typesFileNameToUse, List<Literal> targetLiterals, List<List<ArgSpec>> targetArgSpecs, Set<PredicateNameAndArity> bodyModes,
                                         List<Example> posExamples, List<Example> negExamples, Iterable<Sentence> backgroundFacts) {
        File file = (useCachedFiles ? new CondorFile(typesFileNameToUse) : null);
        if (useCachedFiles && file.exists()) {
            Utils.println("\n% Collection of the types of constants has previously occurred.  If this is incorrect, delete:\n%   '" + file.getPath() + "'");
            return true; // Tell the caller to load this file.
        }
        if (debugLevel > -1) {
            Utils.println("\n% Collecting the types of constants.");
        }
        try {
            CondorFileOutputStream outStream = (createCacheFiles ? new CondorFileOutputStream(typesFileNameToUse) : null);
            PrintStream printStream = (createCacheFiles ? new PrintStream(outStream, false) : null); // (Don't) Request auto-flush (can slow down code).

            collectImplicitTypeConstantsViaModeAndFactInspection(printStream, bodyModes, backgroundFacts);
            if (debugLevel > -1) {
                Utils.println("\n% Looking at the training examples to see if any types of new constants can be inferred.");
            }
            if (printStream != null) {
                printStream.println("\n% Looking at the training examples to see if any types of new constants can be inferred.");
            }
            if (targetLiterals == null) {
                Utils.warning("targetPredicates=null");
            }
            if (targetArgSpecs == null) {
                Utils.warning("targetArgSpecs=null");
            }
            if (targetLiterals != null && targetArgSpecs != null && targetArgSpecs.size() != Utils.getSizeSafely(targetLiterals)) {
                Utils.error("targetArgSpecs = " + targetArgSpecs + " and targetPredicates = " + targetLiterals);
            }
            if (targetLiterals != null && (posExamples != null || negExamples != null)) {
                for (int i = 0; i < Utils.getSizeSafely(targetLiterals); i++) {
                    PredicateName targetPredicate = targetLiterals.get(i).predicateName;
                    List<ArgSpec> argSpecs = targetArgSpecs.get(i);
                    recordTypedConstantsFromTheseExamples(printStream, posExamples, "positive", targetPredicate, argSpecs);
                    recordTypedConstantsFromTheseExamples(printStream, negExamples, "negative", targetPredicate, argSpecs);
                }
            }
            checkThatTypesOfAllConstantsAreKnown(printStream, backgroundFacts);
            if (printStream != null) {
                printStream.close();
            }
        } catch (FileNotFoundException e) {
            Utils.reportStackTrace(e);
            Utils.error("Unable to successfully open this file for writing: " + typesFileNameToUse + ".  Error message: " + e.getMessage());
        }
        return false;
    }
    private int adds = 0;

    private int dups = 0;

    private int inHash = 0;

    public void collectImplicitTypeConstantsViaModeAndFactInspection(PrintStream printStream, Set<PredicateNameAndArity> bodyModes, Iterable<Sentence> backgroundFacts) {
        Map<Term, Set<Type>> alreadyCheckedConstantHash = new HashMap<Term, Set<Type>>(4096);
        for (PredicateNameAndArity predName : bodyModes) {
            // First need to see if this predicate can have DIFFERENT numbers of arguments.  If so, we need to treat each separately.
            Set<Integer> sizes = new HashSet<Integer>(4);
            for (PredicateSpec specs : predName.getPredicateName().getTypeList()) { // Consider each known mode for this predicate.
                Integer length = Utils.getSizeSafely(specs.getSignature());
                sizes.add(length);
            }
            if (debugLevel > 10) {
                Utils.println("\n% Predicate '" + predName + "' can have the following arities: " + sizes);
            }

            for (Integer argSize : sizes) {
                boolean firstTime = true;
                int size = Utils.getSizeSafely(predName.getPredicateName().getTypeListForThisArity(argSize));
                Set<Integer> ambiguous = new HashSet<Integer>(size);
                List<Type> argTypes = new ArrayList<Type>(size);
                for (PredicateSpec specs : predName.getPredicateName().getTypeListForThisArity(argSize)) { // Again consider each known mode for this predicate, but only worry about those with arity = argSize.
                    // We now have to see if all modes for this parity and arity specify the same types for the arguments.
                    // If there is ambiguity then we cannot infer new typed constants since we don't know which mode matches the facts.
                    // (Aside: we could have fact p(dog1, dog2) but only a mode about humans [i.e., the p(dog1,dog2) should be ignored] and this code will infer dog1 and dog2 are humans.  Not clear how to avoid this short of requiring users to always give lists of constants, which is quite the burden.)
                    help_collectImplicitTypeConstantsViaModeAndFactInspection(ambiguous, specs.getSignature(), predName, 0, firstTime, specs.getTypeSpecList(), argTypes);
                    firstTime = false; // The second (and subsequent) time around we need to see if the types are the same, e.g. may only differ in terms of +/-/# etc, which doesn't matter here.
                }
                if (debugLevel > 10) {
                    Utils.println("% '" + predName + "' sig = " + predName.getPredicateName().getTypeListForThisArity(argSize).get(0).getSignature() + " types = " + predName.getPredicateName().getTypeListForThisArity(argSize).get(0).getTypeSpecList() + " argTypes = " + argTypes); //Utils.waitHere();
                }
                if (ambiguous.size() < size) {
                    if (debugLevel > 0) {
                        Utils.println("%  Predicate '" + predName + "/" + argSize + "' can have the following encountered types: " + argTypes);
                    }
                    adds = 0;
                    dups = 0;
                    inHash = 0;
                    int counter = 0;
                    int countMatches = 0;
                    if (debugLevel > 0) {
                        Utils.println("%  Have inferred the type of " + Utils.comma(adds) + " constants and encountered " + Utils.comma(inHash) + " already in the hash table whose types were already known, as well as " + Utils.comma(dups) + " types that were already known via inheritance.");
                    }

                    if (backgroundFacts != null) {
                        for (Sentence sentence : backgroundFacts) {
                            if (sentence instanceof Literal) {
                                Literal fact = (Literal) sentence;
                                counter++; // Still need to check predicate name since the Horn-clause base might have returned some extras (but probably no longer need to check arity).
                                if (fact.predicateName == predName.getPredicateName() && fact.getArity() == argSize) {
                                    countMatches++;

                                    help_matchFactsAndModes(fact, fact.getArguments(), 0, ambiguous, argTypes, printStream, alreadyCheckedConstantHash);
                                }
                            }
                        }
                    }
                    if (debugLevel > 0) {
                        Utils.println("%  Have inferred (checked " + Utils.comma(countMatches) + "/" + Utils.comma(counter) + ") the type of " + Utils.comma(adds) + " constants and encountered " + Utils.comma(inHash) + " already in the hash table whose types were already known, as well as " + Utils.comma(dups) + " types that were already known via inheritance.");
                    }
                }
            }
        }
    }

    private void help_matchFactsAndModes(Literal fact, List<Term> args, int counter, Set<Integer> ambiguous, List<Type> argTypes, PrintStream printStream, Map<Term, Set<Type>> alreadyCheckedConstantHash) {
        //Utils.println("help_matchFactsAndModes: fact = " + fact + " args = " + args + " counter = " + counter + " argTypes = " + argTypes);
        if (args == null) {
            return;
        }
        for (Term arg : args) {
            if (ambiguous.contains(counter)) {
                counter++; // Need to skip this argument.
            }
            else if (Function.isaConsCell(arg)) {
                counter++; // We need to skip lists, since they can be of variable length.
            }
            else if (arg.isGrounded()) {
                Type thisType = argTypes.get(counter);
                if (thisType == null) {
                    if (args.size() > 1) {
                        Utils.println(fact + " thisType = " + thisType);
                    }
                    counter++; // I added this Nov 2010 since it seems to be needed, though didn't run into any specific bug.
                    continue;  // This argument is a specific constant and not a type, so no type inference possible.
                }
                Set<Type> lookup1 = alreadyCheckedConstantHash.get(arg);

                if (lookup1 != null && lookup1.contains(thisType)) {
                    inHash++;
                    // if (args.size() > 1) Utils.println(fact + "   IN HASH: [" + argAsConstant + ", " + thisType + "] Have inferred the type of '" + arg + "' is '" + argTypes.get(counter) + "' from fact: '" + fact + "' and mode '" + argTypes + "'.");
                    counter++;
                    continue; // Already checked if this constant is of this type.
                }
                // Have inferred the type of this constant.
                if (addNewConstant(printStream, stringHandler, arg, thisType, fact)) {
                    // if (args.size() > 1) Utils.waitHere(fact + "   ADD: [" + argAsConstant + ", " + thisType + "] Have inferred the type of '" + arg + "' is '" + argTypes.get(counter) + "' from fact: '" + fact + "' and mode '" + argTypes + "'.");
                    adds++;
                }
                else {
                    // if (args.size() > 1) Utils.println( fact + "   DUP: [" + argAsConstant + ", " + thisType + "] Have inferred the type of '" + arg + "' is '" + argTypes.get(counter) + "' from fact: '" + fact + "' and mode '" + argTypes + "'.");
                    dups++;
                }
                if (lookup1 == null) {
                    lookup1 = new HashSet<Type>(4);
                    alreadyCheckedConstantHash.put(arg, lookup1);
                }
                lookup1.add(thisType);
                counter++;
            }
            else if (arg instanceof Function) {
//            	Function f = (Function) arg;
//            	help_matchFactsAndModes(fact, f.getArguments(), counter, ambiguous, argTypes, printStream, alreadyCheckedConstantHash);
//            	counter += f.countLeaves();
            }
            else if (arg instanceof Variable) {
                counter++; // Simply skip variables.
            }
            else {
                Utils.error("Should not have arg=" + arg);
            }
        }

    }

    private void help_collectImplicitTypeConstantsViaModeAndFactInspection(Set<Integer> ambiguous, List<Term> signature, PredicateNameAndArity predName, int counter, boolean firstTime,
                                                                           List<TypeSpec> typeSpecList, List<Type> argTypes) {
        if (signature == null) {
            Utils.error("Should not have signature = null for '" + predName + "'.");
        }
        for (Term term : signature) {
            if (Function.isaConsCell(term)) {
                counter++; // We need to skip lists, since they can be of variable length.
            }
            else if (term.isGrounded()) {
                TypeSpec spec = typeSpecList.get(counter);
                Type thisType = ((spec.mustBeThisValue()) ? null : spec.isaType); // Cannot do type inferencing when the specification is for a SPECIFIC value.
                if (firstTime) {
                    argTypes.add(thisType);
                }
                else if (argTypes.get(counter) != thisType) {
                    Utils.println("%  Because type='" + thisType + "' is inconsistent with " + predName + argTypes + ", cannot infer constants from argument #" + (counter + 1) + " in mode = " + typeSpecList);
                    ambiguous.add(counter); // Was 'break' but should be able to walk through the other terms.
                }
                counter++;
            }
//            else if (term instanceof Function) {
//                Function f = (Function) term;
//                help_collectImplicitTypeConstantsViaModeAndFactInspection(ambiguous, f.getArguments(), predName, counter, firstTime, typeSpecList, argTypes);
//                counter += f.countLeaves();
//            }
            else {
                Utils.error("Should not have term = " + term);
            }
        }
    }

    // Check all constants in facts and make sure they are typed (and uniquely!).
    public boolean checkThatTypesOfAllConstantsAreKnown(PrintStream printStream, Iterable<Sentence> backgroundFacts) {
        boolean untypedConstantFound = false;
        Set<Term> alreadyCheckedHash = new HashSet<Term>(1024);

        if (backgroundFacts != null) {
            for (Sentence sentence : backgroundFacts) {
                if (sentence instanceof Literal) {
                    Literal fact = (Literal) sentence;

                    if (fact.predicateName.hasMatchingMode(fact)) {
                        for (Term arg : fact.getArguments()) {
                            if (arg.isGrounded()) {
                                if (alreadyCheckedHash.contains(arg)) {
                                    continue;
                                } // Already checked this constant.
                                if (stringHandler.getTypesOfConstant(arg, false) == null) {
                                    if (!untypedConstantFound) {
                                        Utils.println(MessageType.ISA_HANDLER_TYPE_INFERENCE, "\n% The type of the following constants are not known: ");
                                        if (printStream != null) {
                                            printStream.println("\n% The type of the following constants are not known: ");
                                        }
                                        untypedConstantFound = true;
                                    }
                                    Utils.println(MessageType.ISA_HANDLER_TYPE_INFERENCE, "%  " + arg + "  [from: " + fact + "]");
                                    if (arg instanceof NumericConstant && stringHandler.isaHandler.isa(stringHandler.isaHandler.getIsaType("number"), stringHandler.isaHandler.getIsaType("willAnything"))) {
                                        Utils.println(MessageType.ISA_HANDLER_TYPE_INFERENCE, "%  Inferring that '" + arg + "' is of type 'number'.");
                                        if (printStream != null) {
                                            printStream.println("%  Inferring that '" + arg + "' is of type 'number'.");
                                        }
                                        addNewConstant(printStream, stringHandler, arg, stringHandler.isaHandler.getIsaType("number"), fact);
                                    }
                                    else {
                                        Utils.println(MessageType.ISA_HANDLER_TYPE_INFERENCE, "%  Inferring that '" + arg + "' is of type 'willAnything'.");
                                        if (printStream != null) {
                                            printStream.println("%  Inferring that '" + arg + "' is of type 'willAnything'.");
                                        }
                                        addNewConstant(printStream, stringHandler, arg, stringHandler.isaHandler.getIsaType("willAnything"), fact);
                                    }
                                }
                                alreadyCheckedHash.add(arg);
                            }
                        }
                    }
                }
            }
        }
        if (untypedConstantFound) {
            Utils.warning("checkThatTypesOfAllConstantsAreKnown: Note that there were some constants whose type was not known (see list above or in dribble file).");
        }
        if (debugLevel > 0) {
            Utils.println("\n% Have confirmed that the type is known for each constant in the facts file that matches at least one provided mode.");
        }
        //Utils.waitHere();
        return true;
    }
    // Since we only allow one mode specification of the head, we can use that to infer the types of constants.
    // TODO - is this buggy if the mode of the head uses a type that is not a "base level" type, e.g. Animal instead of Dog?
    private int warningCounter = 0;

    public int recordTypedConstantsFromTheseExamples(PrintStream printStream, List<Example> examples, String exampleType, PredicateName targetPredicate, List<ArgSpec> targetArgSpecs) {
        //if (targetPredicate == null)  { Utils.error("Cannot have targetPredicate=null here."); }
        //if (targetModes     == null)  { Utils.error("Cannot have targetModes=null here.");     }
        //if (targetArgSpecs  == null)  { Utils.error("Cannot have targetArgSpecs=null here.");  }
        //if (targetModes.size() > 1)   { Utils.error("Cannot have size(targetModes) > 1.");     }
        if (examples == null) {
            return 0;
        }

        // Collect all the constants in the specified set of examples.
        int countOfAdds = 0;
        int countOfDups = 0;
        for (Literal ex : examples) {
            if (targetPredicate != ex.predicateName) { // && warningCounter++ < 10) {
                // This would be handled later by the next call to recordTyped...
                // Utils.warning(" TypeManagement Warning #" + Utils.comma(warningCounter) + ":  Have an example, '" + ex + "', that doesn't match target predicate = '" + targetPredicate + "'.");
                continue;
            }
            int counter = 0;
            for (Term arg : ex.getArguments()) {
                if (Function.isaConsCell(arg)) {
                    counter++; // We need to skip lists, since they can be of variable length.
                }
                else if (arg.isGrounded()) {
                    if (counter >= targetArgSpecs.size()) {
                        Utils.error("#args do not match!  TargetArgSpecs = " + targetArgSpecs + " while ex = " + ex);
                    }
                    ArgSpec spec = targetArgSpecs.get(counter);
                    if (addNewConstant(printStream, stringHandler, arg, spec.typeSpec.isaType, ex)) {
                        countOfAdds++;
                    }
                    else {
                        countOfDups++;
                    }
                    counter++;
                }
                else if (arg instanceof Function) {
                    Function f = (Function) arg;
                    counter += f.countLeaves();
                }
                else if (arg instanceof Variable) {
                    Utils.writeMe("Should not have variables here: " + arg + " for: " + targetPredicate);
                }
                else {
                    Utils.writeMe("Have a type here for which code needs to be written: " + arg);
                }
            }
        }
        if (debugLevel > 0) {
            Utils.println("  Have recorded " + Utils.comma(countOfAdds) + " new typed constants from the " + Utils.comma(examples) + " " + exampleType + " examples.  Ignored " + Utils.comma(countOfDups) + " duplications.");
        }
        return countOfAdds;
    }

    private int reportCounter = 0;
    // See if this is a new constant of this type.
    public boolean addNewConstant(PrintStream printStream, HandleFOPCstrings stringHandler, Term constant, Type type, Literal generator) {
        if (generator == null) {
            Utils.error("Cannot have generator=null.");
        }
        PredicateName predName = generator.predicateName;
        int predArity = generator.numberArgs();
        if (debugLevel > 1) {
            Utils.println(MessageType.ISA_HANDLER_TYPE_INFERENCE, "Constant '" + constant + "' is being marked as type '" + type + "' by PredicateName = '" + predName + "' which has types = " + predName.getTypeList());
        }
        String name = constant.toString();
        if (name == null) {
            Utils.error("Have no name for this constant: '" + constant + "' from " + generator);
        } // Not sure printing constant here will do anything, but might as well try.
        // See comment next line.  Type constantAsType = stringHandler.getIsaType(constant.getName());
        // I (jws) no longer think this is needed: if (stringHandler.reverseIsa(constantAsType) != null) { Utils.error("This code assumes that type '" + constantAsType + "' is a LEAF in the type hierarchy, but instead it has these children: '" + Utils.limitLengthOfPrintedList(stringHandler.reverseIsa(constantAsType), 25) + "'."); }
        Set<Term> knownConstants = stringHandler.getConstantsOfExactlyThisType(type);

        if (knownConstants != null && knownConstants.contains(constant)) {
            if (debugLevel > 1) {
                Utils.println("Already in the map.");
            }
            return false;
        } // Already in the map.
        if (stringHandler.getTypesOfConstant(constant, false) != null) { // See if any types of this constant are already known.

            List<Type> existingTypes = stringHandler.getTypesOfConstant(constant, false);
            if (existingTypes != null) {
                for (int i = 0; i < existingTypes.size(); i++) {
                    Type existing = existingTypes.get(i);

                    // If the new type is a superclass of an existing type, don't add.
                    if (stringHandler.isaHandler.isa(existing, type)) {
                    	reportCounter++;
                        if (reportCounter <= 25 && debugLevel > 1) {
                            Utils.println(MessageType.ISA_HANDLER_TYPE_INFERENCE, "%    Term '" + constant + "' is already known to be of type '" + existing + ",' so ignoring that it is of parent type '" + type + ".'");
                            if (reportCounter == 25) { Utils.println(MessageType.ISA_HANDLER_TYPE_INFERENCE, "% (Future reports will be suppressed since 25 have been reported.)"); }
                        }
                        return false;
                    }

                    // If the new type is a subclass of an existing type, remove the old attachment to this constant, since the ISA hierarchy contains this information.
                    if (stringHandler.isaHandler.isa(type, existing)) {
                    	reportCounter++;
                        if (reportCounter <= 25 && debugLevel > -1) {
                            Utils.println(MessageType.ISA_HANDLER_TYPE_INFERENCE, "% Already know '" + constant + "' isa '" + existing + ",' but now being told it isa '" + type + ",' which is LOWER in the isa hierarchy.  Editing the hierarchy.");
                            if (reportCounter == 25) { Utils.println(MessageType.ISA_HANDLER_TYPE_INFERENCE, "% (Future reports will be suppressed since 25 have been reported.)"); }
                         }  // TODO figure out what to do here (move isa's around?)
                        // TAW: This used to be: stringHandler.constantToTypesMap.remove(existing).
                        // TAW: However, that was obviously a typo, since constantToTypesMap uses
                        // TAW: constants as keys, not Types.  I change it to the constant being checked.
                        stringHandler.constantToTypesMap.remove(constant); // Remove this since the ISA hierarchy already knows it.
                    }
                }
            }

            if (beenWarnedHashMap == null) {
                beenWarnedHashMap = new HashMap<PredicateName, Set<Type>>(4);
            }
            Set<Type> lookup1a = beenWarnedHashMap.get(predName);  // See if there has been a warning about this type from this predicate.
            if (lookup1a == null) {
                lookup1a = new HashSet<Type>(4);
                beenWarnedHashMap.put(predName, lookup1a);
            }
            if (!lookup1a.contains(type)) { // TODO clean up these two println's
                if (!predName.dontComplainAboutMultipleTypes(predArity) && !dontWorryAboutTheseTypes(existingTypes)) {
                    Utils.println(MessageType.ISA_HANDLER_TYPE_INFERENCE, "\n%   *** WARNING ***  Constant '" + constant + "' is already marked as being of types = " + existingTypes
                            + ";\n%          type = '" + type + "' may be added if not already known.\n%  PredicateName = '" + predName + "', from '" + generator + "',\n%  which has types = " + predName.getTypeList()
                    //        + ".\n%    All generators: " + constant.getGeneratorOfThisConstantsType()
                            + "\n%   Other warnings with this predicate and this new type are not reported in order to keep this printout small.  Use dontComplainAboutMultipleTypes to override.");

                    // Utils.waitHere();
                }
                lookup1a.add(type);
            }
        }

        if (addedConstantHashMap == null) {
            addedConstantHashMap = new HashMap<Term, Map<Type, Literal>>(1024);
        }
        Map<Type, Literal> lookup1b = addedConstantHashMap.get(constant);  // See if this constant has been already assigned to another type, and if so report the literal that caused it to be so.
        if (lookup1b != null && !lookup1b.containsKey(type)) { // Just report the FIRST conflict, since the others can be traced back from the reports (i.e., the first one doesn't know it is a duplicate).
            if (/* !surpressWarning && */!predName.dontComplainAboutMultipleTypes(predArity) && !dontWorryAboutTheseTypes(lookup1b)) {
                if (debugLevel > 1) {
                    Utils.println(MessageType.ISA_HANDLER_TYPE_INFERENCE, "%                    Constant '" + constant + "' was initially marked " + lookup1b);
                }
            }
        }
        if (lookup1b == null) {
            lookup1b = new HashMap<Type, Literal>(4);
            addedConstantHashMap.put(constant, lookup1b);
        }
        if (!lookup1b.containsKey(type)) {
            lookup1b.put(type, generator);
        }
        // Possibly this line should be much earlier in this method, but the other warnings can be helpful.
        Type newType = stringHandler.isaHandler.getIsaType(constant.toString());
        if (newType != type && !stringHandler.isaHandler.okToAddToIsa(newType, type)) { // OK to add constant with same name as type.
            if (debugLevel > 1) {
                Utils.println(MessageType.ISA_HANDLER_TYPE_INFERENCE, "Not OK to add '" + newType + "' isa '" + type + "'.");
            }
            return false;
        }
        if (printStream != null) {
            printStream.println("isa: " + constant + " isa " + type + ";");
        }
        if (debugLevel > 1) {
            Utils.println("addNewConstantOfThisType: '" + constant + "' isa '" + type + "'");
        }
        stringHandler.addNewConstantOfThisType(constant, type);
        //constant.addGeneratorOfThisConstantsType(generator);
        return true;
    }

    private boolean dontWorryAboutTheseTypes(Map<Type, Literal> types) {
        if (types == null) {
            return true;
        }
        for (Type type : types.keySet()) {
            if (!dontWorryAboutThisType(type)) {
                return false;
            }
        }
        return true;
    }

    private boolean dontWorryAboutTheseTypes(List<Type> types) {
        if (types == null) {
            return true;
        }
        for (Type type : types) {
            if (!dontWorryAboutThisType(type)) {
                return false;
            }
        }
        return true;
    }

    private boolean dontWorryAboutThisType(Type type) {
        return type.typeName.equalsIgnoreCase("willAnything") || type.typeName.equalsIgnoreCase("willList");
    }
}
