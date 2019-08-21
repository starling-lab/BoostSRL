/**
 * 
 */
package edu.wisc.cs.will.DataSetUtils;

import java.io.Reader;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.ConsCell;
import edu.wisc.cs.will.FOPC.Constant;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Type;
import edu.wisc.cs.will.FOPC.UniversalSentence;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.ResThmProver.HornClauseProver;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

/**
 * @author shavlik
 * 
 * Note: when looking for typed constants for generated negative examples, only FACTS (and not rules) are currently used.  TODO - or maybe not?
 *
 */
public class CreateSyntheticExamples {
	protected final static int debugLevel = 0; // Used to control output from this class (0 = no output, 1=some, 2=much, 3=all).


	public static List<WorldState> createWorldStatesWithNoPosExamples(HandleFOPCstrings   stringHandler,
																	  FileParser parser,
																	  HornClauseProver    prover,
			  														  List<Example>       posExamples) throws SearchInterrupted {
		return createWorldStatesWithNoPosExamples(stringHandler, parser, prover, posExamples, null);
	}
	public static List<WorldState> createWorldStatesWithNoPosExamples(HandleFOPCstrings stringHandler,
																      FileParser        parser,
			  														  HornClauseProver  prover,
			  														  List<Example>     posExamples,
			  														  String            worldStateName) throws SearchInterrupted {
		List<Sentence> collectorList = parser.readFOPCstream("findAll(worldState(X,Y), worldState(X,Y), All).");
		Literal allWorldStatesQuery = (Literal) ((UniversalSentence) collectorList.get(0)).body;
		BindingList bl = prover.proveSimpleQueryAndReturnBindings(allWorldStatesQuery);
		Term answers = bl.lookup((Variable) allWorldStatesQuery.getArguments().get(2));
		
		List<Term> groundings = ((ConsCell) answers).convertConsCellToList();
		if (groundings == null) { return null; }
		List<WorldState> results = new ArrayList<WorldState>(groundings.size());
		for (Term worldState : groundings) {
			List<Term> args = ((Function) worldState).getArguments();
			Constant  world = (Constant) args.get(0);
			Constant  state = (Constant) args.get(1);
			if (!matchToSomePosExampleWorldState(stringHandler, world, state, posExamples)) { results.add(new WorldState(world, state)); }
		}
		return results;
	}
	
	private static boolean matchToSomePosExampleWorldState(HandleFOPCstrings stringHandler, Constant world, Constant state, List<Example> posExamples) {
		if (posExamples == null) { return false; }
		int posOfWorld = stringHandler.locationOfWorldArg;
		int posOfState = stringHandler.locationOfStateArg;
		for (Example pos : posExamples) {
			if (pos.getArguments().get(stringHandler.getArgumentPosition(posOfWorld, pos.numberArgs())) == world && 
				pos.getArguments().get(stringHandler.getArgumentPosition(posOfState, pos.numberArgs())) == state) { return true; }
		}
		return false;
	}
	
	// Note: any realNegExamples are also returned, since we might need to write all the negative examples to negExamplesFile.
	public static List<Example> createImplicitNegExamples(List<WorldState>    worldStatesToProcess,
												  		  boolean             usingWorldStates,
														  String              provenanceString,
														  Boolean             createCacheFiles, 
														  HandleFOPCstrings   stringHandler,
														  HornClauseProver    prover,
														  List<Literal>       targets, 
														  List<List<ArgSpec>> targetArgSpecs, 
														  List<List<Term>>    targetPredicateSignatures,
														  List<Example>       posExamples, 
														  List<Example>       realNegExamples,
														  Reader              negExamplesReader, 
														  double fractionOfImplicitNegExamplesToKeep,
                                                          Set<PredicateNameAndArity> factPredicates) { // If > 1.1 (allow 0.1 of buffer), then we'll keep this NUMBER of generated examples.
		
		if (debugLevel > 0 && fractionOfImplicitNegExamplesToKeep <= 1.1) { Utils.println("% When creating synthetic examples, keeping at most this fraction of the possible negative examples: " + fractionOfImplicitNegExamplesToKeep);       }
		if (debugLevel > 0 && fractionOfImplicitNegExamplesToKeep >  1.1 && fractionOfImplicitNegExamplesToKeep < Integer.MAX_VALUE) { Utils.println("% Keeping at most this many negative examples: " + (int) fractionOfImplicitNegExamplesToKeep); }
		
		if (usingWorldStates && worldStatesToProcess == null) {
			int size = Utils.getSizeSafely(posExamples);
			if (realNegExamples != null) { size += Utils.getSizeSafely(realNegExamples); }
			
			if (size > 0 ) { worldStatesToProcess = new ArrayList<WorldState>(size); }		
			if (posExamples != null) {
				for (Example ex : posExamples) {
					int  numbArgs = ex.numberArgs();
					WorldState ws = new WorldState((Constant) ex.getArguments().get(stringHandler.getArgumentPosition(stringHandler.locationOfWorldArg, numbArgs)),
												   (Constant) ex.getArguments().get(stringHandler.getArgumentPosition(stringHandler.locationOfStateArg, numbArgs)));
					if (!worldStatesToProcess.contains(ws)) { worldStatesToProcess.add(ws); }
				}
			}
			if (realNegExamples != null) {
				for (Example ex : realNegExamples) {
					int  numbArgs = ex.numberArgs();
					WorldState ws = new WorldState((Constant) ex.getArguments().get(stringHandler.getArgumentPosition(stringHandler.locationOfWorldArg, numbArgs)),
												   (Constant) ex.getArguments().get(stringHandler.getArgumentPosition(stringHandler.locationOfStateArg, numbArgs)));
					if (!worldStatesToProcess.contains(ws)) { worldStatesToProcess.add(ws); }
				}
			}
		}
		
		List<Example> negExamples = null;		
		if (targets != null) for (int i = 0; i < targets.size(); i++) {
			List<Example>  thisTargetExamples = createAllPossibleExamples(provenanceString, stringHandler, prover, targets.get(i),
															              targetArgSpecs.get(i), targetPredicateSignatures.get(i), worldStatesToProcess, posExamples, realNegExamples, factPredicates);
			if (negExamples == null) { negExamples = thisTargetExamples; }
			else                     { negExamples.addAll(thisTargetExamples); }
		}
		int numbRealExamples       = Utils.getSizeSafely(realNegExamples);
		int totalNegsCreated       = Utils.getSizeSafely(negExamples);
		int desiredExamplesCreated = (fractionOfImplicitNegExamplesToKeep <= 1.1 ? (int) (Math.min(1.0, fractionOfImplicitNegExamplesToKeep) * Utils.getSizeSafely(negExamples))
																			     : (int)                fractionOfImplicitNegExamplesToKeep)
									 ; // - numbRealExamples;  // The caller has already subtracted this.
		if (       debugLevel > 2) { Utils.println("% Have " + Utils.comma(negExamples) + " and want " + Utils.comma(desiredExamplesCreated) + " negative examples. fractionOfImplicitNegExamplesToKeep=" + fractionOfImplicitNegExamplesToKeep ); }
		if (totalNegsCreated > desiredExamplesCreated) {
			negExamples = Utils.chooseRandomNfromThisList(desiredExamplesCreated, negExamples);
			if (   debugLevel > 2) { Utils.println("% Now have " + Utils.comma(negExamples) + " negative examples after down-sampling the randomly generated ones."); }
		} else if (desiredExamplesCreated < Integer.MAX_VALUE && desiredExamplesCreated > totalNegsCreated) {
			if (   debugLevel > 2) { Utils.println("% Have only created " + Utils.comma(totalNegsCreated) + " negative examples, which is " + Utils.comma(desiredExamplesCreated - totalNegsCreated) + " short of the requested " + Utils.comma(desiredExamplesCreated) + "."); }
		} else if (debugLevel > 2) { Utils.println("% Have created " + Utils.comma(negExamples) + " implicit negative examples (each " + provenanceString + ")");  } 
		if (       debugLevel > 2) { Utils.waitHere("Have " + Utils.comma(negExamples) + " and want " + Utils.comma(desiredExamplesCreated) + " negative examples."); }
		// Don't lose the 'real' negatives.
		if (numbRealExamples > 0) { negExamples.addAll(realNegExamples); }
		/* TODO - NOW DONE IN ILPouterLoop   if we really need this, then pass along a file name or a directory, etc.  The old way (ie, below) risked creating pseudo negs from pseudo negs.,
		if (createCacheFiles && negExamplesReader != null) {
			if (debugLevel > 0) { Utils.println("%  Writing " + negExamples.size() + " negative examples to " + negExamplesFile + "."); }
			if (fractionOfImplicitNegExamplesToKeep <= 1.1) { Example.writeObjectsToFile(negExamplesFile, negExamples, ".", "// Kept this fraction of the possible negatives: " + fractionOfImplicitNegExamplesToKeep); }
			if (fractionOfImplicitNegExamplesToKeep >  1.1) { Example.writeObjectsToFile(negExamplesFile, negExamples, ".", "// Kept this many of the possible negatives: " + (int) fractionOfImplicitNegExamplesToKeep); }
		}
		else if (createCacheFiles) { 
			Utils.println("% Warning: the negative examples are NOT being saved to a file.  Is this desired?"); 
			Utils.waitHere();
		}
		*/
		// Utils.waitHere();
		return negExamples;
	}
	
	// Create all possible examples for this target predicate, with the specified argument types and signature, from these world-states.
	// Filter those in the 'exceptions' lists (two are provided since often these will be provided positive and negative examples).  TODO - provide a LIST of exception lists?
	public static List<Example> createAllPossibleExamples(String            provenanceString,
														  HandleFOPCstrings stringHandler,
														  HornClauseProver  prover,
														  Literal           target,
														  List<ArgSpec>     targetArgSpecs,
														  List<Term>        targetPredicateSignature,
														  List<WorldState>  worldStatesToProcess,
														  List<Example>     exceptions1,
			  								              List<Example>     exceptions2,
                                                          Set<PredicateNameAndArity> factPredicates) {
		if (target                   == null) { Utils.warning("Can NOT have target == null!");                   return null; }
		if (targetArgSpecs           == null) { Utils.warning("Can NOT have targetArgSpecs == null!");           return null; }
		if (targetPredicateSignature == null) { Utils.warning("Can NOT have targetPredicateSignature == null!"); return null; }
		int numbArgs = targetPredicateSignature.size();
		boolean usingWorldStates = (worldStatesToProcess != null);
		List<WorldState>  worldStatesToProcess2 = worldStatesToProcess;		
		if (!usingWorldStates) {
			worldStatesToProcess2 = new ArrayList<WorldState>(1);
			worldStatesToProcess2.add(new WorldState(null, null)); // Create a dummy world state, so the FOR LOOP below is used once.
		}
			
		if (debugLevel > 0) { Utils.println("\n% Creating some possible examples with " + numbArgs + " getArguments().  Signature = " + targetPredicateSignature + ".  Reason for each: " + provenanceString + "."); }
		Set< Example>  resultsAsSet      = new HashSet<  Example>(4); // Use this to quickly look for duplicates.
		List<Example>  results           = new ArrayList<Example>(4);
		Constant       dummyConstant     = stringHandler.getStringConstant("Dummy"); // Need a filler for the positions from which we don't extract.
		Set<Term>      dummyConstantSet  = new HashSet<Term>(4);
		dummyConstantSet.add(dummyConstant);
		for (WorldState worldState : worldStatesToProcess2) {
			if (debugLevel > 1 && usingWorldStates) { Utils.println("%    WorldState: " + worldState); }
			List<Set<Term>> crossProduct = new ArrayList<Set<Term>>(targetPredicateSignature.size());
			int             leafCounter  = 0;
			for (int argCounter = 0; argCounter < numbArgs; argCounter++) { // Look at each argument in the target's specification.
				Term sig = targetPredicateSignature.get(argCounter);
				if (debugLevel > 1) { Utils.println("\n% signature item = " + sig); }
				
				if (usingWorldStates && argCounter == stringHandler.getArgumentPosition(stringHandler.locationOfWorldArg, numbArgs)) { 
					if (debugLevel > 1) { Utils.println("%   Using the current WORLD argument."); }
					crossProduct.add(dummyConstantSet); 
					leafCounter++;
					continue; 
				}
				if (usingWorldStates && argCounter == stringHandler.getArgumentPosition(stringHandler.locationOfStateArg, numbArgs)) { 
					if (debugLevel > 1) { Utils.println("%   Using the current STATE argument."); }
					crossProduct.add(dummyConstantSet);
					leafCounter++;
					continue; 
				}
				
				Set<Term> groundedTermsOfThisTypeInThisState = null;
				if (sig instanceof Constant) {
					groundedTermsOfThisTypeInThisState = getConstantsOfThisTypeInThisWorldState(stringHandler, targetArgSpecs.get(leafCounter), worldState, prover.getClausebase().getFacts(), factPredicates);
					if (groundedTermsOfThisTypeInThisState == null) { // If none in the state, grab 'globally.'
						groundedTermsOfThisTypeInThisState = getConstantsOfThisTypeInThisWorldState(stringHandler, targetArgSpecs.get(leafCounter), null, prover.getClausebase().getFacts(), factPredicates);
					}
					if (groundedTermsOfThisTypeInThisState == null) { crossProduct = null; break; } // Cannot make any examples from this state since no constants of the necessary type.
					if (debugLevel > 1) { 
						Utils.println("%   For argument #" + argCounter + " (leaf #" + leafCounter + "), constants of type='" + targetArgSpecs.get(leafCounter).typeSpec + "' in world-state='" + worldState + "':"); 
						Utils.println("%      " + Utils.limitLengthOfPrintedList(groundedTermsOfThisTypeInThisState));
					}
					if (debugLevel > 2) { Utils.println("% Existing groundedTermsOfThisTypeInThisState '" + targetArgSpecs.get(leafCounter) + "':\n%   " + Utils.limitLengthOfPrintedList(groundedTermsOfThisTypeInThisState)); }
					leafCounter++;
                } else if (sig instanceof ConsCell) {
                    groundedTermsOfThisTypeInThisState = new HashSet<Term>();
                    groundedTermsOfThisTypeInThisState.add( stringHandler.getNil() );
                    leafCounter++;
				} else if (sig instanceof Function) {
					Function f = (Function) sig;
					groundedTermsOfThisTypeInThisState = createGroundFunctionsInThisWorldState(stringHandler, f, leafCounter, targetArgSpecs, worldState, prover, factPredicates);
					if (groundedTermsOfThisTypeInThisState == null) { // If none in the state, grab 'globally.'
						groundedTermsOfThisTypeInThisState = createGroundFunctionsInThisWorldState(stringHandler, f, leafCounter, targetArgSpecs, null, prover, factPredicates);
					}
					if (groundedTermsOfThisTypeInThisState == null) { crossProduct = null; break; } // Cannot make any examples from this state since no constants of the necessary type.
					if (debugLevel > 1) { 
						Utils.println("%   For function with signature '" + sig + "', grounded instances in world-state='" + worldState + "':"); 
						Utils.println("%      " + Utils.limitLengthOfPrintedList(groundedTermsOfThisTypeInThisState));
					}
					if (debugLevel > 2) { Utils.println("% Existing groundedFunctionsInThisState for this signature '" + f + "':\n%   " + Utils.limitLengthOfPrintedList(groundedTermsOfThisTypeInThisState)); }
					leafCounter += f.countLeaves(); // Need to know where we are in the targetArgSpecs.					
				} else { Utils.error("Cannot handle this type here: " + sig); }
				crossProduct.add(groundedTermsOfThisTypeInThisState);
			}
			if (crossProduct != null) {
				List<List<Term>> allPossibilities = Utils.computeCrossProduct(crossProduct);
				if (debugLevel > 2) { Utils.println("% CrossProduct [#=" + Utils.comma(allPossibilities) + "] = " + Utils.limitLengthOfPrintedList(allPossibilities)); }
				int counter = 0;
				for (List<Term> args : allPossibilities) {
					counter++;
					if (counter % 1000 == 0) { Utils.println("%   Have considered " + Utils.comma(counter) + " possible negative examples for " + worldState + "."); }
					Example  example  = new Example(stringHandler, target.predicateName, null, provenanceString + (usingWorldStates ? " (" + worldState + ")." : "."), "createdNeg", null);
					List<Term> arguments2 = new ArrayList<Term>(numbArgs);
					for (int argCounter = 0; argCounter < numbArgs; argCounter++) {
						if      (usingWorldStates && argCounter == stringHandler.getArgumentPosition(stringHandler.locationOfWorldArg, numbArgs)) { arguments2.add(worldState.getWorld()); }
						else if (usingWorldStates && argCounter == stringHandler.getArgumentPosition(stringHandler.locationOfStateArg, numbArgs)) { arguments2.add(worldState.getState()); }
						else { arguments2.add(args.get(argCounter));	}
					}
					example.setArguments(arguments2);
					if (!resultsAsSet.contains(example) &&   // Watch for duplicates, both newly created and those in the exceptions lists..
						(exceptions1 == null || !exceptions1.contains(example)) && 
						(exceptions2 == null || !exceptions2.contains(example))) {
						 if (debugLevel > 1) { Utils.println("% Newly created candidate-negative example #" + Utils.comma(results) + ": " + example); }
						results.add(     example); 
						resultsAsSet.add(example);
						if (results.size() % 1000 == 0) { Utils.println("%   Have randomly created " + Utils.comma(results) + " putative negative examples."); }
					}
					else if (debugLevel > 1) { Utils.println((resultsAsSet.contains(example) ? "%    Already collected: " : "%    Already in an exceptions list: ") + example); }
				}
			}
		}
		if (debugLevel > 1) { Utils.println("% createAllPossibleExamples: Have created " + Utils.getSizeSafely(results) + " examples."); }
		return results;
	}
	
	private static Set<Term> createGroundFunctionsInThisWorldState(HandleFOPCstrings stringHandler, 
																	Function         f, 
																	int              leafCounter,
																	List<ArgSpec>    targetArgSpecs,
																	WorldState       worldState,
																	HornClauseProver prover,
                                                                    Set<PredicateNameAndArity> factPredicates) {
        if (f == null || f.numberArgs() < 1) {
            Utils.error("Functions without getArguments() should not be used since no 'type' information is available.");
        }
		List<Set<Term>> crossProduct = new ArrayList<Set<Term>>(f.numberArgs());
		int currentCounter = leafCounter;
		for (Term term : f.getArguments()) {
			if (term instanceof Constant) {
				Set<Term> groundedTermsOfThisTypeInThisState = getConstantsOfThisTypeInThisWorldState(stringHandler, targetArgSpecs.get(currentCounter), worldState, prover.getClausebase().getFacts(), factPredicates);
				if (groundedTermsOfThisTypeInThisState == null) { 
					if (debugLevel > 1 || worldState == null) { Utils.println(" No grounded terms for " + targetArgSpecs.get(currentCounter) + " in " + worldState); }
					return null; 
				}
				crossProduct.add(groundedTermsOfThisTypeInThisState);
				currentCounter++;
    		} else if (Function.isaConsCell(term)) {
    			// We need to skip lists, since they can be of variable length. 
    			Utils.warning("Creating a synthetic example with a list in it; currently only using the empty list in these cases.");
    			crossProduct.add(stringHandler.getSetNil()); // We'll simply stick in an empty list, but that isn't what we really want.
    			currentCounter++;
    		} else if (term instanceof Function) {
				Set<Term> groundedTermsOfThisTypeInThisState = createGroundFunctionsInThisWorldState(stringHandler, (Function) term, currentCounter, targetArgSpecs, worldState, prover, factPredicates);
				if (groundedTermsOfThisTypeInThisState == null) {
					if (debugLevel > 1 || worldState == null) { Utils.println(" No grounded versions for " + term + " in " + worldState); }
					return null; 
				}
				crossProduct.add(groundedTermsOfThisTypeInThisState);
				currentCounter += countLeavesInThisFunction((Function) term); // Need to know where we are in the targetArgSpecs.
			} else { Utils.error("Cannot handle this type here: " + term); }
		}
		if (debugLevel > 0) { Utils.println("%      For '" + f  + "', [leaves " + leafCounter + " to " + currentCounter + "] crossProduct = " + Utils.limitLengthOfPrintedList(crossProduct)); }
		List<List<Term>> allPossibilities = Utils.computeCrossProduct(crossProduct);
		if (debugLevel > 0) { Utils.println("%        results: " + Utils.limitLengthOfPrintedList(allPossibilities)); }
		Set<Term>        results          = new HashSet<Term>(allPossibilities.size());
		for (List<Term> args : allPossibilities) {
			results.add(stringHandler.getFunction(f.functionName, args, f.getTypeSpec()));
		}
		return results;
	}
	private static int countLeavesInThisFunction(Function f) {
		if (f == null || f.numberArgs() < 1) { Utils.error("Functions without getArguments() should not be used since no 'type' information is available."); }
		int total = 0;
		for (Term term : f.getArguments()) {
			if (term instanceof ConsCell) {
				// We need to skip lists, since they can be of variable length.
			}
			else if (term instanceof Function) { total +=  countLeavesInThisFunction((Function) term); }
			else { total++; }
		}
		return total;
	}
	
	private static Set<Term> getConstantsOfThisTypeInThisWorldState(HandleFOPCstrings stringHandler, ArgSpec spec, WorldState worldState, Iterable<Literal> facts, Set<PredicateNameAndArity> factPredicates) {
		Type type = spec.typeSpec.isaType;
		Set<Term> results = new HashSet<Term>(4);		
		
		if (debugLevel > 0) { Utils.println("%    Collect constants of spec '" + spec + "' in world state '" + worldState + "'."); }
		if (spec.typeSpec.mustBeThisValue()) { 
			results.add(spec.arg);
			if (debugLevel > 2) { Utils.println("%     Constants of type '" + spec + "': " + Utils.limitLengthOfPrintedList(results)); }
			return results;
		}
		// Need to walk through the facts file to see if (a) a fact is true in this worldState and (b) some of its getArguments() are of the type specified by spec.
        for(Literal lit : facts) {
            if (factPredicates == null || factPredicates.contains(lit.getPredicateNameAndArity()) ) {

                int numbArgs = lit.numberArgs();
                // If worldState = null, then we ignore these special arguments.
                Term worldArg = (worldState == null || worldState.isaNullWorldState() ? null : lit.getArguments().get(stringHandler.getArgumentPosition(stringHandler.locationOfWorldArg, numbArgs)));  // Pull out the world argument.
                Term stateArg = (worldState == null || worldState.isaNullWorldState() ? null : lit.getArguments().get(stringHandler.getArgumentPosition(stringHandler.locationOfStateArg, numbArgs)));  // Pull out the state argument.

                if (worldState == null || worldState.isaNullWorldState() || worldState.equals(worldArg, stateArg)) { // See if a match.
                    help_getConstantsOfThisTypeInThisWorldState(stringHandler, type, lit.getArguments(), results);
                    Map<Integer, List<Object>> constrainInfo = lit.predicateName.getConstrainsArgumentTypes(lit.numberArgs());
                    if (constrainInfo != null) {
                        for (Integer index : constrainInfo.keySet()) {
                            Type typeConstainedTo = (Type) constrainInfo.get(index).get(0);
                            if (stringHandler.isaHandler.isa(typeConstainedTo, type)) {
                                Term arg = lit.getArguments().get(index - 1); // Recall counting from 0 here (but from 1 externally).
                                if (arg instanceof Constant) {
                                    Constant argAsConstant = (Constant) arg;
                                    boolean addResult = results.add(argAsConstant);
                                    if (debugLevel > 2 && addResult) {
                                        Utils.println("%     via constrained, arg='" + arg + "' is of type='" + type);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
		if (worldState == null && Utils.getSizeSafely(results) < 1) {
			Utils.warning("No constants for " + spec);
		}
		if (debugLevel > 2) { Utils.println("%     Constants of type '" + spec + "': " + Utils.limitLengthOfPrintedList(results)); }
		return results;		
	}
	
	private static void help_getConstantsOfThisTypeInThisWorldState(HandleFOPCstrings stringHandler, Type type, List<Term> arguments, Set<Term> results) {
		if (arguments == null) { return; }
		for (Term arg : arguments) { // If so, look at each argument and see if of the proper type (could skip locationOfWorldArg_countingLeftToRight and locationOfStateArg_countingRightToLeft, but not worth it).
			if (arg instanceof Constant) {
				Constant argAsConstant = (Constant) arg;
				if (stringHandler.isaHandler.isa(stringHandler.isaHandler.getIsaType(argAsConstant), type)) { 
					boolean addResult = results.add(argAsConstant);
					if (debugLevel > 2 && addResult) { Utils.println("%     arg='" + arg + "' is of type='" + type); }
				}
    		} else if (arg instanceof ConsCell) {
    			// We need to skip lists, since they can be of variable length.
			} else if (arg instanceof Function) {
				Function f = (Function) arg;
				help_getConstantsOfThisTypeInThisWorldState(stringHandler, type, f.getArguments(), results);
			} else if (arg instanceof Variable) {
				
			} 
            else {
				Utils.error("Need to handle this argument: " + arg);
			}
		}
	}
}
