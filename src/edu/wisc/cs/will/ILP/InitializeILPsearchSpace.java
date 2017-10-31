/**
 * 
 */
package edu.wisc.cs.will.ILP;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.DataSetUtils.ArgSpec;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Constant;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateSpec;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Type;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.Utils.MessageType;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.Initializer;
import edu.wisc.cs.will.stdAIsearch.OpenList;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

/**
 * @author shavlik
 *
 */
public class InitializeILPsearchSpace extends Initializer {

	public boolean alwaysAddMostGeneralHeadClause = true; // Should put this elsewhere and document.  TODO
	public boolean createMinGeneralHeadClause     = true;  // Use one variable per unique constant in the head.
	
	private SingleClauseNode bestNodeFromPreviousSearch;
	/**
	 * 
	 */
	public InitializeILPsearchSpace() {
	}
	
	public SingleClauseNode getBestNodeFromPreviousSearch() {
		return bestNodeFromPreviousSearch;
	}
	public void setBestNodeFromPreviousSearch(SingleClauseNode bestNodeFromPreviousSearch) {
		this.bestNodeFromPreviousSearch = bestNodeFromPreviousSearch;
	}


	public void initializeOpen(OpenList open) throws SearchInterrupted {		
		open.clear();
		
		if (bestNodeFromPreviousSearch != null) {   // If this is non-null, pick up where last search left off.
			if (task.scorer != null) { open.insertByScoreIntoOpenList(bestNodeFromPreviousSearch); }
			else                     { open.addToEndOfOpenList(       bestNodeFromPreviousSearch); } 	
		//	Utils.waitHere("% initializeOpen: " + bestNodeFromPreviousSearch + "  score = " + bestNodeFromPreviousSearch.score);
			return;
		}
		
		LearnOneClause ilpTask = (LearnOneClause) task;
		Unifier              unifier     = ilpTask.unifier;
		List<Example>        posSeeds    = ilpTask.seedPosExamples;

		List<Literal>        targets     = ilpTask.targets;
		List<List<Term>>     varLists    = ilpTask.variablesInTargets;
		List<List<ArgSpec>>  specsList   = ilpTask.targetArgSpecs;
		
		int numbTargets     = Utils.getSizeSafely(targets);
		if (numbTargets < 1) { Utils.error("Have no target concepts ..."); }
		for (int i = 0; i < Utils.getSizeSafely(targets); i++) {
			Literal            target       = targets.get(i);
			PredicateName      targetPred   = target.predicateName;
			List<Term>         variables    = varLists.get(i);
			List<ArgSpec>      specs        = specsList.get(i);
			List<Type>         typesPresent = new ArrayList<Type>(4);
			Map<Type,List<Term>> typesMap   = new HashMap<Type,List<Term>>(4);  // Collect the existing constants and variables that go with each type. 
			for (ArgSpec spec : specs) {
				Type type = spec.typeSpec.isaType;
				
				List<Term> terms = typesMap.get(type);
				if (terms != null) {
					terms.add(spec.arg);
					typesMap.put(type, terms);
				} else { // This type not yet seen.
					List<Term> termsNew = new ArrayList<Term>(1);
					termsNew.add(spec.arg);
					typesMap.put(type, termsNew);
					typesPresent.add(type);
				}
			}

			if (LearnOneClause.debugLevel > 2) { 
				Utils.println("\n%  Target #" + Utils.comma(i) + " being learned: '" + target + "',\n%  with argument types: " + specs); 
				Utils.println("%   typeList:   " + targetPred.getTypeListForThisArity(target.numberArgs())); //Utils.waitHere();
				Utils.println("%   varList:    " + variables);
				Utils.println("%   specsList:  " + specs);

			}

            if ( posSeeds == null ) throw new IllegalStateException("There are not positive seeds selected.  Maybe try LearnOneClause.selectSeedsRandomly()?");

            // Note the get(0) below is due to the weird List returned by getTypeListForThisArity.  The first
            // element of that list is the PredicateSpec and the rest of the list is other stuff.
			PredicateSpec pSpec = targetPred.getTypeListForThisArity(target.numberArgs()).get(0);  

			boolean containsMustBeConstant = containsMustBeConstantType(pSpec);
			// First look at the seeds and see if there are any restricted variablizations.
			boolean addedRestrictedVersion = false;
			List<Literal> targetsCreated = new ArrayList<Literal>(1);
			if (createMinGeneralHeadClause && !ilpTask.isaTreeStructuredTask()) for (Example posSeed : posSeeds) {  // Utils.println("posSeed=" + posSeed);
				BindingList bl = unifier.unify(posSeed, target);
				
				// NOTE: since this process can use CONSTANTS instead of variables, some things with 'var' in their name really should say 'term' - TODO: cleanup once this is better debugged.
				if (bl == null && numbTargets == 1) { Utils.error("Could not unify positive example '" + posSeed + "'\n and target '" + target+ "'."); }
				if (bl != null) { // OK to not match, since multiple seeds.
					if (containsMustBeConstant || !allUniqueBindings(bl, variables, pSpec)) {
						List<Term>         varsNeeded    = getVarsNeeded(bl, variables, pSpec); //Utils.println("varsNeeded=" + varsNeeded);
						Map<Variable,Term> newTheta      = getNewTheta(  bl, variables, pSpec);
						Literal            newTarget     = getNewTarget(target, posSeed, pSpec, newTheta); // ((Literal) target.copy()).applyTheta(newTheta);
						varsNeeded.clear();
						collectStillNeededVars(newTarget.getArguments(), varsNeeded);
						List<ArgSpec>      newSpecs      = collectNewSpecs(specs, variables, varsNeeded);
						PredicateSpec      newPspec      = pSpec;        // No need to change this, the arguments still have the same types.
						List<Type>         newTypesPresent = typesPresent; // Cannot change this, since only arguments of the SAME TYPE and value affect things (so, by definition, the types do not change).
						Map<Type,List<Term>> newTypesMap = collectNewTypes(newSpecs, variables, varsNeeded);
						if (LearnOneClause.debugLevel > 2) { 
							Utils.println(" seed         = " + posSeed);
							Utils.println(" old theta    = " + bl.theta);
							Utils.println(" new theta    = " + newTheta);
							Utils.println(" old vars     = " + variables);
							Utils.println(" new vars     = " + varsNeeded);
							Utils.println(" old target   = " + target);
							Utils.println(" new target   = " + newTarget);
							Utils.println(" old specs    = " + specs);
							Utils.println(" new specs    = " + newSpecs);
							Utils.println(" predSpec     = " + pSpec        + " [should not change]");
						//	Utils.println(" new predSpec = " + newPspec);
							Utils.println(" typesPresent = " + typesPresent + " [should not change]");
						//	Utils.println(" new typesPres= " + newTypesPresent);
							Utils.println(" old typesMap = " + typesMap);
							Utils.println(" new typesMap = " + newTypesMap); // Utils.waitHere();
						}
						// Check for duplicates here if more than one seed.
						boolean isaNewTarget = true;
						for (Literal lit : targetsCreated) {
							BindingList variants = lit.variants(newTarget, new BindingList());
							if (lit.variants(newTarget, new BindingList()) != null) { isaNewTarget = false; break; }
						}
						if (isaNewTarget) {
							SingleClauseRootNode targetAsSearchNode2 = new SingleClauseRootNode(ilpTask, newTarget, newSpecs, varsNeeded, newPspec, newTypesPresent, newTypesMap);
							if (task.scorer != null) { open.insertByScoreIntoOpenList(targetAsSearchNode2); }
							else                     { open.addToEndOfOpenList(       targetAsSearchNode2); }
						
							// Note: can cover 0, even if covering the seed, if the total number covered is less than the minimum specified.
							if (LearnOneClause.debugLevel > -1) { 
								Utils.println("% New min-general root: " + targetAsSearchNode2 + "  score = " + Utils.truncate(targetAsSearchNode2.score, 3));
								//	Utils.waitHere(); 							
							}
							addedRestrictedVersion = true;
						}
					}
				}
			}
			
			//  Utils.println("% addedRestrictedVersion=" + addedRestrictedVersion);
			
			// Stick in the version with all unique variables if no restricted version created (or requested to do so regardless).
			// See chooseTargetMode for how the mode for the head is chosen.
			if (!addedRestrictedVersion || alwaysAddMostGeneralHeadClause) {
				
				if (containsMustBeConstant) {
					// If this code is ever written, should ONLY constrain the specified arguments using one or all of the seeds.
					Utils.warning("TODO: Should handle this case by altering the target in the 'must be constant' arguments.  Or maybe an '@' type was meant?");
				}
				boolean isaNewTarget = true;
				for (Literal lit : targetsCreated) {
					BindingList variants = lit.variants(target, new BindingList());
					if (variants != null) { isaNewTarget = false; break; }
				}
				// Utils.println("isaNewTarget=" + isaNewTarget);
				if (isaNewTarget) {
					SingleClauseRootNode targetAsSearchNode = new SingleClauseRootNode(ilpTask, target, specs, variables, pSpec, typesPresent, typesMap);
					if (task.scorer != null) { open.insertByScoreIntoOpenList(targetAsSearchNode); }
					else                     { open.addToEndOfOpenList(       targetAsSearchNode); } // We want any specific heads to be tried first.
					if (LearnOneClause.debugLevel > -1) { 
						Utils.println(MessageType.ILP_INNERLOOP, "% Most-general root: " + targetAsSearchNode + "  score = " + Utils.truncate(targetAsSearchNode.score, 3));
					//	Utils.waitHere("% |open| = " + open.size());
					}
				}
			}			
		}
	}
	
	private void collectStillNeededVars(List<Term> arguments, List<Term> neededVars) {
		if (arguments == null) { return; }
		for (Term arg : arguments) {
			if      (arg instanceof Variable) { if (!neededVars.contains(arg)) { neededVars.add(arg); } }
			else if (arg instanceof Constant) { if (!neededVars.contains(arg)) { neededVars.add(arg); } }
			else if (arg instanceof Function) {
				collectStillNeededVars(((Function) arg).getArguments(), neededVars);
			} else {Utils.error("Should not reach here .."); }
		}
		
	}
	
	/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	// TODO - clean up and merge some/all of these ...  (they all are a bit different though, so might need to be the same).
	
	private boolean containsMustBeConstantType(PredicateSpec spec) {
		for (TypeSpec tSpec : spec.getTypeSpecList()) {
			if (tSpec.mustBeConstant()) { return true; }
		}
		return false;
	}

	private Map<Type,List<Term>> collectNewTypes(List<ArgSpec> argSpecs, List<Term> origVarsNeeded, List<Term> currentVarsNeeded) {
		if (argSpecs == null) { return null; }
		Map<Type,List<Term>> results = new HashMap<Type,List<Term>>(4);		
		for (ArgSpec spec : argSpecs) {
			Type       type  = spec.typeSpec.isaType;			
			List<Term> terms = results.get(type);
			if (terms != null) {
				terms.add(spec.arg);
				results.put(type, terms);
			} else { // This type not yet seen.
				List<Term> termsNew = new ArrayList<Term>(1);
				termsNew.add(spec.arg);
				results.put(type, termsNew);
			}
		}
		return results;
	}
	
	private List<ArgSpec> collectNewSpecs(List<ArgSpec> specs, List<Term> origVarsNeeded, List<Term> currentVarsNeeded) {
		if (specs == null || currentVarsNeeded == null) { return null; }
		List<ArgSpec> results = new ArrayList<ArgSpec>(1);  //  Utils.println("specs=" + specs);  Utils.println("origVarsNeeded=" + origVarsNeeded);   Utils.println("currentVarsNeeded=" + currentVarsNeeded); 
		for (int i = 0; i < specs.size(); i++)  {
			ArgSpec spec = specs.get(i);  
			if (origVarsNeeded.get(i) == spec.arg) { 
				if (currentVarsNeeded.contains(spec.arg)) {
					results.add(spec);
				} // else { results.add(new ArgSpec(currentVarsNeeded.get(i), spec.typeSpec));	}
			}
			else { Utils.error("Are these not in order?  If so, do a double for loop."); }
		}
		return results;
	}

	// Do all these variables have a UNIQUE match?  Note: equals is properly defined for FOPC functions.
	private boolean allUniqueBindings(BindingList bl, List<Term> vars, PredicateSpec pSpec) {
		if (Utils.getSizeSafely(vars) < 2) { return true; } 
		Map<Term,List<Type>> termsSeen = new HashMap<Term,List<Type>>(4);  // Use List instead instead of Set since these should be small.
		if (Utils.getSizeSafely(vars) != Utils.getSizeSafely(pSpec.getTypeSpecList())) { Utils.error("Mismatch: " + vars + " vs." + pSpec.getTypeSpecList()); }
		for (int i = 0; i < vars.size(); i++) if (vars.get(i) instanceof Variable) {
			Term var = vars.get(i);  // Utils.println("   i1=" + i + " typeSpec=" + pSpec.getTypeSpecList().get(i));
			Type type = pSpec.getTypeSpecList().get(i).isaType;
			Term term = bl.lookup((Variable) var);
			List<Type> lookup = termsSeen.get(term); 
			if (lookup != null && lookup.contains(type)) { return false; }
			if (lookup == null) { lookup = new ArrayList<Type>(1); }
			lookup.add(type);
			termsSeen.put(term, lookup);
		}
		return true;
	}
	
	private List<Term> getVarsNeeded(BindingList bl, List<Term> vars, PredicateSpec pSpec) {
		if (Utils.getSizeSafely(vars) < 2) { return vars; } 
		Map<Term,List<Type>> termsSeen = new HashMap<Term,List<Type>>(4);  // Use List instead instead of Set since these should be small.
		List<Term>          varsNeeded = new ArrayList<Term>(1);
		if (Utils.getSizeSafely(vars) != Utils.getSizeSafely(pSpec.getTypeSpecList())) { Utils.error("Mismatch: " + vars + " vs." + pSpec.getTypeSpecList()); }
		for (int i = 0; i < vars.size(); i++) if (vars.get(i) instanceof Variable) { // Utils.println("   i2=" + i + " typeSpec=" + pSpec.getTypeSpecList().get(i));
			Variable var = (Variable) vars.get(i);
			Type    type = pSpec.getTypeSpecList().get(i).isaType;
			Term    term = bl.lookup(var);
			List<Type> lookup = termsSeen.get(term);
			if (lookup != null && lookup.contains(type)) { continue; } // Have a duplicate, skip it.
			if (lookup == null) { lookup = new ArrayList<Type>(1); }
			lookup.add(type);
			termsSeen.put(term, lookup);
			varsNeeded.add(var);
		}
		return varsNeeded;
	}
	
	private Map<Variable,Term> getNewTheta(BindingList bl, List<Term> vars, PredicateSpec pSpec) {
		if (Utils.getSizeSafely(vars) < 2) { return bl.theta; } 
		Map<Term,List<TypeVarPair>> termsSeen = new HashMap<Term,List<TypeVarPair>>(4);  // Use List instead instead of Set since these should be small.
		Map<Variable,Term>          newTheta  = new HashMap<Variable,Term>(4);
		if (Utils.getSizeSafely(vars) != Utils.getSizeSafely(pSpec.getTypeSpecList())) { Utils.error(); }
		for (int i = 0; i < vars.size(); i++) if (vars.get(i) instanceof Variable) {  // Utils.println("   i3=" + i + " typeSpec=" + pSpec.getTypeSpecList().get(i));
			Variable var = (Variable) vars.get(i);
			Type    type = pSpec.getTypeSpecList().get(i).isaType;
			Term    term = bl.lookup(var);
			List<TypeVarPair> lookup = termsSeen.get(term); // Utils.println("       var=" + var + " type=" + type + " term=" + term + "  lookup=" + lookup); 
			if (lookup != null) for (TypeVarPair pair : lookup) if (pair.type == type) { // Have a duplicate, need to add it to the returned result.
				newTheta.put(var, pair.variable);
			}
			if (lookup == null) { lookup = new ArrayList<TypeVarPair>(1); }
			lookup.add(new TypeVarPair(type, var));
			termsSeen.put(term, lookup);
		}
		return newTheta;
	}
	
	private Literal getNewTarget(Literal oldTarget, Example example, PredicateSpec pSpec, Map<Variable,Term> theta) {
		return ((LearnOneClause) task).stringHandler.getLiteral(oldTarget.predicateName, help_getNewTarget(oldTarget.getArguments(), 0, example.getArguments(), pSpec, theta));
	}
	private List<Term> help_getNewTarget(List<Term> args, int counter, List<Term> exampleArgs, PredicateSpec pSpec, Map<Variable,Term> theta) {
		if (args == null) { return null; }
		List<Term> result = new ArrayList<Term>(args.size());
		for (int i = 0; i < args.size(); i++) {
			Term arg   = args.get(i);
			Term exArg = exampleArgs.get(i); // Since the target unifies with the seed, we can follow along.
			if (arg instanceof Variable) {
				TypeSpec tSpec = pSpec.getTypeSpecList().get(counter);
				if (tSpec.mustBeConstant()) { // The reason for this method  is to handle this case.
					result.add(exArg); // Use the constant in the example.
				} else {
					Term lookup = repeatedlyLookup(arg, theta);
					result.add(lookup == null ? arg : lookup); // Buggy if bound to null?  What does applyTheta do here?
				}
				counter++;
			} else if (arg instanceof Constant) {
				result.add(arg);
				counter++;
			} else if (arg instanceof Function) {
				Function f   = (Function) arg;
				Function exF = (exArg instanceof Function ? (Function) exArg : f); // Cannot go deeper into example (so it must have a variable; just be 'sloppy' here since this should be very rare).
				List<Term> newArgs = help_getNewTarget(f.getArguments(), counter, exF.getArguments(), pSpec, theta);
				result.add( ((LearnOneClause) task).stringHandler.getFunction(f.functionName, newArgs, f.getTypeSpec()));
				counter += (Function.isaConsCell(arg) ? 1 : f.countLeaves());
			}
		}
		return result;
	}
	
	private Term repeatedlyLookup(Term arg, Map<Variable,Term> theta) {
        Term result = arg;

        if (arg instanceof Variable) {
            Variable variable = (Variable) arg;

            Term lookup = theta.get(variable);
		
            if (lookup != null) {
                result = repeatedlyLookup(lookup, theta);
            }
        }

        return result;
	}

    // A simple 'helper' class.
    private class TypeVarPair {
        protected Type     type;
        protected Variable variable;

        public TypeVarPair(Type type, Variable var) {
            this.type = type;
            variable  = var;
        }
    }

}


