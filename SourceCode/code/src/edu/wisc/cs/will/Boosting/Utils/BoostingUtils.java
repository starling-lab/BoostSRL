/**
 * 
 */
package edu.wisc.cs.will.Boosting.Utils;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.wisc.cs.will.Boosting.Advice.AdviceReader;
import edu.wisc.cs.will.Boosting.EM.HiddenLiteralSamples;
import edu.wisc.cs.will.Boosting.RDN.JointRDNModel;
import edu.wisc.cs.will.Boosting.RDN.LearnBoostedRDN;
import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.RDN.RunBoostedRDN;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.Boosting.Trees.RegressionMLNModel;
import edu.wisc.cs.will.Boosting.Trees.RegressionTree;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.ConsCell;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.PredicateSpec;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.ILP.LearnOneClause;
import edu.wisc.cs.will.ResThmProver.DefaultProof;
import edu.wisc.cs.will.ResThmProver.Proof;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.RegressionValueOrVector;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author Tushar Khot
 *
 */
public class BoostingUtils {

	// Unfortunately Map's need to know the type of the list as they have to create new lists
	// This method assumes "ArrayList"
	public static <T> void castMapToRegRDNEgToMapToEg(Map<T, List<RegressionRDNExample>> input_rex,
			                                          Map<T, List<Example>> output_ex) {
		if (input_rex == null) {
			return;
		}
		if (output_ex == null) {
			Utils.error("Must initialize output_ex");
			Utils.waitHere();
		}
			
		for (T key : input_rex.keySet()) {
			output_ex.put(key, new ArrayList<Example>());
			BoostingUtils.castCollectionOfRegressionRDNExampleToExamples(input_rex.get(key),
								output_ex.get(key));
		}
	}

	public static List<Example> convertToListOfExamples(List<RegressionRDNExample> examples) {
		if (examples == null) { return null; }
		List<Example> results = new ArrayList<Example>(examples.size());
		for (RegressionRDNExample ex : examples) { results.add(ex); }
		return results;
	}

	public static <T> Map<T,List<Example>> castHashMapToRegRDNEgToHashMapToEg(Map<T,List<RegressionRDNExample>> input_rex) {
		if (input_rex == null) {
			return null;
		}
		HashMap<T, List<Example>> output = new HashMap<T, List<Example>>();
		castMapToRegRDNEgToMapToEg(input_rex, output);
		return output;
	}

	public static void castCollectionOfRegressionRDNExampleToExamples(
			Collection<RegressionRDNExample> input_rex,
			Collection<Example> outputEgs) {
		if (input_rex == null) {
			return ;
		}
		if (outputEgs == null) {
			Utils.error("Must initialize outputEgs");
			Utils.waitHere();
		}
		for (RegressionRDNExample regressionRDNExample : input_rex) {
			outputEgs.add(regressionRDNExample);
		}
	}

	public static List<RegressionRDNExample> castToListOfRegressionRDNExamples(List<Example> examples) {
		if (examples == null) { return null; }
		List<RegressionRDNExample> results = new ArrayList<RegressionRDNExample>(examples.size());
		for (Example ex : examples) { results.add((RegressionRDNExample)ex); }
		return results;
	}
	
	public static RegressionValueOrVector getRegressionValueOrVectorFromTerm(Term leafTerm) {
		if (leafTerm instanceof NumericConstant) {
			return new RegressionValueOrVector(((NumericConstant) leafTerm).value.doubleValue());
		}
		if (leafTerm instanceof ConsCell) {
			ConsCell valarray = (ConsCell)leafTerm;
			double[] regVec = new double[valarray.length()];
			int index = 0;
			for (Term term : valarray) {
				double val  = ((NumericConstant) term).value.doubleValue();
				regVec[index++] = val;
			}
			return new RegressionValueOrVector(regVec);
		}
		Utils.error("Uknown type of constant in leaf: " + leafTerm.toPrettyString());
		return null;
	}

	/**
	 * Be very careful while using it. Use it only when the regression values dont matter. This method creates regression
	 * examples with arbitrary regression values and should be used if it is going to be converted later.
	 * Use castToListOfRegressionRDNExamples, if you know its only a type issue and dont want to create new RegressionRDNExample
	 * @param examples
	 * @param originalTruthValue
	 * @return
	 */
	public static List<RegressionRDNExample> convertToListOfRegressionRDNExamples(List<Example> examples, boolean originalTruthValue) {
		if (examples == null) { return null; }
		List<RegressionRDNExample> results = new ArrayList<RegressionRDNExample>(examples.size());
		for (Example ex : examples) { results.add(new RegressionRDNExample(ex, originalTruthValue)); }
		return results;
	}

	public static String getLabelForModelNumber(int modelNumber) {
		return (modelNumber > 0 ? "Model" + modelNumber : ""); // Model 0 is only implicitly named, in case we only want one model.
	}

	public static String getLabelForCurrentModel() {
		return RunBoostedRDN.nameOfCurrentModel == null ? "" : "_" + RunBoostedRDN.nameOfCurrentModel;
	}

	public static String getLabelForResultsFileMarker() {
		return RunBoostedRDN.resultsFileMarker  == null ? "" : "_" + RunBoostedRDN.resultsFileMarker;
	}

	public static String getModelFile(CommandLineArguments cmdArgs, String target, boolean includeExtension) {
		String filename = cmdArgs.getModelDirVal() + "bRDNs/" + target;
		if (cmdArgs.getModelFileVal() != null) {
			 filename += "_" + cmdArgs.getModelFileVal();
		}
		filename += getLabelForCurrentModel() + (includeExtension ? ".model" : "");
		Utils.ensureDirExists(filename);
		return filename;
	}

	public static List<PredicateNameAndArity> convertBodyModesToPNameAndArity(Set<PredicateNameAndArity> pnames) {
		List<PredicateNameAndArity> pars = new ArrayList<PredicateNameAndArity>();
		for (PredicateNameAndArity predicate : pnames) {
			// For each spec for the predicate
			for (PredicateSpec spec : predicate.getPredicateName().getTypeList()) {
				if (spec.getTypeSpecList() != null) {
					int arity = spec.getTypeSpecList().size();
					PredicateNameAndArity par = new PredicateNameAndArity(predicate.getPredicateName(), arity);
					// TODO(TVK) use a set.
					if (!pars.contains(par)) {
						pars.add(par);
					}
				}
			}
		}
		return pars;
	}
	

	public static Set<Literal> getRelatedFacts(Term input, List<PredicateNameAndArity> allPredicates,
										LearnOneClause learnClause) {
		Set<Literal> relatedFacts = new HashSet<Literal>();
		//HornClauseProver prover = learnClause.getProver();
		//FileParser parser = learnClause.getParser();
		HandleFOPCstrings handler = learnClause.getStringHandler();

		// For each predicate
		for (PredicateNameAndArity predicateArity : allPredicates) {
			// not_predicate()  always would return true and should be ignored.
			// TODO Find a better way to handle this case
			if (predicateArity.getPredicateName().name.contains("not_")) {
				continue;
			}

			List<Term> args = new ArrayList<Term>();
			// For each argument 
			for (int i = 0; i < predicateArity.getArity(); i++) {
				args.add(handler.getGeneratedVariable(handler.convertToVarString("Arg" + i), true));
			}


			// Now try putting the term as an argument at every location.
			for (int i = 0; i < args.size(); i++) {
				Term bkup = args.get(i);
				// args.set(i, input);
				Literal query = handler.getLiteral(predicateArity.getPredicateName(), args);

				BindingList bl = new BindingList();
				bl.addBinding((Variable)bkup, input);
				// System.out.println("Querying " + query+ "  " + bl);

				Literal boundQuery = query.applyTheta(bl);
				//	System.out.println("Query: " + boundQuery);
				BindingList proofBindings = null;
				Proof proof = new DefaultProof(learnClause.getContext(), boundQuery );

				// Every call to prove() will return the next possible
				// SLD resolution's BindingList, or null if there 
				// are no more resolutions.

				while (  ( proofBindings = proof.prove() ) != null ) {
					// Here proofBindings will contains the bindings 
					// for all the free variables if the proof succeeded.
					// If you just need the binding of the variable, you have them.
					// If you want the full literal, just apply the bindings to the boundQuery.
					Literal boundResult = boundQuery.applyTheta(proofBindings);
					if (!boundResult.containsVariables()) {
						//	   System.out.println(boundResult);
						//	   done=true;
						relatedFacts.add(boundResult);
					}
				}
			}
		}

		return relatedFacts;
	}

	public static double sigmoid(double numRegExp, double denoRegExp) {
		return 1/ (Math.exp(denoRegExp - numRegExp) + 1);
	}
	
	public static void loadAdvice(WILLSetup setup, JointRDNModel fullModel, String file, boolean isMLN) {
		if (!Utils.fileExists(file)) {
			Utils.println("File: " + file + " doesnt exist.Hence no advice loaded");
			return;
		}
		List<Sentence> advices = new ArrayList<Sentence>();
		AdviceReader advReader = new AdviceReader(setup.getInnerLooper().getParser(), setup.getContext(), setup.getHandler());
		advReader.readAdviceFromFile(file, advices);
		for (String pred : fullModel.keySet()) {
			for (Sentence advice : advices) {
				Clause cl = advice.asClause(); 
				if (cl.getDefiniteClauseHead().predicateName.name.equals(pred)) {
					if (fullModel.get(pred).getPrior_advice() == null) {
						if (isMLN) {
							fullModel.get(pred).setPrior_advice(new RegressionMLNModel(setup));
						} else {
							fullModel.get(pred).setPrior_advice(new RegressionTree(setup));
						}
					}
					fullModel.get(pred).getPrior_advice().addClause(cl);
				}
			}
		}
	}


	public static String getCheckPointFile(String saveModelName) {
		return saveModelName + ".ckpt";
	}

	public static String getCheckPointExamplesFile(String saveModelName) {
		return saveModelName + ".ckptEgs";
	}

	public static String getCheckPointFlattenedLitFile(String saveModelName) {
		return saveModelName + ".ckptLits";
	}

	public static double computeHiddenStateCLL(
			HiddenLiteralSamples sampledStates,
			Map<String, List<RegressionRDNExample>> hiddenExamples) {
		double cll=0;
		double counter = 0;
		double accuracyCounter = 0;
		double correct = 0;
		for (String predName : hiddenExamples.keySet()) {
			for (RegressionRDNExample eg : hiddenExamples.get(predName)) {
				ProbDistribution probDist = sampledStates.sampledProbOfExample(eg);
				double prob = 1;
				if (probDist.isHasDistribution()) {
					double[] probs = probDist.getProbDistribution();
					
					int mostLikelyState = -1;
					double highestProb = 0.0; 
					for (int i = 0; i < probs.length; i++) {
						if (probs[i] > highestProb) {
							highestProb = probs[i];
							mostLikelyState = i;
						}
						if (eg.getOriginalHiddenLiteralVal() == i) {
							prob = probs[i];
						} else {
							prob = 1 - probs[i];
						}
						if (prob == 0) {
							prob = 1e-5;
						}
						cll += Math.log(prob);
						counter++;
					}
					if (mostLikelyState == eg.getOriginalHiddenLiteralVal()) {
						correct++;
					}
					accuracyCounter++;
				} else {
					prob = probDist.getProbOfBeingTrue();
					if (eg.getOriginalHiddenLiteralVal() == 0) {
						// False example with true prob < 0.5 ?
						if (prob < 0.5) {
							correct++;
						}
						prob = 1-prob;
					} else {
						// True example with true prob >= 0.5
						if (prob >= 0.5) {
							correct++;
						}
					}
					if (prob == 0) {
						prob = 1e-5;
					}
					cll += Math.log(prob);
					counter++;
					accuracyCounter++;
				}
				
			}
		}
		Utils.println("Hidden data accuracy: " + (correct / accuracyCounter) + " (" + correct + "/" + accuracyCounter + ").");
		return cll/counter;
		
	}
	
	
	
}
