/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.Boosting.RDN;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.sun.org.apache.bcel.internal.generic.GETSTATIC;

import edu.wisc.cs.will.Boosting.EM.HiddenLiteralSamples;
import edu.wisc.cs.will.Boosting.RDN.Models.RelationalDependencyNetwork;
import edu.wisc.cs.will.Boosting.RDN.MultiClassExampleHandler.ArgumentList;
import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;
import edu.wisc.cs.will.Boosting.Utils.CommandLineArguments;
import edu.wisc.cs.will.DataSetUtils.CreateSyntheticExamples;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.DataSetUtils.RegressionExample;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings.VarIndicator;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.PredicateSpec;
import edu.wisc.cs.will.FOPC.PrettyPrinter;
import edu.wisc.cs.will.FOPC.PrettyPrinterOptions;
import edu.wisc.cs.will.FOPC.RelevanceStrength;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.ILP.ActiveAdvice;
import edu.wisc.cs.will.ILP.ActiveAdvice.ClauseInfo;
import edu.wisc.cs.will.ILP.AdviceProcessor;
import edu.wisc.cs.will.ILP.ChildrenClausesGenerator;
import edu.wisc.cs.will.ILP.Gleaner;
import edu.wisc.cs.will.ILP.ILPouterLoop;
import edu.wisc.cs.will.ILP.LearnOneClause;
import edu.wisc.cs.will.ILP.ScoreOCCNode;
import edu.wisc.cs.will.ILP.ScoreRegressionNode;
import edu.wisc.cs.will.ILP.ScoreSingleClause;
import edu.wisc.cs.will.ResThmProver.DefaultHornClauseContext;
import edu.wisc.cs.will.ResThmProver.DefaultHornClausebase;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.ResThmProver.HornClauseProver;
import edu.wisc.cs.will.ResThmProver.HornClausebase;
import edu.wisc.cs.will.ResThmProver.LazyGroundClauseIndex;
import edu.wisc.cs.will.ResThmProver.LazyGroundNthArgumentClauseIndex;
import edu.wisc.cs.will.ResThmProver.LazyHornClausebase;
import edu.wisc.cs.will.ResThmProver.VariantClauseAction;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.VectorStatistics;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.stdAIsearch.BestFirstSearch;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchStrategy;

/**
 *
 * @author shavlik
 * @author tushar
 */
public final class WILLSetup {

	private static final int  debugLevel = 0; // Don't set to a negative number (JWS).
	private ILPouterLoop      outerLooper;
	// These are meant for ease of access and should never be modified.
	// They can also be obtained by using outerLooper.
	private LearnOneClause    innerLooper;
	private HandleFOPCstrings handler;
	private HornClauseContext context;
	private HornClauseProver  prover;
	private MultiClassExampleHandler multiclassHandler;
	
	private Map<String, List<Example>> backupPosExamples; // Use LIST since there can be duplicates.
	private Map<String, List<Example>> backupNegExamples; // These hold the original examples for all targets.
	private Map<String, List<RegressionRDNExample>> hiddenExamples = null; // Holds the list of hidden literals.	
	private HiddenLiteralSamples lastSampledWorlds = null;
	
	private double weightOnPosExamples = 1.0;
	private double weightOnNegExamples = 1.0; // 0.2; // TODO This should be 1.0 but I (JWS) am manually setting it for now. 

	private String  fileExtension           = Utils.defaultFileExtension;
	private String  fileExtensionWithPeriod = Utils.defaultFileExtensionWithPeriod;
	private boolean checkpointEnabled       = false;
	public boolean useMLNs					= false;
	public boolean learnClauses				= false;
	private boolean errorIfNoExamples       = false;
        public boolean GroundedRelationalRW2    = false; //Added By Navdeep Kaur
	
	/**
	 * Cached list of predicate and arities for neighboring facts
	 */
	List<PredicateNameAndArity> neighboringFactFilterList = null;
	
	public CommandLineArguments cmdArgs;
	public WILLSetup() { }

	private String getRunTypeMarker() {
		boolean learn = cmdArgs.isLearnVal();
		boolean infer = cmdArgs.isInferVal();
		
		if (learn && infer) { return "_learnPlusInfer"; } // Dribble files might overlap in this case.
		if (learn)          { return "_learn";          }
		if (infer)          { return "_infer";          }
		return                       "_runTypeIsUnknown";
	}
	
	private boolean bagOriginalPosExamples = false; // Should the examples be bagged upon reading them in?
	private boolean bagOriginalNegExamples = false;
	public  boolean setup(CommandLineArguments args, String directory, boolean forTraining) throws SearchInterrupted {
		this.cmdArgs = args;
		this.useMLNs = args.isLearnMLN();
		this.learnClauses = args.isLearningMLNClauses();
		// Added By Navdeep Kaur
		this.GroundedRelationalRW2 = args.isGroundedRelationalRW();

		
		Utils.Verbosity defaultVerbosity = (Utils.isDevelopmentRun() ? Utils.Verbosity.Developer : Utils.Verbosity.Medium);

	//	Utils.seedRandom((long) 12345); // Use this if we want to repeat runs exactly.
		Utils.seedRandom(System.currentTimeMillis() % 100000); // Only use the last few digits (though probably doesn't matter).  JWS
		Utils.setVerbosity(defaultVerbosity);

		File dir = new CondorFile(directory);

		if ( dir.isDirectory() == false ) {
			throw new IllegalArgumentException("Unable to find task directory: " + directory + ".");
		}

		directory     = dir.getPath();
		String prefix = dir.getName();

		// Slice the '/' off the prefix if it was passed in with one ...
		if ( prefix.endsWith("/" ) ) {
			prefix = prefix.substring(0, prefix.length() - 1);
		}

		String[] newArgList = new String[4];
		newArgList[0] = directory + "/" + prefix + "_" + cmdArgs.getStringForTestsetPos()   + fileExtensionWithPeriod;
		newArgList[1] = directory + "/" + prefix + "_" + cmdArgs.getStringForTestsetNeg()   + fileExtensionWithPeriod;
		newArgList[3] = directory + "/" + prefix + "_" + cmdArgs.getStringForTestsetFacts() + fileExtensionWithPeriod;
		newArgList[2] = directory + "/" + prefix + "_bk"                                    + fileExtensionWithPeriod;



		String appendToPrefix="";
		if (forTraining && cmdArgs.getModelFileVal() != null) {
			appendToPrefix = cmdArgs.getModelFileVal();
		}
		if (!forTraining && cmdArgs.outFileSuffix != null) {
			appendToPrefix = cmdArgs.outFileSuffix;
		} else {
			if (!forTraining && cmdArgs.getModelFileVal() != null) {
				appendToPrefix = cmdArgs.getModelFileVal();
			}
		}
		String resultsDir = cmdArgs.getResultsDirVal(); // Try to place dribble files in the directory where RESULTS will go.
		if (resultsDir == null) { resultsDir = directory + "/"; } 
		
		//String modelSuffix = (cmdArgs.getModelFileVal() != null ? "_" + cmdArgs.getModelFileVal() : "");
		Utils.createDribbleFile(resultsDir + prefix + getRunTypeMarker() + appendToPrefix  + "_dribble" + fileExtensionWithPeriod);
		Utils.touchFile(        resultsDir + prefix + getRunTypeMarker() + appendToPrefix  + "_started" + fileExtensionWithPeriod);
		createRegressionOuterLooper(newArgList, directory, prefix, cmdArgs.getSampleNegsToPosRatioVal(), cmdArgs.isLearnRegression() || cmdArgs.isLearnProbExamples());

		
		// Disabled by TVK (04/18/12)
		// Utils.appendString(new CondorFile(resultsDir + prefix+"/" + getRunTypeMarker() + "_setupAt" + fileExtensionWithPeriod), "/ Setup" + getRunTypeMarker() + " at " + Utils.getDateTime() + ".\n");
		if (cmdArgs.isCreateSyntheticEgs()) {
			getInnerLooper().setSyntheticExamplesEnabled(true);
		}
		// This next chunk of code handles advice and creates BK.  IT THEN EXITS.  One should then MANUALLY edit your standard BK file to import the file of BK created.
		String adviceFile = cmdArgs.getAdviceFileVal();
		if (adviceFile != null) {
			try { 
				getInnerLooper().setRelevanceFile(adviceFile);
				getInnerLooper().setRelevanceEnabled(true);
				
				AdviceProcessor ap = getInnerLooper().getAdviceProcessor();
			//	Utils.println("|pos| = " + getInnerLooper().getPosExamples().size() + " |neg| = " + getInnerLooper().getNegExamples().size());
				ActiveAdvice    aa = ap.getActiveAdvice(RelevanceStrength.getWeakestRelevanceStrength(), getInnerLooper().getPosExamples(), getInnerLooper().getNegExamples());

				PrettyPrinterOptions ppo = new PrettyPrinterOptions();
				ppo.setMultilineOutputEnabled(true);
				//ppo.setMaximumLineWidth(100);
				ppo.setMaximumLiteralsPerLine(1);
				ppo.setNewLineAfterImplication(true);
				ppo.setMaximumIndentationAfterImplication(6);
				
				StringBuilder sb = new StringBuilder();
				sb.append("\n% The Primary Clauses:\n");
				for (PredicateNameAndArity pnna : aa.getClauses().keySet()) {
					for (ClauseInfo clauseInfo : aa.getClauses().getValues(pnna)) {
						Clause anAdviceClause = clauseInfo.getClause();
						// Prepend "advice_" for each of finding these in learned trees.  TEMP HACK
						sb.append( "mode:  advice_" + anAdviceClause.posLiterals.get(0).predicateName + "(+world, +scenario).\n"); // TEMP HACK
						sb.append( "cost:  advice_" + anAdviceClause.posLiterals.get(0).predicateName + "/2, 0.5;\n"); // TEMP HACK
						String s = "       advice_" + anAdviceClause.posLiterals.get(0) 
												    + " :- " 
											//  	+ "write(calling, " + anAdviceClause.posLiterals.get(0) + "), "
												    + "helper_advice_"      + anAdviceClause.posLiterals.get(0) + ","
											//  	+ "write(succeeded, "   + anAdviceClause.posLiterals.get(0) + "), "
												    + "true.\n";
						s       += "helper_advice_" + PrettyPrinter.print(anAdviceClause, "", "", ppo, null);
						sb.append(s).append("\n\n");
					}
				}
				
				Set<PredicateNameAndArity> supporters = aa.getSupportClauses().keySet();
				if (Utils.getSizeSafely(supporters) > 0) {
					sb.append("\n% The Supporting Clauses:\n");
					for (PredicateNameAndArity pnna : aa.getSupportClauses().keySet()) {
						for (Clause supportClause : aa.getSupportClauses().getValues(pnna)) {
							// Prepend "advice_" for each of finding these in learned trees.  TEMP HACK
							sb.append( "mode:  advice_" + supportClause.posLiterals.get(0).predicateName + "(+world, +scenario).\n"); // TEMP HACK
							sb.append( "cost:  advice_" + supportClause.posLiterals.get(0).predicateName + "/2, 0.5;\n"); // TEMP HACK
							String s = "       advice_" + supportClause.posLiterals.get(0) 
														+ " :- "
												//		+ "write(calling, " + supportClause.posLiterals.get(0) + "), "
														+ "helper_advice_"      + supportClause.posLiterals.get(0) + ","
												//		+ "write(succeeded, "   + supportClause.posLiterals.get(0) + "), "
														+ "true.\n";
							s       += "       advice_" + PrettyPrinter.print(supportClause, "", "", ppo, null);
							sb.append(s).append("\n\n");
						}
					}
				}

				String parent = new CondorFile(adviceFile).getParent(); // Put the BK in the same dir as the advice.
				File f = new CondorFile((parent != null ? parent + "/" :  "") + "wargusAdviceAsBK.txt");
				Utils.writeStringToFile(getInnerLooper().getStringHandler().getStringToIndicateCurrentVariableNotation() + "\n" + sb, f);
				Utils.waitHere("\n\nADVICE CONVERTED TO STANDARD BK AND WRITTEN TO:\n\n   " + f + "\n\nYOU SHOULD EXIT NOW AND MANUALLY IMPORT THE ABOVE FILE!\n");
				System.exit(0);
				
			} catch (FileNotFoundException e) {
				Utils.reportStackTrace(e);
				Utils.error("Encountered a problem: " + e);
			} catch (IllegalStateException e) {
				Utils.reportStackTrace(e);
				Utils.error("Encountered a problem: " + e);
			} catch (Exception e) {
				Utils.reportStackTrace(e);
				Utils.error("Encountered a problem: " + e);
			} catch (Error e) {
				Utils.reportStackTrace(e);
				Utils.error("Encountered a problem: " + e);
			}
		}
		Utils.println("\n% Initializing the ILP inner looper.");
		//getInnerLooper().initialize();
		getOuterLooper().initialize(false);
		
	//	Utils.waitHere("dribble to: " + resultsDir + prefix + "_dribble" + fileExtensionWithPeriod);
		// If the model directory is not set ...
		Utils.println("% Old dir" + cmdArgs.getModelDirVal());
		if (cmdArgs.getModelDirVal() == null) {
			Utils.println("Setting model dir");	
			cmdArgs.setModelDirVal(getOuterLooper().getWorkingDirectory() + "/models/");
		}
		if (cmdArgs.getResultsDirVal() == null) { // Usually we want MODEL and RESULTS to be the same, but not if we're running on a fresh testset (i.e., one completely separate from the trainset).
			cmdArgs.setResultsDirVal(cmdArgs.getModelDirVal());
		}
		
		// Following code for non regression examples
		/*if (cmdArgs.isLearnRegression()) {
			return true;
		}*/
		if (getInnerLooper().createdSomeNegExamples) {
			Example.writeObjectsToFile(newArgList[1], getInnerLooper().getNegExamples(), ".", "// Negative examples, including created ones.");
		}		

		if (cmdArgs.getBagOriginalExamples()) {
			bagOriginalPosExamples = true;
			bagOriginalNegExamples = true;
		} else {
			bagOriginalPosExamples = false;
			bagOriginalNegExamples = false;			
		}
		
		List<Literal> targets = getInnerLooper().targets;
		Set<Integer>  arities = new HashSet<Integer>(4);
		if (targets != null) for (Literal target : targets) { arities.add(target.getArity()); }

		List<Example> posExamplesRaw = getOuterLooper().getPosExamples(); // Use LIST since there can (legally) be duplicates.
		List<Example> negExamplesRaw = getOuterLooper().getNegExamples() == null ? new ArrayList<Example>(): getOuterLooper().getNegExamples();
		List<Example> posExamples    = new ArrayList<Example>(posExamplesRaw.size());
		List<Example> negExamples    = new ArrayList<Example>(negExamplesRaw.size());
		
		if (targets != null) {
			for (Example pos : posExamplesRaw) {
				if (arities.contains(pos.getArity())) { 
					// If not in the list of targets, we would add to facts
					if (cmdArgs.getTargetPredVal().contains(pos.predicateName.name)) {
						posExamples.add(pos);
					} else {
						addFact(pos);
					}
				} else { 
					Utils.println(" Ignore this pos (arity not in " + arities + "): " + pos); 
				}
			}
			for (Example neg : negExamplesRaw) {
				if (arities.contains(neg.getArity())) {
					// If not in the list of targets, we would add to facts
					if (cmdArgs.getTargetPredVal().contains(neg.predicateName.name)) {
						negExamples.add(neg);
					}
				} else { 
					Utils.println(" Ignore this neg (arity not in " + arities + "): " + neg); 
				}
			}
			if (posExamplesRaw.size() != posExamples.size() || negExamplesRaw.size() != negExamples.size()) {
			//	Utils.waitHere();
			}
		} else { // If no targets (say because only testing and there are no positive examples), then simply accept all the examples.
			//posExamples.addAll(posExamplesRaw);
			//negExamples.addAll(negExamplesRaw);
			for (Example pos : posExamples) {
				// If not in the list of targets, we would add to facts
				if (cmdArgs.getTargetPredVal().contains(pos.predicateName.name)) {
					posExamples.add(pos);
				} else {
					addFact(pos);
				}
			}

			for (Example neg : negExamplesRaw) {
				// If not in the list of targets, we would add to facts
				if (cmdArgs.getTargetPredVal().contains(neg.predicateName.name)) {
					negExamples.add(neg);
				}
			}
		}

		Utils.println("\n% Have " + Utils.comma(posExamplesRaw) + " 'raw' positive examples and kept " + Utils.comma(posExamples) + ".");
		Utils.println(  "% Have " + Utils.comma(negExamplesRaw) + " 'raw' negative examples and kept " + Utils.comma(negExamples) + ".");
		
		
		////////////////////////////////////////////////// TEMP
		////////////////////////////////////////////////// TEMP
		////////////////////////////////////////////////// TEMP
		
		if (false) for (Example ex : posExamples) {
			Term firstArg = ex.getArgument(0);
			Term  lastArg = ex.getArgument(ex.getArity() - 1);
			Literal   lit = getInnerLooper().getStringHandler().getLiteral(getInnerLooper().getStringHandler().getPredicateName("isaNounPhrase"));
			lit.addArgument(firstArg);
			lit.addArgument( lastArg);
			if (getInnerLooper().matchingFactExists(getInnerLooper().getContext().getClausebase(), lit) == null) {
				Utils.waitHere("Cannot prove: " + lit + "   " + ex);
			} else {
				Utils.println("Can prove: "     + lit + "   " + ex);
			}
		}
		
		
		
		// These shouldn't be RegressionRDNExamples. They are assumed to be "Example"s. 
		backupPosExamples = getExamplesByPredicateName(posExamples, forTraining && bagOriginalPosExamples); // Do bagging on the outermost loop.
		backupNegExamples = getExamplesByPredicateName(negExamples, forTraining && bagOriginalNegExamples);	// But only if TRAINING.
		// Needed to get examples from fact files.
		fillMissingExamples();
		
		
		// check if multi class trees are enabled.
		// We still create the multi class handler object
		multiclassHandler = new MultiClassExampleHandler();
		if (!cmdArgs.isDisableMultiClass()) {
			multiclassHandler.initArgumentLocation(this);
			for (String pred : backupPosExamples.keySet()) {
				multiclassHandler.addConstantsFromLiterals(backupPosExamples.get(pred));
				if (backupNegExamples.containsKey(pred)) {
					multiclassHandler.addConstantsFromLiterals(backupNegExamples.get(pred));
				}
			}
		}
		
		if (cmdArgs.isLearnOCC() && cmdArgs.getDropPos() > 0) {
			double dropPos = cmdArgs.getDropPos();
			// Move some pos to neg
			for (String pred : backupPosExamples.keySet()) {
				List<Example> posEg = backupPosExamples.get(pred);
				for (int i = 0; i < posEg.size(); i++) {
					if (Utils.random() < dropPos) {
						Example eg = posEg.remove(i);
						backupNegExamples.get(pred).add(eg);
						i--;
					}
				}
			}
		}

		String hiddenLitFile = directory + "/" + prefix + "_" + cmdArgs.getStringForTestsetHidden()  + fileExtensionWithPeriod; 
		if (!cmdArgs.getHiddenStrategy().equalsIgnoreCase("ignore")) {
			readHiddenLiterals(hiddenLitFile);
		}
		if (cmdArgs.getHiddenStrategy().equals("EM")) {
			getHandler().setUseStrictEqualsForLiterals(true);
		}
		// dont sample if already exists
		if (hiddenExamples == null && cmdArgs.getHiddenLitProb() >= 0) {
			double negLitProb = cmdArgs.getHiddenLitProb();
			if (cmdArgs.getHiddenNegLitProb() > 0) {
				negLitProb = cmdArgs.getHiddenNegLitProb();
			}
			sampleHiddenExamples(cmdArgs.getHiddenLitProb(), negLitProb);
		}
		// For hidden literals, move the hidden literals to negative examples to prevent any bugs or move to different sets based on strategy
		
		if (hiddenExamples != null) {
			if (cmdArgs.getHiddenStrategy().equals("infer")) {
				// Keep all examples and report only the non-hidden examples
				if (!cmdArgs.isReportHiddenEx()) {
					keepHiddenPosNegExamples();
				}
			} else {
				if (cmdArgs.getHiddenStrategy().equals("noise")) {
					flipHiddenPosNegExamples();
				} else {
					moveHiddenPosToNeg();
				}
			}
		
			
			
			if (cmdArgs.getHiddenStrategy().equals("infer") || cmdArgs.getHiddenStrategy().equals("noise")) {
				
				/*
				 * for (String predName : hiddenExamples.keySet()) {
				 
					if (backupPosExamples.containsKey(predName)) {
						Utils.error("Examples from the hidden literal provided. Should only do inference and not use hidden literals.");
					}
					for (RegressionRDNExample hiddenRex : hiddenExamples.get(predName)) {
						Iterable<Literal> facts = getContext().getClausebase().getPossibleMatchingFacts(hiddenRex.asLiteral(), null);
						if (facts != null && facts.iterator().hasNext()) {
							removeFact(hiddenRex.asLiteral());
							// Set original truth value too since that will be used for inference and would be used to compute CLL/AUC PR
							hiddenRex.setOriginalTruthValue(true);
							hiddenRex.setOriginalHiddenLiteralVal(true);
						} else {
							hiddenRex.setOriginalTruthValue(false);
							hiddenRex.setOriginalHiddenLiteralVal(false);
						}

					}
				}
*/			} 
		}
		
		
		
		if (backupPosExamples != null) for (String target : backupPosExamples.keySet()) {
			Collection<Example> posegs = backupPosExamples.get(target);
			Collection<Example> negegs = backupNegExamples.get(target);
			// weigh the negative examples based on ratio of examples
			// If you have 10X negative examples, each negative example would be weighed 0.1
			// This is not the weight due to sampling. This is the weight to make large skews in 
			// data be equivalent to equal positive and negative examples. 
			// Weights are recalculated later if any sampling is done.
			//if (cmdArgs.isReweighExamples()) {
				//weightOnNegExamples = (double)posegs.size() /  (double)negegs.size();
			//}
			if (posExamples       != null && Math.abs(weightOnPosExamples - 1.0) > 0.000001) for (Example pos : posegs) {
				pos.setWeightOnExample(weightOnPosExamples);
			}
			if (backupNegExamples != null && Math.abs(weightOnNegExamples - 1.0) > 0.000001) for (Example pos : negegs) {
				pos.setWeightOnExample(weightOnNegExamples);
			}
			Example.labelTheseExamples("#pos=", posegs);  // Used in comments only.
			Example.labelTheseExamples("#neg=", negegs);  // Used in comments only.
			Utils.println("\n% processing backup's for " + target +"\n%  POS EX = " + Utils.comma(posegs) +  "\n%  NEG EX = " + Utils.comma(negegs)	);
			
		}
		if (Utils.getSizeSafely(backupPosExamples) < 1) {
			if (Utils.getSizeSafely(backupNegExamples) < 1) { Utils.println("No pos nor neg examples!"); return false; }
			if (false) {
			// No positive examples, so flip-flop pos and neg until Tushar fixes the code.
			List<Example> hold_posExamplesRaw = posExamplesRaw;
			List<Example> hold_posExamples    = posExamples;
			posExamples = negExamples;
			negExamples = hold_posExamples;
			getOuterLooper().setPosExamples(negExamplesRaw);
			getOuterLooper().setNegExamples(hold_posExamplesRaw);
			}
		}
//////////////////////////////////////////////////TEMP
		////////////////////////////////////////////////// TEMP
		
		if (cmdArgs.getDoInferenceIfModNequalsThis() >= 0) { // See if we have been requested to select a subset (e.g., because the test set is too large to run at once).
			int valueToKeep = cmdArgs.getDoInferenceIfModNequalsThis();
			int modN        = CommandLineArguments.modN;
			List<Example> new_posExamples = new ArrayList<Example>(posExamples.size() / Math.max(1, modN));
			List<Example> new_negExamples = new ArrayList<Example>(negExamples.size() / Math.max(1, modN));
			int counter = 0;
			
			for (Example ex : posExamples) { if (counter % modN == valueToKeep) { new_posExamples.add(ex); } counter++; }
			for (Example ex : negExamples) { if (counter % modN == valueToKeep) { new_negExamples.add(ex); } counter++; }
			
			Utils.println("% whenModEquals: valueToKeep = " + valueToKeep + ",  modN = " + modN + ",  counter = " + Utils.comma(counter) 
							+ "\n%  POS: new = " + Utils.comma(new_posExamples) +  " old = " + Utils.comma(posExamples)
							+ "\n%  NEG: new = " + Utils.comma(new_negExamples) +  " old = " + Utils.comma(negExamples)
							);
			
			posExamples = new_posExamples;
			negExamples = new_negExamples;
			getOuterLooper().setPosExamples(posExamples); // Set these in case elsewhere they are again gotten.
			getOuterLooper().setNegExamples(negExamples);
		}
		if (Utils.getSizeSafely(backupPosExamples) + Utils.getSizeSafely(backupNegExamples) < 1) {
			Utils.println("No pos nor neg examples after calling getDoInferenceIfModNequalsThis()!"); 
			return false; 
		}
		
		reportStats();
		String lookup = getHandler().getParameterSetting("recursion");
		if (lookup != null) {
			allowRecursion = Boolean.parseBoolean(lookup);
			Utils.println("Recursion set to:" + allowRecursion);
		}
		
		if (cmdArgs.getBagOriginalExamples()) { // DecisionForest Decision Forest DF DF df50
			Utils.waitHere("Is this still being used?");
			getOuterLooper().randomlySelectWithoutReplacementThisManyModes = 0.50; // TODO - allow this to be turned off (or the fraction set) when bagging.
		}
		
		
		// Create db file in alchemy format.
		if (cmdArgs.getOutputAlchDBFile() != null) {
			try {
				outputFactsAndExamples(directory  + "/" + cmdArgs.getOutputAlchDBFile());
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
				Utils.waitHere(e.getMessage());
			}
		}
		// Create hidden fact file from the sampled hidden examples.
		if (cmdArgs.isCreateHiddenFile()) {
			try {
				outputHiddenLiterals(hiddenLitFile);
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
				Utils.waitHere(e.getMessage());
			}
		}
		return true;
	}
	
	private void flipHiddenPosNegExamples() {
		for (String predName : hiddenExamples.keySet()) {
			if (!backupPosExamples.containsKey(predName)) {
				Utils.error("Should be in test example set: " + predName);
			}
			if (getMulticlassHandler().isMultiClassPredicate(predName)) {
				Utils.error("Not implemented");
			}
			List<Example> addToPos = new ArrayList<Example>();
			List<Example> addToNeg = new ArrayList<Example>();
			
			for (int i = 0; i < backupPosExamples.get(predName).size(); i++) {
				if (isHidden(backupPosExamples.get(predName).get(i).asLiteral())) {
					addToNeg.add(backupPosExamples.get(predName).remove(i));
					i--;
				}
			}
			for (int i = 0; i < backupNegExamples.get(predName).size(); i++) {
				if (isHidden(backupNegExamples.get(predName).get(i).asLiteral())) {
					addToPos.add(backupNegExamples.get(predName).remove(i));
					i--;
				}
			}
			Utils.println("Flipped " + addToPos.size() + " examples from neg to pos for predicate: " + predName);
			backupPosExamples.get(predName).addAll(addToPos);
			Utils.println("Flipped " + addToNeg.size() + " examples from pos to neg for predicate: " + predName);
			backupNegExamples.get(predName).addAll(addToNeg);
			hiddenExamples = null;
		}
	}

	private void moveHiddenPosToNeg() {
		for (String predName : hiddenExamples.keySet()) {
			String cleanPredName = predName;
			if (predName.startsWith(multiclassPredPrefix)) { cleanPredName = predName.substring(multiclassPredPrefix.length()); } 
			List<Example> currPosExamples = backupPosExamples.get(cleanPredName);
			
			Utils.println("Original +ve egs: " + currPosExamples.size());
			Utils.println("Original -ve egs: " + backupNegExamples.get(cleanPredName).size());
			for (RegressionRDNExample hiddenRex : hiddenExamples.get(predName)) {
				String hiddenRep  = hiddenRex.toPrettyString("");
				boolean foundEg=false;
				for (int i = 0; i < currPosExamples.size(); i++) {
					
					String egRep = null;
					int value = 0;
					boolean ismulticlass = false;
					if (!getMulticlassHandler().isMultiClassPredicate(cleanPredName)) {
						egRep = currPosExamples.get(i).toPrettyString("");
						value = 1;
					} else {
						RegressionRDNExample newRex = getMulticlassHandler().morphExample(currPosExamples.get(i));
						egRep = newRex.toPrettyString("");
						value = newRex.getOriginalValue();
						ismulticlass = true;
					}

					if (egRep.equals(hiddenRep)) {
						hiddenRex.setOriginalHiddenLiteralVal(value);
						// Do not remove from positive examples for multi-class
						// We use only the positive examples in multi-class examples
						
						if (!ismulticlass || cmdArgs.getHiddenStrategy().equals("false")) {
							backupNegExamples.get(cleanPredName).add(currPosExamples.get(i));
							currPosExamples.remove(i);
							i--;
						} else {
							// To ensure the original value is never used
							((RegressionRDNExample)currPosExamples.get(i)).setOriginalValue(-1);
						}
						foundEg = true;
						break;
					}
				}
				//if (!foundEg) {
//					Utils.waitHere("Didn't find: " + hiddenRep);
				//}
			}
			Utils.println("New +ve egs: " + currPosExamples.size());
			Utils.println("New -ve egs: " + backupNegExamples.get(cleanPredName).size());
			//Utils.waitHere("#hidden="+ hiddenExamples.get(predName).size());
		}
	}

	private void keepHiddenPosNegExamples() {
		int rmCounter = 0;
		int leftCounter = 0;
		// Remove pos/neg examples that are hidden
		for (String predName : hiddenExamples.keySet()) {
			if (!backupPosExamples.containsKey(predName)) {
				Utils.error("Should be in test example set: " + predName);
			}
			for (int i = 0; i < backupPosExamples.get(predName).size(); i++) {
				if (!isHidden(backupPosExamples.get(predName).get(i).asLiteral())) {
					addFact(backupPosExamples.get(predName).get(i).asLiteral());
					backupPosExamples.get(predName).remove(i);
					i--;
					rmCounter++;
				} else {
					leftCounter++;
				}
			}
			for (int i = 0; i < backupNegExamples.get(predName).size(); i++) {
				if (!isHidden(backupNegExamples.get(predName).get(i).asLiteral())) {
					//	No need to add this fact since in neg
					backupNegExamples.get(predName).remove(i);
					i--;
					rmCounter++;
				} else {
					leftCounter++;
				}
			}
		}
		Utils.println("removed " + rmCounter + " examples and left with: " + leftCounter + " examples");
	}

	private void outputHiddenLiterals(String dbFile) throws IOException {
		Utils.println("Writing hidden literals to " + dbFile);
		BufferedWriter outWriter = new BufferedWriter(new FileWriter(dbFile));
		for (String predName : hiddenExamples.keySet()) {
			for (Example eg : hiddenExamples.get(predName)) {
				if (eg.predicateName.name.startsWith(multiclassPredPrefix)) {
					RegressionRDNExample rex = (RegressionRDNExample)eg;
					Example newEg = getMulticlassHandler().createExampleFromClass(rex, rex.getOriginalHiddenLiteralVal());
					outWriter.write(newEg.toPrettyString("") + ".");
				} else {
					outWriter.write(eg.toPrettyString("") + ".");
				}
				outWriter.newLine();
			}
		}
		outWriter.close();
		
	}

	private void outputFactsAndExamples(String dbFile) throws IOException {
		BufferedWriter outWriter = new BufferedWriter(new FileWriter(dbFile));
		// Output all facts that don't match the pos/neg examples
		for (Literal lit : getContext().getClausebase().getFacts()) {
			String predName = lit.getPredicateName().name;
			if (!backupPosExamples.containsKey(predName)) {
				outWriter.write(lit.toPrettyString());
				outWriter.newLine();
			}
		}
		
		for (String predName : backupPosExamples.keySet()) {
			for (Example eg : backupPosExamples.get(predName)) {
				if (!isHidden(eg.asLiteral())) {
					outWriter.write(eg.toPrettyString(""));
					outWriter.newLine();
				}
			}
		}
		
		for (String predName : backupNegExamples.keySet()) {
			for (Example eg : backupNegExamples.get(predName)) {
				// No need for negs if not hidden predicate
				if (hiddenExamples == null || !hiddenExamples.containsKey(predName)) {
					continue;
				}
				
				if (!isHidden(eg.asLiteral())) {
					outWriter.write("!" + eg.toPrettyString(""));
					outWriter.newLine();
				}
			}
		}
		outWriter.close();
	}
	private boolean isHidden(Literal lit) {

		String predName = lit.predicateName.name;
		if (predName.startsWith(multiclassPredPrefix)) { 
			predName = predName.substring(multiclassPredPrefix.length()); 
		} else {
			if (getMulticlassHandler().isMultiClassPredicate(predName)) {
				lit =  getMulticlassHandler().morphExample(new Example(lit));
			}
		}
		
		if (hiddenExamples == null || !hiddenExamples.containsKey(predName)) {
			return false;
		}
		
		boolean isHidden = false;
		String egRep = lit.toPrettyString("");
		
		// Check if this literal is hidden.
		for (RegressionRDNExample hiddenEx : hiddenExamples.get(predName)) {
			String hiddenRep = hiddenEx.toPrettyString("");
			if (hiddenRep.equals(egRep)) {
				isHidden = true;
				break;
			}
		}
		return isHidden;
	}
	
	private void sampleHiddenExamples(double hiddenPosLitProb, double hiddenNegLitProb) {
		if (hiddenExamples == null) {
			hiddenExamples  = new HashMap<String, List<RegressionRDNExample>>();
		}
		Set<String> hiddenPred = cmdArgs.getHiddenPredVal();
		if (hiddenPred == null) {
			hiddenPred = cmdArgs.getTargetPredVal();
		}
		int counter = 0;
		for (String predName : hiddenPred) {
			if (!backupPosExamples.containsKey(predName)) {
				continue;
			}
			for (Example eg : backupPosExamples.get(predName)) {
				if (Math.random() < hiddenPosLitProb) {
					RegressionRDNExample rex = new RegressionRDNExample(eg, false);
					if (getMulticlassHandler().isMultiClassPredicate(predName)) {
						RegressionRDNExample mcEx = getMulticlassHandler().morphExample(rex);
						mcEx.setHiddenLiteral(true);
						addToHiddenExamples(mcEx);
					} else {
						rex.setHiddenLiteral(true);
						addToHiddenExamples(rex);
					}
					counter++;
				}
			}
		}
		Utils.println("Number of hidden examples added from pos: " + counter);
		counter  = 0;
		for (String predName : hiddenPred) {
			if (!backupNegExamples.containsKey(predName)) {
				continue;
			}
			// Ignore neg examples for sampling multiclass examples
			if (getMulticlassHandler().isMultiClassPredicate(predName)) {
				continue;
			}
			for (Example eg : backupNegExamples.get(predName)) {
				if (Math.random() < hiddenNegLitProb) {
					RegressionRDNExample rex = new RegressionRDNExample(eg, false);
					rex.setHiddenLiteral(true);
					addToHiddenExamples(rex);
					counter++;
				}
			}
		}
		Utils.println("Number of hidden examples added from neg: " + counter);
	}
	
	public void addToHiddenExamples(RegressionRDNExample rex) {
		String predName = rex.predicateName.name;
		if (predName.startsWith(multiclassPredPrefix)) { predName = predName.substring(multiclassPredPrefix.length()); }
		if (!hiddenExamples.containsKey(predName)) {
			hiddenExamples.put(predName, new ArrayList<RegressionRDNExample>());
		}
		hiddenExamples.get(predName).add(rex);

	}

	private void readHiddenLiterals(String file) {
		if (!Utils.fileExists(file)) {
			return;
		}
		FileParser parser = this.getInnerLooper().getParser();
		List<Literal> hiddenLit = parser.readLiteralsInFile(file, true);
		hiddenExamples  = new HashMap<String, List<RegressionRDNExample>>();
		Set<String> hiddenPred = cmdArgs.getHiddenPredVal();
		if (hiddenPred == null) {
			hiddenPred = cmdArgs.getTargetPredVal();
		}
		int counter=0;
		for (Literal lit : hiddenLit) {
			boolean isMultiClass = false;
			String predName = lit.predicateName.name;
//			if (predName.startsWith(multiclassPredPrefix)) { 
//				predName = predName.substring(multiclassPredPrefix.length());
//				isMultiClass = true;
//			}
			// Ignore non-query hidden literal
			if (!hiddenPred.contains(predName)) {
				continue;
			}
			RegressionRDNExample rex = null;
			if (getMulticlassHandler().isMultiClassPredicate(predName)) {
				rex = getMulticlassHandler().morphExample(new Example(lit));
			} else {
				rex = new RegressionRDNExample(lit, false, "hidden");	
			}
			rex.setHiddenLiteral(true);
			addToHiddenExamples(rex);
			counter++;
			
		}
		Utils.println("Read " + counter + " hidden examples.");
	}
	

	/**
	 * This method moves facts to Examples if they are part of the joint inference task.
	 */
	private void fillMissingExamples() {
		Set<String> missingPositiveTargets = new HashSet<String>();
		Set<String> missingNegativeTargets = new HashSet<String>();
		for (String pred : cmdArgs.getTargetPredVal()) {
			// Make sure all targets have facts
			if (!backupPosExamples.containsKey(pred) ||
				 backupPosExamples.get(pred) == null ||
				 backupPosExamples.get(pred).isEmpty()) {
				Utils.println("% No pos ex for " + pred);
				missingPositiveTargets.add(pred);
			}
			// Make sure all targets have facts
			if (!backupNegExamples.containsKey(pred) ||
				backupNegExamples.get(pred) == null ||
				backupNegExamples.get(pred).isEmpty()) {
				Utils.println("% No neg ex for " + pred);
				missingNegativeTargets.add(pred);
			}
			// Initialize the hash map
			if (backupPosExamples.get(pred) == null) {
				backupPosExamples.put(pred, new ArrayList<Example>());
			}
			if (backupNegExamples.get(pred) == null) {
				backupNegExamples.put(pred, new ArrayList<Example>());
			}
		}
		
		if (missingPositiveTargets.size() != missingNegativeTargets.size()) {
			// Is this an error?  
			// Utils.error("Some targets missing in positive(" + missingPositiveTargets + ") or negative examples(" + missingNegativeTargets +").");
		}
		
		if (missingPositiveTargets.isEmpty()) {
			return;
		}
		// These predicates are in facts.
		predicatesAsFacts.addAll(missingPositiveTargets);
		
		for (Literal lit : getContext().getClausebase().getFacts()) {
			String litPredicate = lit.predicateName.name;
			if (missingPositiveTargets.contains(litPredicate)) {
			//Utils.println("Adding example: " + lit);	
				// Telling WILL that this is an example.
				getInnerLooper().confirmExample(lit);
				
				RegressionRDNExample eg = new RegressionRDNExample(lit, true, "% Obtained from facts.");
				addExampleToMap(eg, backupPosExamples);
				if (!disableFactBase) {
					addedToFactBase.add(eg);
				}
			}
		}
		
		if (missingNegativeTargets.size() > 0) {
			// Update targetArgSpecs so that predicates are available for creating negatives.
			getInnerLooper().chooseTargetMode(true);
			
			for (int i = 0; i < getInnerLooper().getTargets().size(); i++) {
				String predName = getInnerLooper().getTargets().get(i).predicateName.name;
				//Utils.println("considering " + predName);
				if (missingNegativeTargets.contains(predName)) {
					// Only create negs for predicates completely missing from pos/neg or 
					// for any predicate missing negs iff createSyntheticexamples is enabled.
					if (cmdArgs.isCreateSyntheticEgs() || missingPositiveTargets.contains(predName)) {
						Utils.println("Creating neg ex for: " + predName);
						List<Example> 
						negEgs =	CreateSyntheticExamples.createAllPossibleExamples("% Negative example created from facts.",
								getHandler(), getProver(), getInnerLooper().getTargets().get(i),getInnerLooper().getTargetArgSpecs().get(i),
								getInnerLooper().getExamplePredicateSignatures().get(i), null,
								new ArrayList<Example>(backupPosExamples.get(predName)), null, null);
						for (Example negEx : negEgs) {
							//if (negEx.predicateName.name.equals("hasposition")) { Utils.println("adding neg: " + negEx);}
							getInnerLooper().confirmExample(negEx);
						}
						backupNegExamples.put(predName, negEgs);
					}
				}
			}
		}
		// If no examples found, return
		for (String predName : cmdArgs.getTargetPredVal()) {
			if (missingPositiveTargets.contains(predName) && 
					(!backupPosExamples.containsKey(predName) || backupPosExamples.get(predName).isEmpty()) && 
				missingNegativeTargets.contains(predName) &&
					(!backupNegExamples.containsKey(predName) || backupNegExamples.get(predName).isEmpty())) {
				// Missing all examples of a particular type.
				String mesg = "No examples(positive & negative) found for predicate: " + predName;
				if (errorIfNoExamples) {
					Utils.error(mesg);
				} else {
					Utils.warning(mesg);
				}
				return;
			}
		}
		// Update targetArgSpecs.
		getInnerLooper().chooseTargetMode(true);
		
		
	}

	private void addExampleToMap(Example eg, Map<String,List<Example>> exampleMap) {
		String litPredicate = eg.predicateName.name;
		// TODO Auto-generated method stub
		if(!exampleMap.containsKey(litPredicate) ||	exampleMap.get(litPredicate) == null) {
			exampleMap.put(litPredicate, new ArrayList<Example>());
		}
		exampleMap.get(litPredicate).add(eg);
		// if (true) { Utils.waitHere("is this called? JWS 12/10"); }
	}

	public void reportStats() {
		Utils.println("\n% Memory usage by WILLSetup (just counts # targets?):");
		Utils.println("%  |backupPosExamples| = " + Utils.comma(backupPosExamples));
		Utils.println("%  |backupNegExamples| = " + Utils.comma(backupNegExamples));
		Utils.println("%  |predicatesAsFacts| = " + Utils.comma(predicatesAsFacts));
		Utils.println("%  |addedToFactBase|   = " + Utils.comma(addedToFactBase));
	}	
	
	public void prepareFactsAndExamples(String predicate) {
		prepareFactsAndExamples(backupPosExamples, backupNegExamples, predicate, 
				true,  // for learning?
				false, // Sampling hidden states?
				null);
	}
	
	public boolean allowRecursion = false;
	public static final String recursivePredPrefix = "recursive_";
	public static final String multiclassPredPrefix = "multiclass_";

	// Maintain a list of predicates that are already added, so that we can save on time.
	private HashSet<String> predicatesAsFacts = new HashSet<String>();
	private HashSet<Literal> addedToFactBase  = new HashSet<Literal>();	
	private boolean disableFactBase = true;
	
	private Set<PredicateNameAndArity> backupTargetModes=new HashSet<PredicateNameAndArity>();
	public void removeAllTargetsBodyModes() {
		
		for (PredicateNameAndArity bodyMode: getInnerLooper().getBodyModes()) {
			for(String target: cmdArgs.getTargetPredVal()) {
				if (bodyMode.getPredicateName().name.equals(target)) {
					// Since we are iterating over the modes, can't erase them here
					// erase the modes after the for loop
					backupTargetModes.add(bodyMode);
				}
			}
		}
		
		// Remove modes now
		for (PredicateNameAndArity mode : backupTargetModes) {
			getInnerLooper().removeBodyMode(mode);
		}		
	}
	
	public void addAllTargetModes() {
		if (backupTargetModes.isEmpty()) {
			return;
		}
		
		for (PredicateNameAndArity mode : backupTargetModes) {
			getInnerLooper().addBodyMode(mode);
		}
		backupTargetModes.clear();
	}
	
	public void prepareFactsAndExamples(Map<String, List<Example>> posEg,
										Map<String, List<Example>> negEg,
										String predicate, boolean forLearning, boolean forSamplingHidden, 
										String only_mod_pred) {
	//	Utils.println("% prepareFactsAndExamples(before): |posEg| = " + Utils.comma(posEg.get(predicate)) + ", |negEg| = " + Utils.comma(negEg.get(predicate)));
		long start = System.currentTimeMillis();
		if (allowRecursion || posEg.keySet().size() > 1 || negEg.keySet().size() > 1) { // JWS added the negEq check since we need to work with only NEG examples (ie, on an unlabeled testset).
			getInnerLooper().resetCachedClauseGroundings();
			//long start1 = System.currentTimeMillis();
			prepareFactsForJoint(posEg, negEg, predicate, only_mod_pred, forLearning, forSamplingHidden);
			//long end = 
		}
		prepareExamplesForTarget(posEg.get(predicate), negEg.get(predicate), predicate, forLearning);
		if (allowRecursion || posEg.keySet().size() > 1) {
			if (only_mod_pred != null) {
				recomputeFacts(predicate);
				recomputeFacts(recursivePredPrefix + predicate);
				recomputeFacts(only_mod_pred);
			} else {
				// Need to recompute all facts.
				for (String pred : cmdArgs.getTargetPredVal()) {
					recomputeFacts(recursivePredPrefix + predicate);
					recomputeFacts(pred);
				}
			}
			getInnerLooper().resetCachedClauseGroundings();
		}
		long end = System.currentTimeMillis();
	//	Utils.println("% prepareFactsAndExamples(after): |posEg| = " + Utils.comma(posEg.get(predicate)) + ", |nrgEg| = " + Utils.comma(negEg.get(predicate)));
		if (debugLevel > 1) { 
			Utils.waitHere("% Time taken for preparing WILL: " + Utils.convertMillisecondsToTimeSpan(end - start, 3) + ".");
		} else {
			//Utils.println("% Time taken for preparing WILL: " + Utils.convertMillisecondsToTimeSpan(end - start, 3) + ".");
		}
	}
	
	private RelationalDependencyNetwork rdnForPrecompute = null;
	private BoostingPrecomputeManager recomputer = null;
	// While doing joint inference, we may only precompute facts that influence some targets.
	private Set<String> onlyPrecomputeThese = null;
	
	public void setOnlyPrecomputeThese(Set<String> precompute) {
		onlyPrecomputeThese = precompute;
	}
	
	/**
	 * @return the hiddenExamples
	 */
	public Map<String, List<RegressionRDNExample>> getHiddenExamples() {
		return hiddenExamples;
	}

	/**
	 * @param hiddenExamples the hiddenExamples to set
	 */
	public void setHiddenExamples(Map<String, List<RegressionRDNExample>> hiddenExamples) {
		this.hiddenExamples = hiddenExamples;
	}

	private void recomputeFacts(String predicate) {
		if (onlyPrecomputeThese != null &&
			!onlyPrecomputeThese.contains(predicate)) {
			return;
		}
		if (rdnForPrecompute == null) {
			rdnForPrecompute = new RelationalDependencyNetwork(null, this);
			recomputer = new BoostingPrecomputeManager(this);
		}
		// Utils.println("% Recomputing for: " + predicate);
		// Get the children for this predicate of type COMPUTED
		Collection<PredicateName> recomputeThese = rdnForPrecompute.getPredicatesComputedFrom(predicate);
		if(recomputeThese != null && recomputeThese.size() > 0) {
			ArrayList<PredicateName> orderedPrecomputes = getOrderOfPrecomputes(recomputeThese);
			for (PredicateName pName : orderedPrecomputes) {
				// Utils.println("% Deleting and recomputing facts for: " + pName);
				deleteAllFactsForPredicate(pName);
				recomputer.recomputeFactsFor(pName, true);
			}
		}
	}

	private ArrayList<PredicateName> getOrderOfPrecomputes(
			Collection<PredicateName> recomputeThese) {
		ArrayList<PredicateName> predicateNames=new ArrayList<PredicateName>();
		// Creating a copy to make sure, we dont erase from original
		Set<PredicateName> inputPredicateNames = new HashSet<PredicateName>(recomputeThese);
		FileParser parser = getInnerLooper().getParser();
		for (int i = 0; i < getInnerLooper().getParser().getNumberOfPrecomputeFiles(); i++) {
			List<Sentence> precomputeThese = parser.getSentencesToPrecompute(i);
			if (precomputeThese == null) {
				continue;
			}
			for (Sentence sentence : precomputeThese) {
				List<Clause> clauses = sentence.convertToClausalForm();
				if (clauses == null) {
					continue;
				}
				// Take each clause
				for (Clause clause : clauses) {
					if (!clause.isDefiniteClause()) { 
						Utils.error("Can only precompute Horn ('definite' actually) clauses.  You provided: '" + sentence + "'."); 
					}

					PredicateName headPredName = clause.posLiterals.get(0).predicateName;
					if(inputPredicateNames.contains(headPredName)) {
						predicateNames.add(headPredName);
						inputPredicateNames.remove(headPredName);
					}
				}
			}
		}
		return predicateNames;
	}

	private void deleteAllFactsForPredicate(PredicateName pName) {
		List<PredicateSpec> specs = pName.getTypeList();
		if (specs == null) {
			Utils.error("No specs for " + pName);
		}
		// Just take the first spec to get the number of arguments.
		int numArgs = specs.get(0).getArity();
		List<Term> args = new ArrayList<Term>();
		for (int i = 0; i < numArgs; i++) {
			String var = getHandler().convertToVarString("arg" + i);
			args.add(getHandler().getVariableOrConstant(var));
		}
		Literal pLit = getHandler().getLiteral(pName, args);
		Clause cl = getHandler().getClause(pLit, true);
//		Utils.println("Fact size:" + getContext().getClausebase().getFacts().size());
		getContext().getClausebase().retractAllClausesWithUnifyingBody(cl);
	//	Utils.println("Fact size:" + getContext().getClausebase().getFacts().size());
		
	}

	public void prepareExamplesForTarget(String predicate) {
		prepareExamplesForTarget(backupPosExamples.get(predicate), backupNegExamples.get(predicate), predicate, true);
	}	
	
	public void prepareExamplesForTarget(List<Example> newPosEg,
								         List<Example> newNegEg,
								         String predicate, 
								         boolean forLearning) {

		if (debugLevel > 1) { Utils.println("% prepareWILLForPredicate: |newPosEg| = " + Utils.comma(newPosEg) + " |newNegEg| = " + Utils.comma(newNegEg));}
		getOuterLooper().setPosExamples(new ArrayList<Example>(newPosEg));
		getOuterLooper().setNegExamples(new ArrayList<Example>(newNegEg));
//		((DefaultHornClausebase)getProver().getClausebase()).resetIndexes();
		String prefix = null;
		if (forLearning) {
			if (debugLevel > 1) { Utils.println("\n% Morphing task.");}
			if (multiclassHandler.isMultiClassPredicate(predicate)) {
				Utils.println("Morphing to regression vector");
				getOuterLooper().setLearnMultiValPredicates(true);
				morphToRegressionVectorExamples(newPosEg, newNegEg, cmdArgs.isLearnMLN() && cmdArgs.isLearningMLNClauses());
				prefix = WILLSetup.multiclassPredPrefix;
			} else {
				getOuterLooper().setLearnMultiValPredicates(false);
				// 	Move the examples into facts and get facts to predicates.
				getOuterLooper().morphToRDNRegressionOuterLoop(1, 0, cmdArgs.getSampleNegsToPosRatioVal(), cmdArgs.getSamplePosProbVal(), cmdArgs.isLearnMLN() && cmdArgs.isLearningMLNClauses(), cmdArgs.reweighExamples, cmdArgs.isLearnRegression() || cmdArgs.isLearnProbExamples());
			}
            if (hiddenExamples != null &&
            	(cmdArgs.getHiddenStrategy().equals("EM") || cmdArgs.getHiddenStrategy().equals("MAP"))) {
            	updateHiddenExamples(getOuterLooper().getPosExamples());
            	updateHiddenExamples(getOuterLooper().getNegExamples());
            }

		}
		// Set target literal to be just one literal.
		if (forLearning && cmdArgs.isJointModelDisabled()) {
			getOuterLooper().innerLoopTask.setTargetAs(predicate, true, prefix);
		} else {
			getOuterLooper().innerLoopTask.setTargetAs(predicate, false, prefix);
		}
		handler.getPredicateName(predicate).setCanBeAbsent(-1);

		
	}
	/**
	 * 
	 * No need for any sampling since only positive examples used.
	 * TODO: Subsample positives
	 * TODO: allow weights for examples
	 * @param newPosEg
	 * @param newNegEg
	 * @param notLearnTrees
	 */
	private void morphToRegressionVectorExamples(List<Example> newPosEg,
			List<Example> newNegEg, boolean notLearnTrees) {
		getOuterLooper().setFlagsForRegressionTask(notLearnTrees);
		List<Example> positiveExamples = new ArrayList<Example>(4);

		// Ignore the neg Eg since they are present as '0's in the regression vector
		for (Example example : newPosEg) {
			//Utils.println("morph example: " + example);
			positiveExamples.add(multiclassHandler.morphExample(example));
		}
		
		getOuterLooper().setPosExamples(positiveExamples);
		getOuterLooper().setNegExamples(new ArrayList<Example>(0));
	}

	private void updateHiddenExamples(List<Example> egList) {
		// Check if example is hidden
		for (Example eg : egList) {
			// It should be of regression rdn example type
			if (eg instanceof RegressionRDNExample) {
				String egRep = eg.toPrettyString("");
				String predName = eg.predicateName.name;
				if (predName.startsWith(multiclassPredPrefix)) { predName = predName.substring(multiclassPredPrefix.length()); }
				if (!hiddenExamples.containsKey(predName)) {
					continue;
				}
				for (RegressionRDNExample hiddenEx : hiddenExamples.get(predName)) {
					String hiddenExRep = hiddenEx.toPrettyString("");
					if (hiddenExRep.equals(egRep)) {
						RegressionRDNExample rex = (RegressionRDNExample)eg;
						rex.setHiddenLiteral(true);
						// Utils.println("Found hidden example:" + rex.toPrettyString(""));
						break;
					}
				}
			} else {
				Utils.waitHere("Make sure that example is of correct type: " + eg);
			}
		}
		
	}

	// TODO TVK remove the common stuff from getJointExamples
	public Map<String,List<Example>> getExamplesByPredicateName(List<Example> examples, boolean createBootstrapSample) {  // Use LIST since there can be duplicates.
		Map<String,List<Example>> result = new HashMap<String,List<Example>>();
		if (createBootstrapSample) { // Added by JWS.
			int numExamples = Utils.getSizeSafely(examples);
			for (int i = 0; i < numExamples; i++) {
				Example eg = examples.get(Utils.random0toNminus1(numExamples));
				String target = eg.predicateName.name; 
				if (!result.containsKey(target)) {
					result.put(target, new ArrayList<Example>());
				}
				result.get(target).add(eg);
			}
		} else {
			for (Example eg : examples) {
				String target = eg.predicateName.name; 
				if (!result.containsKey(target)) {
					result.put(target, new ArrayList<Example>());
				}
				result.get(target).add(eg);
			}
		}
		return result;
	}
	
	public HashMap<String,List<RegressionRDNExample>> getJointExamples(Set<String> targets) {
		HashMap<String,List<RegressionRDNExample>> result = new HashMap<String,List<RegressionRDNExample>>();
		
		// TODO Currently assuming they are marked as examples already.
		int counterPos = 0, counterNeg = 0;
		for (String pred : targets) {
			if (!result.containsKey(pred)) {
				result.put(pred, new ArrayList<RegressionRDNExample>());
			}
			List<Example> lookupPos = backupPosExamples.get(pred);  Utils.println("\n% for " + pred + " |lookupPos| = " + Utils.comma(lookupPos));
			if (lookupPos != null) for (Example ex : lookupPos) {
				RegressionRDNExample rex = new RegressionRDNExample(getHandler(), ex.extractLiteral(), 1, ex.provenance, ex.extraLabel);
				if (cmdArgs.isLearnRegression()) {
					if (ex instanceof RegressionExample) {
						rex.originalRegressionOrProbValue = ((RegressionExample)ex).getOutputValue();
					} else {
						Utils.waitHere("Expected regression examples for learning regression trees");
					}
				}
				rex.setOriginalTruthValue(true);
				String target = ex.predicateName.name;
				if (targets.contains(target)) { 
					if (!result.containsKey(target)) {
						result.put(target, new ArrayList<RegressionRDNExample>());
					}
					result.get(target).add(rex); counterPos++;

				} else {
					Utils.error("Didn't expect this example as target. Model absent: " + target);
				}
			}
			List<Example> lookupNeg = backupNegExamples.get(pred);  Utils.println("% for " + pred + " |lookupNeg| = " + Utils.comma(lookupNeg));
			if (lookupNeg != null) for (Example ex  : lookupNeg) {
				RegressionRDNExample rex = new RegressionRDNExample(getHandler(), ex.extractLiteral(), 0, ex.provenance, ex.extraLabel);
				rex.setOriginalTruthValue(false);
				if (cmdArgs.isLearnRegression()) {
					if (ex instanceof RegressionExample) {
						rex.originalRegressionOrProbValue = ((RegressionExample)ex).getOutputValue();
					} else {
						Utils.waitHere("Expected regression examples for learning regression trees");
					}
				}
				String target = ex.predicateName.name;
				if (targets.contains(target)) { 
					if (!result.containsKey(target)) {
						result.put(target, new ArrayList<RegressionRDNExample>());
					}
					result.get(target).add(rex); counterNeg++;
				} else {
					Utils.error("Didn't expect this example as target. Model absent: " + target);
				}
			}	

		}

		Utils.println("% getJointExamples: |pos| = " + Utils.comma(counterPos) + ", |neg| = " + Utils.comma(counterNeg));
		return result;
	}
	
	public void addAllExamplesToFacts() {
		prepareFactsForJoint(backupPosExamples, backupNegExamples, null, null, true, false);
	}
	private void prepareFactsForJoint(Map<String,List<Example>> posEg,
									  Map<String,List<Example>> negEg, 
									  String predicate, String onlyModPred,
									  boolean forLearning, boolean removeFactsInEgListOnly) {
		// to  be safe
		removeFactsInEgListOnly = true;
		Set<String> newlyAddedPredicates = new HashSet<String>();
		//Utils.println("PredicatesAsFacts:" + Utils.toString(predicatesAsFacts, ","));
		int counter=0;
		if (predicate == null) {
			//Utils.waitHere("predicate set to null!");
		}
		for (String target : posEg.keySet()) {
			//Utils.println("Removing facts for: " + target + " size:" + posEg.get(target).size());
			if (predicate != null && target.equals(predicate)) {
				if (predicatesAsFacts.contains(target) && 
					disableFactBase && !allowRecursion) {
			//		Utils.println("Removing all facts");
					//if (posEg.get(target).size() > 0) {
						//PredicateNameAndArity pna = posEg.get(target).get(0).getPredicateNameAndArity();
					long rstart  = System.currentTimeMillis();
					//getContext().getClausebase().retr
					if (removeFactsInEgListOnly) {
						for (Example eg : posEg.get(target)) {
							if (!disableFactBase) {
								addedToFactBase.remove(eg);
							}
							removeFact(eg);
						}
					} else {
						removeAllFacts(target);
					}
					long rend = System.currentTimeMillis();
					//Utils.println("Time to remove:"  + Utils.convertMillisecondsToTimeSpan(rend-rstart));
						//retractAllClausesForPredicate(pna);
					//}
				} else {
					for (Example eg : posEg.get(target)) {
						counter++;
						// Remove this fact from clausebase.
						if (predicatesAsFacts.contains(target) && 
								(disableFactBase || addedToFactBase.contains(eg))) {
							if (!disableFactBase) {
								addedToFactBase.remove(eg);
							}
							removeFact(eg);
						}
						// add the recursive fact
						if (allowRecursion) {
							Literal lit = getHandler().getLiteral(handler.getPredicateName(recursivePredPrefix + eg.predicateName.name), eg.getArguments());
							if (disableFactBase || !addedToFactBase.contains(lit)) {
								addFact(lit);
								if (!disableFactBase) {
									addedToFactBase.add(lit);
								}
							}
						}
						if (counter % 1000 == 0) {
							//Utils.println("% prepareFactsForJoint processed this many pos examples so far: " + Utils.comma(counter));
						}
					}
				}
			} else {
				for (Example eg : posEg.get(target)) {
					counter++;
					// Remove the recursion fact as this is not the target predicate 
					if (allowRecursion) {
						Literal lit = getHandler().getLiteral(handler.getPredicateName(recursivePredPrefix + eg.predicateName.name), eg.getArguments());
						// if target predicate is set to null, we add the recursive fact as we want to add all examples as facts
						// for sampling hidden states
						if (predicate != null) {
							if (disableFactBase || addedToFactBase.contains(lit)) {
								if (!disableFactBase) {
									addedToFactBase.remove(lit);
								}
								removeFact(lit);
							}
						} else {
							if (!disableFactBase) {
								addedToFactBase.add(lit);
							}
							addFact(lit);
						}
					} 

					if ((onlyModPred == null || eg.predicateName.name.equals(onlyModPred)) &&
						(!(predicatesAsFacts.contains(eg.predicateName.name) && forLearning)) && 
						(disableFactBase || !addedToFactBase.contains(eg))) {
						if (!disableFactBase) {
							addedToFactBase.add(eg);
						}
						addFact(eg);
					}
					if (counter % 1000 == 0) {
						//Utils.println("% prepareFactsForJoint processed this many pos examples so far: " + Utils.comma(counter));
					}
				}
				// update the set
				newlyAddedPredicates.add(target);
			}
		}
		counter=0;
		for (String target : negEg.keySet()) {
			for (Example eg : negEg.get(target)) {
				if (predicate == null || !target.equals(predicate)) {
					// update the set
					newlyAddedPredicates.add(target);
				}
				// Either way remove this fact
				if (predicatesAsFacts.contains(eg.predicateName.name) &&
					(onlyModPred == null || eg.predicateName.name.equals(onlyModPred)) &&
					(disableFactBase || addedToFactBase.contains(eg))) {
					removeFact(eg);
					counter++;
					if (!disableFactBase) {
						addedToFactBase.remove(eg);
					}
				}
				if (allowRecursion) {
					Literal lit = getHandler().getLiteral(handler.getPredicateName(recursivePredPrefix + eg.predicateName.name), eg.getArguments());
					if (disableFactBase || addedToFactBase.contains(lit)) {
						removeFact(lit);
						counter++;
						if (!disableFactBase) {
							addedToFactBase.remove(lit);
						}
					}
				} 
				counter++;
				if (counter % 10000 == 0) {
					//Utils.println("% prepareFactsForJoint processed this many neg examples so far: " + Utils.comma(counter));
				}
			}
		}
		predicatesAsFacts.addAll(newlyAddedPredicates);
		// Remove the target as predicate
		// Remove the target as predicate
		if (predicate != null) {
			predicatesAsFacts.remove(predicate);
		}
		//predicatesAsFacts.remove(predicate);
		
	}

	private void removeAllFacts(String predicate) {
		// if (predicate.startsWith(recursivePredPrefix + "genre")) { Utils.println("Removing all facts: " + recursivePredPrefix); }
		List<Literal> delFacts = new ArrayList<Literal>();
		for(DefiniteClause cl: getContext().getClausebase().getAssertions()) {
			if(cl.isDefiniteClauseFact()) {
				Literal lit = cl.getDefiniteClauseFactAsLiteral();
				if (lit.predicateName.name.equals(predicate)) {
					if (getContext().getClausebase() instanceof DefaultHornClausebase) {
						delFacts.add(lit);
					}
				}
			}
		}
		// Deleting after finding all facts so that we don't pollute the iterator
		for (Literal lit : delFacts) {
			getContext().getClausebase().removeClause(lit);
		}
		
	}

	public Clause convertFactToClause(String fact) {
		if(cmdArgs.isUseYapVal()) {
			return convertFactToClause(fact, VarIndicator.uppercase);
		}
		return getInnerLooper().getParser().parseDefiniteClause(fact);
//		return     convertFactToClause(fact, VarIndicator.questionMarks);
	}
	public Clause convertFactToClause(String fact, VarIndicator  newVarIndicator) {
		VarIndicator oldVarIndicator = getHandler().getVariableIndicatorNoSideEffects();
		getHandler().setVariableIndicator(newVarIndicator);
		getHandler().keepQuoteMarks = false;
//		Utils.println("% convertFactToClause: " + fact);
		Clause cl = getInnerLooper().getParser().parseDefiniteClause(fact);
		getHandler().setVariableIndicator(oldVarIndicator);
		return cl;
	}



	/**
	 * @param outerLooper the outerLooper to set
	 */
	public void setOuterLooper(ILPouterLoop outerLooper) {
		this.outerLooper = outerLooper;
		this.innerLooper = outerLooper.innerLoopTask;
		this.handler     = outerLooper.innerLoopTask.getStringHandler();
		this.context     = outerLooper.innerLoopTask.getContext();
		this.prover      = outerLooper.innerLoopTask.getProver();
		neighboringFactFilterList = null;
	}

	/**
	 * @return the outerLooper
	 */
	public ILPouterLoop getOuterLooper() {

		return outerLooper;
	}

	/**
	 * @return the innerLooper
	 */
	public LearnOneClause getInnerLooper() {
		return innerLooper;
	}

	/**
	 * @return the handler
	 */
	public HandleFOPCstrings getHandler() {
		return handler;
	}

	/**
	 * @return the context
	 */
	public HornClauseContext getContext() {
		return context;
	}

	public void removeFact(Literal eg) {
		//Utils.println("Remove fact:" + eg);
		//if (eg.predicateName.name.startsWith(WILLSetup.recursivePredPrefix + "genre")) { Utils.println("Removing " + eg); }
		getContext().getClausebase().retractAllClausesWithUnifyingBody(eg);
	}

	public void addFact(Literal eg) {
		if (getMulticlassHandler() != null && getMulticlassHandler().isMultiClassPredicate(eg.predicateName.name)) {
			//Utils.waitHere("adding " + eg);
		}
		if (eg instanceof RegressionRDNExample) {
			
		}
		//if (eg.predicateName.name.startsWith(WILLSetup.recursivePredPrefix + "genre")) { Utils.println("Adding " + eg); }
		//Utils.println("Added fact:" + eg);
		getContext().getClausebase().assertFact(eg);
	}

	/**
	 * @return the prover
	 */
	public HornClauseProver getProver() {
		return prover;
	}
	
	// Pulled out by JWS (7/8/10) so could be called elsewhere for a plain regression-tree learning.
	public ILPouterLoop createRegressionOuterLooper(String[] newArgList, String directory, String prefix, double negToPosRatio, boolean isaRegressionTaskRightAway) throws SearchInterrupted {
		System.out.println("newArgList"+newArgList);
		System.out.println("directory"+directory);
		System.out.println("prefix"+prefix);
		try {
			SearchStrategy         strategy = new BestFirstSearch();
			ScoreSingleClause        scorer = (cmdArgs.isLearnOCC() ? new ScoreOCCNode() :  new ScoreRegressionNode(cmdArgs.isLearnMLN()));
			// We're (sometimes) using A SMALL INDEX HERE, since the memory needs are already very large (i.e., trade off time for space).
			// We need to keep all the literals related to a specific proof (i.e., test of a hypothesis) around, but are willing to redo between proofs.
			// if (runningLargeTask) { // TODO - add 'runningLargeTask' to the passed-in arguments.
					LazyGroundNthArgumentClauseIndex.setMaximumIndexSize(100); // Need to set these BEFORE creating the LazyHornClausebase.
					LazyGroundClauseIndex.setMaximumIndexSize(           100);
			// }
					
			HandleFOPCstrings stringHandler = new HandleFOPCstrings(true); // Let the first file read set the default.  (Are libraries read first?)
			HornClausebase clausebase = null;
			if (cmdArgs.isUsingDefaultClausebase()) {
				clausebase = new DefaultHornClausebase(stringHandler); 
			} else {
				clausebase = new LazyHornClausebase(stringHandler);
			}
			
			HornClauseContext context = new DefaultHornClauseContext(clausebase);
			
		//	if (runningLargeTask) { // TODO - add this to the pass-in arguments.
				context.getStringHandler().variantFactHandling = VariantClauseAction.SILENTLY_KEEP_VARIANTS;
				context.getStringHandler().variantRuleHandling = VariantClauseAction.WARN_AND_REMOVE_VARIANTS;
		//	}
			
			stringHandler.keepQuoteMarks                       = true;
			stringHandler.useFastHashCodeForLiterals           = false;
			stringHandler.dontComplainIfMoreThanOneTargetModes = true;
			boolean                                     useRRR = false;
		//	Utils.println("% newArgList[0] = " + newArgList[0]);
		//	Utils.println("% newArgList[1] = " + newArgList[1]);
		//	Utils.println("% newArgList[2] = " + newArgList[2]);
		//	Utils.println("% newArgList[3] = " + newArgList[3]); // Utils.waitHere("directory = " + directory + "  prefix = " + prefix);
			Utils.println("\n% Calling ILPouterLoop from createRegressionOuterLooper.");
			setOuterLooper(new ILPouterLoop(directory, prefix, newArgList, strategy, scorer, new Gleaner(), context, useRRR, isaRegressionTaskRightAway));
			Utils.println("\n% The outer looper has been created.");
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Encountered a problem: " + e);
		}
		
		Gleaner gleaner = (Gleaner) getInnerLooper().searchMonitor;
		getOuterLooper().writeGleanerFilesToDisk = true;
		getOuterLooper().setCheckpointEnabled(checkpointEnabled);
		getInnerLooper().setDumpGleanerEveryNexpansions(1000);
		gleaner.reportingPeriod             =   1000;

		getInnerLooper().maxSearchDepth     =  10000;
		getInnerLooper().verbosity          =      0;

		getInnerLooper().maxNumberOfNewVars =      7;
		getInnerLooper().maxDepthOfNewVars  =      7;
		getInnerLooper().maxPredOccurrences =      5;
		getInnerLooper().restartsRRR        =     25;
		getOuterLooper().max_total_nodesExpanded = 10000000;
		getOuterLooper().max_total_nodesCreated  = 10 * getOuterLooper().max_total_nodesExpanded;
		getHandler().setStarMode(TypeSpec.minusMode);
		getInnerLooper().setMEstimatePos(0.1);
		getInnerLooper().setMEstimateNeg(0.1);
		getInnerLooper().setMaxNegCoverage(0.499);
		// Set to true by TVK (04/18/12)
		if(true) {
		getInnerLooper().getProver().setMaxNodesToConsider(1000000);
		getInnerLooper().getProver().setMaxNodesToCreate( 10000000);
		getInnerLooper().getProver().setMaximumClockTimePerIterationInMillisec(300000); // JWS: this is (sometimes) set high (multiple minutes), e.g. for a threshold calc for the breast-cancer dataset.
		getInnerLooper().setMaximumClockTimePerIterationInMillisec(           7200000); // Units are milliseconds.  So 3600000 = 1 hour.
		} else {
		getInnerLooper().getProver().setMaxNodesToConsider(100000);
		getInnerLooper().getProver().setMaxNodesToCreate( 1000000);
		getInnerLooper().getProver().setMaximumClockTimePerIterationInMillisec(60000); // JWS: this is (sometimes) set high (ten minutes) for a threshold calc for the breast-cancer dataset.
		getInnerLooper().setMaximumClockTimePerIterationInMillisec(3600000); // Units are milliseconds.  So 3600000 = 1 hour.
		}
		getInnerLooper().overwritePrecomputeFileIfExists = true;
		// NOTE: currently the code does not test for this (setMaxAcceptableNodeScoreToStop) until AFTER the first clause is learned
		// (it is left to the caller to decide that a tree should be tried - it is still possible
		// only a LEAF is returned since the ILP inner loop might not find an acceptable root node).

		// Commented the following lines as they are set in morphToRDNRegressionOuterLoop
		//outerLooper.learningTreeStructuredTheory        = true;
		//outerLooper.innerLoopTask.isaTreeStructuredTask = true; // TODO - couple this with setting the above (via a setter).
		getInnerLooper().regressionTask = isaRegressionTaskRightAway;  // Sometimes we start out with a BOOLEAN task then later turn into a regression one.

		double minFractionOnBranches = Math.max(0.005, 0.05 / negToPosRatio);  // This is a fraction of the current set of examples at the root.
		getOuterLooper().setMaxAcceptableNodeScoreToStop(0.0025); // If a set has less than this much VARIANCE per example, it will become a leaf.
		getOuterLooper().setOverallMinPosWeight(10); // If a recursive call involves fewer than this number of examples, make a leaf node (ALSO IMPACTS THE INITIAL CALL?)
		if (!cmdArgs.isLearnRegression() && !cmdArgs.isLearnProbExamples()) {
			getInnerLooper().setMinPosCoverageAsFraction(minFractionOnBranches);   // For a clause to be acceptable, it needs to cover at least this fraction of the examples (and not more than 1 minus this fraction).
		}
		// MLN conditions removed by TVK (04/18/12)
		//if (!cmdArgs.isLearnMLN()) {
		getInnerLooper().setMinPosCoverage(minFractionOnBranches);   // For a clause to be acceptable, it needs to cover at least this fraction of the examples.
		// The next line overrides the one immediately above this comment.
		getInnerLooper().setMinPosCoverage(3); // Need to be careful here, since data might be quite skewed.  Should really be something like 10% of the majority category.
		//}
		if (//!cmdArgs.isLearnMLN() && 
			!cmdArgs.isLearnRegression()) {
			getOuterLooper().setMaxRecallOfAcceptableClause(1 - minFractionOnBranches); // And cannot cover too many of the examples.
		}
		if (cmdArgs.isLearnMLN()) {
			getOuterLooper().setLearnMLNTheory(true);
		}
		if (cmdArgs.isUseProbabilityWeights()) {
			getInnerLooper().useProbabilityWeights = true;
		}
		// USE THIS LATER SINCE SOMETIMES WE NEED TO USE AN 'ACCESSOR'?
		//getOuterLooper().setMaxRecallOfAcceptableClause(1 - minFractionOnBranches); // And cannot cover too many of the examples.			
		
		getOuterLooper().numberPosSeedsToUse           = (int) Math.ceil(5 * negToPosRatio); // Since WILL focuses on seeds to filter out candidate clauses, we need a good number here because some seeds will go on the "false" branch.  Want to have enough so that on average can find the maximally acceptable skew for the true/false branches.  Or maybe OK to miss these to save time by having a smaller set of seeds?
		getInnerLooper().clausesMustCoverFractPosSeeds = 0.999999 / getOuterLooper().numberPosSeedsToUse; // Only require ONE to be covered (other constraints will filter clauses).
		getOuterLooper().setMinPrecisionOfAcceptableClause(0.001); // Need to cover at least 1% of the examples, even if the root.
		getOuterLooper().setMaxNumberOfLiteralsAtAnInteriorNode(cmdArgs.getMaxLiteralsInAnInteriorNode());
		
		getOuterLooper().setMaxTreeDepth(5); // Counting is from 0 (i.e., this is really "max number of ancestor nodes").  maxNumberOfClauses might 'dominate' this setting.
		
		
		
		
		getOuterLooper().innerLoopTask.maxFreeBridgersInBody = 1; // Math.max(2, outerLooper.getMaxNumberOfLiteralsAtAnInteriorNode()); // This is the body of ONE node.  By allowing more bridgers that literals we can, say, create comparators between two extracted values.
		// Add 1 here since the root has literals but is at depth 0.
		// We don't want the individual trees to get too complicated, so limit to 4 literals (so if 2 lits per nodes and depth is 2, instead of a max of 6 literals, the limit of 4 will be used).
		getOuterLooper().setMaxTreeDepthInLiterals(Math.max(4, (getOuterLooper().getMaxTreeDepth() + 1) * (getOuterLooper().innerLoopTask.maxFreeBridgersInBody + getOuterLooper().getMaxNumberOfLiteralsAtAnInteriorNode()))); // Recall there could be some bridgers at each interior node, so this is allowing some bridgers.
		
		ChildrenClausesGenerator.modForReportingExpansions = 1; // Since we won't be doing a lot of expansions, let's see all of them.
		// Reminder: "consider" means "expand" (i.e., remove from the OPEN list and generate its children);  "create" is a counter on children.
		int matLitsAtNode = cmdArgs.getMaxLiteralsInAnInteriorNode() + getOuterLooper().innerLoopTask.maxFreeBridgersInBody;
		getInnerLooper().setMaxNodesToConsider(matLitsAtNode > 1 ?     10 :     50); // For reasons of time, don't want to expand too many nodes (does this setting matter if maxLits=1?).  Eg, expand the root, pick the best child, expand it, then pick the overall best unexpanded child, and repeat a few more times. 
		getInnerLooper().setMaxNodesToCreate(  matLitsAtNode > 1 ?  10000 :  50000); // This can be high since we want the # of expansions to be the limiting factor.
		getOuterLooper().maxNumberOfClauses =  matLitsAtNode > 1 ?     12 :     16 ; // This is the maximum number of non-leaf nodes (tree building is via BEST-FIRST search).  MaxTreeDepth might 'dominate' this setting.
		getOuterLooper().maxNumberOfCycles  =     2 * getOuterLooper().maxNumberOfClauses;
		if (cmdArgs.isLearnRegression()) {
			getInnerLooper().minNumberOfNegExamples = 0; // This should be zero since we really don't have any negatives here (we instead are doing regression).
		} else {
			// TVK : This SHOULDN'T be zero here, it is set later in morph. This is used to create negative examples.
			getInnerLooper().minNumberOfNegExamples = 10; // This should be zero since we really don't have any negatives here (we instead are doing regression).
		}
		getInnerLooper().fractionOfImplicitNegExamplesToKeep = 1;
		// Other constraints say that at least half the examples must be covered, and sometimes we need to use the negation to do that.
	//	if (cmdArgs.getMaxLiteralsInAnInteriorNode() <= 1 && getOuterLooper().innerLoopTask.maxFreeBridgersInBody < 1) { getInnerLooper().setIgnoreNegatedLiterals(true); }

		// TODO - is this time PER TREE?  I think so ...
		double maxHoursToRunPerTree = getOuterLooper().getMaxTreeDepth() * 4.0; // TODO - determine if when time runs out, a reasonable model results. JWS: I think that sometimes timing out makes a NOT_* seem better than it should.
		// TODO - should also have a maxTime for learning ALL N trees.  Maybe write the remaining trees as adding zero to the wgt'ed sum, since other code looks for maxTrees.
		getOuterLooper().setMaximumClockTimeInMillisec((long) (maxHoursToRunPerTree * 60 * 60 * 1000));

	//	getOuterLooper().initialize(false);  // We're leaving this for the caller, in case the caller needs to do somethings before initialization.		
		return getOuterLooper();
	}

	/**
	 * @param lastSampledWorlds the lastSampledWorlds to set
	 */
	public void setLastSampledWorlds(HiddenLiteralSamples lastSampledWorlds) {
		this.lastSampledWorlds = lastSampledWorlds;
	}
	public HiddenLiteralSamples getLastSampledWorlds() {
		return this.lastSampledWorlds;
	}
	
	public List<PredicateNameAndArity> getListOfPredicateAritiesForNeighboringFacts() {
		if (neighboringFactFilterList == null) {
			Set<PredicateNameAndArity> pars = new HashSet<PredicateNameAndArity>();
			String lookup=null;
			boolean addAllModes = true;
			if ((lookup =  getHandler().getParameterSetting("useAllBodyModesForNeighboringFacts")) != null) {
				addAllModes = Utils.parseBoolean(lookup);
			}
			if (addAllModes) {
				pars.addAll(BoostingUtils.convertBodyModesToPNameAndArity(getInnerLooper().getBodyModes()));
			}
			if ((lookup =  getHandler().getParameterSetting("includePredicatesForNeighboringFacts")) != null) {
				lookup = lookup.replaceAll("\"", "");
				List<String> preds = Utils.parseListOfStrings(lookup);
				for (String pred : preds) {
					pars.addAll(convertStringToPnameArity(pred));
				}
			}
			if ((lookup =  getHandler().getParameterSetting("excludePredicatesForNeighboringFacts")) != null) {
				lookup = lookup.replaceAll("\"", "");
				List<String> preds = Utils.parseListOfStrings(lookup);
				for (String pred : preds) {
					pars.removeAll(convertStringToPnameArity(pred));
				}
			}
			neighboringFactFilterList = new ArrayList<PredicateNameAndArity>(pars);
		}
		return neighboringFactFilterList;
	}
	
	private List<PredicateNameAndArity> convertStringToPnameArity(String pname) {
		String[] parts = pname.split("/");
		List<PredicateNameAndArity> pars = new ArrayList<PredicateNameAndArity>();
		// Arity given
		if (parts.length > 1) {
			String pred = parts[0];
			int arity = Integer.parseInt(parts[1]);
			pars.add(new PredicateNameAndArity(getHandler().getPredicateName(pred), arity));
		} else {

			PredicateName predicate = getHandler().getPredicateName(parts[0]);
			// For each spec for the predicate
			for (PredicateSpec spec : predicate.getTypeList()) {
				if (spec.getTypeSpecList() != null) {
					int arity = spec.getTypeSpecList().size();
					PredicateNameAndArity par = new PredicateNameAndArity(predicate, arity);
					if (!pars.contains(par)) {
						pars.add(par);
					}
				}
			}
		}
		return pars;
	}

	public List<Boolean> getBitMaskForNeighboringFactArguments(String target) {
		List<Boolean> bitmask = new ArrayList<Boolean>();
		String lookup;
		if ((lookup =  getHandler().getParameterSetting("bitMaskForNeighboringFactArgsFor" + target)) != null) {
			lookup = lookup.replaceAll("\"", "");
			List<String> bools = Utils.parseListOfStrings(lookup);
			for (String bool : bools) {
				bitmask.add(Utils.parseBoolean(bool));
			}
		} else {
			bitmask.add(false); // AR
			bitmask.add(false); // PA
			bitmask.add(false); // SE
			bitmask.add(true);
			bitmask.add(true);
		}
		return bitmask;
	}

	/**
	 * @return the multiclassHandler
	 */
	public MultiClassExampleHandler getMulticlassHandler() {
		return multiclassHandler;
	}

}
