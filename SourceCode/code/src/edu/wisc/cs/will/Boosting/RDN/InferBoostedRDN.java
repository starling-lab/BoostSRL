package edu.wisc.cs.will.Boosting.RDN;

import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

import edu.wisc.cs.will.Boosting.Common.SRLInference;
import edu.wisc.cs.will.Boosting.MLN.MLNInference;
import edu.wisc.cs.will.Boosting.Trees.ClauseBasedTree;
import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;
import edu.wisc.cs.will.Boosting.Utils.CommandLineArguments;
import edu.wisc.cs.will.Boosting.Utils.ThresholdSelector;
import edu.wisc.cs.will.DataSetUtils.ComputeAUC;
import edu.wisc.cs.will.DataSetUtils.PredicateModes;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.StringConstant;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.ILP.CoverageScore;
import edu.wisc.cs.will.Utils.GzippedBufferedWriter;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.Utils.condor.CondorFileWriter;

public class InferBoostedRDN {
	

	private boolean useAccuracyMeasure    = false;
	private boolean normalizeProbs        = false;
	private boolean printExamples         = false;	
	private boolean writeQueryAndResults  = true;
	private boolean printExamplesForTuffy = false;
	private boolean writeResultsAsRules   = false;
	private boolean useOldFileLocations	  = true;
	private double  minRecallForAUCPR     = 0;
	private double minLCTrees			  = 20;
	private double incrLCTrees			  = 2;
	
	private CommandLineArguments cmdArgs;	
	private WILLSetup            setup;
	private JointRDNModel        model;
	
	public static final String RDNTreeStats = "RDNtreePathStats";
	public InferBoostedRDN(CommandLineArguments args, WILLSetup setup) {
		this.cmdArgs = args;
		this.setup   = setup;
		setParamsUsingSetup(setup);
		if (Utils.getUserName().equalsIgnoreCase("tkhot")) {
			useOldFileLocations = true;	
		}
	}
	
	public void runInference(JointRDNModel rdns, double thresh) {
		model = rdns;
		// JointModelSampler sampler = new JointModelSampler(rdns, setup, cmdArgs);
		Map<String,List<RegressionRDNExample>> targetExamples = setup.getJointExamples(cmdArgs.getTargetPredVal());
		Map<String,List<RegressionRDNExample>> jointExamples = setup.getHiddenExamples();
		if (jointExamples == null) {
			jointExamples = new HashMap<String, List<RegressionRDNExample>>();
		}
		jointExamples.putAll(targetExamples);
		boolean negativesSampled = false;
		
		Utils.println("\n% Starting inference in bRDN.");
		SRLInference sampler = null;
		if (cmdArgs.isLearnMLN()) {
			if (jointExamples.keySet().size() > 1) {
				sampler = new JointModelSampler(rdns, setup, cmdArgs,true);
			} else {
				if (!cmdArgs.isPrintAllExamplesToo()) {
					Utils.println("\n% Subsampling the negative examples.");
					subsampleNegatives(jointExamples);
					negativesSampled = true;
				}
				sampler = new MLNInference(setup, rdns);
			}
		} else {
			sampler = new JointModelSampler(rdns, setup, cmdArgs);
			// We can sub sample negatives if no recursion or joint inference.
			if (!sampler.getRdn().needsJointInference() &&
				!sampler.getRdn().hasRecursion()) {
				subsampleNegatives(jointExamples);
				negativesSampled = true;
			}
		}
			
		int startCount = cmdArgs.getMaxTreesVal();
		int increment = 1;
		if (cmdArgs.isPrintLearningCurve()) {
			startCount = (int)minLCTrees;
			increment = (int)incrLCTrees;
			for (String targ : jointExamples.keySet()) {
				File f = new File(getLearningCurveFile(targ, "pr"));
				if (f.exists()) { f.delete();}
				 f = new File(getLearningCurveFile(targ, "cll"));
				if (f.exists()) { f.delete();}
			}
		}
		for(; startCount <= cmdArgs.getMaxTreesVal();startCount+=increment) {
			sampler.setMaxTrees(startCount);
			Utils.println("% Trees = " + startCount);
			sampler.getMarginalProbabilities(jointExamples);
			HashMap<String, List<RegressionRDNExample>> backupJointExamples = null;
			if (startCount != cmdArgs.getMaxTreesVal()) {
				backupJointExamples = new HashMap<String, List<RegressionRDNExample>>();
				for (String targ : jointExamples.keySet()) {
					backupJointExamples.put(targ, new ArrayList<RegressionRDNExample>(jointExamples.get(targ)));
				}
			}
			
			// Remove hidden examples from the reporting if we do not know their true values
			// Normally, the missing data is artificially generated so we know the true value.
			if (!cmdArgs.isReportHiddenEx()) {
				removeHiddenExamples(jointExamples, setup.getHiddenExamples());
			}
			
			// Subsample the negatives for reporting.
			if (!negativesSampled && !cmdArgs.isPrintAllExamplesToo()) {
				Utils.println("\n% Subsampling the negative examples for reporting.");
				subsampleNegatives(jointExamples);
				negativesSampled=true;
			}

		
			// clear the query file.
			if (writeQueryAndResults) {
				for (String target : jointExamples.keySet()) {
					File f = new File(getQueryFile(target));
					if (f.exists()) {
						f.delete();
					}
					if (cmdArgs.isPrintAllExamplesToo()) {
						f = new File(getFullQueryFile(target));
						if (f.exists()) {
							f.delete();
						}
					}
				}
			}
			String modelSuff = cmdArgs.getModelFileVal();
			boolean allExamples = false;
			if (cmdArgs.isPrintAllExamplesToo()) {
				cmdArgs.setModelFileVal(modelSuff + "_full");
				allExamples = true;
			}
			processExamples(jointExamples, thresh, startCount, allExamples);
			if (cmdArgs.isPrintAllExamplesToo()) {
				if (!negativesSampled) {
					subsampleNegatives(jointExamples);
					cmdArgs.setModelFileVal(modelSuff);
					allExamples = false;
					processExamples(jointExamples, thresh, startCount, allExamples);
				} else {
					Utils.error("Negatives sampled already!!");
				}
			}
			jointExamples = backupJointExamples;
		}
	}
	
	private void removeHiddenExamples(
			Map<String, List<RegressionRDNExample>> jointExamples,
			Map<String, List<RegressionRDNExample>> hiddenExamples) {
		int numRemoved = 0;
		for (String predName : jointExamples.keySet()) {
			if (!hiddenExamples.containsKey(predName)) {
				continue;
			}
			List<RegressionRDNExample> examples = jointExamples.get(predName);
			List<RegressionRDNExample> hidExamples = hiddenExamples.get(predName);
			
			
			for (int i = examples.size()-1; i >= 0;  i--) {
				RegressionRDNExample origEx = examples.get(i);
				if (setup.getMulticlassHandler().isMultiClassPredicate(origEx.predicateName.name)) {
					origEx = setup.getMulticlassHandler().morphExample(origEx);
				}
				for (RegressionRDNExample hidRex : hidExamples) {
					if (hidRex.toString().equals(origEx.toString())) {
						examples.remove(i);
						i++;
						numRemoved++;
						break;
					}
				}
			
			}
		}
		Utils.println("Removed " + numRemoved + " examples before reporting.");	
	}

	private void processExamples(
			Map<String, List<RegressionRDNExample>> jointExamples,
			double thresh, int startCount, boolean usingAllEgs) {
		for (String pred : jointExamples.keySet()) {
			// clear the results file for each predicate
			if (writeQueryAndResults) {
				File f = new File(getResultsFile(pred));
				if (f.exists()) {
					f.delete();
				}
				if (cmdArgs.isPrintAllExamplesToo()) {
					f = new File(getFullResultsFile(pred));
					if (f.exists()) {
						f.delete();
					}
				}
			}
			double f1 = getF1ForEgs(jointExamples.get(pred), thresh, pred, startCount, usingAllEgs);
		}
	}

	private void subsampleNegatives(Map<String, List<RegressionRDNExample>> jointExamples) {
		if (cmdArgs.getTestNegsToPosRatioVal() < 0) {
			return; // No subsampling.
		}
		Map<String,Integer> numpos = new HashMap<String,Integer>();
		Map<String,Integer> numneg = new HashMap<String,Integer>();
		for (String  pred : jointExamples.keySet()) {
			numpos.put(pred, 0);
			numneg.put(pred, 0);
			for (RegressionRDNExample rex : jointExamples.get(pred)) {
				if (rex.isOriginalTruthValue()) {
					numpos.put(pred, numpos.get(pred) + 1);  // JWS: should count then do one PUT at the end.
				} else {
					numneg.put(pred, numneg.get(pred) + 1);
				}
			}
		}		
		
		// Subsample negative examples.
		for (String target : jointExamples.keySet()) {
			int pos = numpos.get(target);
			int neg = numneg.get(target);
			Utils.println("% Initial size of testset negs: " + Utils.comma(neg) + " for " + target);
			double sampleNeg = cmdArgs.getTestNegsToPosRatioVal();
			// get the sampling prob
			double sampleProb = sampleNeg * ((double)pos / (double)neg);

			// Don't sample if sampleProb is negative.
			if (sampleProb > 0) {

				// Rather than randomly sampling, we sample deterministically so that all runs get the same testset examples
				// Since the seed is fixed,the random number generator would return the same values.
				Random rand = new Random(1729);

				// Reverse order so that we can delete it.
				neg=0;
				for (int i = jointExamples.get(target).size()-1; i>=0 ; i--) {
					RegressionRDNExample rex = (RegressionRDNExample)(jointExamples.get(target).get(i));
					if (!rex.isOriginalTruthValue()) {
						// Remove this example, as we are subsampling.
						if (rand.nextDouble() >= sampleProb) {
							jointExamples.get(target).remove(i);
						} else {
							neg++;
						}
					}
				}
				Utils.println("% Final size of negs: " + Utils.comma(neg) + " for " + target);
			}
		}
	}

	private void setParamsUsingSetup(WILLSetup willSetup) {
		String lookup;
		if ((lookup =  willSetup.getInnerLooper().getStringHandler().getParameterSetting("useAccuracy")) != null) {
			useAccuracyMeasure = Boolean.parseBoolean(lookup);
		}
		if ((lookup =  willSetup.getInnerLooper().getStringHandler().getParameterSetting("normProb")) != null) {
			normalizeProbs = Boolean.parseBoolean(lookup);
		}
		if ((lookup =  willSetup.getInnerLooper().getStringHandler().getParameterSetting("printEg")) != null) {
			printExamples = Boolean.parseBoolean(lookup);
		}
		if ((lookup =  willSetup.getInnerLooper().getStringHandler().getParameterSetting("minRecallForAUCPR")) != null) {
			minRecallForAUCPR = Double.parseDouble(lookup);
		}
		if ((lookup =  willSetup.getInnerLooper().getStringHandler().getParameterSetting("minLCTrees")) != null) {
			minLCTrees = Double.parseDouble(lookup);
		}
		if ((lookup =  willSetup.getInnerLooper().getStringHandler().getParameterSetting("incrLCTrees")) != null) {
			incrLCTrees = Double.parseDouble(lookup);
		}
	}
	
	private void reportResultsToCollectorFile(BufferedWriter collectorBW, String modelName, String category, ProbDistribution prob, double wgt, RegressionRDNExample example) throws IOException {
		if (category == null) { collectorBW.append("// Results of '" + (modelName == null ? "unnamedModel" : modelName) + "'.\n\nuseLeadingQuestionMarkVariables: true.\n\n");  return; }
	//	double logWt = Utils.getLogWeightForProb(prob);
		collectorBW.append("modelPrediction(model(" + modelName + "), category(" + category + "), prob(" + prob + "), wgt(" + wgt + "), " + example + ").\n"
								// This line no longer needed (see 10/1/10 email to Feng from JWS):	+ getMLNclauseForProbabilisticEvidence(example, logWt) + "\n"
							+ "\n"); // No need to lock since locked in outer code.
	}
	
	private String getTreeStatsFile(String target, boolean getLocalFile) {
		// Cut-pasted-and-edited from writeToCollectorFile.
		String fileNamePrefix = "testSetResults/testSetInferenceResults" + cmdArgs.getExtraMarkerForFiles(true) + BoostingUtils.getLabelForCurrentModel() + BoostingUtils.getLabelForResultsFileMarker();
		String fileName       = Utils.replaceWildCards(cmdArgs.getResultsDirVal() + fileNamePrefix + "_RDNtreePathStats" + Utils.defaultFileExtensionWithPeriod);
		Utils.ensureDirExists(fileName);
		Utils.println("\n% getTreeStatsFile:\n%    " + fileName);
		return fileName;
	}
	
	private String getQueryFile() {
		return setup.getOuterLooper().getWorkingDirectory() + "/query.db";
	}
	private String getQueryFile(String target) {
		if (useOldFileLocations) {
			return setup.getOuterLooper().getWorkingDirectory() + "/query_" + target + ".db";
		}
		return getQueryFile(target, false);
	}
	private String getFullQueryFile(String target) {
		if (useOldFileLocations) {
			return setup.getOuterLooper().getWorkingDirectory() + "/query_full_" + target + ".db";
		}
		return getQueryFile(target, false);
	}
	
	private String getQueryFile(String target, boolean getLocalFile) {
		String modelDir = cmdArgs.getResultsDirVal(); // Try to put in the place other results go.
		String result   = Utils.replaceWildCards((getLocalFile ? "MYSCRATCHDIR"
                 											   : (modelDir != null ? modelDir : setup.getOuterLooper().getWorkingDirectory()))
                 								 + "bRDNs/" + (target == null || target.isEmpty() ? "" : target + "_") 
                 								 + "query" + cmdArgs.getExtraMarkerForFiles(true) + BoostingUtils.getLabelForCurrentModel() + ".db");
		Utils.ensureDirExists(result);
		return result;
	}
	
	private String getResultsFile(String target) {
		if (useOldFileLocations) {
			String suff ="";
			if (cmdArgs.getModelFileVal() != null) {
				suff = cmdArgs.getModelFileVal() + "_";
			}
			return setup.getOuterLooper().getWorkingDirectory() + "/results_" + suff + target + ".db";
		}
		return getResultsFile(target, false);
	}
	
	private String getFullResultsFile(String target) {
		if (useOldFileLocations) {
			String suff ="";
			if (cmdArgs.getModelFileVal() != null) {
				suff = cmdArgs.getModelFileVal() + "_";
			}
			return setup.getOuterLooper().getWorkingDirectory() + "/results_full_" + suff + target + ".db";
		}
		return getResultsFile(target, false);
	}
	
	private String getResultsFile(String target, boolean getLocalFile) {
		String modelDir = cmdArgs.getResultsDirVal();
		String result =  Utils.replaceWildCards((getLocalFile ? "MYSCRATCHDIR"
														      : (modelDir != null ? modelDir : setup.getOuterLooper().getWorkingDirectory()))
												+ "bRDNs/" + (target == null || target.isEmpty() ? "" : target + "_") 
												+ "results" + cmdArgs.getExtraMarkerForFiles(true) 
												+ BoostingUtils.getLabelForCurrentModel() + BoostingUtils.getLabelForResultsFileMarker()
												+ (cmdArgs.getModelFileVal() == null ? "" : "_" + cmdArgs.getModelFileVal()) + ".db");
		Utils.ensureDirExists(result);
		return result;
	}
	private String getTestsetInfoFile(String target) {
		String modelDir = cmdArgs.getResultsDirVal();
		String result   = Utils.replaceWildCards((modelDir != null ? modelDir : setup.getOuterLooper().getWorkingDirectory())
												+ "bRDNs/" + (target == null || target.isEmpty() ? "" : target + "_") 
												+ "testsetStats" + cmdArgs.getExtraMarkerForFiles(true) 
												+ BoostingUtils.getLabelForCurrentModel() + BoostingUtils.getLabelForResultsFileMarker()
												+ (cmdArgs.getModelFileVal() == null ? "" : "_" + cmdArgs.getModelFileVal()) + ".txt");
		Utils.ensureDirExists(result);
		return result;
	}
	

	private String getLearningCurveFile(String target, String type) {
		return setup.getOuterLooper().getWorkingDirectory() + "/curve" +
				(cmdArgs.getModelFileVal() == null ? "" : "_" + cmdArgs.getModelFileVal()) +
				(target.isEmpty() ? "" : "_"+target) + "." + type;
	}
	public double getF1ForEgs(List<RegressionRDNExample> examples, double threshold,
							  String target, int trees, boolean usingAllEgs) {			
		// We repeatedly loop over the examples, but the code at least is cleaner.
		// Update the probabilities here if needed, such as normalizing.
		
		// Update true positive, false positives etc.
		CoverageScore  score = new CoverageScore();
		String resultsString = "useLeadingQuestionMarkVariables: true.\n\n" + updateScore(examples, score, threshold);
		if (trees == cmdArgs.getMaxTreesVal()) {

			// Print examples and some 'context' for possible use by other MLN software.
			if (printExamplesForTuffy || writeQueryAndResults) {
				printExamples(examples, target, usingAllEgs);
			}

			// Write to "collector file"
			if (!useOldFileLocations) {
				writeToCollectorFile(examples);
			}
		}

		
		ComputeAUC auc = computeAUCFromEg(examples, target);
		
		
		if (cmdArgs.isPrintingTreeStats()) {
			printTreeStats(examples, target);
		}
		if (cmdArgs.isPrintLearningCurve()) {			
			Utils.appendString(new File(getLearningCurveFile(target, "pr")), trees + " " + auc.getPR() + "\n");
			Utils.appendString(new File(getLearningCurveFile(target, "cll")), trees + " " + auc.getCLL() + "\n");
		}
		{
			ThresholdSelector selector = new ThresholdSelector();
			for (RegressionRDNExample regEx : examples) {
				// This code should only be called for single-class examples
				selector.addProbResult(regEx.getProbOfExample().getProbOfBeingTrue(), regEx.isOriginalTruthValue());
			}
			double thresh = selector.selectBestThreshold();
			Utils.println("% F1 = " + selector.lastComputedF1);
			Utils.println("% Threshold = " + thresh);
		}
		Utils.println(   "\n%   AUC ROC   = " + Utils.truncate(auc.getROC(), 6));
		Utils.println(     "%   AUC PR    = " + Utils.truncate(auc.getPR(),  6));
		Utils.println(     "%   CLL	      = " + Utils.truncate(auc.getCLL(),  6));
		resultsString += "\n//  AUC ROC   = " + Utils.truncate(auc.getROC(), 6);
		resultsString += "\n//  AUC PR    = " + Utils.truncate(auc.getPR(),  6);
		resultsString += "\n//  CLL       = " + Utils.truncate(auc.getCLL(),  6);
		resultsString += "\naucROC(" +  target + ", " + Utils.truncate(auc.getROC(), 6) + ").";
		resultsString += "\naucPR( " +  target + ", " + Utils.truncate(auc.getPR(),  6) + ").\n";
		String fileNameForResults = (writeQueryAndResults ? getTestsetInfoFile(target) : null);
	//	Utils.waitHere("writeQueryAndResults = " + writeQueryAndResults + "\n" + fileNameForResults);
	
		if (threshold != -1) {
			Utils.println("%   Precision = " + Utils.truncate(score.getPrecision(), 6)       + (threshold != -1 ? " at threshold = " + Utils.truncate(threshold, 3) : " "));
			Utils.println("%   Recall    = " + Utils.truncate(score.getRecall(),    6));
			Utils.println("%   F1        = " + Utils.truncate(score.getF1(),        6));
			resultsString += "\n//   Precision = " + Utils.truncate(score.getPrecision(), 6) + (threshold != -1 ? " at threshold = " + Utils.truncate(threshold, 3) : " ");
			resultsString += "\n//   Recall    = " + Utils.truncate(score.getRecall(),    6);
			resultsString += "\n//   F1        = " + Utils.truncate(score.getF1(),        6);
			resultsString += "\nprecision(" + target + ", " + Utils.truncate(score.getPrecision(), 6) + ", usingThreshold(" + threshold + ")).";
			resultsString += "\nrecall(   " + target + ", " + Utils.truncate(score.getRecall(),    6) + ", usingThreshold(" + threshold + ")).";
			resultsString += "\nF1(       " + target + ", " + Utils.truncate(score.getF1(),        6) + ", usingThreshold(" + threshold + ")).";
			if (writeQueryAndResults) { Utils.writeStringToFile(resultsString + "\n", new CondorFile(fileNameForResults)); }
			return score.getF1();
		}
		
		if (writeQueryAndResults) { Utils.writeStringToFile(resultsString + "\n", new CondorFile(fileNameForResults)); }
		return -1;
		
	}
	


	private ComputeAUC computeAUCFromEg(List<RegressionRDNExample> examples, String target) {
		Utils.println("\n% Computing Area Under Curves.");
		List<Double> positiveProbs = new ArrayList<Double>(); // TODO - need to handle WEIGHTED EXAMPLES.  Simple approach: have a eachNegRepresentsThisManyActualNegs and make this many copies.
		List<Double> negativeProbs = new ArrayList<Double>();
		for (RegressionRDNExample regressionRDNExample : examples) {
			// This code should only be called for single-class examples
			double  prob  = regressionRDNExample.getProbOfExample().getProbOfBeingTrue();
			boolean isPos = regressionRDNExample.isOriginalTruthValue();
			if (isPos) {
				positiveProbs.add(prob);
			} else {
				negativeProbs.add(prob);
			}
		}
		String extraMarker      = cmdArgs.getExtraMarkerForFiles(true) + BoostingUtils.getLabelForCurrentModel() + BoostingUtils.getLabelForResultsFileMarker();		
		// If models are being written somewhere, then also write AUC's there (this allows us to avoid writing in a dir that only contains INPUT files) - hence, multiple runs can simultaneously use the same input dir, yet write to different output dirs.
		String aucTempDirectory = null;
		if (useOldFileLocations) {
			aucTempDirectory = setup.getOuterLooper().getWorkingDirectory() + "/AUC/" + (cmdArgs.getModelFileVal() == null ? "" : cmdArgs.getModelFileVal() +"/");
			if (cmdArgs.getTargetPredVal().size() > 1) {
				aucTempDirectory += target + "/";
			}
			extraMarker = "";
			ComputeAUC.deleteAUCfilesAfterParsing = false;
		} else {
			Utils.replaceWildCards(Utils.isRunningWindows() ? "MYSCRATCHDIR" + "calcAUC/" + target + "/" :  cmdArgs.getDirForAUCfiles(target, setup));
		}
		// Utils.waitHere(aucTempDirectory);
		ComputeAUC          auc = new ComputeAUC(positiveProbs, negativeProbs, aucTempDirectory, cmdArgs.getAucPathVal(), extraMarker, minRecallForAUCPR, cmdArgs.useLockFiles);
		return auc;
	}
	
	private String ensureThisIsaSubdir(String modelDirRaw) {
		String modelDir = Utils.replaceWildCards(modelDirRaw);
		if (modelDir == null)      { return null;     }
		if (modelDir.length() < 2) { return modelDir; }
		if (modelDir.contains(":")) {
			modelDir = modelDir.substring(modelDir.indexOf(':') + 1);
		}
		while (modelDir.length() > 0 && modelDir.charAt(0) == File.separatorChar) {
			modelDir = modelDir.substring(1); // Remove any leading (back) slashes
		}
		return modelDir;
	}

	private void writeToCollectorFile(List<RegressionRDNExample> examples) {
	//	Utils.waitHere("modelDir = " + cmdArgs.getModelDirVal() + "\n as a subdir: " + ensureThisIsaSubdir(cmdArgs.getModelDirVal()));
		String fileNamePrefix = "testSetResults/testSetInferenceResults" + cmdArgs.getExtraMarkerForFiles(true) + BoostingUtils.getLabelForCurrentModel() + BoostingUtils.getLabelForResultsFileMarker();
		String localPrefix    = "MYSCRATCHDIR" + "bRDNs/" + ensureThisIsaSubdir(cmdArgs.getResultsDirVal());
		String fileName       = Utils.replaceWildCards(localPrefix + fileNamePrefix + "_unsorted" + Utils.defaultFileExtensionWithPeriod);
		String fileNameSorted = Utils.replaceWildCards(localPrefix + fileNamePrefix +   "_sorted" + Utils.defaultFileExtensionWithPeriod);
		// Also see getTreeStatsFile
		
		int posCounter = 0;
		int negCounter = 0;
		try {
			File           collectorFile = Utils.ensureDirExists(fileName);
			BufferedWriter collectBuffer = new BufferedWriter(new CondorFileWriter(collectorFile)); // Clear the file if it already exists.
			
			Utils.println("\nwriteToCollectorFile: Writing out predictions on " + Utils.comma(examples) + " examples for '" + cmdArgs.getTargetPredVal() + BoostingUtils.getLabelForCurrentModel() + BoostingUtils.getLabelForResultsFileMarker()  + "'\n  " + fileName);
			if (collectorFile != null) { reportResultsToCollectorFile(collectBuffer, RunBoostedRDN.nameOfCurrentModel, null, null, 0.0, null); }
			for (RegressionRDNExample pex : examples) {
				ProbDistribution prob    = pex.getProbOfExample();
				double wgtOnEx = pex.getWeightOnExample();
			
				if (pex.isOriginalTruthValue()) { posCounter++; } else { negCounter++; }
				if (collectorFile != null) { reportResultsToCollectorFile(collectBuffer, RunBoostedRDN.nameOfCurrentModel, pex.isOriginalTruthValue() ? "pos" : "neg", prob, wgtOnEx, pex); }
			}
			if (collectBuffer != null) { collectBuffer.close(); }
			if (collectorFile != null) { sortLinesInPredictedProbsFile(RunBoostedRDN.nameOfCurrentModel, fileName, fileNameSorted); }
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Something went wrong:\n   " + e);
		}
		
		Utils.moveAndGzip(fileName,       cmdArgs.getResultsDirVal() + fileNamePrefix + "_unsorted" + Utils.defaultFileExtensionWithPeriod, true);
		Utils.moveAndGzip(fileNameSorted, cmdArgs.getResultsDirVal() + fileNamePrefix +   "_sorted" + Utils.defaultFileExtensionWithPeriod, true);
		Utils.println("writeToCollectorFile:  " + fileName + "\n   |pos| = " + Utils.comma(posCounter) + "\n   |neg| = " + Utils.comma(negCounter));
	}
	
	private void sortLinesInPredictedProbsFile(String modelName, String fileToRead, String fileToWrite) {
		Utils.ensureDirExists(fileToWrite);
		List<Literal> lits = setup.getInnerLooper().getParser().readLiteralsInFile(fileToRead, false, false);
		CompareProbsInModelPredictions comparator = new CompareProbsInModelPredictions();
		Collections.sort(lits, comparator);
		Utils.writeObjectsToFile(fileToWrite, lits, ". // #COUNT", "// Results of '" + modelName + "' sorted by the predicted probability.\n\nuseLeadingQuestionMarkVariables: true.\n\n");
	}
	
	/**
	 * HashMap comparator. Needs the hash map as input since the comparator
	 * only gets the key as the input for the comparison. ValueComparator
	 * uses the input map to find the actual values for each key and sorts
	 * based on them.
	 * @author tkhot
	 *
	 */
	public static class ValueComparator implements Comparator<String> {

		Map<String, Double> base;
		public ValueComparator(Map<String, Double> input) {
			base = input;
		}
		@Override
		public int compare(String arg0, String arg1) {
			if(base.get(arg0) > base.get(arg1)) {
				return 1;
			}
			if (base.get(arg0) < base.get(arg1)) {
				return -1;
			}
			return arg0.compareTo(arg1);
			
		}
		
	}
	
	/**
	 * Should be called only for single-class examples
	 * @param examples
	 * @param target
	 */
	private void printTreeStats(List<RegressionRDNExample> examples, String target) {
		String treeStats = getTreeStatsFile(target, Utils.isRunningWindows());
		Map<String, Integer> idCounts = new HashMap<String, Integer>();
		Map<String, Double> idProbs = new HashMap<String, Double>();
		long totalExamples = 0;
		for (RegressionRDNExample regressionRDNExample : examples) {
			String id = regressionRDNExample.leafId;
			if(id.isEmpty()) {
				Utils.waitHere("No path id associated with example:" + regressionRDNExample);
			}
			if (!idCounts.containsKey(id)) {
				idCounts.put(id, 0);
				idProbs.put(id, regressionRDNExample.getProbOfExample().getProbOfBeingTrue());
			} else {
				if (idProbs.get(id) != regressionRDNExample.getProbOfExample().getProbOfBeingTrue()) {
					Utils.waitHere("Example should have probability:" + idProbs.get(id) +
							" but has prob:" + regressionRDNExample.getProbOfExample() + " for id:" + id);
				}
			}
			idCounts.put(id, idCounts.get(id)+1);
			totalExamples++;
		}
		try {
			Utils.println("Printing tree stats to " + treeStats);
			GzippedBufferedWriter bw = new GzippedBufferedWriter(treeStats);
			
			// Sort by probabilities(lowest comes first)
			Map<String, Double> sortedMap = new TreeMap<String, Double>(new ValueComparator(idProbs));
			sortedMap.putAll(idProbs);
			writeTreeStatsToCSV(idCounts, sortedMap, treeStats.replace(".txt", ".csv"));
			
			// Print counts & probs
			// Reverse probabilities as we want highest first here.
			List<String> reversedIds = new ArrayList<String>(sortedMap.keySet());
			Collections.reverse(reversedIds);
			
			for (String id : reversedIds) {
				double frac = (double)idCounts.get(id) / (double)totalExamples;
				bw.write(String.format("%s(\"%s\", %.4f, %d, %.4f).", RDNTreeStats, id, sortedMap.get(id), idCounts.get(id), frac));
				bw.newLine();
			}
			// Print leaf id as list
			for (String id : sortedMap.keySet()) {
				bw.write(String.format("TreeIdList(%s, [%s]).", id , getLeafIdToList(id)));
				bw.newLine();
			}
			
			// Print clauses for each leaf.
			for (int i = 0; i < model.get(target).getNumTrees(); i++) {
				ClauseBasedTree reg = model.get(target).getTree(0, i);
				for (int j = 0; j < reg.getRegressionClauses().size(); j++) {
					Clause cl = reg.getRegressionClauses().get(j);
					StringBuffer bodyStr = null; 
					for (Literal lit : cl.negLiterals) {
						if (!lit.predicateName.equals(setup.getHandler().standardPredicateNames.negationByFailure) &&
							!lit.equals(setup.getHandler().cutLiteral)) {
							if (bodyStr == null) {
								bodyStr = new StringBuffer();
							} else {
								bodyStr.append(",");
							}
							bodyStr.append(lit.toString());
						}
					}
					if (bodyStr == null) { bodyStr = new StringBuffer(); }
					String clStr = StringConstant.makeSureNameIsSafe(bodyStr.toString());
					bw.write(String.format("LeafToClause([%d,%d],\"%s\").", i+1, j+1, clStr));
					bw.newLine();
				}
			}
			
			bw.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}
	
	public static void writeTreeStatsToCSV(Map<String, Integer> idCounts , Map<String, Double> sortedMap, String csvFile) throws IOException {
		BufferedWriter treeCSV = new BufferedWriter(new CondorFileWriter(csvFile));
		treeCSV.write("Max Prob. of eg dropped,Cumulative Fraction of eg dropped, Fraction of eg, Count of eg");
		treeCSV.newLine();
		long totalExamples = 0;
		for (String id : idCounts.keySet()) {
			totalExamples += idCounts.get(id);
		}
		double totalFrac = 0;
		
		for (String id : sortedMap.keySet()) {
			double frac = (double)idCounts.get(id) / (double)totalExamples;
			totalFrac += frac;
			treeCSV.write(String.format("%.4f,%.4f,%.4f,%d", sortedMap.get(id), totalFrac, frac, idCounts.get(id)));
			treeCSV.newLine();
		}
		treeCSV.close();
	}
	
	private String getLeafIdToList(String id) {
		String[] leafs = id.split("_");
		StringBuffer buff = new StringBuffer();
		for (int i = 0; i < leafs.length; i++) {
			if (i!=0) {
				buff.append(",");
			}
			buff.append(String.format("[%d, %s]", i+1, leafs[i]));
		}
		return buff.toString();
	}

	private void printExamples(List<RegressionRDNExample> examples, String target, boolean usingAllEgs) {
		
		boolean collectRelatedFacts = false; // Will collect the 'context' around a fact.  Turn off until we think this is needed.  It is a slow calculation.
		
		PredicateModes pmodes = new PredicateModes(setup.getInnerLooper());
		List<PredicateNameAndArity> pars = setup.getListOfPredicateAritiesForNeighboringFacts();
		// Should be set somewhere else
		List<Boolean> bit_mask = setup.getBitMaskForNeighboringFactArguments(target);		

		// List<PredicateNameAndArity> pars = BoostingUtils.convertBodyModesToPNameAndArity(setup.getInnerLooper().getBodyModes());
		// Write all examples to a query.db file
		// Results/Probs to results.db
		String         resultsFileString      = "?";
		String         queryFileString        = "?";
		String         resultsFileStringLocal = "?";
		String         queryFileStringLocal   = "?";
		BufferedWriter queryFile   = null;
		BufferedWriter resultsFile = null;
		try {
			if (usingAllEgs) {
				queryFileString        = getFullQueryFile(  target);
				resultsFileString      = getFullResultsFile(target);
			} else {
				queryFileString        = getQueryFile(  target);
				resultsFileString      = getResultsFile(target);
			}
			if (!useOldFileLocations) {
				queryFileStringLocal   = getQueryFile(  target, Utils.isRunningWindows());
				resultsFileStringLocal = getResultsFile(target, Utils.isRunningWindows());
			} else {
				queryFileStringLocal = queryFileString;
				resultsFileStringLocal = resultsFileString;
			}
		//	Utils.waitHere("resultsFileStringLocal = " + resultsFileStringLocal);
		//	Utils.waitHere("queryFileStringLocal   = " + queryFileStringLocal);
			queryFile              = new BufferedWriter(new CondorFileWriter(queryFileStringLocal, true));
			resultsFile            = new BufferedWriter(new CondorFileWriter(resultsFileStringLocal,   true));
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Problem in printExamples: " + e);
		}
		Utils.println("\nprintExamples: Writing out predictions (for Tuffy?) on " + Utils.comma(examples) + " examples for '" + target 
						+ "' to:\n  " + resultsFileString+ "\n and to:\n  " + queryFileString);
		
		// Write the examples to query/results files.
		for (RegressionRDNExample pex : examples) {
			// Should be called only for single class
			double prob = pex.getProbOfExample().getProbOfBeingTrue();
			String prefix = "";
			double printProb = prob;
			if (!pex.isOriginalTruthValue()) {
				prefix = "!";
				printProb = 1-prob;
			}
			try {
				queryFile.write(prefix + pex.toString() + "\n");
				if (writeResultsAsRules) {
					double logWt = Utils.getLogWeightForProb(prob);
					resultsFile.write(getMLNclauseForProbabilisticEvidence(pex, logWt) + "\n");
				} else {
					resultsFile.write(prefix + pex.toString()+ " " + printProb + "\n"); // + " //" + pex.provenance + "\n");
					//"//" + pex.provenance);
				}
				
				if (collectRelatedFacts) {
					// Print related facts for this example.
					Set<Literal> facts = new HashSet<Literal>();				
					int i=0;
					for (Term arg : pex.getArguments()) {
						if (bit_mask.get(i)) { 
							facts.addAll(BoostingUtils.getRelatedFacts(arg, pars, setup.getInnerLooper()));
						}
						i++;
					}
					resultsFile.write("/*\n");
					for (Literal fact : facts) {
						resultsFile.write(fact +".\n");
					}
					resultsFile.write("*/\n");
				}
			} catch (IOException e) {
				Utils.reportStackTrace(e);
				Utils.error("Something went wrong: " + e);
			}
		}

		try {
			queryFile.close();
			resultsFile.close();
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Something went wrong: " + e);
		}
		
		if (!resultsFileString.equals(queryFileStringLocal)) {
			Utils.moveAndGzip(queryFileStringLocal,   queryFileString,   true);
		}
		
		if (!resultsFileString.equals(resultsFileStringLocal)) {
			Utils.moveAndGzip(resultsFileStringLocal, resultsFileString, true);
		}

	}

	private boolean writeAllResultsToCSVfile = true;

	private String getNameOfCSVfile() {
		String modelDir = cmdArgs.getResultsDirVal(); // Try to put in the place other results go.
		String result   = Utils.replaceWildCards((modelDir != null ? modelDir : setup.getOuterLooper().getWorkingDirectory())
                 								 + "bRDNs/" // + (target == null || target.isEmpty() ? "" : target + "_") 
                 								 + "predictions" + cmdArgs.getExtraMarkerForFiles(true) + BoostingUtils.getLabelForCurrentModel() + ".csv");
		Utils.ensureDirExists(result);
		return result;
	}
	
	/**
	 * Should be called with only single-value examples
	 * @param examples
	 * @param score
	 * @param threshold
	 * @return
	 */
	public String updateScore(List<RegressionRDNExample> examples, CoverageScore score, double threshold) {
		double sum   = 0;
		double count = 0, countOfPos = 0, countOfNeg = 0;
		double llSum = 0;
		int numbToPrint = Utils.getSizeSafely(examples);
		double maxToPrintOnAve = 250.0;
		if (printExamples && numbToPrint > maxToPrintOnAve) { 
			Utils.println("% Note: since more than " + Utils.truncate(maxToPrintOnAve, 0) + " examples, will randomly report.");
		}
		StringBuilder sb = (writeAllResultsToCSVfile ? new StringBuilder() : null);
		for (RegressionRDNExample regressionEx : examples) {
			double prob = regressionEx.getProbOfExample().getProbOfBeingTrue();
			double wtOnEx = regressionEx.getWeightOnExample();
			count += wtOnEx;
			// Positive Example ??
			if (regressionEx.isOriginalTruthValue()) {
				//if (printExamples && Utils.random() < maxToPrintOnAve / numbToPrint) {
				if (printExamples && Utils.random() < maxToPrintOnAve / numbToPrint) { 
					Utils.println("% Pos #" + Utils.truncate(score.getTruePositives() + score.getFalseNegatives(), 0) + ": '" + regressionEx + "' prob = " + Utils.truncate(prob, 6));
//					Utils.println(regressionEx.provenance);
				} // Wasteful to call random() if not needed,but not a big deal.
				
				if (writeAllResultsToCSVfile) { sb.append("pos, " + prob + ", " + regressionEx + "\n"); } // The comma's in examples will become columns (the first and last will be 'corrupted' with the predicate name and parens), but that might be of use.
				
				sum   += prob * wtOnEx; // Compute a WEIGHTED sum.
				countOfPos += wtOnEx;
			/*	double egProb=prob;
				if (prob == 0) {
					egProb = 1e-15;
				}
				llSum += Math.log(egProb) * wtOnEx;*/
				
				if (prob > threshold) {
					score.addToTruePositive(wtOnEx);
				} else {
					score.addToFalseNegative(wtOnEx);
				}
				
			} else {
				//if (printExamples && Utils.random() < maxToPrintOnAve / numbToPrint) {
				if (printExamples && Utils.random() < maxToPrintOnAve / numbToPrint) {
					Utils.println("% Neg #" + Utils.truncate(score.getTrueNegatives() + score.getFalsePositives(), 0)+ ": '" + regressionEx + "' prob = " + Utils.truncate(prob, 6) );
					//Utils.println(regressionEx.provenance);
				}
				
				if (writeAllResultsToCSVfile) { sb.append("neg, " + prob + ", " + regressionEx + "\n"); }
				
				sum   += (1 - prob) * wtOnEx; // Compute a WEIGHTED sum.
				/*double egProb=1-prob;
				if (egProb == 0) {
					egProb = 1e-15;
				}
				llSum += Math.log(egProb) * wtOnEx;*/
				
				countOfNeg += wtOnEx;
				if (prob > threshold) {
					score.addToFalsePositive(wtOnEx);
				} else {
					score.addToTrueNegative(wtOnEx);
				}
			}
		}
		
		if (writeAllResultsToCSVfile) { Utils.writeStringToFile(sb.toString(), new CondorFile(getNameOfCSVfile())); }
		
		// TODO JWS - should use GEOMETRIC Mean if this is over a TRAIN SET.  (For a TEST [or TUNE] it is fine to do an expected value.)
		String testsetReport1 = " (Arithmetic) Mean Probability Assigned to Correct Output Class: " + Utils.truncate(sum, 3) + "/" + Utils.truncate(count, 2) + " = " + Utils.truncate(sum / count, 6) + "\n";
		
		Utils.println(testsetReport1);
		String testsetReport2 = " The weighted count of positive examples = " + Utils.truncate(countOfPos, 3) + " and the weighted count of negative examples = " + Utils.truncate(countOfNeg, 3);
		Utils.println(testsetReport2);
		//Utils.println("\n% CLL: " + Utils.truncate(llSum, 2) + "/" + Utils.truncate(count, 2) + " = " + Utils.truncate(llSum / count, 6));

		return "//" + testsetReport1 +   "testsetLikelihood(sum(" + Utils.truncate(sum, 3) + "), countOfExamples(" + Utils.truncate(count, 2) + "), mean(" + Utils.truncate(sum / count, 6) + ")).\n\n"
			+  "//" + testsetReport2 + "\nweightedSumPos(" + Utils.truncate(countOfPos, 3) + ").\nweightedSumNeg(" + Utils.truncate(countOfNeg, 3) + ").\n";

	}
	
	private String getMLNclauseForProbabilisticEvidence(RegressionRDNExample pex, double logWgt) {
		if (logWgt < 0) { // Keep wgts positive.
			return "predicted_" + pex.toString() + ".\n" + -logWgt + " predicted_" + pex.toString() + " => not " + pex.toString() + ".";
		}
		return     "predicted_" + pex.toString() + ".\n" +  logWgt + " predicted_" + pex.toString() + " => "     + pex.toString() + ".";
	}
}

class CompareProbsInModelPredictions implements java.util.Comparator<Literal> {
	
	public int compare(Literal lit1, Literal lit2) {
		if (lit1 == lit2) { return 0; }		   
		Term arg2_lit1      = lit1.getArgument(2);	
		Term arg2_lit2      = lit2.getArgument(2);
		Term arg0_arg2_lit1 = ((Function) arg2_lit1).getArgument(0);
		Term arg0_arg2_lit2 = ((Function) arg2_lit2).getArgument(0);
		NumericConstant   nc1 = (NumericConstant) arg0_arg2_lit1;
		NumericConstant   nc2 = (NumericConstant) arg0_arg2_lit2;
		double           dbl1 = nc1.value.doubleValue();
		double           dbl2 = nc2.value.doubleValue();
			   
		if (dbl1 < dbl2) { // We want HIGHER numbers at the front of the sorted list.
			return 1;
		}
		if (dbl1 > dbl2) {
		   return -1;
		}
		return 0;
	}
}
