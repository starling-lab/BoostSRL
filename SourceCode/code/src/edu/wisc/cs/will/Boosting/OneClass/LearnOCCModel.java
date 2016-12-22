/**
 * 
 */
package edu.wisc.cs.will.Boosting.OneClass;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;
import edu.wisc.cs.will.Boosting.RDN.ConditionalModelPerPredicate;
import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.RDN.RunBoostedRDN;
import edu.wisc.cs.will.Boosting.RDN.SingleModelSampler;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.Boosting.RDN.Models.PhiFunctionForRDN;
import edu.wisc.cs.will.Boosting.Trees.FeatureTree;
import edu.wisc.cs.will.Boosting.Trees.LearnRegressionTree;
import edu.wisc.cs.will.Boosting.Trees.RegressionTree;
import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;
import edu.wisc.cs.will.Boosting.Utils.CommandLineArguments;
import edu.wisc.cs.will.Boosting.Utils.LineSearch;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Theory;
import edu.wisc.cs.will.FOPC.TreeStructuredTheory;
import edu.wisc.cs.will.ILP.ILPouterLoop;
import edu.wisc.cs.will.Utils.RegressionValueOrVector;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.Utils.condor.CondorFileInputStream;
import edu.wisc.cs.will.Utils.condor.CondorFileOutputStream;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

/**
 * @author tkhot
 *
 */
public class LearnOCCModel {

	private String targetPredicate;

	protected final static int debugLevel = 1; // Used to control output from this class (0 = no output, 1=some, 2=much, 3=all).

	
	private WILLSetup setup;
	
	
	private CommandLineArguments cmdArgs;
	
	private int maxTrees;
	
	// private PropositionalizationModel currModel;
	
	private PairWiseExampleScore egScores;
	
	public LearnOCCModel(CommandLineArguments cmdArgs, WILLSetup setup) {
		this.cmdArgs = cmdArgs;
		this.setup   = setup;
		
		maxTrees = cmdArgs.getMaxTreesVal();
	}

	public void setTargetPredicate(String pred) {
		targetPredicate = pred;	
	}

	public void loadCheckPointModel(
			PropositionalizationModel propositionalizationModel) {
		String saveModelName = BoostingUtils.getModelFile(cmdArgs, targetPredicate, true);
		String chkPointFile = BoostingUtils.getCheckPointFile(saveModelName);
		File willFile = getWILLsummaryFile();
		File chkFile = new File(chkPointFile);
		if (chkFile.exists() && chkFile.length() > 0) {
//		if (Utils.fileExists(chkPointFile)) {
			Utils.println("Loading checkpoint model from " + chkPointFile);
			propositionalizationModel.loadModel(chkPointFile, setup, -1);
			Utils.println("Found " + propositionalizationModel.getNumTrees() + " trees in checkpoint");
			String addString = "\n//// Loaded checkpoint from " + chkPointFile + " at " + Utils.getDateTime() + 
							  ".\n//// Number of trees loaded:" + propositionalizationModel.getNumTrees() ;
			Utils.appendString(willFile, addString);
		}
			
	}

	public void learnNextModel(RunOneClassModel runOneClassModel,
			PropositionalizationModel propModel,
			int moreTrees) {

		Utils.println("\n% Learn model for: " + targetPredicate);
		long start = System.currentTimeMillis();
		setup.prepareFactsAndExamples(targetPredicate);

		if (cmdArgs.isNoTargetModesInitially()) {
			setup.removeAllTargetsBodyModes();
		}
		
		learnModel(targetPredicate, propModel, moreTrees);
		long end = System.currentTimeMillis();

		if (propModel.getNumTrees() == maxTrees) {
			Utils.println("% Time taken to learn model for '" + targetPredicate + "': " + Utils.convertMillisecondsToTimeSpan(end - start, 3) + ".");
		}
	}

	private void learnModel(String pred,
							PropositionalizationModel propModel, int moreTrees) {
		
		String saveModelName = BoostingUtils.getModelFile(cmdArgs, pred, true);
		if(propModel.getNumTrees() == 0) {
			propModel.setTargetPredicate(pred);
			propModel.setTreePrefix(pred + (cmdArgs.getModelFileVal() == null ? "" : "_" + cmdArgs.getModelFileVal()));
		}
		

		List<RegressionRDNExample> old_eg_set = null;
		long start = System.currentTimeMillis();
		if (cmdArgs.isDisabledBoosting()) {
			maxTrees=1;
			// Increase the depth and number of clauses
			// TODO : Maybe make this settable ? Or assume caller sets it ?
			ILPouterLoop outerLoop = setup.getOuterLooper();
			outerLoop.setMaxTreeDepth(10);
			outerLoop.setMaxTreeDepthInLiterals(12);
			outerLoop.maxNumberOfClauses = 20;
			outerLoop.maxNumberOfCycles = 20;
			outerLoop.setMaxAcceptableNodeScoreToStop(0.0001);
		}

		
		// Learn maxTrees models.
		int i = 0;
		if (propModel.getNumTrees() == 0 && cmdArgs.useCheckPointing()) {
			loadCheckPointModel(propModel);
		}

		// check if rdn already has some trees from checkpoint
		i=propModel.getNumTrees();
		
		int maxTreesForThisRun = Math.min(maxTrees, (i+moreTrees));
	
		if(i >= maxTrees) {
			propModel.setNumTrees(maxTrees);
		}
		if (i == 0) {
			dumpTheoryToFiles(null, -1);  // Print something initially in case a run dies (i.e., be sure to erase any old results right away).
		}
		for (; i < maxTreesForThisRun; i++) {
	
			
	
			// Do we need this here? It is called before executeOuterLoop and in dumpTheoryToFiles.
			setup.getOuterLooper().resetAll();


				// Build data set for this model in this iteration.
				long bddstart = System.currentTimeMillis();						
				List<RegressionRDNExample> newDataSet = buildDataSet(targetPredicate, propModel);
				long bbend = System.currentTimeMillis();
				Utils.println("Time to build dataset: " + Utils.convertMillisecondsToTimeSpan(bbend-bddstart));
				FeatureTree	tree = getFeatureTree(newDataSet, i);
				
				
				
				propModel.addTree(tree);  // This code assume modelNumber=0 is learned first.
				old_eg_set = newDataSet;
		
			if (cmdArgs.useCheckPointing()) {
				createCheckPointForModel(propModel, saveModelName);
			}
			List<FeatureVector> posFeatures = new ArrayList<FeatureVector>();
			for (RegressionRDNExample rex : newDataSet) {
				if (rex.getOriginalValue() == 1) {
					FeatureVector fvec = propModel.getFeatureVector(rex);
					posFeatures.add(fvec);
				}
			}
			propModel.setOneClassExamples(posFeatures);
			if ((i + 1) % 10 == 0) { 
				propModel.saveModel(saveModelName);
			} // Every now and then save the model so we can see how it is doing.
		}

		
		
	}
	
	private List<RegressionRDNExample> buildDataSet(String pred, PropositionalizationModel currModel) {
		List<RegressionRDNExample> all_exs = new ArrayList<RegressionRDNExample>();

		getSampledPosNegEx(all_exs);
		

		BuildPairWiseScore scorer = new BuildPairWiseScore(currModel);
		egScores = scorer.buildScore(all_exs);
		
		  
		// TODO Auto-generated method stub
		return all_exs;
	}
	
	private FeatureTree getFeatureTree(List<RegressionRDNExample> newDataSet, int i) {
		TreeStructuredTheory th = null;
		Theory thry = null;
		try {
			// WILL somehow loses all the examples after every run.  TODO - JWS: Guess there is some final cleanup. 
			setup.getOuterLooper().setPosExamples(BoostingUtils.convertToListOfExamples(newDataSet));
			// Make sure the invented predicates (if any) have unique names.
			setup.getHandler().setInventedPredicateNameSuffix("_" + (i + 1));
			setup.getOuterLooper().setPrefixForExtractedRules("");
			setup.getOuterLooper().setPostfixForExtractedRules("");
			
			
			setup.getInnerLooper().occScorer = egScores;
			setup.getOuterLooper().setLearnOCCTree(true);
			
			thry = setup.getOuterLooper().executeOuterLoop();

			if (thry instanceof TreeStructuredTheory) {
				th = (TreeStructuredTheory)thry;
				dumpTheoryToFiles(th, i);
			}
		} catch (SearchInterrupted e) {
			Utils.reportStackTrace(e);
			Utils.error("Problem in getWILLTree.");
		}
		
		FeatureTree      tree    = new FeatureTree(setup);
		tree.parseTheory(thry);
		return tree;
	}
	
	
	public void getSampledPosNegEx(List<RegressionRDNExample> all_exs) {
		setup.prepareExamplesForTarget(targetPredicate);
		all_exs.addAll(BoostingUtils.castToListOfRegressionRDNExamples(setup.getOuterLooper().getPosExamples()));
		Utils.println("% Dataset size: " + Utils.comma(all_exs));
	}

	/*************
	 * LOGGING
	 **************/

	
	
	
	private File getWILLsummaryFile() {  // Always recompute in case 'targetPredicate' changes.
	//	return new CondorFile(getWILLFile(setup.getOuterLooper().getWorkingDirectory() + "/" +  cmdArgs.getModelDirVal(), cmdArgs.getModelFileVal(), targetPredicate));
		return Utils.ensureDirExists(getWILLFile(cmdArgs.getModelDirVal(), cmdArgs.getModelFileVal(), targetPredicate));
	}
	
	public static final String getWILLFile(String dir, String postfix, String predicate) {
		String filename = dir + "/WILLtheories/" + predicate + "_learnedFeatureTrees" + BoostingUtils.getLabelForCurrentModel();
		if (postfix != null) {
			filename += "_" + postfix;
		}
		filename += Utils.defaultFileExtensionWithPeriod;
		return filename;
	}
	
	private void dumpTheoryToFiles(Theory th, int i) {
		String stringToPrint = (i < 0 ? "" : "\n%%%%%  WILL-Produced Tree #" + (i + 1) + " @ " + Utils.getDateTime() + ".  [" + Utils.reportSystemInfo() + "]  %%%%%\n\n");
		if (debugLevel > 0 && i >= 0) { Utils.println(stringToPrint); }
		File file = getWILLsummaryFile();
		if (i >= 0) { Utils.appendString(file, stringToPrint + th.toPrettyString(), cmdArgs.useLockFiles); } 
		else { // Write a file right away in case a run crashes.
			
			// First save the old model file
			// Rename single model files.
			if (file.exists()) {
				RunBoostedRDN.renameAsOld(file);
			}
			
			
			stringToPrint = setup.getHandler().getStringToIndicateCurrentVariableNotation();  // Assume we don't change the variable indicator mid-run.
			stringToPrint += "\n% maxTreeDepthInNodes                 = " + Utils.comma(setup.getOuterLooper().getMaxTreeDepth())                        + "\n";
			stringToPrint +=   "% maxTreeDepthInLiterals              = " + Utils.comma(setup.getOuterLooper().getMaxTreeDepthInLiterals())              + "\n";
			stringToPrint +=   "% maxNumberOfLiteralsAtAnInteriorNode = " + Utils.comma(setup.getOuterLooper().getMaxNumberOfLiteralsAtAnInteriorNode()) + "\n";
			stringToPrint +=   "% maxFreeBridgersInBody               = " + Utils.comma(setup.getOuterLooper().innerLoopTask.maxFreeBridgersInBody)      + "\n";
			stringToPrint +=   "% maxNumberOfClauses                  = " + Utils.comma(setup.getOuterLooper().maxNumberOfClauses)                       + "\n";
			stringToPrint +=   "% maxNodesToConsider                  = " + Utils.comma(setup.getOuterLooper().innerLoopTask.getMaxNodesToConsider())    + "\n";
			stringToPrint +=   "% maxNodesToCreate                    = " + Utils.comma(setup.getOuterLooper().innerLoopTask.getMaxNodesToCreate())      + "\n";
			stringToPrint +=   "% maxAcceptableNodeScoreToStop        = " + Utils.truncate(setup.getOuterLooper().getMaxAcceptableNodeScoreToStop(), 3)  + "\n";
			stringToPrint +=   "% negPosRatio                         = " + Utils.truncate(cmdArgs.getSampleNegsToPosRatioVal(),3)                       + "\n";
			stringToPrint +=   "% testNegPosRatio                     = " + Utils.truncate(cmdArgs.getTestNegsToPosRatioVal(),  3)                       + "\n";
			stringToPrint +=   "% # of pos examples                   = " + Utils.comma(setup.getOuterLooper().getNumberOfPosExamples())                 + "\n";
			stringToPrint +=   "% # of neg examples                   = " + Utils.comma(setup.getOuterLooper().getNumberOfNegExamples())                 + "\n";
			// Utils.waitHere("dumpTheoryToFiles: \n" + stringToPrint);
			Utils.writeStringToFile(stringToPrint + "\n", file); 
		}
		if (i >= 0) {
			if (debugLevel > 0) { Utils.println(th.toPrettyString()); }
			// 	Model directory is set to the working directory as the default value.
			if (th instanceof TreeStructuredTheory) {
				String tree_dotfile = cmdArgs.getModelDirVal() + "bRDNs/dotFiles/WILLTreeFor_" + targetPredicate + i + BoostingUtils.getLabelForCurrentModel() + ".dot";
				Utils.ensureDirExists(tree_dotfile);
				((TreeStructuredTheory)th).writeDOTFile(tree_dotfile);
			}
		}
	}

	
	private void createCheckPointForModel(PropositionalizationModel model, String saveModelName) {
		String chkptFile = BoostingUtils.getCheckPointFile(saveModelName);
		model.saveModel(chkptFile);
	// No saving example for now
//		// Save the examples if not re-sampling e.g.s
//		if (!resampleExamples) {
//			String chkptEgFile = BoostingUtils.getCheckPointExamplesFile(saveModelName);
//			// Need to write examples only during first iteration
//			if (Utils.fileExists(chkptEgFile)) {
//				try {
//
//					ObjectOutputStream oos = new ObjectOutputStream(new CondorFileOutputStream(chkptEgFile));
//					for (RegressionRDNExample eg : egs) {
//						oos.writeObject(eg);
//					}
//					oos.close();
//				} 
//				catch(Exception e) {
//					Utils.reportStackTrace(e);
//					Utils.error("Problem in writing examples in createCheckPointForModel.");
//				}
//			}
//		}
		
	}
}
