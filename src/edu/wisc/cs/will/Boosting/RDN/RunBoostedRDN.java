/**
 * 
 */
package edu.wisc.cs.will.Boosting.RDN;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;
import edu.wisc.cs.will.Boosting.EM.HiddenLiteralSamples;
import edu.wisc.cs.will.Boosting.KBAdvice.Advice;
import edu.wisc.cs.will.Boosting.KBAdvice.AdviceInstance;
import edu.wisc.cs.will.Boosting.RDN.Models.RelationalDependencyNetwork;
import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;
import edu.wisc.cs.will.Boosting.Utils.CommandLineArguments;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.Utils.RegressionValueOrVector;
import edu.wisc.cs.will.Utils.Utils;

/**
 * The main class to call the boosting code.
 * @author Tushar Khot
 *
 */
public class RunBoostedRDN extends RunBoostedModels {
	JointRDNModel fullModel;
	public RunBoostedRDN() {
		fullModel = null;
	}
	
	public void runJob() {
		if (cmdArgs.isLearnVal()) {
			Utils.println("\n% Starting a LEARNING run of bRDN.");
			long start = System.currentTimeMillis();
			learnModel();
			long end = System.currentTimeMillis();
			Utils.println("\n% Total learning time ("  + Utils.comma(cmdArgs.getMaxTreesVal()) + " trees): " + Utils.convertMillisecondsToTimeSpan(end - start, 3) + ".");
		}
		if (cmdArgs.isInferVal()) {
			Utils.println("\n% Starting an INFERENCE run of bRDN.");
			long   start    = System.currentTimeMillis();
			inferModel();
			long end = System.currentTimeMillis();
			Utils.println("\n% Total inference time (" + Utils.comma(cmdArgs.getMaxTreesVal()) + " trees): " + Utils.convertMillisecondsToTimeSpan(end - start, 3) + ".");
		}
	}
	
	public static int    numbModelsToMake          =  1; // Each 'tree' in the sequence of the trees is really a forest of this size. TODO - allow this to be settable.
//	public static int    numbFullTheoriesToCombine = 10; // This is the number of separate complete predictions of TESTSET probabilities to combine.  TODO - allow this to be settable.
	public static String nameOfCurrentModel        = null; // "Run1"; // NOTE: file names will look best if this starts with a capital letter.  If set (ie, non-null), will write testset results out.
	public static String resultsFileMarker         = null; // Allow caller to put extra markers in results file names.
	
	public Map<String,Map<Example, Double>> evaluateAdvice() {
		List<String> tgts = new ArrayList<String>(cmdArgs.getTargetPredVal());
		String fileText = "";
		try {
			fileText = Utils.readFileAsString(cmdArgs.getkbpllFiles());
		} catch (IOException e) {
			// TODO Auto-generated catch block
			System.out.println("Not a valid advice file");
			e.printStackTrace();
			System.exit(1);
		}
		
		Advice advice = new Advice();
		
		String[] linesInFile = fileText.split("\n");
		for (int i = 0;i<linesInFile.length;i++) {
			Utils.println("Next line: " + linesInFile[i]);
			String singleLine = linesInFile[i];
			if(singleLine.trim().length()<1)
				continue;
			
			AdviceInstance newAdvice = new AdviceInstance();
			
			String[] targets = singleLine.split(",");
			for (String string : targets) {
				if(!tgts.contains(string.trim())) {
					Utils.printlnErr("Target " + string + " not contained in the set of possible targets");
				}
				if(!string.contains("!"))
					newAdvice.addPrefTarget(string.trim());
			}
			
			singleLine=linesInFile[++i];
			
			targets = singleLine.split(",");
			Utils.println("LINE" + targets.toString());

			for (String string : targets) {
				if(!tgts.contains(string.trim())) {
					Utils.printlnErr("Target " + string + " not contained in the set of possible targets");
				}
				if(!string.contains("!"))
					newAdvice.addNonPrefTarget(string.trim());
			}
			
			singleLine=linesInFile[++i];
			
			newAdvice.setFile(singleLine.trim());
			
			advice.addAdvice(newAdvice);
			
		}
		
		Utils.println("Finding the advice");
		for(AdviceInstance ai : advice.advice) {
			Utils.println("Pref Targets: " + ai.prefTargets);
			Utils.println("NonPrefTargets: " + ai.nonPrefTargets);
		}
		
		Map<String,Map<Example, Double>> adviceMap = new HashMap<String,Map<Example, Double>>();
		Map<String,List<Example>> exs = new HashMap<String,List<Example>>();
		for (String string : tgts) {
			adviceMap.put(string, new HashMap<Example, Double>());
			exs.put(string, new ArrayList<Example>());
		}
		
		for (Example e : setup.getOuterLooper().getPosExamples()) {
			if(e.toPrettyString().contains("!")) {
				System.out.println("negation in a pos ex");
				System.exit(1);
			}
			for(String string : tgts) {
				if(e.toPrettyString().contains(string)) {
					exs.get(string).add(e);
				}
			}
		}
		
		for (Example e : setup.getOuterLooper().getNegExamples()) {
			if(e.toPrettyString().contains("!")) {
				System.out.println("negation in a pos ex");
				System.exit(1);
			}
			for(String string : tgts) {
				if(e.toPrettyString().contains(string)) {
					exs.get(string).add(e);
				}
			}
		}
		
		for (String string : tgts) {	
			for (Example example : exs.get(string)) {
				Utils.println("Putting example " + example.toPrettyString() + " in the map under " + string);
				adviceMap.get(string).put(example, 0.0);
			}
		}
		
		
		
		for (AdviceInstance advInst : advice.advice) {
			List<String> relevantTargets = new ArrayList<String>();
			relevantTargets.addAll(advInst.prefTargets);
			relevantTargets.addAll(advInst.nonPrefTargets);
			
			String fileString = "";
			
			try {
				fileString += Utils.readFileAsString(advInst.getFile());
				
			} catch (IOException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
				System.exit(1);
			}
			
			String targetedUnsedInAdviceModel = null;
			for(String target : relevantTargets) {
				if(fileString.contains(target+"(")) {
					if(targetedUnsedInAdviceModel!=null){
						Utils.error("Cannot have clauses with different targets in the same file");
						Utils.exit("");
					}
					targetedUnsedInAdviceModel=target;
				}
			}
			if(targetedUnsedInAdviceModel==null){
				Utils.error("No target found in the file containing the advice clauses");
				Utils.exit("");
			}
			
			
			
			//Create advice file for each relevant target
			for (String target : relevantTargets) {
				String targetFileString = fileString.replaceAll(targetedUnsedInAdviceModel+"\\(", target+"\\(");
				File nextFile = new File(cmdArgs.getTrainDirVal() + "/advice."+target);
				Utils.writeStringToFile(targetFileString, nextFile);
			}
//			for (String target : relevantTargets) {
				fullModel = new JointRDNModel();
				String yapFile = cmdArgs.getYapBiasVal();
				Map<String, LearnBoostedRDN> learners = new HashMap<String, LearnBoostedRDN>();
				int minTreesInModel = Integer.MAX_VALUE;
		
				for (String pred : relevantTargets) {//cmdArgs.getTargetPredVal()) {
					fullModel.put(pred, new ConditionalModelPerPredicate(setup));
					fullModel.get(pred).setTargetPredicate(pred);
					
					LearnBoostedRDN learner = new LearnBoostedRDN(cmdArgs, setup);
					learner.setTargetPredicate(pred);
					learners.put(pred, learner);
					if (cmdArgs.useCheckPointing()) {
						learner.loadCheckPointModel(fullModel.get(pred));
					}
					minTreesInModel = Math.min(fullModel.get(pred).getNumTrees(), minTreesInModel);
				}
		
				for(String target : relevantTargets){
					String adviceFile = cmdArgs.getTrainDirVal() + "/advice." + target;//setup.getOuterLooper().getWorkingDirectory() + "/" + cmdArgs.getPriorAdvice(); //TODO Change cmdArgs
					System.out.println("Why? " + adviceFile);
					BoostingUtils.loadAdvice(setup, fullModel, adviceFile, true);
				}
				
				
				for(String target : relevantTargets) {
					for(Example ex: exs.get(target)) {
				//		RegressionRDNExample e = (RegressionRDNExample)ex;
						Utils.println(ex.toPrettyString() + "for target " + target);
						RegressionValueOrVector rval = fullModel.get(target).getPrior_advice().getRegressionValue(ex);
						System.out.println(ex + " " + fullModel.get(target).getPrior_advice().getRegressionValue(ex));
						if(rval.getSingleRegressionValue()>0) {
							for (String ptarget : advInst.prefTargets) {
								Utils.println("SMETNG " + ex.toPrettyString() + "\t\"" + ptarget +"\"");
								Utils.println(adviceMap.keySet().toString());
								Utils.println("" + adviceMap.get(ptarget).size());
			//					Utils.println("" + adviceMap.get(ptarget));
								if(!target.contains(ptarget))
									continue;
								double curValForEx = adviceMap.get(ptarget).remove(ex);
								adviceMap.get(ptarget).put(ex,curValForEx+1);
							}
							for (String ptarget : advInst.nonPrefTargets) {
								Utils.println("SMETNG " + ex.toPrettyString() + "\t" + ptarget);
								if(!target.contains(ptarget))
									continue;
								adviceMap.get(ptarget).put(ex,adviceMap.get(ptarget).remove(ex)-1);
							}
						}
					}
				}
			//}
			
//			for(Example ex: exs) {
//				for (String ptarget : advInst.prefTargets) {
//					Utils.println(ex.toPrettyString() + "\t" + adviceMap.get(ptarget).get(ex));
//				}
				
//			}
			
			for(String target : tgts) {
				String filename = cmdArgs.getTrainDirVal() + "/gradients_" + target + ".adv_grad";
				try {
					FileWriter fw = new FileWriter(filename);
					BufferedWriter bw = new BufferedWriter(fw);
					for (Example example : exs.get(target)) {
						String msg = example.toPrettyString() + "\t" + adviceMap.get(target).get(example) + "\n";
						bw.write(msg);
					}
					
					bw.close();
					fw.close();
				} catch (Exception e) {
					// TODO: handle exception
					Utils.printlnErr("Error during writing advice gradients to file");
				}
			}
			
			
		}
		
		
		return adviceMap;

	}
	
	public void learn() {
		Map<String,Map<Example, Double>> advice = null;
		if(cmdArgs.getkbpllFiles()!=null) {
			advice = evaluateAdvice();
		}
		fullModel = new JointRDNModel();
		String yapFile = cmdArgs.getYapBiasVal();
		Map<String, LearnBoostedRDN> learners = new HashMap<String, LearnBoostedRDN>();
		int minTreesInModel = Integer.MAX_VALUE;
		for (String pred : cmdArgs.getTargetPredVal()) {
			fullModel.put(pred, new ConditionalModelPerPredicate(setup));
			fullModel.get(pred).setTargetPredicate(pred);
			
			LearnBoostedRDN learner = new LearnBoostedRDN(cmdArgs, setup);
			if(cmdArgs.getkbpllFiles()!=null) {
				learner.adviceGradients = advice.get(pred);
			}
			learner.setTargetPredicate(pred);
			learners.put(pred, learner);
			if (cmdArgs.useCheckPointing()) {
				learner.loadCheckPointModel(fullModel.get(pred));
			}
			minTreesInModel = Math.min(fullModel.get(pred).getNumTrees(), minTreesInModel);
		}

		if (!cmdArgs.isDisableAdvice()) {
			String adviceFile = setup.getOuterLooper().getWorkingDirectory() + "/" + cmdArgs.getPriorAdvice();
			BoostingUtils.loadAdvice(setup, fullModel, adviceFile, true);
		}
		
		int iterStepSize = cmdArgs.getMaxTreesVal();
		if ((cmdArgs.getHiddenStrategy().equals("EM") || cmdArgs.getHiddenStrategy().equals("MAP"))
			&& setup.getHiddenExamples() != null) {
			iterStepSize = 2;
		}
		if (cmdArgs.getRdnIterationStep() != -1) {
			iterStepSize  = cmdArgs.getRdnIterationStep();
		}
		boolean newModel=true;
		

		
		for (int i=0; i < cmdArgs.getMaxTreesVal(); i+=iterStepSize) {

			if ((cmdArgs.getHiddenStrategy().equals("EM") || cmdArgs.getHiddenStrategy().equals("MAP"))  
				&& setup.getHiddenExamples() != null && newModel) {
				long sampleStart = System.currentTimeMillis();
				JointModelSampler jtSampler = new JointModelSampler(fullModel, setup, cmdArgs, false);
				HiddenLiteralSamples sampledStates = new HiddenLiteralSamples();
				// Setup facts based on the true data
				setup.addAllExamplesToFacts();
				if ( i > minTreesInModel) { minTreesInModel = i; } 
				int maxSamples = 30*((minTreesInModel/iterStepSize) + 1);
				maxSamples = 500;
				// TODO (tvk) Get more samples but pick the 200 most likely states.
				//if (cmdArgs.getNumberOfHiddenStates() > 0 ) {
				//	maxSamples = cmdArgs.getNumberOfHiddenStates();
				//}
				if (cmdArgs.getHiddenStrategy().equals("MAP")) { 
					maxSamples = -1; 
				}
				boolean returnMap = false;
				if (cmdArgs.getHiddenStrategy().equals("MAP")) {
					returnMap = true;
				}
				jtSampler.sampleWorldStates(setup.getHiddenExamples(), sampledStates, false, maxSamples, returnMap);
//				if (cmdArgs.getHiddenStrategy().equals("MAP")) {
//					sampledStates = sampledStates.getMostLikelyState();
//					Utils.println("% Percent of true states:" + sampledStates.getWorldStates().get(0).percentOfTrues());
//				}
				if (sampledStates.getWorldStates().size() == 0) { Utils.waitHere("No sampled states");}
				// This state won't change anymore so cache probs;
				Utils.println("Building assignment map");
				sampledStates.buildExampleToAssignMap();
				
				if (cmdArgs.getHiddenStrategy().equals("EM")) {
					// Build the probabilities for each example conditioned on the assignment to all other examples
					Utils.println("Building probability map");
					sampledStates.buildExampleToCondProbMap(setup, fullModel);
					if (cmdArgs.getNumberOfHiddenStates() > 0 ) {
						Utils.println("Picking top K=" + cmdArgs.getNumberOfHiddenStates());
						sampledStates.pickMostLikelyStates(cmdArgs.getNumberOfHiddenStates());
					}
				}
				double cll = BoostingUtils.computeHiddenStateCLL(sampledStates, setup.getHiddenExamples());
				Utils.println("CLL of hidden states:" + cll);
				//Utils.println("Prob of states: " + sampledStates.toString());
				setup.setLastSampledWorlds(sampledStates);
				newModel = false;
				long sampleEnd = System.currentTimeMillis();
				Utils.println("Time to sample world state: " + Utils.convertMillisecondsToTimeSpan(sampleEnd-sampleStart));
			}
			for (String pred : cmdArgs.getTargetPredVal()) {
				SingleModelSampler sampler = new SingleModelSampler(fullModel.get(pred), setup, fullModel, false);
				if (cmdArgs.getTargetPredVal().size() > 1) {
					yapFile = getYapFileForPredicate(pred, cmdArgs.getYapBiasVal());
					Utils.println("% Using yap file:" + yapFile);
				}
			
				if (fullModel.get(pred).getNumTrees() >= (i+iterStepSize)) {
					continue;
				}
				int currIterStep =  (i+iterStepSize) - fullModel.get(pred).getNumTrees();
				newModel=true;
				Utils.println("% Learning " + currIterStep + " trees in this iteration for " + pred);
				learners.get(pred).learnNextModel(this, sampler, fullModel.get(pred), currIterStep);
				if (cmdArgs.isCombineVal())
				CombinedTree.addTrees(pred); //added by Kaushik Roy
			}
			// iterStepSize++;
		}
		
		for (String pred : cmdArgs.getTargetPredVal()) {
			//LearnBoostedRDN      learner       = new LearnBoostedRDN(cmdArgs, setup);
			//String               saveModelName = BoostingUtils.getModelFile(cmdArgs, pred, true);
			//ConditionalModelPerPredicate model         = learner.learnModel(pred, yapFile, this); // This will save the model every N trees.
			//model.saveModel(saveModelName); // Do a final save since learnModel doesn't save every time (though we should make it do so at the end).
			//fullModel.put(pred, model); 
		}
		// Only clear checkpoint after all models are learnt
		for (String pred : cmdArgs.getTargetPredVal()) {
			String               saveModelName = BoostingUtils.getModelFile(cmdArgs, pred, true);
			fullModel.get(pred).saveModel(saveModelName); // Do a final save since learnModel doesn't save every time (though we should make it do so at the end).
			// 	No need for checkpoint file anymore
			clearCheckPointFiles(saveModelName);
		}
	}

	private String getYapFileForPredicate(String target, String yapFile) {
		if (yapFile.isEmpty()) { return ""; }
		int pos = yapFile.lastIndexOf("/");
		String result = yapFile.substring(0, pos+1) + target + "_" + yapFile.substring(pos + 1, yapFile.length());
		return result;
	}
	
	
	public void loadModel() {
		if (fullModel == null) {
			fullModel = new JointRDNModel();
		}

		Utils.println("\n% Getting bRDN's target predicates.");
		for (String pred : cmdArgs.getTargetPredVal()) {
			ConditionalModelPerPredicate rdn = null;
			if (fullModel.containsKey(pred)) {
				rdn = fullModel.get(pred);
				rdn.reparseModel(setup);
			} else {
				Utils.println("% Did not learn a model for '" + pred + "' this run.");
				// YapFile doesn't matter here.
				rdn = new ConditionalModelPerPredicate(setup);
			
				if (useSingleTheory(setup)) {
					rdn.setHasSingleTheory(true);
					rdn.setTargetPredicate(pred);
					rdn.loadModel(LearnBoostedRDN.getWILLFile(cmdArgs.getModelDirVal(), cmdArgs.getModelFileVal(), pred), setup, cmdArgs.getMaxTreesVal());
				} else {
					rdn.setTargetPredicate(pred);
					rdn.loadModel(BoostingUtils.getModelFile(cmdArgs, pred, true), setup, cmdArgs.getMaxTreesVal());
				}
				rdn.setNumTrees(cmdArgs.getMaxTreesVal());
				fullModel.put(pred, rdn);
			}
		}
		if (!cmdArgs.isDisableAdvice()) {
			String adviceFile = setup.getOuterLooper().getWorkingDirectory() + "/" + cmdArgs.getPriorAdvice();
			BoostingUtils.loadAdvice(setup, fullModel, adviceFile, false);
		}
	}
	
	public void infer() {
		InferBoostedRDN infer = new InferBoostedRDN(cmdArgs, setup);
		infer.runInference(fullModel, 0.5);
	}
	
	private boolean useSingleTheory(WILLSetup setup2) {
		String lookup;
		if ((lookup =  setup2.getHandler().getParameterSetting("singleTheory")) != null) {
			return Boolean.parseBoolean(lookup);
		}
		return false;
	}
	

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		
		args = Utils.chopCommentFromArgs(args); 
		CommandLineArguments cmd = RunBoostedModels.parseArgs(args);
		if (cmd == null) {
			Utils.error(CommandLineArguments.getUsageString());
		}
		RunBoostedModels runClass = null;
		runClass = new RunBoostedRDN();
		if (cmd.isLearnMLN()) {
			Utils.error("Use RunBoostedModels or RunBoostedMLN, if you want to learn MLNs(-mln) instead of RunBoostedRDN");
		}
		runClass.setCmdArgs(cmd);
		runClass.runJob();
	}
}


