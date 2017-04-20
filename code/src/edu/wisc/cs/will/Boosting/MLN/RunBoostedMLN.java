/**
 * 
 */
package edu.wisc.cs.will.Boosting.MLN;

import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import edu.wisc.cs.will.Boosting.Advice.AdviceReader;
import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;
import edu.wisc.cs.will.Boosting.EM.HiddenLiteralSamples;
import edu.wisc.cs.will.Boosting.RDN.InferBoostedRDN;
import edu.wisc.cs.will.Boosting.RDN.JointModelSampler;
import edu.wisc.cs.will.Boosting.RDN.JointRDNModel;
import edu.wisc.cs.will.Boosting.RDN.LearnBoostedRDN;
import edu.wisc.cs.will.Boosting.RDN.ConditionalModelPerPredicate;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.Boosting.Trees.RegressionMLNModel;
import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;
import edu.wisc.cs.will.Boosting.Utils.CommandLineArguments;
import edu.wisc.cs.will.FOPC.AllOfFOPC;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CondorFileWriter;
import graphdbInt.GraphDB;
import graphdbInt.GenerateSchema;
//import edu.wisc.cs.will.test.ILP.AdviceTest;

/**
 * MLN-Boost specific code for learning and inference
 * For e.g. RDN-Boost learns all the trees for one predicate at a time whereas MLN-Boost learns
 * one tree at a time for every predicate
 * Also sets the required flags for MLN-Boost.
 * @author tkhot
 *
 */
public class RunBoostedMLN extends RunBoostedModels {

	JointRDNModel fullModel = null;
	public static GraphDB gdb; //change by MD & DD
	//public static CommandLineArguments cmdGlob;//change by MD & DD
	public void learn() {
		fullModel = new JointRDNModel();
		Map<String, LearnBoostedRDN> learners = new HashMap<String, LearnBoostedRDN>();
		int minTreesInModel = Integer.MAX_VALUE;
		
		
		for (String pred : cmdArgs.getTargetPredVal()) {
			fullModel.put(pred, new ConditionalModelPerPredicate(setup));
			fullModel.get(pred).setTargetPredicate(pred);
			
			LearnBoostedRDN learner = new LearnBoostedRDN(cmdArgs, setup);
			learner.setTargetPredicate(pred);
			learners.put(pred, learner);
			if( cmdArgs.useCheckPointing()) {
				learner.loadCheckPointModel(fullModel.get(pred));
			}
			minTreesInModel = Math.min(fullModel.get(pred).getNumTrees(), minTreesInModel);
		}
		if (!cmdArgs.isDisableAdvice()) {
			String adviceFile = setup.getOuterLooper().getWorkingDirectory() + "/" + cmdArgs.getPriorAdvice();
			BoostingUtils.loadAdvice(setup, fullModel, adviceFile, true);
		}
		MLNInference sampler = new MLNInference(setup, fullModel);
		
		int iterStepSize = 1;
		if (cmdArgs.getTargetPredVal().size() == 1) {
			iterStepSize = cmdArgs.getMaxTreesVal();
		}

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
//					if (cmdArgs.getHiddenStrategy().equals("MAP")) {
//						sampledStates = sampledStates.getMostLikelyState();
//						Utils.println("% Percent of true states:" + sampledStates.getWorldStates().get(0).percentOfTrues());
//					}
					if (sampledStates.getWorldStates().size() == 0) { Utils.waitHere("No sampled states");}
					// This state won't change anymore so cache probs;
					Utils.println("Building assignment map");
					sampledStates.buildExampleToAssignMap();
					
					if (cmdArgs.getHiddenStrategy().equals("EM")) {
						// Build the probabilities for each example conditioned on the assignment to all other examples
						Utils.println("Building probability map");
						sampledStates.buildExampleToCondProbMap(setup, fullModel);
						if (cmdArgs.getNumberOfHiddenStates() > 0 ) {
							Utils.println("Picking top K");
							sampledStates.pickMostLikelyStates(cmdArgs.getNumberOfHiddenStates());
						}
					}
					//double cll = BoostingUtils.computeHiddenStateCLL(sampledStates, setup.getHiddenExamples());
					//Utils.println("CLL of hidden states:" + cll);
					//Utils.println("Prob of states: " + sampledStates.toString());
					setup.setLastSampledWorlds(sampledStates);
					newModel = false;
					long sampleEnd = System.currentTimeMillis();
					Utils.println("Time to sample world state: " + Utils.convertMillisecondsToTimeSpan(sampleEnd-sampleStart));
				}
			for (String pred : cmdArgs.getTargetPredVal()) {

				if (fullModel.get(pred).getNumTrees() >= (i+iterStepSize)) {
					continue;
				}
				int currIterStep =  (i+iterStepSize) - fullModel.get(pred).getNumTrees();
				Utils.println("% Learning " + currIterStep + " trees in this iteration for " + pred);
				newModel = true;
				learners.get(pred).learnNextModel(this, sampler, fullModel.get(pred), currIterStep); 
			}
		}
		
		for (String pred : cmdArgs.getTargetPredVal()) {
			String saveModelName = BoostingUtils.getModelFile(cmdArgs, pred, true);
			fullModel.get(pred).saveModel(saveModelName); // Do a final save since learnModel doesn't save every time (though we should make it do so at the end).
			// No need for checkpoint file anymore
			clearCheckPointFiles(saveModelName);
		}
	
	}
	@Override
	protected void afterLearn() {
		super.afterLearn();
		if (cmdArgs.isLearningMLNClauses()) {
			saveModelAsMLN();			
		}
	}
	
	
	private void saveModelAsMLN() {

		String mlnFile=setup.getOuterLooper().getWorkingDirectory() + "/"+
		(cmdArgs.getModelFileVal() == null ? "" : cmdArgs.getModelFileVal()) + ".mln";
		BufferedWriter writer = null;
		try {
			writer = new BufferedWriter(new CondorFileWriter(mlnFile));
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		AllOfFOPC.printUsingAlchemyNotation = true;
		boolean oldSTD = setup.getHandler().usingStdLogicNotation();
		boolean oldAnon = setup.getHandler().underscoredAnonymousVariables;
		setup.getHandler().underscoredAnonymousVariables=false;
		setup.getHandler().prettyPrintClauses=false;
		setup.getHandler().useStdLogicNotation();
		
		Set<String> modes = setup.getInnerLooper().getAlchemyModeStrings(setup.getInnerLooper().getBodyModes());
		modes.addAll(setup.getInnerLooper().getAlchemyModeStrings(setup.getInnerLooper().getTargetModes()));
		for (String str : modes) {
			try {
				writer.write(str);
				writer.newLine();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		
		for (ConditionalModelPerPredicate model : fullModel.values()) {
			for (Entry<Clause, Double> entry : model.convertToSingleMLN().entrySet()) {
				try {
					entry.getKey().setWeightOnSentence(entry.getValue());
					writer.write(entry.getKey().toString());
					writer.newLine();
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		}
		if (!oldSTD) {
			setup.getHandler().usePrologNotation();
		}
		setup.getHandler().underscoredAnonymousVariables = oldAnon;
		AllOfFOPC.printUsingAlchemyNotation = false;
		try {
			writer.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

	}
	
	public void loadModel() {
		if (fullModel == null) {
			fullModel = new JointRDNModel();
		}
		Set<String> modelPreds = cmdArgs.getLoadPredModelVal();
		if (modelPreds == null) {
			modelPreds = cmdArgs.getTargetPredVal();
		}
		for (String pred : modelPreds) {
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
					rdn.loadModel(BoostingUtils.getModelFile(cmdArgs, pred, true), setup, cmdArgs.getMaxTreesVal());
				}
				rdn.setNumTrees(cmdArgs.getMaxTreesVal());
				fullModel.put(pred, rdn);
			}
		}
		if (!cmdArgs.isDisableAdvice()) {
			String adviceFile = setup.getOuterLooper().getWorkingDirectory() + "/" + cmdArgs.getPriorAdvice();
			BoostingUtils.loadAdvice(setup, fullModel, adviceFile, true);
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
		//cmdGlob = cmd;//change MD & DD
		if (cmd == null) {
			Utils.error(CommandLineArguments.getUsageString());
		}
		try //change MD & DD
		{
			if(cmd.isLearnVal())
			{
				GenerateSchema.generateSchema(cmd.getTrainDirVal(), "/train_bk.txt");
				gdb = new GraphDB(cmd.getTrainDirVal()+"/train_facts.txt",cmd.getTrainDirVal()+"/schema.db", "train",true);
			}
			else if(cmd.isInferVal())
			{
				GenerateSchema.generateSchema(cmd.getTestDirVal(), "/test_bk.txt");
				gdb = new GraphDB(cmd.getTestDirVal()+"/test_facts.txt",cmd.getTestDirVal()+"/schema.db", "test",true);
			}
		}
		catch(Exception e)
		{
			e.printStackTrace();
		}
		RunBoostedModels runClass = null;
		runClass = new RunBoostedMLN();
		if (!cmd.isLearnMLN()) {
			Utils.waitHere("Set \"-mln\"  in cmdline arguments to ensure that we intend to learn MLNs. Will now learn an MLN.");
		}
		cmd.setLearnMLN(true);
		runClass.setCmdArgs(cmd);
		runClass.runJob();
	}
}

