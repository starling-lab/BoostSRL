/**
 * 
 */
package edu.wisc.cs.will.Boosting.OneClass;

import java.util.HashMap;
import java.util.Map;

import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;
import edu.wisc.cs.will.Boosting.EM.HiddenLiteralSamples;
import edu.wisc.cs.will.Boosting.MLN.MLNInference;
import edu.wisc.cs.will.Boosting.RDN.ConditionalModelPerPredicate;
import edu.wisc.cs.will.Boosting.RDN.InferBoostedRDN;
import edu.wisc.cs.will.Boosting.RDN.JointModelSampler;
import edu.wisc.cs.will.Boosting.RDN.JointRDNModel;
import edu.wisc.cs.will.Boosting.RDN.LearnBoostedRDN;
import edu.wisc.cs.will.Boosting.RDN.RunBoostedRDN;
import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;
import edu.wisc.cs.will.Boosting.Utils.CommandLineArguments;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author tkhot
 *
 */
public class RunOneClassModel extends RunBoostedModels {

	
	private Map<String, PropositionalizationModel> fullModel;
	/**
	 * 
	 */
	public RunOneClassModel() {
		fullModel = new HashMap<String, PropositionalizationModel>();
	}

	/* (non-Javadoc)
	 * @see edu.wisc.cs.will.Boosting.Common.RunBoostedModels#learn()
	 */
	@Override
	public void learn() {
		//PropositionalizationModel model = new PropositionalizationModel();
		Map<String, LearnOCCModel> learners = new HashMap<String, LearnOCCModel>();
		int minTreesInModel = Integer.MAX_VALUE;
		
		
		for (String pred : cmdArgs.getTargetPredVal()) {
			fullModel.put(pred, new PropositionalizationModel());
			fullModel.get(pred).setTargetPredicate(pred);
			
			LearnOCCModel learner = new LearnOCCModel(cmdArgs, setup);
			learner.setTargetPredicate(pred);
			learners.put(pred, learner);
			if( cmdArgs.useCheckPointing()) {
				learner.loadCheckPointModel(fullModel.get(pred));
			}
			minTreesInModel = Math.min(fullModel.get(pred).getNumTrees(), minTreesInModel);
		}
	
	
		int iterStepSize = 1;
		//if (cmdArgs.getTargetPredVal().size() == 1) {
			iterStepSize = cmdArgs.getMaxTreesVal();
		//}

		if (cmdArgs.getRdnIterationStep() != -1) {
			iterStepSize  = cmdArgs.getRdnIterationStep();
		}
		boolean newModel=true;
		for (int i=0; i < cmdArgs.getMaxTreesVal(); i+=iterStepSize) {
		
			for (String pred : cmdArgs.getTargetPredVal()) {

				if (fullModel.get(pred).getNumTrees() >= (i+iterStepSize)) {
					continue;
				}
				int currIterStep =  (i+iterStepSize) - fullModel.get(pred).getNumTrees();
				Utils.println("% Learning " + currIterStep + " trees in this iteration for " + pred);
				newModel = true;
				learners.get(pred).learnNextModel(this, fullModel.get(pred), currIterStep);
			}
		}
		
		for (String pred : cmdArgs.getTargetPredVal()) {
			String saveModelName = BoostingUtils.getModelFile(cmdArgs, pred, true);
			fullModel.get(pred).saveModel(saveModelName); // Do a final save since learnModel doesn't save every time (though we should make it do so at the end).
			// No need for checkpoint file anymore
			clearCheckPointFiles(saveModelName);
		}
	}

	/* (non-Javadoc)
	 * @see edu.wisc.cs.will.Boosting.Common.RunBoostedModels#loadModel()
	 */
	@Override
	public void loadModel() {
		if (fullModel == null) {
			fullModel = new HashMap<String, PropositionalizationModel>(); 
		}

		Utils.println("\n% Getting occ's target predicates.");
		for (String pred : cmdArgs.getTargetPredVal()) {
			PropositionalizationModel propModel = null;
			if (fullModel.containsKey(pred)) {
				propModel = fullModel.get(pred);
				propModel.reparseModel(setup);
			} else {
				Utils.println("% Did not learn a model for '" + pred + "' this run.");
				// YapFile doesn't matter here.
				propModel = new PropositionalizationModel();
				propModel.setTargetPredicate(pred);
				propModel.loadModel(BoostingUtils.getModelFile(cmdArgs, pred, true), setup, cmdArgs.getMaxTreesVal());
				
				propModel.setNumTrees(cmdArgs.getMaxTreesVal());
				fullModel.put(pred, propModel);
			}
		}
		

	}

	/* (non-Javadoc)
	 * @see edu.wisc.cs.will.Boosting.Common.RunBoostedModels#infer()
	 */
	@Override
	public void infer() {
		InferOCCModel infer = new InferOCCModel(cmdArgs, setup);
		infer.runInference(fullModel);

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
		runClass = new RunOneClassModel();
		if (cmd.isLearnMLN()) {
			Utils.error("Use RunBoostedModels or RunBoostedMLN, if you want to learn MLNs(-mln) instead of RunOneClassModel");
		}
		if (!cmd.isLearnOCC()) {
			Utils.waitHere("Set \"-occ\"  in cmdline arguments to ensure that we intend to learn OCC. Will now learn an OCC.");
		}
		runClass.setCmdArgs(cmd);
		runClass.runJob();
	}

}
