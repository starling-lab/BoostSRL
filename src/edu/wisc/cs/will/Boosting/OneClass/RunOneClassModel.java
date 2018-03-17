/**
 * 
 */
package edu.wisc.cs.will.Boosting.OneClass;

import java.io.File;
import java.io.IOException;
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
import edu.wisc.cs.will.Utils.check_disc;
import edu.wisc.cs.will.Utils.disc;

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
		boolean disc_flag=false;
		disc discObj= new disc();
		
		/*Check for discretization*/
		
		check_disc flagObj=new check_disc();
		
		if((cmd.getTrainDirVal()!=null)) 
		{
		try {
			disc_flag=flagObj.checkflagvalues(cmd.getTrainDirVal());
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		/*Updates the names of the training and Test file based on discretization is needed or not*/
		cmd.update_file_name(disc_flag);
		}
		else if((cmd.getTestDirVal()!=null)) 
		{
			try {
			System.out.println("cmd.getTestDirVal()"+cmd.getTestDirVal());
			disc_flag=flagObj.checkflagvalues(cmd.getTestDirVal());
			
			/*Updates the names of the training and Test file based on discretization is needed or not*/
			cmd.update_file_name(disc_flag);
//			System.out.println("Hellooooooooooooooooooooo"+cmd.get_filename());
			
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		}
		if (cmd.getTrainDirVal()!=null)
			
			{   
				File  f = new File(cmd.getTrainDirVal()+"\\"+cmd.trainDir+"_facts_disc.txt");
			    
				if(f.exists())
				 {
					f.delete();
				 }
				
			    try {
//			    	System.out.println("Hellooooooooooooooooooooo"+cmd.getTrainDirVal());
			    	if (disc_flag==true)
			    	{	
					discObj.Discretization(cmd.getTrainDirVal());
			    	}
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			    
			}
		if (cmd.getTestDirVal()!=null)
				
			{   
					
				File f = new File(cmd.getTestDirVal()+"\\"+cmd.testDir+"_facts_disc.txt");
				
				if(f.exists())
				{
					f.delete();
				}
				
				/*This module does the actual discretization step*/
			    try {
			    	if (disc_flag==true)
			    	{	
					 discObj.Discretization(cmd.getTestDirVal());
			    	} 
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			   
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
