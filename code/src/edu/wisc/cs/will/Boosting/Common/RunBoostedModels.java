/**
 * Generic code to call MLN-Boost and RDN-Boost
 */
package edu.wisc.cs.will.Boosting.Common;

import java.io.File;

import edu.wisc.cs.will.Boosting.MLN.RunBoostedMLN;
import edu.wisc.cs.will.Boosting.OneClass.RunOneClassModel;
import edu.wisc.cs.will.Boosting.RDN.CombinedTree;
import edu.wisc.cs.will.Boosting.RDN.RunBoostedRDN;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.Boosting.Regression.RunBoostedRegressionTrees;
import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;
import edu.wisc.cs.will.Boosting.Utils.CommandLineArguments;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.Utils.disc;

/**
 * @author tkhot
 *
 */
public abstract class RunBoostedModels {
	public static CommandLineArguments cmdGlob;
	protected CommandLineArguments cmdArgs; 
	public CommandLineArguments getCmdArgs() {
		return cmdArgs;
	}

	public void setCmdArgs(CommandLineArguments cmdArgs) {
		CombinedTree.cmd = cmdArgs;
		this.cmdArgs = cmdArgs;
		cmdGlob = this.cmdArgs;
	}

	protected WILLSetup  setup;
	
	public RunBoostedModels() {
		
	}
	
	public static CommandLineArguments parseArgs(String[] args) {
		CommandLineArguments cmdArgs = new CommandLineArguments();
		if (cmdArgs.parseArgs(args)) {
			return cmdArgs;
		}
		return null;
	}
	
	public void runJob() {
		if (cmdArgs.isLearnVal()) {
			long start = System.currentTimeMillis();
			learnModel();
			long end = System.currentTimeMillis();
			Utils.println("\n% Total learning time ("  + Utils.comma(cmdArgs.getMaxTreesVal()) + " trees): " + Utils.convertMillisecondsToTimeSpan(end - start, 3) + ".");
		}
		
		if (cmdArgs.isInferVal()) {
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
	public abstract void learn();
	
	public void learnModel() {
		setupWILLForTrain();
		beforeLearn();
		learn();
		afterLearn();
	}

	protected void setupWILLForTrain() {
		setup     = new WILLSetup();
		try {
			Utils.println("\n% Calling SETUP.");
			setup.setup(cmdArgs, cmdArgs.getTrainDirVal(), true);
		} catch (SearchInterrupted e) {
			Utils.reportStackTrace(e);
			Utils.error("Problem in setupWILLForTrain.");
		}
	}
	
	/**
	 * Override this method if you want to take some steps before calling learn.
	 */
	protected void beforeLearn() {
		Utils.println(cmdArgs.getModelDirVal());
		File dir = new CondorFile(cmdArgs.getModelDirVal());
		Utils.ensureDirExists(dir);
		
		// Rename old model files to prevent accidental re-use.
		renameOldModelFiles();
	}
	/**
	 * Override to call methods after learning.
	 */
	protected void afterLearn() {
		Utils.println("cached groundings hit: " + setup.getInnerLooper().num_hits + "\nMisses: " +setup.getInnerLooper().num_misses);
	}
	
	protected void clearCheckPointFiles(String saveModelName) {
		if (Utils.fileExists(BoostingUtils.getCheckPointFile(saveModelName))) {
			Utils.delete(BoostingUtils.getCheckPointFile(saveModelName));
		}
		if (Utils.fileExists(BoostingUtils.getCheckPointExamplesFile(saveModelName))) {
			Utils.delete(BoostingUtils.getCheckPointExamplesFile(saveModelName));
		}
		if (Utils.fileExists(BoostingUtils.getCheckPointFlattenedLitFile(saveModelName))) {
			Utils.delete(BoostingUtils.getCheckPointFlattenedLitFile(saveModelName));
		}
		
	}
	private void renameOldModelFiles() {
		for (int i = 0; i < numbModelsToMake; i++) {
			// Rename model files.
			for (String pred : cmdArgs.getTargetPredVal()) {
				String filename = BoostingUtils.getModelFile(cmdArgs, pred, true);
				File f = new CondorFile(filename);
				if (f.exists()) {
					renameAsOld(f);
				}
			}
		}		
	}

	
	public static void renameAsOld(File f) {
	//	File   newF         = new CondorFile(f.getAbsoluteFile() + ".old");
	/*	THIS WAS MAKING THE OLD FILE BE A DIRECTORY RATHER THAN A FILE FOR SOME ODD REASON (JWS)  ...
	 * */
		String justFileName = f.getName();
		File   parent       = f.getParentFile();
		File   newF         = new CondorFile(parent, "old_" + justFileName);
	//	Utils.waitHereRegardless("renameAsOld: " + f + "\n name = " + justFileName + "\n parent = " + parent + "\n newF = " + newF);
	
		if (newF.exists()) {
			if (!newF.delete()) {
				Utils.error("Couldn't delete the file: " + newF.getAbsolutePath());
			}
		}
		if (!f.renameTo(newF)) {
			Utils.error("Couldn't rename from " + f.getAbsolutePath() + " to " + newF.getAbsolutePath());
		}
	}
	
	public abstract void loadModel();
	
	public abstract void infer();
	public void inferModel() {
		if(!setupWILLForTest()) {
			return;
		}
		beforeInfer();
		infer();
		afterInfer();
	}
	

	protected void afterInfer() {
		
		
	}

	protected void beforeInfer() {
		loadModel();
		if (cmdArgs.outFileSuffix != null) {
			cmdArgs.setModelFileVal(cmdArgs.outFileSuffix);
		}
	}

	protected boolean setupWILLForTest() {
		setup = new WILLSetup();
		try {
			if(!setup.setup(cmdArgs, cmdArgs.getTestDirVal(), false)) {
				Utils.println("\nSetup failed (possibly because there are no examples), so will not infer anything.");
				return false;
			}
		} catch (SearchInterrupted e) {
			Utils.reportStackTrace(e);
			Utils.error("Problem in inferModel.");
		}
		return true;
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
		if (cmd.isLearnMLN()) {
			runClass = new RunBoostedMLN();
		} else {
			if (cmd.isLearnRegression()) {
				runClass = new RunBoostedRegressionTrees();
			}
			else {
				if (cmd.isLearnOCC()) {
					runClass = new RunOneClassModel();
				} else {
					runClass = new RunBoostedRDN();
				}
			}
		}
		runClass.setCmdArgs(cmd);
		runClass.runJob();
	}
	
}
