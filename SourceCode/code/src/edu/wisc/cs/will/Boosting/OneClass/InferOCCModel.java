/**
 * 
 */
package edu.wisc.cs.will.Boosting.OneClass;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;
import edu.wisc.cs.will.Boosting.Utils.CommandLineArguments;
import edu.wisc.cs.will.DataSetUtils.ComputeAUC;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author tkhot
 *
 */
public class InferOCCModel {

	
	private WILLSetup setup;
	
	private CommandLineArguments cmdArgs;
	
	private double  minRecallForAUCPR     = 0;

	
	public InferOCCModel(CommandLineArguments cmdArgs, WILLSetup setup) {
		this.cmdArgs = cmdArgs;
		this.setup = setup;
	}

	public void runInference(Map<String, PropositionalizationModel> fullModel) {
		Map<String,List<RegressionRDNExample>> jointExamples = setup.getJointExamples(cmdArgs.getTargetPredVal());
		subsampleNegatives(jointExamples);
		Utils.println("\n% Starting inference in OCC.");
		
		for (String pred : jointExamples.keySet()) {
			List<RegressionRDNExample> examples = jointExamples.get(pred);
			PropositionalizationModel propModel = fullModel.get(pred);
			
			if (propModel == null) {
				Utils.error("No model learned for " + pred);
				return;
			}
			
			for (RegressionRDNExample example : examples) {
				FeatureVector vec = propModel.getFeatureVector(example);
				double prob = getExampleProb(example, propModel);
				example.setProbOfExample(new ProbDistribution(prob));
				// System.out.println(example.toString() + "\t" + vec.toString());
				// System.out.println(vec.toMatlabString());
				//System.out.println(prob + " " + (example.isOriginalTruthValue() ? "1" : "0"));
			}
			ComputeAUC auc = computeAUCFromEg(examples, pred);
			Utils.println(   "\n%   AUC ROC   = " + Utils.truncate(auc.getROC(), 6));
			Utils.println(     "%   AUC PR    = " + Utils.truncate(auc.getPR(),  6));
			Utils.println(     "%   CLL	      = " + Utils.truncate(auc.getCLL(),  6));
	
		}
		
		
		
	}

	private double getExampleProb(RegressionRDNExample example,
			PropositionalizationModel propModel) {
		//int counter = 0;
		FeatureVector egVec = propModel.getFeatureVector(example);
		//double sumProb = 0;
		KernelEstimator kEst = new KernelEstimator();
		List<Double> dists = new ArrayList<Double>();
		for (FeatureVector fvec : propModel.getOneClassExamples()) {
			//counter++;
			double dist = egVec.getDistance(fvec);
			dists.add(dist);
			//double prob = (3.0/4.0) * (1.0 - Math.pow((dist/1.0), 2.0));
			//sumProb += prob;
		}
		return kEst.getProbabilityFromDistance(dists);
		//return sumProb/counter;
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
	
			aucTempDirectory = setup.getOuterLooper().getWorkingDirectory() + "/AUC/" + (cmdArgs.getModelFileVal() == null ? "" : cmdArgs.getModelFileVal() +"/");
			if (cmdArgs.getTargetPredVal().size() > 1) {
				aucTempDirectory += target + "/";
			}
			extraMarker = "";
			ComputeAUC.deleteAUCfilesAfterParsing = false;
		ComputeAUC          auc = new ComputeAUC(positiveProbs, negativeProbs, aucTempDirectory, cmdArgs.getAucPathVal(), extraMarker, minRecallForAUCPR, cmdArgs.useLockFiles);
		return auc;
	}
	
}
