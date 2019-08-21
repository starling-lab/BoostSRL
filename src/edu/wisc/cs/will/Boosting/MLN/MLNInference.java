package edu.wisc.cs.will.Boosting.MLN;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import edu.wisc.cs.will.Boosting.Common.SRLInference;
import edu.wisc.cs.will.Boosting.RDN.ConditionalModelPerPredicate;
import edu.wisc.cs.will.Boosting.RDN.JointRDNModel;
import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.Boosting.RDN.Models.RelationalDependencyNetwork;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.RegressionValueOrVector;
import edu.wisc.cs.will.Utils.Utils;
/**
 * Class used for inference in MLNs
 * @author tkhot
 *
 */
public class MLNInference extends SRLInference {

	protected Map<String, Long> timePerModel = new HashMap<String, Long>();
	protected Map<String, Long> cachedRegressionClauseWeights = null; 
	public MLNInference(WILLSetup setup, JointRDNModel model) {
		super(setup);
		this.jointModel = model;
		cachedRegressionClauseWeights = new HashMap<String, Long>();
		// RDN should be built in getRDN() to ensure updated model is used.
	//	rdn = new RelationalDependencyNetwork(model, setup);
	}
	
	public void resetCache() {
		cachedRegressionClauseWeights = new HashMap<String, Long>();
	}
	@Override
	public ProbDistribution getExampleProbability(Example eg) {
		double regression = 0;
		RegressionRDNExample rex = (RegressionRDNExample)eg;
		RegressionValueOrVector reg = null;
		if (rex.isHasRegressionVector()) {
			double[] probs = new double[rex.getOutputVector().length];
			Arrays.fill(probs, 0);
			reg = new RegressionValueOrVector(probs);
		} else {
			reg = new RegressionValueOrVector(0);
		}
		for (ConditionalModelPerPredicate mod : jointModel.values()) {
			String pred = mod.getTargetPredicate();
			long start = System.currentTimeMillis();
			mod.setCache(cachedRegressionClauseWeights);
			// TODO(TVK!) see if this works
			//regression += mod.returnModelRegressionWithPrior(eg);
			if (mod.getTargetPredicate().equals(eg.predicateName.name)) {
				reg.addValueOrVector(mod.returnModelRegressionWithPrior(eg));
//				System.out.println("I am reg with prior::"+reg);
				//regression += mod.returnModelRegressionWithPrior(eg);
			} else {
				reg.addValueOrVector(mod.returnModelRegression(eg));
//				System.out.println("I am reg with without prior::"+reg);
				//regression += mod.returnModelRegression(eg);
			}
			long end = System.currentTimeMillis();
			addToTimePerModel(pred, end-start);	
		}
		
		// return BoostingUtils.sigmoid(regression, 0);

		return new ProbDistribution(reg, true);
		
	}
	private void addToTimePerModel(String pred, long l) {
		if (!timePerModel.containsKey(pred)) {
			timePerModel.put(pred, new Long(0));
		}
		timePerModel.put(pred, timePerModel.get(pred) + l);
	}
	
	public void clearTimes() {
		timePerModel.clear();
	}
	public String getTimePerModel() {
		String result = "";
		for (String pred : timePerModel.keySet()) {
			result += pred + ":" + Utils.convertMillisecondsToTimeSpan(timePerModel.get(pred)) + "\n";
		}
		return result;
	}
	@Override
	public void setMaxTrees(int max) {
		for (ConditionalModelPerPredicate mod : jointModel.values()) {
			mod.setNumTrees(max);
		}
	}
	/**@override
	 * @return the rdn
	 */
	public RelationalDependencyNetwork getRdn() {
		// Since the joint model is updated, create RDN on the fly
		return new RelationalDependencyNetwork(jointModel, setup);
	}

}
