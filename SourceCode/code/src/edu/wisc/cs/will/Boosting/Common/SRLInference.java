package edu.wisc.cs.will.Boosting.Common;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.wisc.cs.will.Boosting.EM.HiddenLiteralSamples;
import edu.wisc.cs.will.Boosting.EM.HiddenLiteralState;
import edu.wisc.cs.will.Boosting.MLN.MLNInference;
import edu.wisc.cs.will.Boosting.RDN.JointModelSampler;
import edu.wisc.cs.will.Boosting.RDN.JointRDNModel;
import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.Boosting.RDN.Models.DependencyPredicateNode.PredicateType;
import edu.wisc.cs.will.Boosting.RDN.Models.RelationalDependencyNetwork;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.Utils;

/**
 * Generic inference interfact for RFGB
 * @author tkhot
 *
 */
public abstract class SRLInference {
	
	protected WILLSetup setup;
	protected RelationalDependencyNetwork rdn;
	protected JointRDNModel jointModel;
	
	public SRLInference(WILLSetup setup) {
		this.setup = setup;
	}
	
	/**
	 * 
	 * @param eg - Return this example's probability
	 * @return
	 */
	public abstract ProbDistribution getExampleProbability(Example eg);
	
	
	public abstract void setMaxTrees(int max);
	 
	
	
	/**
	 * 
	 * @param rex - Set the probability for this example
	 */
	public void setExampleProbability(RegressionRDNExample rex) {
		rex.setProbOfExample(getExampleProbability(rex));
	}
	
	public void getProbabilities(List<RegressionRDNExample> allExs) {
		int counter = 0;
		long start = System.currentTimeMillis();
		
		for (RegressionRDNExample ex : allExs) {
			if (this instanceof MLNInference) {
				((MLNInference)this).resetCache();
			}
			counter++; 
			setExampleProbability(ex);
			/*if (counter % 5000 == 0) { 
				long end = System.currentTimeMillis();
				Utils.println("%   #" + Utils.comma(counter) + " get probability (" + Utils.truncate(ex.getProbOfExample(), 6) + ") of " + (ex.extraLabel == null ? "" : "'" + ex.extraLabel + "' ") + ex + ".   Time spent since last report: " + Utils.convertMillisecondsToTimeSpan(end - start) + ".");
				if (this instanceof MLNInference) {
					Utils.println(((MLNInference)this).getTimePerModel());
					((MLNInference)this).clearTimes();
				}
			  start = end;
			}*/
		}
	}
	
	/**
	 * Compute the averaged probability over each sample
	 * @param samples
	 * @param allExs
	 */
	public void getProbabilitiesUsingSampledStates(HiddenLiteralSamples samples, List<RegressionRDNExample> allExs) {
		List<ProbDistribution> exProb = new ArrayList<ProbDistribution>(allExs.size());
		String currTarget = null;
		for (int i = 0; i < allExs.size(); i++) {
			exProb.add(null);
			if (currTarget == null) {
				currTarget = allExs.get(i).predicateName.name;
			} else {
				if (!currTarget.equals(allExs.get(i).predicateName.name)) {
					Utils.waitHere("Expected all examples to be of same type:" + allExs.get(i).predicateName.name + " but also found: " + currTarget);
				}
			}
		}
		
		if (getRdn() == null) {
			Utils.waitHere("Expected RDN to be set!");
		}
		
		// Have to collect the predicate names because query parents returns predicatename and not strings
		Set<String> predsInSample = new HashSet<String>(samples.getPredicates());
		
		// Remove multiclass prefix from predicate name
		if (currTarget.startsWith(setup.multiclassPredPrefix)) {
			currTarget = currTarget.substring(setup.multiclassPredPrefix.length());
		}
		if (! (this instanceof MLNInference)) {
			boolean marginalizeAll = true;
			for( PredicateName queryPars : getRdn().getQueryParents(currTarget)) {
				// Don't marginalize this predicate
				predsInSample.remove(queryPars.name);
				// There will be something left after marginalizing
				marginalizeAll = false;
			}


			// Save marginalizing time
			if (marginalizeAll && !getRdn().isRecursive(currTarget)) {
				Utils.println("Computing without sampling since no hidden/query parents.");
				getProbabilities(allExs);
				return;
			}
		}
		// Makes it slower so disabled for now
		if (false) {
			if (!getRdn().isRecursive(currTarget)) {
				Utils.println("Marginalize out predicate: " + currTarget + " since no recursion.");
				samples = samples.marginalizeOutPredicate(currTarget);
			}

			for (String marginalPred : predsInSample) {
				Utils.println("Marginalize out predicate: " + marginalPred + " since not present in parents.");
				samples = samples.marginalizeOutPredicate(marginalPred);
			}

		}
		Utils.println("Computing using " + samples.getWorldStates().size() + " samples.");
		// If doesn't depend on the world state, just return the probabilities ie every predicate has been marginalized out.
		// Shouldn't be called anymore
		if (samples.getWorldStates().size() == 0) {
			Utils.waitHere("This code shouldn't be called anymore as we check for marginalizeAll before.");
			getProbabilities(allExs);
			return;
		}
		for (int i = 0; i < samples.getWorldStates().size(); i++) {
			getProbabilitiesUsingSample(samples.getWorldStates().get(i), allExs);
			double currWorldProb = samples.getProbabilities().get(i);
			for (int j = 0; j < allExs.size(); j++) {
				RegressionRDNExample ex = allExs.get(j);
				// exProb.get(j) can be null initially.
				ProbDistribution newDistr = new ProbDistribution(ex.getProbOfExample());
				newDistr.scaleDistribution(currWorldProb);
				if (exProb.get(j) != null && newDistr.isHasDistribution() != exProb.get(j).isHasDistribution()) {
					Utils.waitHere("Mismatch between example distributions for " + ex.toString() + " distr:" + newDistr.isHasDistribution());
				}
				if (exProb.get(j) != null) {
					newDistr.addDistribution(exProb.get(j));
				}
				
				exProb.set(j, newDistr);
			}
			if (i%100 == 99) {
				Utils.println("done with #" + (i+1) + " samples.");
			}
		}
		for (int j = 0; j < allExs.size(); j++) {
			RegressionRDNExample ex = allExs.get(j);
			ex.setProbOfExample(exProb.get(j));
		}
	}
	
	
	
	/**
	 * set the probability of the examples using the worldState as facts
	 * @param worldState
	 * @param allExs
	 */
	private void getProbabilitiesUsingSample(HiddenLiteralState worldState,
			List<RegressionRDNExample> allExs) {
		
		updateFactsFromState(setup, worldState);
		
		getProbabilities(allExs);
	}

	public static void updateFactsFromState(WILLSetup setup, HiddenLiteralState worldState) {
		int countPos = 0;
		int countNeg = 0;
		for (Literal posEx : worldState.getPosExamples()) {
			
			if (posEx.predicateName.name.startsWith(WILLSetup.multiclassPredPrefix)) {
				RegressionRDNExample mcRex = (RegressionRDNExample)posEx;
				int maxVec = mcRex.getOutputVector().length;
				int assign = worldState.getAssignment((Example)posEx);
				if (assign < 0 || assign >= maxVec) { Utils.waitHere("Assignment: " + assign + " not within bound: " + maxVec);}
				for (int i = 0; i < maxVec; i++) {
					Example eg =  setup.getMulticlassHandler().createExampleFromClass(mcRex, i);
					if (i == assign) {
						//Utils.println("Adding hidden example: " + eg.toString());
						addAsPosFact(eg, setup);
						countPos++;
					} else {
						addAsNegFact(eg, setup);
						countNeg++;
					}
				}
			} else {
				addAsPosFact(posEx, setup);
				countPos++;
			}
		}
		for (Literal negEx : worldState.getNegExamples()) {
			//Utils.waitHere("Adding neg!:" +negEx);
			addAsNegFact(negEx, setup);
			countNeg++;
		}
		//Utils.println("adding pos=" + countPos + " facts and neg=" + countNeg + " facts.");
	}

	private static  void addAsNegFact(Literal negEx, WILLSetup setup) {
		if (setup.allowRecursion) {
			Literal lit = setup.getHandler().getLiteral(setup.getHandler().getPredicateName(
					WILLSetup.recursivePredPrefix + negEx.predicateName.name), negEx.getArguments());
			setup.removeFact(lit);
		}
		setup.removeFact(negEx);
	}

	private static void addAsPosFact(Literal posEx, WILLSetup setup) {
		if (setup.allowRecursion) {
			Literal lit = setup.getHandler().getLiteral(setup.getHandler().getPredicateName(
					WILLSetup.recursivePredPrefix + posEx.predicateName.name), posEx.getArguments());
			setup.addFact(lit);
		}
		setup.addFact(posEx);
	}

	public void getMarginalProbabilities(Map<String, List<RegressionRDNExample>> jointExamples) {
		for (List<RegressionRDNExample> examples : jointExamples.values()) {
			getProbabilities(examples);
		}
	}

	/**
	 * Returns true, if the predicate is using recursion.
	 * @param target
	 * @return
	 */
	protected boolean isRecursive(String target) {
		return rdn.isRecursive(target);
	}

	/**
	 * 
	 * @param target predicate name to evaluate for
	 * @return true, if the target predicate has no query ancestors.
	 */
	protected boolean hasNoTargetParents(String target) {
		return (rdn.getAncestorsOfType(target, PredicateType.QUERY).size() == 0);
	}

	/**
	 * @return the rdn
	 */
	public RelationalDependencyNetwork getRdn() {
		return rdn;
	}
	
}
