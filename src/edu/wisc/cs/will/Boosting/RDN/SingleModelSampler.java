package edu.wisc.cs.will.Boosting.RDN;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.Boosting.Common.SRLInference;
import edu.wisc.cs.will.Boosting.RDN.MultiClassExampleHandler.ConstantLookupList;
import edu.wisc.cs.will.Boosting.RDN.Models.RelationalDependencyNetwork;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.RegressionValueOrVector;
import edu.wisc.cs.will.Utils.Utils;

public class SingleModelSampler extends SRLInference {
	
	private ConditionalModelPerPredicate conditionalModel = null ;
	
	private boolean hasRecursion;
	
	private int burnInSteps = 20;
	
	private int numOfSamples = 200;
	

	public SingleModelSampler(ConditionalModelPerPredicate model, WILLSetup setup, JointRDNModel jointmodel, boolean isRecursive) {
		super(setup);
		this.conditionalModel = model;
		this.jointModel = jointmodel;
		hasRecursion = isRecursive;
	}
	
	/**
	 * WILLSetup should have been called before
	 * @param eg
	 */
	public void setSample(List<RegressionRDNExample> eg) {
		for (Example example : eg) {
			RegressionRDNExample rex = (RegressionRDNExample)example;
			ProbDistribution prob = conditionalModel.returnModelProbability(example);
			/*
			if (Utils.random() <= prob) {
				rex.setSampledTruthValue(true);
				setup.addFact(getRecursiveFact(rex));
			} else {
				rex.setSampledTruthValue(false);
				setup.removeFact(getRecursiveFact(rex));
			}*/
			
			int prevValue = rex.getSampledValue();
			
			rex.setSampledValue(prob.randomlySelect());
			if (!rex.isHasRegressionVector()  ) {
				if (rex.getSampledValue() == 1) {
					setup.addFact(getRecursiveFact(rex));
				} else {
					setup.removeFact(getRecursiveFact(rex));
				}
			} else {
				if (prevValue != rex.getSampledValue()) {
					Example removeEg = setup.getMulticlassHandler().createExampleFromClass(rex, prevValue);
					Example addEg = setup.getMulticlassHandler().createExampleFromClass(rex, rex.getSampledValue());
					setup.removeFact(getRecursiveFact(removeEg));
					setup.addFact(getRecursiveFact(addEg));
				}
			}
		}
	}
	
	// TODO Lot of common stuff with JointModelSampler, refactor
	
	
	private Literal getRecursiveFact(Example rex) {
		Literal lit = setup.getHandler().getLiteral(
				setup.getHandler().getPredicateName(WILLSetup.recursivePredPrefix + rex.predicateName.name), rex.getArguments());
		return lit;
	}

	/**
	 * WILLSetup should have been called before
	 * 
	 */
	public void getProbabilitiesUsingSamples(List<RegressionRDNExample> ex) {
		Utils.println("Using recursion sampling");
		// List<Integer> sample = new ArrayList<Integer>(Collections.nCopies(ex.size(), 0));
		List<double[]> valueCounts = new ArrayList<double[]>();
		String target = conditionalModel.getTargetPredicate();
		int size = setup.getMulticlassHandler().numConstantsForPredicate(target);
		
		
		for (int i = -burnInSteps; i < numOfSamples; i++) {
			long start = System.currentTimeMillis();
			setSample(ex);
			long end = System.currentTimeMillis();
		//	Utils.println("Setting sample: " + (end-start)/1000);
			if (i>=0) {
				start = System.currentTimeMillis();
				countSample(ex, valueCounts, size);
				end = System.currentTimeMillis();
			//	Utils.println("counting sample: " + (end-start)/1000);
			}
			if (i%10 == 0) {
				Utils.println("Done with " + i + " samples");
			}
		}
		setProbability(valueCounts, ex, numOfSamples);
	}
	
	private void setProbability(List<double[]> valueCounts, List<RegressionRDNExample> ex, int numSample) {
		for (int i = 0; i < ex.size(); i++) {
			RegressionRDNExample eg = (RegressionRDNExample)ex.get(i);
			double[] counts = valueCounts.get(i);
			
			ProbDistribution distr = new ProbDistribution(new RegressionValueOrVector(counts), false);
			eg.setProbOfExample(distr);
			//double prob = (double)sample.get(i)/(double)numSample;
			//eg.setProbOfExample(prob);
		}
	}

	private void countSample(List<RegressionRDNExample> ex, List<double[]> valueCounts, int totalVals) {
		for (int i = 0; i < ex.size(); i++) {
			if (valueCounts.size() <= i) {
				valueCounts.add(new double[totalVals]);
			}
			RegressionRDNExample eg = (RegressionRDNExample)ex.get(i);
			int val = eg.getSampledValue();
			valueCounts.get(i)[val] += 1;
		}
	}
	/*
	private void countSample(List<RegressionRDNExample> ex, List<Integer> sample) {
		for (int i = 0; i < ex.size(); i++) {
			RegressionRDNExample eg = (RegressionRDNExample)ex.get(i);
			if (eg.getSampledTruthValue()) {
				sample.set(i, sample.get(i) + 1);
			}
		}
	}*/
	/*
	// TODO If you have recursive rules, generate samples.
	public void getProbabilities(List<RegressionRDNExample> allExs) {
		int counter = 0;
		long  start = System.currentTimeMillis();
		for (RegressionRDNExample ex : allExs) {
			counter++; 
			getExampleProbability(ex);
			if (counter % 1000 == 0) { 
				long end = System.currentTimeMillis();
				Utils.println("%   #" + Utils.comma(counter) + " get probability (" + Utils.truncate(ex.getProbOfExample(), 6) + ") of " + (ex.extraLabel == null ? "" : "'" + ex.extraLabel + "' ") + ex + ".   Time spent since last report: " + Utils.convertMillisecondsToTimeSpan(end - start) + ".");
				start = end;
			}
		}
	}*/

	public ProbDistribution getExampleProbability(Example eg) {
		return conditionalModel.returnModelProbability(eg);
	}
	
	
	@Override
	public void getProbabilities(List<RegressionRDNExample> allExs) {
		if (hasRecursion) {
			getProbabilitiesUsingSamples(allExs);
		} else {
			super.getProbabilities(allExs);
		}
		
	}

	@Override
	public void setMaxTrees(int max) {
		conditionalModel.setNumTrees(max);
		
	}
	
	/**@override
	 * @return the rdn
	 */
	public RelationalDependencyNetwork getRdn() {
		// Since the joint model is updated, create RDN on the fly
		return new RelationalDependencyNetwork(jointModel, setup);
	}
	
}	

