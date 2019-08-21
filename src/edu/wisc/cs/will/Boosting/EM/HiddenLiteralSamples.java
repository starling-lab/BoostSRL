/**
 * 
 */
package edu.wisc.cs.will.Boosting.EM;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.wisc.cs.will.Boosting.RDN.JointRDNModel;
import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.VectorStatistics;

/**
 * 
 * Class to store sampled world states for the hidden literals along with probability of each world state
 * @author tkhot
 *
 */
public class HiddenLiteralSamples {

	List<HiddenLiteralState> worldStates;
	List<Double>     probabilities;
	// Only used while adding samples. Used to compute the probability of each world after sampling.
	List<Long>       counts;
	
	Map<HiddenLiteralState, Integer> worldStateToIndex;
	
	public HiddenLiteralSamples() {
		worldStates = new ArrayList<HiddenLiteralState>();
		probabilities = new ArrayList<Double>();
		counts = new ArrayList<Long>();
		worldStateToIndex = new HashMap<HiddenLiteralState, Integer>();
	}
	
	
	
	public HiddenLiteralSamples marginalizeOutPredicate(String predicate) {
		HiddenLiteralSamples marginalSample = new HiddenLiteralSamples();
		// Basic check 
		if (getPredicates().size() == 1 && getPredicates().contains(predicate)) {
			return marginalSample;
		}
		for (int i = 0; i < worldStates.size(); i++) {
			HiddenLiteralState	 state =  worldStates.get(i);
			HiddenLiteralState marginalState = state.marginalizeOutPredicate(predicate);
			Integer index = marginalSample.worldStateToIndex.get(marginalState);
			if (index == null) {
				index = marginalSample.worldStates.size();
				marginalSample.worldStateToIndex.put(marginalState, index);
				marginalSample.worldStates.add(marginalState);
				marginalSample.probabilities.add(0.0);
			}
			Double prob = marginalSample.probabilities.get(index);
			marginalSample.probabilities.set(index, probabilities.get(i) + prob);
		}
		return marginalSample;
	}
	
	
	public void buildExampleToAssignMap() {
		// TODO store a map here too.
		for (int j = 0; j < worldStates.size(); j++) {
			HiddenLiteralState state = worldStates.get(j);
			state.buildLiteralToAssignMap();
		}
	}
	
	public ProbDistribution sampledProbOfExample(Example eg) {
		double sumProb = 0;
		boolean isMultiClass = false;
		double[] sumVec = null;
		int size = 0;
		RegressionRDNExample rex = (RegressionRDNExample)eg;
		if (rex.isHasRegressionVector()) {
			isMultiClass = true;
			size = rex.getOutputVector().length;
			sumVec = new double[size];
			Arrays.fill(sumVec, 0.0);
		}
		//ProbDistribution probDistr = new Pro
		for (int j = 0; j < worldStates.size(); j++) {
			HiddenLiteralState state = worldStates.get(j);
			int index = state.getAssignment(eg);
			if (isMultiClass) {
				double[] probVec = VectorStatistics.scalarProduct(VectorStatistics.createIndicator(size, index),
						probabilities.get(j));
				sumVec = VectorStatistics.addVectors(sumVec, probVec);
			} else {
				if (index == 1) {
					sumProb += probabilities.get(j);
				}
			}
		}
		ProbDistribution probDistr = null;
		if (isMultiClass) {
			probDistr = new ProbDistribution(sumVec);
		} else {
			probDistr = new ProbDistribution(sumProb);
		}
		return probDistr;
	}
	
	
	/**
	 * @return the worldStates
	 */
	public List<HiddenLiteralState> getWorldStates() {
		return worldStates;
	}


	/**
	 * If the number of probabilities == 0  or less than number of world state
	 * then the counters were not updated to probabilities using the number of 
	 * samples.
	 * @return the probabilities
	 */
	public List<Double> getProbabilities() {
		return probabilities;
	}




	public void updateSample(Map<String, List<RegressionRDNExample>> jointExamples) {
		HiddenLiteralState state = new HiddenLiteralState(jointExamples);
		Integer index = worldStateToIndex.get(state);
		if (index == null) {
			index = worldStates.size();
			worldStates.add(state);
			worldStateToIndex.put(state, index);
			counts.add(new Long(0));
			// Utils.println("Found new state: " + state.getStringRep());
		}
		counts.set(index, counts.get(index) + 1);
	}
	
	public void setProbabilitiesFromCounters(long numSamples) {
		for (Long count : counts) {
			probabilities.add((double)count/(double)numSamples);
		}
	}
	
	@Override
	public String toString() {
		String rep = "";
		for (int i = 0; i < worldStates.size(); i++) {
			rep += "\n";
			rep += worldStates.get(i).getStringRep();
			rep += ":" + probabilities.get(i);
		}	
		return rep;
	}



	public Set<String> getPredicates() {
		if (worldStates.size() == 0) {
			return new HashSet<String>();
		}
		return worldStates.get(0).getPredicates();
	}



	public HiddenLiteralSamples getMostLikelyState() {
		
		HiddenLiteralSamples marginalSample = new HiddenLiteralSamples();
		HiddenLiteralState mostLikelyState = null;
		double maxProb = -1;
		for (int i = 0; i < worldStates.size(); i++) {
			Double prob = probabilities.get(i);
			if (prob > maxProb) {
				maxProb = prob;
				HiddenLiteralState state =  worldStates.get(i);
				mostLikelyState = state;
			}
		}
		
		if (mostLikelyState == null) {
			Utils.error("No world state found");
		}
		int index = 0;
		marginalSample.worldStateToIndex.put(mostLikelyState, index);
		marginalSample.worldStates.add(mostLikelyState);
		marginalSample.probabilities.add(1.0);
		
		// To compute the difference between MAP and EM probs
		 this.buildExampleToAssignMap();
//		 double sqrdSum = 0;
//		 long count = 0;
//		for ( Literal lit : marginalSample.getWorldStates().get(0).getPosExamples()) {
//			ProbDistribution probDist = this.sampledProbOfExample((Example)lit);
//			if (probDist.isHasDistribution()) {
//				Utils.waitHere("Not implemented");
//			} else {
//				sqrdSum += Math.pow(1-probDist.getProbOfBeingTrue(), 2);
//				count++;
//			}
//		}
//		for ( Literal lit : marginalSample.getWorldStates().get(0).getNegExamples()) {
//			ProbDistribution probDist = this.sampledProbOfExample((Example)lit);
//			if (probDist.isHasDistribution()) {
//				Utils.waitHere("Not implemented");
//			} else {
//				sqrdSum += Math.pow(probDist.getProbOfBeingTrue(), 2);
//				count++;
//			}
//		}
//		Utils.println("% Squared diff betwn MAP and EM: " + sqrdSum + "/" + count +
//				" = " + sqrdSum/(double)count);
		return marginalSample;
	}



	/**
	 * @param worldStates the worldStates to set
	 */
	public void setWorldStates(List<HiddenLiteralState> worldStates) {
		this.worldStates = worldStates;
	}



	/**
	 * @param probabilities the probabilities to set
	 */
	public void setProbabilities(List<Double> probabilities) {
		this.probabilities = probabilities;
	}



	/**
	 * @return the worldStateToIndex
	 */
	public Map<HiddenLiteralState, Integer> getWorldStateToIndex() {
		return worldStateToIndex;
	}



	/**
	 * @param worldStateToIndex the worldStateToIndex to set
	 */
	public void setWorldStateToIndex(
			Map<HiddenLiteralState, Integer> worldStateToIndex) {
		this.worldStateToIndex = worldStateToIndex;
	}



	public void buildExampleToCondProbMap(WILLSetup setup, JointRDNModel jtModel) {
		for (int j = 0; j < worldStates.size(); j++) {
			HiddenLiteralState state = worldStates.get(j);
			state.buildExampleToCondProbMap(setup, jtModel);
		}
	}
	
	/**
	 * Will pick the top k states with the highest state pseudo probabilities
	 * @param maxStates
	 */
	public void pickMostLikelyStates(int maxStates) {
		
		if (worldStates.size() < maxStates) {
			Utils.waitHere("Sampled less than max states: " + worldStates.size() + " < " + maxStates);
			return;
		}
		List<Integer> mostLikely = getMostLikelyStates(maxStates);
		
		for (int i = worldStates.size() - 1; i >=0 ; i--) {
			if (!mostLikely.contains(i)) {
				worldStates.remove(i);
				probabilities.remove(i);
			} 
		}
		
		// Rebuild map
		worldStateToIndex = new HashMap<HiddenLiteralState, Integer>();
		for (int i = 0; i < worldStates.size(); i++) {
			worldStateToIndex.put(worldStates.get(i), i);
		}
		
	}



	private List<Integer> getMostLikelyStates(int maxStates) {
		List<Double> probabilities = new LinkedList<Double>();
		List<Integer> indexes = new LinkedList<Integer>();
		for (int i = 0; i < worldStates.size(); i++) {
			double prob = worldStates.get(i).getStatePseudoProbability();
			int j = 0;
			for (j = 0; j < probabilities.size(); j++) {
				if (probabilities.get(j) < prob) {
					break;
				}
			}
			probabilities.add(j, prob);
			indexes.add(j, i);
			while (probabilities.size() > maxStates) {
				probabilities.remove(probabilities.size()-1);
				indexes.remove(indexes.size()-1);
				// probabilities = probabilities.subList(0, maxStates);
				// indexes =  indexes.subList(0, maxStates);
			}
		}
		return indexes;
	}
	
}
