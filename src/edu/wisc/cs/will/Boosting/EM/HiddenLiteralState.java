/**
 * 
 */
package edu.wisc.cs.will.Boosting.EM;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import edu.wisc.cs.will.Boosting.Common.SRLInference;
import edu.wisc.cs.will.Boosting.MLN.MLNInference;
import edu.wisc.cs.will.Boosting.RDN.JointRDNModel;
import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.RDN.SingleModelSampler;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.Utils;

/**
 * Class to store one world state
 * @author tkhot
 *
 */
public class HiddenLiteralState {
	/**
	 * Hash maps from predicate name to literals and their assignments in this world state
	 * Can't rely on the "sampledState" within each example as that may keep changing.
	 * Used Integer instead of Boolean. For multi-class examples, it indicates the index of 
	 * the class label.
	 */
	private Map<String, List<RegressionRDNExample>> predNameToLiteralMap;
	private Map<String, List<Integer>> predNameToAssignMap;
	
	// Cache the string representation of literal to assignment map;
	private Map<String, Integer> literalRepToAssignMap = null;
	private Map<String, ProbDistribution> literalRepToCondDistrMap = null;
	private List<Literal> trueFacts = null;
	private List<Literal> falseFacts = null;

	private double statePseudoProbability  = 1;
	
	public HiddenLiteralState(List<RegressionRDNExample> groundLits) {
		predNameToLiteralMap = new HashMap<String, List<RegressionRDNExample>>();
		for (RegressionRDNExample lit : groundLits) {
			String predName = lit.predicateName.name;
			if (!predNameToLiteralMap.containsKey(predName)) {
				predNameToLiteralMap.put(predName, new ArrayList<RegressionRDNExample>());
			}
			predNameToLiteralMap.get(predName).add(lit);
		}
		initAssignment();
	}
	public HiddenLiteralState(Map<String, List<RegressionRDNExample>> jointExamples, Map<String, List<Integer>> assignment) {
		predNameToLiteralMap = new HashMap<String, List<RegressionRDNExample>>(jointExamples);
		predNameToAssignMap = new HashMap<String, List<Integer>>(assignment);
	}
	public HiddenLiteralState(Map<String, List<RegressionRDNExample>> jointExamples) {
		predNameToLiteralMap = new HashMap<String, List<RegressionRDNExample>>(jointExamples);
		initAssignment();
	}

	public void addNewExamplesFromState(HiddenLiteralState newState) {
		for (String newPred : newState.predNameToLiteralMap.keySet()) {
			if (!this.predNameToLiteralMap.containsKey(newPred)) {
				this.predNameToLiteralMap.put(newPred, new ArrayList<RegressionRDNExample>());
				this.predNameToAssignMap.put(newPred, new ArrayList<Integer>());
			}
			List<RegressionRDNExample> newExamples = newState.predNameToLiteralMap.get(newPred);
			for (int i = 0; i < newExamples.size(); i++) {
				this.predNameToLiteralMap.get(newPred).add(newExamples.get(i));
				this.predNameToAssignMap.get(newPred).add(newState.predNameToAssignMap.get(newPred).get(i));
			}
		}
	}
	
	public void initAssignment() {
		predNameToAssignMap = new HashMap<String, List<Integer>>();
		for (String predName : predNameToLiteralMap.keySet()) {
			for (RegressionRDNExample lit : predNameToLiteralMap.get(predName)) {
				if (!predNameToAssignMap.containsKey(predName)) {
					predNameToAssignMap.put(predName, new ArrayList<Integer>());
				}
				predNameToAssignMap.get(predName).add(lit.getSampledValue());
			}
		}
	}
	
	
	public String toPrettyString() {
		StringBuilder sb = new StringBuilder();
		for (String predName : predNameToLiteralMap.keySet()) {
			for (int i = 0; i < predNameToLiteralMap.get(predName).size(); i++) {
				sb.append(predNameToLiteralMap.get(predName).get(i).toPrettyString(""));
				sb.append(":");
				sb.append(predNameToAssignMap.get(predName).get(i));
				sb.append("\n");
			}
		}
		return sb.toString();
	}
	/**
	 * Mainly for debugging
	 * @return
	 */
	public double percentOfTrues() {
		long numTrue = 0;
		long total = 0;
		for (String key : predNameToAssignMap.keySet()) {
			for (Integer val : predNameToAssignMap.get(key)) {
				if (val == 1) {
					numTrue++;
				}
				total++;
			}
		}
		return (double)numTrue/(double)total;
	}
	
	public HiddenLiteralState marginalizeOutPredicate(String predicate) {
		HiddenLiteralState marginState = new HiddenLiteralState(this.predNameToLiteralMap, this.predNameToAssignMap);
		marginState.predNameToLiteralMap.remove(predicate);
		marginState.predNameToAssignMap.remove(predicate);
		return marginState;
	}
	
	@Override
	public int hashCode()  {
		return getStringRep().hashCode();
	}
	
	
	@Override
	public boolean equals(Object obj) {
		if (obj == null) { return false;}
		if (! (obj instanceof HiddenLiteralState)) {
			return false;
		}
		HiddenLiteralState other = (HiddenLiteralState)obj;
		String otherRep = other.getStringRep();
		String rep = this.getStringRep();
		return otherRep.equals(rep);
	}
	
	public String getStringRep() {
		// Generate string that can uniquely determine this world state
		// Note we assume that all world states use the same order of literals for a given predicate
		StringBuilder rep = new StringBuilder();
		for (String key : predNameToAssignMap.keySet()) {
			rep.append(key +":");
			/*for (Boolean bool : predNameToAssignMap.get(key)) {
				rep.append(bool?"1":"0");
			}*/
			for (Integer val : predNameToAssignMap.get(key)) {
				rep.append(val);
			}
			rep.append(".");
		}
		return rep.toString();
	}

	public Set<String> getPredicates() {
		return predNameToLiteralMap.keySet();
	}
	
	public void buildLiteralToAssignMap() {
		literalRepToAssignMap = new HashMap<String, Integer>();
		for (String predName : predNameToLiteralMap.keySet()) {
			for (int i = 0; i < predNameToLiteralMap.get(predName).size(); i++) {
				String litRep = predNameToLiteralMap.get(predName).get(i).toPrettyString("");
				Integer assign = predNameToAssignMap.get(predName).get(i);
				literalRepToAssignMap.put(litRep, assign);
			}
		}
	}
	
	public Integer getAssignment(Example eg) {
		// Compare string rep
		String egRep =  eg.toString();
				
		if (literalRepToAssignMap != null) {
			if (literalRepToAssignMap.get(egRep) == null) { 
				Utils.waitHere("Example: " + eg + " not stored in cached worldState");
			}
			return literalRepToAssignMap.get(egRep);
		}
		String pred = eg.predicateName.name;
		List<RegressionRDNExample> litList = predNameToLiteralMap.get(pred);
		
		for (int i = 0; i <  litList.size(); i++) {
			String thisRep = ((Example)litList.get(i)).toString(); 
			if (egRep.equals(thisRep)) {
				return predNameToAssignMap.get(pred).get(i);
				/*if (predNameToAssignMap.get(pred).get(i)) {
					return true;
				} else {
					return 0;
				}*/
			}
		}
		Utils.waitHere("Example: " + eg + " not stored in worldState");
		return 0;
	}
	
	/*public boolean isTrue(Example eg) {
		// Compare string rep
		String egRep =  eg.toString();
				
		if (literalRepToAssignMap != null) {
			if (literalRepToAssignMap.get(egRep) == null) { 
				Utils.waitHere("Example: " + eg + " not stored in cached worldState");
			}
			return literalRepToAssignMap.get(egRep) == Boolean.TRUE;
		}
		String pred = eg.predicateName.name;
		List<RegressionRDNExample> litList = predNameToLiteralMap.get(pred);
		
		for (int i = 0; i <  litList.size(); i++) {
			String thisRep = ((Example)litList.get(i)).toString(); 
			if (egRep.equals(thisRep)) {
				if (predNameToAssignMap.get(pred).get(i)) {
					return true;
				} else {
					return false;
				}
			}
		}
		Utils.waitHere("Example: " + eg + " not stored in worldState");
		return false;
	}*/
	
	
	public Iterable<Literal> getPosExamples() {
		return new ExampleIterable(this, 1);
	}
	
	public Iterable<Literal> getNegExamples() {
		return new ExampleIterable(this, 0);
	}
	

	public static class ExampleIterable implements Iterable<Literal> {

		HiddenLiteralState state;
		Integer match;
		public ExampleIterable(HiddenLiteralState state, Integer match) {
			this.state = state;
			this.match = match;
		}
		@Override
		public Iterator<Literal> iterator() {
			return new ExampleIterator(state, match);
		}
		
	}
	
	public static class ExampleIterator implements Iterator<Literal> {

		Iterator<String> predKeyIterator;
		String currentPred;
		int exampleIndex;
		HiddenLiteralState state;
		Integer matchState;
		boolean gotoNext;
		public ExampleIterator(HiddenLiteralState state, Integer match) {
			this.state = state;
			matchState = match;
			predKeyIterator = state.predNameToLiteralMap.keySet().iterator();
			currentPred = predKeyIterator.next();
			exampleIndex = -1;
			gotoNext = true;
		}

		@Override
		public boolean hasNext() {
			// Already called hasNext
			if (!gotoNext) {
				return currentPred != null;
			} else {
				if (updateToNextMatchingLiteral()) {
					gotoNext = false;
					return true;
				} else {
					gotoNext = false;
					return false;
				}
			}
			
		}
		
		public boolean updateToNextMatchingLiteral() {
			// hasNext has already updated the index for the next literal.
			if (!gotoNext) {
				return true;
			}
			do {
				List<RegressionRDNExample> egs = state.predNameToLiteralMap.get(currentPred);
				for (int i = exampleIndex+1; i < egs.size(); i++) {
					if (egs.get(i).isHasRegressionVector()) {
						// Mutli-class examples always stored as positive examples
						if (matchState == 1) {
							exampleIndex = i;
							return true;
						}
					} else {
						if (state.predNameToAssignMap.get(currentPred).get(i) == matchState) {    
							exampleIndex = i;
							return true;
						}
					}
				}
				exampleIndex  = -1;
				if (predKeyIterator.hasNext()) { 
					currentPred = predKeyIterator.next();
				} else {
					currentPred = null;
				}
			} while(currentPred != null);
			
			return false;
		}

		@Override
		public Literal next() {
			if (updateToNextMatchingLiteral()) {
				gotoNext = true;
				return state.predNameToLiteralMap.get(currentPred).get(exampleIndex);
			}
			throw new NoSuchElementException();
		}

		@Override
		public void remove() {
			state.predNameToLiteralMap.get(currentPred).remove(exampleIndex);
			state.predNameToAssignMap.get(currentPred).remove(exampleIndex);
			
		}
		
	}

	public void buildExampleToCondProbMap(WILLSetup setup, JointRDNModel jtModel) {
		
		if (literalRepToAssignMap == null) {
			Utils.error("Make sure to call buildLiteralToAssignMap before this method call");
		}
		literalRepToCondDistrMap = new HashMap<String, ProbDistribution>();
		statePseudoProbability   = 1;
		SRLInference.updateFactsFromState(setup, this);
		for (String predName : predNameToLiteralMap.keySet()) {
			SRLInference sampler = null;
			if (setup.useMLNs) {
				sampler = new MLNInference(setup, jtModel);
			} else {
				// Since we are only calculating the conditional probabilities given all the other assignments
				// to the hidden states as facts, we do not need to worry about recursion (last arg).
				sampler= new SingleModelSampler(jtModel.get(predName), setup, jtModel, false);
			}
			List<RegressionRDNExample> literalList = predNameToLiteralMap.get(predName);
			// Create a new list since we modify the example probabilities
			List<RegressionRDNExample> newList = new ArrayList<RegressionRDNExample>();
			for (RegressionRDNExample rex : literalList) {
				newList.add(new RegressionRDNExample(rex));
			}
			sampler.getProbabilities(newList);

			for (RegressionRDNExample newRex : newList) {
				ProbDistribution distr = newRex.getProbOfExample();
				/*if (newRex.predicateName.name.contains("thal")) {
					if (!distr.isHasDistribution()) {
						Utils.waitHere("TEMP: Expected multi class example: " + newRex.toString());
					}
				}*/
				String rep = newRex.toPrettyString("");
				literalRepToCondDistrMap.put(rep, distr);
				if (!literalRepToAssignMap.containsKey(rep)) {
					Utils.error("No assignment for: " + rep);
				}
				statePseudoProbability *= distr.probOfTakingValue(literalRepToAssignMap.get(rep));
				//System.out.println(statePseudoProbability);
				//if (statePseudoProbability == 0.0) { Utils.waitHere("Zero state prob after " + rep + " with " + distr + " for " + literalRepToAssignMap.get(rep)); }
			}
		} 
		
		
	}
	
	
	public void updateStateFacts(WILLSetup setup) {
		trueFacts = new ArrayList<Literal>();
		falseFacts=new ArrayList<Literal>();
		for (Literal posEx : getPosExamples()) {

			if (posEx.predicateName.name.startsWith(WILLSetup.multiclassPredPrefix)) {
				RegressionRDNExample mcRex = (RegressionRDNExample)posEx;
				int maxVec = mcRex.getOutputVector().length;
				int assign = getAssignment((Example)posEx);
				if (assign < 0 || assign >= maxVec) { Utils.waitHere("Assignment: " + assign + " not within bound: " + maxVec);}
				for (int i = 0; i < maxVec; i++) {
					Example eg =  setup.getMulticlassHandler().createExampleFromClass(mcRex, i);
					if (i == assign) {
						trueFacts.add(eg);
						if (setup.allowRecursion) {
							Literal lit = setup.getHandler().getLiteral(setup.getHandler().getPredicateName(
									WILLSetup.recursivePredPrefix + eg.predicateName.name), eg.getArguments());
							trueFacts.add(lit);

						}
					} else {
						falseFacts.add(eg);
						if (setup.allowRecursion) {
							Literal lit = setup.getHandler().getLiteral(setup.getHandler().getPredicateName(
									WILLSetup.recursivePredPrefix + eg.predicateName.name), eg.getArguments());
							falseFacts.add(lit);

						}
					}
				}
			} else {
				trueFacts.add(posEx);
				if (setup.allowRecursion) {
					Literal lit = setup.getHandler().getLiteral(setup.getHandler().getPredicateName(
							WILLSetup.recursivePredPrefix + posEx.predicateName.name), posEx.getArguments());
					trueFacts.add(lit);
				}
			}
		}
		for (Literal negEx : getNegExamples()) {
			falseFacts.add(negEx);
			if (setup.allowRecursion) {
				Literal lit = setup.getHandler().getLiteral(setup.getHandler().getPredicateName(
						WILLSetup.recursivePredPrefix + negEx.predicateName.name), negEx.getArguments());
				falseFacts.add(lit);
			}
		}
	}
	
	/**
	 * @return the statePseudoProbability
	 */
	public double getStatePseudoProbability() {
		return statePseudoProbability;
	}
	/**
	 * @param statePseudoProbability the statePseudoProbability to set
	 */
	public void setStatePseudoProbability(double statePseudoProbability) {
		this.statePseudoProbability = statePseudoProbability;
	}
	
	public ProbDistribution getConditionalDistribution(Literal ex) {
		String rep  = ex.toPrettyString("");
		if (literalRepToCondDistrMap == null) {
			Utils.error("Conditional distribution not set.");
		}
		if (!literalRepToCondDistrMap.containsKey(rep)) {
			Utils.error("Example: " + rep + " unseen in the hidden state");
		}
		return literalRepToCondDistrMap.get(rep);
	}
	
	
	public static void statePredicateDifference(HiddenLiteralState lastState, 
												HiddenLiteralState newState,
												Set<PredicateName> modifiedPredicates,
												String target) {
		if (newState == null) { 
			Utils.waitHere("newState not expected to be null. Will not update the facts.");
			return;
		}
		if (newState.trueFacts == null) {
			Utils.error("Expected the true facts for this state to be built.");
		}
		
		for (Literal addLit : newState.trueFacts) {
			// We know its modified, no need to check it.
			if (modifiedPredicates.contains(addLit.predicateName)) {
				continue;
			}
			// Do not add facts for the target predicate
			if (addLit.predicateName.name.equals(target)) {
				continue;
			}
			if (lastState == null) {
				modifiedPredicates.add(addLit.predicateName);
			} else {
				boolean addThisLit = true;
				String addLitRep = addLit.toString();
				for (Literal oldStateLit : lastState.trueFacts) {
					// If true in the last state, no need to add
					if (oldStateLit.toString().equals(addLitRep)) {
						addThisLit = false;
						break;
					}
				}
				if (addThisLit) {
					modifiedPredicates.add(addLit.predicateName);
				}
			}
		}
		
		for (Literal rmLit : newState.falseFacts) {
			// We know its modified, no need to check it.
			if (modifiedPredicates.contains(rmLit.predicateName)) {
				continue;
			}
			// Do not rm facts for the target predicate
			if (rmLit.predicateName.name.equals(target)) {
				continue;
			}
			if (lastState == null) {
				modifiedPredicates.add(rmLit.predicateName);
			} else {
				boolean rmThisLit = true;
				String rmLitRep = rmLit.toString();
				for (Literal oldStateLit : lastState.falseFacts) {
					// If true in the last state, no need to add
					if (oldStateLit.toString().equals(rmLitRep)) {
						rmThisLit = false;
						break;
					}
				}
				if (rmThisLit) {
					modifiedPredicates.add(rmLit.predicateName);
				}
			}
		}
	}
	/**
	 * Returns the examples that need to be added/removed from the fact base to move from
	 * lastState to newstate
	 * @param lastState Old assignment of facts
	 * @param newState New assignment of facts
	 * @param addExamples Facts to be added
	 * @param rmExamples Facts to be removed
	 */
	public static void stateDifference(HiddenLiteralState lastState,
									   HiddenLiteralState newState,
									   List<Literal> addExamples,
									   List<Literal> rmExamples,
									   String target) {
		if (newState == null) { 
			Utils.waitHere("newState not expected to be null. Will not update the facts.");
			return;
		}
		if (newState.trueFacts == null) {
			Utils.error("Expected the true facts for this state to be built.");
		}
		
		for (Literal addLit : newState.trueFacts) {
			// Do not add facts for the target predicate
			if (addLit.predicateName.name.equals(target)) {
				rmExamples.add(addLit);
				continue;
			}
			if (lastState == null) {
				addExamples.add(addLit);
			} else {
				boolean addThisLit = true;
				String addLitRep = addLit.toString();
				for (Literal oldStateLit : lastState.trueFacts) {
					// If true in the last state, no need to add
					if (oldStateLit.toString().equals(addLitRep)) {
						addThisLit = false;
						break;
					}
				}
				if (addThisLit) {
					addExamples.add(addLit);
				}
			}
		}
		
		// If no last state, not sure which facts are true. Hence remove all
		// Actually might be faster to remove all the lits rather than check the last state
//		if (lastState == null) {

		rmExamples.addAll(newState.falseFacts);

		//		} else {
//			// Since there can be many false facts in newstate, only check for the ones that were  true in the last state
//			for (Literal rmLit : lastState.trueFacts) {
//				String rmLitRep = rmLit.toString();
//					boolean rmThisLit = true;
//			
//				}
//			}
//		}
		
//		for (String predName : newState.predNameToLiteralMap.keySet()) {
//			int index = 0;
//			for (Literal literal : newState.predNameToLiteralMap.get(predName)) {
//				int newAssignment = newState.predNameToAssignMap.get(predName).get(index);
//				if (lastState != null) {
//					// Debugging
//					Literal lastStateLiteral = lastState.predNameToLiteralMap.get(predName).get(index);
//					if (lastStateLiteral.toString().equals(literal.toString())) {
//						Utils.error("Example mismatch between world states. LastState example: " + lastStateLiteral + ". NewState example: " + literal);
//					}
//					int lastAssignment = lastState.predNameToAssignMap.get(predName).get(index);
//					// Need to add/remove this example, if mismatch in assignment
//					if (lastAssignment != newAssignment) {
//						
//					}
//				}
//				
//				index++;
//			}
//		}
//		
	}
}


