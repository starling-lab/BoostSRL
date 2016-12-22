/**
 * 
 */
package edu.wisc.cs.will.Boosting.Trees;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;
import edu.wisc.cs.will.Boosting.Utils.NumberGroundingsCalculator;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.ILP.LearnOneClause;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.RegressionValueOrVector;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author tkhot
 *
 */
public class RegressionMLNModel extends RegressionTree {

	private NumberGroundingsCalculator calc;
	
	private Map<String, Long> cachedRegressionClauseWeights = null; 
	/**
	 * @param setup
	 */
	public RegressionMLNModel(WILLSetup setup) {
		super(setup);
		resetGroundingCalculator();
	}
	
	public void setCachedValues(Map<String, Long> cache) {
		cachedRegressionClauseWeights = cache;
	}
	
	public void addToCache(Clause cl, Literal eg, long val) {
		if (cachedRegressionClauseWeights == null) {
			return;
		}
		String key = getCacheKey(cl, eg);
		cachedRegressionClauseWeights.put(key, new Long(val));
	}
	private String getCacheKey(Clause cl, Literal eg) {
		return cl.toString() + ":::" + eg.toString();
	}
	public boolean inCache(Clause cl, Literal eg) {
		if (cachedRegressionClauseWeights == null) {
			return false;
		}
		String key = getCacheKey(cl, eg);
		return cachedRegressionClauseWeights.containsKey(key);
	}
	public long cachedWeight(Clause cl, Literal eg) {
		if (cachedRegressionClauseWeights == null) {
			Utils.error("No cache provided");
		}
		String key = getCacheKey(cl, eg);
		return cachedRegressionClauseWeights.get(key);
	}
	
	
	@Override
	public void setSetup(WILLSetup setup) {
		super.setSetup(setup);
		resetGroundingCalculator();
	}
	
	private void resetGroundingCalculator() {
		calc = new NumberGroundingsCalculator(setup.getContext());
	}


	@Override
	protected RegressionValueOrVector getRegressionClauseWt(Clause clause, Example ex) {
		
		if (clause.getPositiveLiterals().size() != 1) {
			Utils.error("Expected horn clause: " + clause);
		}
		Literal head = clause.getPosLiteral(0).copy(false);
		Term y = head.getArgument(head.numberArgs()-1);
		//Utils.println(head + " term " + y);
		// double value = ((NumericConstant) y).value.doubleValue();
		RegressionValueOrVector val = BoostingUtils.getRegressionValueOrVectorFromTerm(y);
		head.removeArgument(y);
		List<Literal> new_head = new ArrayList<Literal>();
		new_head.add(head);
		
		List<Literal> new_body = clause.getDefiniteClauseBody();
		//Utils.println(clause.toString());
		// remove the cut to get number of proofs
		if (new_body.size() > 0 &&
			new_body.get(new_body.size()-1).equals(setup.getHandler().cutLiteral)) {
			new_body.remove(new_body.size() - 1);
		}
		Clause cl = new Clause(setup.getHandler(), new_head, new_body);
		// Ignore the negation by failure literals as the ordering takes care
		if (calc.isOnlyInHead(cl, ex)) {
			for (int i = 0; i < new_body.size(); i++) {
				Literal lit = new_body.get(i);
				if(lit.predicateName.equals(setup.getHandler().standardPredicateNames.negationByFailure)) {
					new_body.remove(i);
					i--;
				}
			}
			if (!setup.learnClauses) {
				setBreakAfterFirstMatch(true);
			}
		} else {
			setBreakAfterFirstMatch(false);
		}

		
		cl = new Clause(setup.getHandler(), new_head, new_body);
		long num = 0;
		if (inCache(cl, ex)) {
			num=cachedWeight(cl, ex);
		} else {
			num = calc.countNumberOfNonTrivialGroundings(cl, ex);
			addToCache(cl, ex, num);
		}
		// If the clause head unifies with the example and it has no groundings, we want to evaluate the next
		// clause. So return Nan. If the example doesn't unify with the head, then it doesn't matter if we return 0 or Nan, 
		// as both will not have any impact on final regression value.
		if (num ==0) {
			return null;
		} 
		val.multiply(num);
		return val;
		
		/*
		LearnOneClause loc = setup.getInnerLooper();
		BindingList theta = loc.getUnifier().unify(head, ex);
		if (theta != null) {
			List<Literal> new_body = theta.applyTheta(clause.getDefiniteClauseBody());

			// remove the cut to get number of proofs
			if (new_body.get(new_body.size()-1).equals(setup.getHandler().cutLiteral)) {
				new_body.remove(new_body.size() - 1);
			}
			/*Utils.println(clause.toString());
			for(Clause clneg: clause.convertForProofByNegation()) {
				Utils.println("%>>" + clneg);
			}*//*
			// Ignore the negation by failure literals as the ordering takes care
			for (int i = 0; i < new_body.size(); i++) {
				Literal lit = new_body.get(i);
				if(lit.predicateName.equals(setup.getHandler().standardPredicateNames.negationByFailure)) {
					new_body.remove(i);
					i--;
				}
			}
			long num = 0;
			if (false) {
				//Clause cl = loc.getStringHandler().getClause(new_body, true);
				//num = setup.getInnerLooper().numberOfGroundings(cl, null);
			} else {
				num = calc.countGroundingsForConjunction(new_body, null);
			}
			if (num != 0) {
				ex.provenance += " + " + value + "*" + num ; 
				return value * num;
			} else { 
				return Double.NaN;
			}
		} else {
			double sum = Double.NaN;
			int index=-1;
			for (Literal negLit : clause.getNegativeLiterals()) {
				index++;
				BindingList negtheta = loc.getUnifier().unify(negLit, ex);
				if (negtheta != null) {
					List<Literal> headLits = new ArrayList<Literal>();
					headLits.add(head);
					List<Literal> newPos = negtheta.applyTheta(headLits);
					List<Literal> newNeg = negtheta.applyTheta(clause.getNegativeLiterals());
					// Ignore the unified literal
					newNeg.remove(index);
					
					// For the first iteration, let the example be part of the facts
					if (Double.isNaN(sum)) {
						setup.getContext().getClausebase().assertFact(ex);
					}
					
					//Clause newClause = new Clause(setup.getHandler(), newNeg, newPos, "");
					//long num = setup.getInnerLooper().numberOfGroundings(newClause, null);
					long num = calc.countGroundingsForConjunction(newPos, newNeg);
					
					// Retract the fact for other iterations
					if (Double.isNaN(sum)) {
						setup.getContext().getClausebase().retractAllClausesWithUnifyingBody(ex);
					}
					
					if (num > 0) {
						if (Double.isNaN(sum)) {
							sum = 0;
						} else {
							Utils.waitHere("2+ possible groundings for eg:" + ex + " in " + clause);
						}
						// Return negative value as the literal is in the body.
						// which means , setting eg to "FALSE" would have more groundings. 
						sum += -value*num;
					}
				}
			}
			return sum
		}*/

	}

}
