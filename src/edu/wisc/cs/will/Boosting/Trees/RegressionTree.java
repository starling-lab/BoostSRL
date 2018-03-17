package edu.wisc.cs.will.Boosting.Trees;


import edu.wisc.cs.will.ResThmProver.HornClausebase;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.sun.org.apache.bcel.internal.generic.INSTANCEOF;

import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.FOPC.AllOfFOPC;
import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.ConnectedSentence;
import edu.wisc.cs.will.FOPC.Constant;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.ILP.LearnOneClause;
import edu.wisc.cs.will.Utils.VectorStatistics;

public class RegressionTree extends ClauseBasedTree {

	// Meta information about each clause. For e.g. # +ve examples
	// Used for one class classification
	private ArrayList<ClauseMetaInformation> clauseMeta; 

	public static final String NOT_PREFIX = "\\+";


	public RegressionTree(WILLSetup setup) {
		super(setup);
	} 

	/**
	 * This function adds the predicates that are used in this tree ie
	 * the parents for the head predicate.
	 * @param preds - Adds the parent predicate to this collection
	 * Duplicate detection is responsibility of the caller
	 */
	public void getParentPredicates(Collection<PredicateName> preds) {
		for (Clause cl : regressionClauses) {

			if (cl == null || cl.negLiterals == null)
				continue;
			//Utils.println(cl.toString());
			// Body literals
			for(Literal lit: cl.negLiterals) {
				if (lit instanceof Sentence) { 
					//Utils.println(lit + " isa sentence");
					Sentence sent = lit;
					if (sent instanceof ConnectedSentence) {
						//Utils.println(lit + " isa conn sentence");
						ConnectedSentence cSent = (ConnectedSentence)sent;
						addToPredicates(cSent.getSentenceA(), preds);
						addToPredicates(cSent.getSentenceB(), preds);
					} else {
						addToPredicates(sent, preds);
					}
				} else {				
					//Utils.println(lit.predicateName.toString());
					preds.add(lit.predicateName);
				}

			}
		}
	}

	private void addToPredicates(Sentence sentenceA,
			Collection<PredicateName> preds) {
		if(sentenceA == null) {
			return;
		}
		for (Literal lit : sentenceA.getNegatedQueryClause().negLiterals) {
			preds.add(lit.predicateName);
		}
	}


	/**
	 * @param addLeafIdToProvenance the addLeafIdToProvenance to set
	 */
	public void setAddLeafId(boolean addLeafIdToProvenance) {
		this.addLeafId = addLeafIdToProvenance;
	}

	public Set<Literal> getGroundParents(RegressionRDNExample example,
			Map<String, List<RegressionRDNExample>> jointExamples) {
		Set<Literal> groundParents = new HashSet<Literal>();
		for (Clause clause : regressionClauses) {
			// Remove the regression value argument
			Literal head = clause.getDefiniteClauseHead();
			Literal new_head_lit = head.copy(false);
			Term    y    = new_head_lit.getArgument(new_head_lit.numberArgs() - 1);
			new_head_lit.removeArgument(y);
			
			
			// 
			Unifier unifier = setup.getInnerLooper().getUnifier();
			BindingList headBl = unifier.unify(new_head_lit, example);
			
			
			List<BindingList> possibleBindings = new ArrayList<BindingList>();
			possibleBindings.add(headBl);
			List<Literal> body = clause.getDefiniteClauseBody();
			for (Literal bodyLit : body) {
				// Check for the predicate being present as a query predicate
				String predName = bodyLit.predicateName.name;
				if (predName.startsWith(WILLSetup.recursivePredPrefix)) { predName = predName.substring(WILLSetup.recursivePredPrefix.length()); }
				if (predName.startsWith(WILLSetup.multiclassPredPrefix)) { predName = predName.substring(WILLSetup.multiclassPredPrefix.length()); }
				if (jointExamples.containsKey(predName)) {
					
					// If it is a query predicate, get all the ground literals
					for (BindingList bl : possibleBindings) {
						Literal groundParent = bodyLit.applyTheta(bl);
						// Make sure the variable naming is uniform across all parents
						int varIndex = 1;
						int termIndex = 0;
						for (Term term : groundParent.getArguments()) {
							if (!term.isGrounded()) {
								Variable newVar = setup.getHandler().getExternalVariable(term.getTypeSpec(), setup.getHandler().getVariablePrefix() + "Var" + (varIndex++), false);
								groundParent.setArgument(termIndex, newVar);
							}
							termIndex++;
						}
						groundParents.add(groundParent);
					}
				} else {

					HornClausebase factBase = setup.getContext().getClausebase();
					List<BindingList> newBLs = new ArrayList<BindingList>();
					for (BindingList bl : possibleBindings) {
						//System.out.println("Getting facts matching: " + bodyLit + " with bl: " + bl);
						Literal groundLit = bodyLit.applyTheta(bl);
						Iterable<Literal> matchingFacts = factBase.getPossibleMatchingFacts(groundLit, null);
						if (matchingFacts != null && matchingFacts.iterator().hasNext()) {
							for (Literal fact : matchingFacts) {
								BindingList factBL  = setup.getInnerLooper().getUnifier().unify(fact, groundLit);
								// The facts sometimes doesn't match the actual input
								if (factBL == null) { continue;}
								//if (factBL == null)  { Utils.error("Fact: " + fact + " doesn't match the input lit: " + groundLit);}
								//System.out.println("Got fact:"  + fact);
								factBL.addBindings(bl);
								newBLs.add(factBL);
							}
						}
					}
					possibleBindings = newBLs;
				}
			}
		}
		return groundParents;
	}
	
	public static class ClauseMetaInformation {
		public int numPos=0;
		public int numExs=0;
		
		public ClauseMetaInformation(String readFrom) {
			String[] parts=readFrom.split(":");
			numPos = Integer.parseInt(parts[0]);
			numExs = Integer.parseInt(parts[1]);
		}
		
		public String toString() {
			return numPos + ":" + numExs;
		}
		
		
	}
}
