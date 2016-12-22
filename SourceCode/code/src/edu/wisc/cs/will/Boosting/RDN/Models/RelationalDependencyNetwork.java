package edu.wisc.cs.will.Boosting.RDN.Models;

import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.wisc.cs.will.Boosting.RDN.JointRDNModel;
import edu.wisc.cs.will.Boosting.RDN.ConditionalModelPerPredicate;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.Boosting.RDN.Models.DependencyNetworkEdge.EdgeType;
import edu.wisc.cs.will.Boosting.RDN.Models.DependencyPredicateNode.PredicateType;
import edu.wisc.cs.will.Boosting.Utils.CommandLineArguments;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;


/**
 * @author Tushar Khot
 *
 */
public class RelationalDependencyNetwork extends DependencyNetwork {
	
	/*public static void main(String[] arg) {
		String directory="";
		WILLSetup setup = new WILLSetup();
		CommandLineArguments args = new CommandLineArguments();
		args.parseArgs(arg);
		try {
			setup.setup(args, args.getTrainDirVal(), false);
		} catch (SearchInterrupted e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		RelationalDependencyNetwork rdn = new RelationalDependencyNetwork(fullModel, setup);
	}*/
	
	// Predicate to RDN Node map
	// private HashMap<String, DependencyNode> stringRepToNode;


	// --------------------------------------
	// Cache
	// ---------------------------------------

	private HashMap<String, HashMap<PredicateType, Set<PredicateName>>> predicateToAncestorMap;
	private HashMap<String,                        Set<PredicateName>> predicateToQueryParentsMap;	
	private HashMap<String,                        Set<PredicateName>> predicateToComputedChildrenMap;

	/**
	 * Set to true, if there is any target predicate that depends on another target predicate
	 */
	private Boolean needsJointInf = null;	
	
	/**
	 * Set to true, if there is any recursive node in RDN.
	 */
	private Boolean hasRecursion = null;	

	/**
	 * 
	 * @param fullModel
	 * @param setup
	 */
	public RelationalDependencyNetwork(JointRDNModel fullModel, WILLSetup setup) {
		super();
		// This is not a cached variable
		// stringRepToNode = new HashMap<String, DependencyPredicateNode>();
		initializeRDNUsingModel(fullModel, setup);
		initializeRDNUsingPrecompute(setup);
		resetCache();
		intializeRDNBooleans();
	}
	
	/**
	 * Call this whenever a node or a link is added to the graph.
	 */
	private void resetCache() {
		predicateToAncestorMap = new HashMap<String, HashMap<PredicateType, Set<PredicateName>>>();
		predicateToQueryParentsMap = new HashMap<String, Set<PredicateName>>();
		predicateToComputedChildrenMap = new HashMap<String, Set<PredicateName>>();
	}

	/**
	 * Sets the various booleans such as hasRecursion
	 */
	private void intializeRDNBooleans() {
		// Joint Inference
		needsJointInf = false;
		for (DependencyNode node : stringRepToNode.values()) {
			DependencyPredicateNode target  = (DependencyPredicateNode)node;
			if (target.getType() == PredicateType.QUERY) {
				Collection<PredicateName> ancestors = getAncestorsOfType(target.getPredicate().name, PredicateType.QUERY);
				if (ancestors.size() > 0) {
					needsJointInf = true;
					break;
				}
			}
		}
		
		
		//Recursion
		hasRecursion = false;
		for (DependencyNode node : stringRepToNode.values()) {
			if (((DependencyPredicateNode)node).getType() == PredicateType.RECURSIVE) {
				hasRecursion = true;
				break;
			}
		}
		
		
	}

	public boolean hasRecursion() {
		if(hasRecursion == null) {
			Utils.error("hasRecursion not set.");
		}
		return hasRecursion;
	}

	public boolean isRecursive(String target) {
		return (getAncestorsOfType(target, PredicateType.RECURSIVE).size() > 0);
	}	
	public boolean needsJointInference() {
		if(needsJointInf == null) {
			Utils.error("needsJointInf not set.");
		}
		return needsJointInf;
	}	

	private void initializeRDNUsingPrecompute(WILLSetup setup) {

		HashMap<PredicateName, Set<PredicateName>> predicateToParents = new HashMap<PredicateName, Set<PredicateName>>();

		for (int i = 0; i < setup.getInnerLooper().getParser().getNumberOfPrecomputeFiles(); i++) {
			List<Sentence> sentences = setup.getInnerLooper().getParser().getSentencesToPrecompute(i);
			if (sentences == null)
				continue;
			for (Sentence sentence : sentences) {
				List<Clause> clauses = sentence.convertToClausalForm();
				if (clauses == null) {
					continue;
				}
				// Take each clause
				for (Clause clause : clauses) {
					if (!clause.isDefiniteClause()) { 
						Utils.error("Can only precompute Horn ('definite' actually) clauses.  You provided: '" + sentence + "'."); 
					}

					PredicateName pName = clause.posLiterals.get(0).predicateName;

					if (!predicateToParents.containsKey(pName)) {
						predicateToParents.put(pName, new HashSet<PredicateName>());
					}
					Set<PredicateName> parents = predicateToParents.get(pName);

					// Take parents from the body of the clause
					for (Literal lit : clause.negLiterals) {
						parents.add(lit.predicateName);
					}

				}
			}
		}
		for (Clause clause : setup.getContext().getClausebase().getBackgroundKnowledge()) {
			if (!clause.isDefiniteClause()) { 
				Utils.error("Ignoring clause: '" + clause + "'.");
				continue;
			}

			PredicateName pName = clause.posLiterals.get(0).predicateName;

			if (!predicateToParents.containsKey(pName)) {
				predicateToParents.put(pName, new HashSet<PredicateName>());
			}
			Set<PredicateName> parents = predicateToParents.get(pName);
			if (clause.negLiterals == null || clause.negLiterals.size() <= 0) {
				// Utils.println("No neg literals in clause: " + clause);
				continue;
			}
			// Take parents from the body of the clause
			for (Literal lit : clause.negLiterals) {
				parents.add(lit.predicateName);
			}
		}

		for (PredicateName pName : predicateToParents.keySet()) {
			// Facts are sometimes(LazyHornClauseBase) stored as fact(x) :- .
			// This would be interpreted as "fact" being a precompute, which is wrong. 
			// So make sure that the rule has some predicates in the body, before labelling 
			// a predicate as precompute. 
			if (predicateToParents.get(pName) != null &&
				predicateToParents.get(pName).size() > 0) {
				// Rule has non-empty body, so it is a precomputed predicate.
				getDependencyNode(pName).setType(PredicateType.COMPUTED);
				// Add links for each parent
				for (PredicateName parent : predicateToParents.get(pName)) {
					if (parent.name.contains("wumpus") || pName.name.equals("wumpus")) {
						Utils.waitHere("Adding link between " + parent + " & " + pName);
					}
					addLink(parent, pName, EdgeType.DETERMINISTIC);
				}
			}
		}
	}

	private void initializeRDNUsingModel(JointRDNModel fullModel, WILLSetup setup) {
		if (fullModel == null) {
			// No model provided. Model is only for precomputes.
			return;
		}
		for (String pname : fullModel.keySet()) {
			PredicateName predname = setup.getHandler().getPredicateName(pname);
			// Set type to query
			getDependencyNode(predname).setType(PredicateType.QUERY);
			ConditionalModelPerPredicate model = fullModel.get(pname);
			Set<PredicateName> parents = new HashSet<PredicateName>();
			model.getParentPredicates(parents);
			for (PredicateName parent : parents) {
				addLink(parent, predname, EdgeType.PROBABILISTIC);
			}
		}
	}

	public void addLink(PredicateName parent, PredicateName child, EdgeType type) {	
		// Check if we have parent node
		DependencyNode parNode = getDependencyNode(parent);
		DependencyNode chiNode = getDependencyNode(child);
		DependencyNetworkEdge edge = getDependencyEdge(parNode, chiNode, type);
		parNode.addChild(edge);
		chiNode.addParent(edge);
		resetCache();
	}

	private DependencyNetworkEdge getDependencyEdge(
			DependencyNode parNode, DependencyNode chiNode,
			EdgeType type) {
		DependencyNetworkEdge edge = new DependencyNetworkEdge(parNode, chiNode, type);
		return edge;
	}

	public DependencyPredicateNode getDependencyNode(PredicateName parent) {
		// System.out.println("stringRepToNode=" + stringRepToNode + " parent= " + parent);
		if (!stringRepToNode.containsKey(parent.name)) {
			DependencyPredicateNode newPar = new DependencyPredicateNode(parent); 
			stringRepToNode.put(parent.name, newPar);
			resetCache();
		}
		return (DependencyPredicateNode)stringRepToNode.get(parent.name);
	}

//	public void printNetworkInDOT(Writer stream) throws IOException {
//		printNetworkInDOT(stream,true);
//	}
//
//	public void printNetworkInDOT(Writer stream, boolean leaveUnusedPrecomputes) throws IOException {
//		// Number all nodes.
//		int counter=0;
//		for (DependencyPredicateNode node : predicateToRDNNodeMap.values()) {
//			String predString = node.getPredicate().toString();
//			if (predString.equals("all") ||
//				predString.equals("is")  ||
//				predString.equals("==")  ||
//				predString.equals("=")  ||
//				predString.equals("addList")  ||
//				predString.equals(">")   ||
//				predString.equals("!")   ||
//				predString.equals("member")) {
//				continue;
//			}
//			
//			if (node.getType() == PredicateType.COMPUTED &&
//				node.getChildren().isEmpty()) {
//				continue;
//			}
//			
//			node.setNumberForDOTGraph(counter++);
//		}
//		stream.write("digraph RDN{\n");
//		// Rename recursive predicates
//		for (String pname : predicateToRDNNodeMap.keySet()) {
//			DependencyNode node = predicateToRDNNodeMap.get(pname);
//			if (pname.startsWith(WILLSetup.recursivePredPrefix)) {
//				String target = pname.replace(WILLSetup.recursivePredPrefix, "");
//				DependencyNode targetNode = predicateToRDNNodeMap.get(target);
//				node.setNumberForDOTGraph(targetNode.getNumberForDOTGraph());
//			}
//			
//		}
//		
//		// For each node
//		for (String pname : predicateToRDNNodeMap.keySet()) {
//			DependencyNode node = predicateToRDNNodeMap.get(pname);
//			if (!pname.startsWith(WILLSetup.recursivePredPrefix)) {
//				if (node.getNumberForDOTGraph() != -1) {
//					stream.write(node.getNumberForDOTGraph() + "[" + node.textForDOT() + "];\n");
//				}
//			}
//			// Write edges
//			for (int i = 0; i < node.numParents(); i++) {
//				DependencyNode parent = (DependencyNode)node.getParent(i).getStart();
//				if (node.getNumberForDOTGraph() != -1 && parent.getNumberForDOTGraph() != -1) {
//					stream.write(parent.getNumberForDOTGraph() + " -> " + node.getNumberForDOTGraph() +
//							"[" +  node.getParent(i).textForDOT() + "];\n");
//				}
//			}
//		}
//		stream.write("}\n");
//	}

	public Collection<PredicateName> getQueryParents(String predicate) {
		if (!predicateToQueryParentsMap.containsKey(predicate)) {
			// Not in the cache. build the cache for node
			DependencyNode node = stringRepToNode.get(predicate);
			// Queue of ancestors
			ArrayList<DependencyNetworkEdge> ancestors_queue = new ArrayList<DependencyNetworkEdge>();
			Set<PredicateName> ancestors = new HashSet<PredicateName>();
			Set<PredicateName> nodesConsidered = new HashSet<PredicateName>();  
			// Search for ancestors
			ancestors_queue.addAll(node.getParents());
			while(!ancestors_queue.isEmpty()) {
				// Since we are looking at parents, we need source
				DependencyPredicateNode ancestor = (DependencyPredicateNode)ancestors_queue.remove(0).getStart();
				// Ignore nodes already seen.
				if (nodesConsidered.contains(ancestor.getPredicate())) {
					Utils.println("\n% getQueryParents: Already seen this ancestor: " + ancestor.getPredicate()); 
					continue;
				}
				nodesConsidered.add(ancestor.getPredicate());
				PredicateType aType = ancestor.getType();
				if (aType == PredicateType.QUERY) {
					ancestors.add(ancestor.getPredicate());
				}
				if (aType == PredicateType.COMPUTED) {
					// 	Add the parents of the ancestor, if this node is computed
					ancestors_queue.addAll(ancestor.getParents());
				}
			}
			predicateToQueryParentsMap.put(predicate, ancestors);
		}	
		return predicateToQueryParentsMap.get(predicate);
	}
	public Collection<PredicateName> getAncestorsOfType(String predicate,
			PredicateType type) {
		
		if (!predicateToAncestorMap.containsKey(predicate)) {
			// Not in the cache. build the cache for node
			DependencyNode node = stringRepToNode.get(predicate);
			if (node == null) {
				Utils.error("Doesn't contain the predicate " + predicate + " in the RDN");
			}
			// Queue of ancestors
			ArrayList<DependencyNetworkEdge> ancestors = new ArrayList<DependencyNetworkEdge>();
			HashMap<PredicateType, Set<PredicateName>> ancestorsOfType = new HashMap<PredicateType, Set<PredicateName>>();
			Set<PredicateName> nodesConsidered = new HashSet<PredicateName>();  

			// Search for ancestors
			ancestors.addAll(node.getParents());
			while(!ancestors.isEmpty()) {
				// Since we are looking at parents, we need source
				DependencyPredicateNode ancestor = (DependencyPredicateNode)ancestors.remove(0).getStart();
				// Ignore nodes already seen.
				if (nodesConsidered.contains(ancestor.getPredicate())) {
					continue;
				}
				nodesConsidered.add(ancestor.getPredicate());

				PredicateType aType = ancestor.getType();
				if (!ancestorsOfType.containsKey(aType)) {
					ancestorsOfType.put(aType, new HashSet<PredicateName>());
				}
				if (ancestorsOfType.get(aType).add(ancestor.getPredicate())) {
					// 	Add the parents of the ancestor, if this node was never seen before
					// ie if it is not already in the ancestor set, it is new.
					ancestors.addAll(ancestor.getParents());
				}
			}
			predicateToAncestorMap.put(predicate, ancestorsOfType);
		}	
		
		
		HashMap<PredicateType, Set<PredicateName>> map = predicateToAncestorMap.get(predicate);

		// We have already computed the ancestors for this node.
		if (map.containsKey(type)) {
			return map.get(type);
		}
		// No ancestors of this type found. Return empty list
		return new HashSet<PredicateName>();
	}

	public Collection<PredicateName> getPredicatesComputedFrom(String predicate) {
		if (!predicateToComputedChildrenMap.containsKey(predicate)) {
			// Not in the cache. build the cache for node
			DependencyNode node = stringRepToNode.get(predicate);
			// Queue of ancestors
			ArrayList<DependencyNetworkEdge> children_queue = new ArrayList<DependencyNetworkEdge>();
			Set<PredicateName> children = new HashSet<PredicateName>();
			Set<PredicateName> nodesConsidered = new HashSet<PredicateName>();  

			if (node != null) {
				// Search for ancestors
				children_queue.addAll(node.getChildren());
				while(!children_queue.isEmpty()) {
					// Since we are looking at children, we need dest
					DependencyPredicateNode child = (DependencyPredicateNode)children_queue.remove(0).getEnd();
					// Ignore nodes already seen.
					if (nodesConsidered.contains(child.getPredicate())) {
						continue;
					}
					nodesConsidered.add(child.getPredicate());

					PredicateType aType = child.getType();
					if (aType == PredicateType.COMPUTED) {
						children.add(child.getPredicate());
					}
					if (aType != PredicateType.QUERY) {
						children_queue.addAll(child.getChildren());
					}
				}
			}
			predicateToComputedChildrenMap.put(predicate, children);
		}	
		return predicateToComputedChildrenMap.get(predicate);
	}

}
