package edu.wisc.cs.will.Boosting.RDN.Models;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.wisc.cs.will.Boosting.RDN.ConditionalModelPerPredicate;
import edu.wisc.cs.will.Boosting.RDN.JointRDNModel;
import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.Boosting.RDN.Models.DependencyExampleNode.ExampleType;
import edu.wisc.cs.will.Boosting.RDN.Models.DependencyNetworkEdge.EdgeType;
import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.Utils.Utils;

public class GroundDependencyNetwork extends DependencyNetwork {

	private Map<String, List<RegressionRDNExample>> jointExamples;
	
	private boolean undirectedMLNModel = false;
	
	private Set<String> queryExampleStr;
	private WILLSetup willSetup = null;
	private int numExamples = 0;
	public GroundDependencyNetwork(WILLSetup setup, Map<String, List<RegressionRDNExample>> queryExamples) {
		super();
		this.jointExamples = queryExamples;
		this.willSetup     = setup;
		this.queryExampleStr = new HashSet<String>();
	}
	
	public void buildNetwork(JointRDNModel jointModel) {
		numExamples = 0;
		// Before creating the graph, create nodes for the query examples to ensure that
		// the query nodes contains regressionRDNExamples
		for (String predicate : jointExamples.keySet()) {
			for (RegressionRDNExample example : jointExamples.get(predicate)) {
				// Add the node for this example without any parents
				getExampleNode(example, ExampleType.QUERY);
				
				if (!queryExampleStr.add(example.toString())) {
					Utils.error("Repeated example:" + example.toString());
				}
				numExamples++;
			}
		}
		
		// Go through each example and find the dependencies
		for (String predicate : jointExamples.keySet()) {
			// Check if we have a model for the predicate
			ConditionalModelPerPredicate condModel = jointModel.get(predicate);
			if (condModel == null) { Utils.error("No model for predicate: " + predicate);}
				
			for (RegressionRDNExample example : jointExamples.get(predicate)) {	
				// Pass the other query examples, so that model may return only the query parent examples
				Set<Literal> parent = condModel.getGroundParents(example, jointExamples);
				for (Literal parentLit : parent) {
					if (jointExamples.containsKey(parentLit.predicateName.name)) {
						if (willSetup.getMulticlassHandler().isMultiClassPredicate(parentLit.predicateName.name)) {
							parentLit = parentLit.copy(true);
							willSetup.getMulticlassHandler().removeConstants(parentLit);
						}
						addParentExample(example, parentLit);	
					}
					
				}
			}
		}
		// Add edges from predicate("const1", "const2") to predicate("const1", ?var) 
		introduceEdgesFromGroundtoVariableNodes();
		Utils.println("#Examples in ground network=" + numExamples + "\n #Nodes=" + stringRepToNode.size());
	}
	
	public void introduceEdgesFromGroundtoVariableNodes() {
		// Check for each node
		for (String rep : stringRepToNode.keySet()) {
			DependencyExampleNode genNode = (DependencyExampleNode)stringRepToNode.get(rep);
			Literal genLit = genNode.getExample();
			// If grounded, then it can't generalize any other node
			if (!genLit.isGrounded()) {
				for (DependencyNode possibleSpecNode : stringRepToNode.values()) {
					if (possibleSpecNode == genNode) { continue; }
					Literal specLiteral = ((DependencyExampleNode)possibleSpecNode).getExample();
					BindingList bl = willSetup.getInnerLooper().getUnifier().unify(genLit, specLiteral);
					// Only add edge if they unify
					if (bl != null) {
						// Since unifier returns a bindinglist if genLit generalizes specLiteral or vice versa,
						// we need to make sure to add edge only if genLit generalizes specLiteral
						Literal lit = genLit.applyTheta(bl);
						if (lit.equals(specLiteral)) {
							addEdge(possibleSpecNode, genNode, EdgeType.DETERMINISTIC);
						}
					}
				}	
			}
		}
	}
	
	public void calculateNumberofComponents(List<Map<String, List<RegressionRDNExample>>> examplesPerComponent) {
		Set<String> seenLiterals = new HashSet<String>();
		int numOfComponents = 0;
		int totalSize = 0;
		int totalExamples=0;
		for (String litRep: queryExampleStr) {
			if (seenLiterals.contains(litRep)) {
				continue;
			}
			List<DependencyNode> nodeStack = new ArrayList<DependencyNode>();
			nodeStack.add(stringRepToNode.get(litRep)) ;
			int stackIndex = 0;
			int compSize = 0;
		//	System.out.println("Starting next component");
			while(nodeStack.size() > stackIndex) {
				DependencyNode pop = nodeStack.get(stackIndex);
				Literal nodeLit = ((DependencyExampleNode)pop).getExample();
				String nodeLitRep = nodeLit.toString();
				stackIndex++;
				if (nodeLit.isGrounded()) {
					// This node/literal is a ground evidence literal. So we do not depend on its parents/children
					// in the ground network
					if (!queryExampleStr.contains(nodeLitRep)) {
						continue;
					} else {
						if (examplesPerComponent != null) {
							if (examplesPerComponent.size() <= numOfComponents) {
								examplesPerComponent.add(new HashMap<String, List<RegressionRDNExample>>());
							}
							String predName = nodeLit.predicateName.name;
							if (predName.startsWith(WILLSetup.multiclassPredPrefix)) { predName = predName.substring(WILLSetup.multiclassPredPrefix.length());}
							
							Map<String, List<RegressionRDNExample>> compEgs = examplesPerComponent.get(numOfComponents);
							if (!compEgs.containsKey(predName)) {
								compEgs.put(predName, new ArrayList<RegressionRDNExample>());
							}
							if (nodeLit instanceof RegressionRDNExample) {
								compEgs.get(predName).add((RegressionRDNExample)nodeLit);
							} else {
								Utils.error("Expected example to be of type RegressionRDNExample: " + nodeLit.toString());
							}
						}
						totalExamples++;
					}
					compSize++;
				}

				
				if (seenLiterals.contains(nodeLitRep)) {
					Utils.error("Examples already seen: " + nodeLitRep);
				} else {
				//	System.out.println("Adding: " + nodeLitRep);
					seenLiterals.add(nodeLitRep);
				}
				
				for (int i = 0; i < pop.numChildren(); i++) {
					DependencyNode newNode = pop.getChild(i).getEnd();
					//String newLitRep = ((DependencyExampleNode)newNode).getExample().toString();
					if (!nodeStack.contains(newNode)) {
						nodeStack.add(newNode);
					}
				}

				for (int i = 0; i < pop.numParents(); i++) {
					DependencyNode newNode = pop.getParent(i).getStart();
					//String newLitRep = ((DependencyExampleNode)newNode).getExample().toString();
					if (!nodeStack.contains(newNode)) {
						nodeStack.add(newNode);
					}
				}

			}
			numOfComponents++;
			// if (compSize > 1) { Utils.println("Size of component: " + compSize);}
			totalSize += compSize;
		}
		Utils.println("Num of components: " + numOfComponents);
		Utils.println("Average size: " + ((double)totalSize/(double)numOfComponents));
		if (numExamples != totalExamples) { Utils.waitHere("Mismatch in number of examples. Expected=" + numExamples + " QueryNodes=" + totalExamples);}
	}

	private void addParentExample(RegressionRDNExample example,
			Literal parentLit) {
		DependencyNode node = getExampleNode(example, null);
		DependencyNode pNode = getExampleNode(parentLit, null);
		addEdge(pNode, node, EdgeType.PROBABILISTIC);
		if (isUndirectedMLNModel()) {
			addEdge(node, pNode, EdgeType.PROBABILISTIC);
		}

	}

	private DependencyNode getExampleNode(Literal parentLit, ExampleType type) {
		
		// If type is null, guesss the type based on literal
		if (type == null) {
			if (!parentLit.isGrounded()) {
				type = ExampleType.VARIABLIZED;
			} else {
				if (parentLit.predicateName.name.startsWith(WILLSetup.recursivePredPrefix)) {
					type = ExampleType.RECURSIVE;
				} else {
					type = ExampleType.EVIDENCE;
				}
			}
		}
		String litStr = parentLit.toString();
		
		if (!stringRepToNode.containsKey(litStr)) {
			DependencyExampleNode node = new DependencyExampleNode(parentLit, type);
			stringRepToNode.put(litStr, node);
			return node;
		}
		return stringRepToNode.get(litStr);
	}

	private void addEdge(DependencyNode pNode, DependencyNode node,
			EdgeType type) {
		DependencyNetworkEdge dnEdge = new DependencyNetworkEdge(pNode, node, type);
		node.addParent(dnEdge);
		pNode.addChild(dnEdge);
	}

	/**
	 * @return the undirectedMLNModel
	 */
	public boolean isUndirectedMLNModel() {
		return undirectedMLNModel;
	}

	/**
	 * @param undirectedMLNModel the undirectedMLNModel to set
	 */
	public void setUndirectedMLNModel(boolean undirectedMLNModel) {
		this.undirectedMLNModel = undirectedMLNModel;
	}
}
