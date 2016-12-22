package edu.wisc.cs.will.Boosting.RDN.Models;

import java.util.ArrayList;
import java.util.Collection;

public abstract class DependencyNode {

	protected ArrayList<DependencyNetworkEdge> parents;
	protected ArrayList<DependencyNetworkEdge> children;
	private int numberForDOTGraph = -1;

	public DependencyNode() {
		parents = new ArrayList<DependencyNetworkEdge>();
		children = new ArrayList<DependencyNetworkEdge>();
	}
	
	
	public abstract String labelForDOT();
	public abstract String colorForDOT() ;
	public abstract String  textForDOT();
	public abstract boolean ignoreNodeForDOT();

	/**
	 * 
	 * @param i - the index of parent edge
	 * @return the ith parent edge 
	 */
	public DependencyNetworkEdge getParent(int i) {
		return parents.get(i);
	}

	/**
	 * 
	 * @param i - the index of child edge
	 * @return the ith child edge
	 */
	public DependencyNetworkEdge getChild(int i) {
		return children.get(i);
	}

	/**
	 * 
	 * @return the number of parents
	 */
	public int numParents() {
		return parents.size();
	}

	/**
	 * 
	 * @return the number of children
	 */
	public int numChildren() {
		return children.size();
	}

	/**
	 * 
	 * @param edge - add this edge to the dependency network as parent
	 */
	public void addParent(DependencyNetworkEdge edge) {
		parents.add(edge);
	}

	/**
	 * 
	 * @param edge - add this edge to the dependency network as child
	 */
	public void addChild(DependencyNetworkEdge edge) {
		children.add(edge);
	}

	public Collection<DependencyNetworkEdge> getParents() {
		// TODO Auto-generated method stub
		return parents;
	}

	/**
	 * @return the children
	 */
	public ArrayList<DependencyNetworkEdge> getChildren() {
		return children;
	}


	/**
	 * @return the numberForDOTGraph
	 */
	public int getNumberForDOTGraph() {
		return numberForDOTGraph;
	}


	/**
	 * @param numberForDOTGraph the numberForDOTGraph to set
	 */
	public void setNumberForDOTGraph(int numberForDOTGraph) {
		this.numberForDOTGraph = numberForDOTGraph;
	}

}