package edu.wisc.cs.will.Boosting.RDN.Models;


/**
 * @author Tushar Khot
 *
 */
public class DependencyNetworkEdge {
	private DependencyNode start;
	private DependencyNode end;
	public enum EdgeType {
		DETERMINISTIC,
		PROBABILISTIC,
	}
	
	private EdgeType edge;

	
	
	public DependencyNetworkEdge(DependencyNode start,
			DependencyNode end, EdgeType edge) {
		super();
		this.start = start;
		this.end = end;
		this.edge = edge;
	}

	/**
	 * @return the start
	 */
	public DependencyNode getStart() {
		return start;
	}

	/**
	 * @param start the start to set
	 */
	public void setStart(DependencyNode start) {
		this.start = start;
	}

	/**
	 * @return the end
	 */
	public DependencyNode getEnd() {
		return end;
	}

	/**
	 * @param end the end to set
	 */
	public void setEnd(DependencyNode end) {
		this.end = end;
	}

	/**
	 * @return the edge
	 */
	public EdgeType getEdge() {
		return edge;
	}

	/**
	 * @param edge the edge to set
	 */
	public void setEdge(EdgeType edge) {
		this.edge = edge;
	}

	public String labelForDOT() {
		// TODO Auto-generated method stub
		return "";
		//return edge.toString();
	}
	
	public String styleForDOT() { 
		switch(edge) {
		case DETERMINISTIC: return "dashed";
		case PROBABILISTIC: return "solid";
		}
		return "dotted";
	}
	public String textForDOT() {
		return "label=\"" + labelForDOT() +"\" style=" + styleForDOT();
	}
}
