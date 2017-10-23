package edu.iu.cs.RelationalRandomWalks;

import java.util.HashSet;

public class Node {

	public String name;
	public int Nodeid;
	public HashSet<Edge> IncomingEdge = new HashSet<Edge>();
	public HashSet<Edge> OutgoingEdge = new HashSet<Edge>();
	
	public Node(String xname,int xNodeid)
	{
		this.name = xname;
		this.Nodeid = xNodeid;
	}
	
	
}
