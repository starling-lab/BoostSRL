package edu.iu.cs.RelationalRandomWalks;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.Arrays;
import java.util.HashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;


public class Graph {

	public HashMap<String,Edge> GraphEdges = new HashMap<String,Edge>();
	public HashMap<String,Node> GraphNodes = new HashMap<String,Node>();
	String StartEntity;
	String EndEntity;
	String DirectoryPath;
	int MaxRWLength;
	
	public int NodeId = 0;
	public int EdgeId =0;
	public boolean NodeIdIncrement=false;
		
	void ReadInputFile(String filename) throws IOException
	{
		Edge eInverse;
		BufferedReader bfRead2 = new BufferedReader(new FileReader(filename));
		String lineRead;
		
		Pattern pattern = Pattern.compile("(.*)\\((.*)\\)");
				
		while((lineRead=bfRead2.readLine())!=null)
		{
			String [] sLine = lineRead.split("\\|");
			Matcher matcher = pattern.matcher(sLine[0]);
			if (!matcher.matches()) {
				System.out.println("bad formated schema: " + sLine[0]);
			}
			else
			{
				String Relation = matcher.group(1);	
				String Entity[] = (matcher.group(2)).split(",");
						
				Node nodeArg1 = new Node(Entity[0],NodeId);
				Node nodeArg2 = new Node(Entity[1],++NodeId);
				Edge e = new Edge(Relation,EdgeId,nodeArg1,nodeArg2);
				e.isInverse = false;
				
				if(!Arrays.asList(sLine).contains("NoTwin"))
				{
					eInverse = new Edge("_"+Relation,++EdgeId,nodeArg2,nodeArg1);
					eInverse.isInverse = true;
					
					if(Arrays.asList(sLine).contains("NoBF"))
					{
						eInverse.NoForward = true;
					}
					if(Arrays.asList(sLine).contains("NoBB"))
					{
						eInverse.NoBackTwice = true;
					}
					if(Arrays.asList(sLine).contains("NoFB"))
					{
						e.NoBack = true;
					}
				}
				else
				{
					e.NoInverse = true;
					eInverse = null;
				}
					
				if(Arrays.asList(sLine).contains("NoFF"))
				{
					e.NoForwardTwice = true;
				}
				
				if(!(this.GraphNodes.containsKey(Entity[0])))
				{
					nodeArg1.OutgoingEdge.add(e);
					if(eInverse!=null)
						nodeArg1.IncomingEdge.add(eInverse);
					this.GraphNodes.put(Entity[0], nodeArg1);
							
					NodeIdIncrement = true;
					
				}
				else
				{
					this.GraphNodes.get(Entity[0]).OutgoingEdge.add(e);
					if(eInverse!=null)
					this.GraphNodes.get(Entity[0]).IncomingEdge.add(eInverse);
					
				}
							
				if(!this.GraphNodes.containsKey(Entity[1]))
				{
					nodeArg2.IncomingEdge.add(e);
					if(eInverse!=null)
						nodeArg2.OutgoingEdge.add(eInverse);
					this.GraphNodes.put(Entity[1], nodeArg2);
				
					NodeIdIncrement = true;
				}
				else
				{
					this.GraphNodes.get(Entity[1]).IncomingEdge.add(e);
					if(eInverse!=null)
					this.GraphNodes.get(Entity[1]).OutgoingEdge.add(eInverse);
					
				}
							
				if(!this.GraphEdges.containsKey(Relation))
				{
					this.GraphEdges.put(Relation, e);
					if(eInverse!=null)
						this.GraphEdges.put("_"+Relation, eInverse);
					EdgeId++;
				}
				
				if(NodeIdIncrement)
					NodeId++;
			}
			
		}
		bfRead2.close();
	
}

	
	public static void main(String[] args) {
		
		// TODO Auto-generated method stub

	}

}
