package edu.iu.cs.RelationalRandomWalks;


import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;


public class GenerateRandomWalks {
	
	HashSet<String> FinalRandomWalks = new HashSet<String>();
	HashSet<String> IntermediateRandomWalks = new HashSet<String>();
	HashSet<String> Storetriplets = new HashSet<String>();
	
	void AddStartEntity(String start)
	{
		IntermediateRandomWalks.add(start);
	}
	
	void GenerateTriplets(HashMap<String,Edge> edg)
	{
		Set<String> key = edg.keySet();
		for(String k:key)
		{
			String temp = edg.get(k).fromNode.name+"("+edg.get(k).Name+")"+edg.get(k).ToNode.name;
			Storetriplets.add(temp);
		}
	}
	
	HashMap<String,String> SplitString(String S)
	{
		String [] sLine = S.split("(\\()|(\\))");
		HashMap<String,String> hs = new HashMap<String,String>();
		hs.put("LastEntity", sLine[sLine.length-1]);
		hs.put("FirstEntity", sLine[0]);
		
		if(sLine.length-2 > 0)
		{			
			hs.put("LastRelation",sLine[sLine.length-2]);
		}
		
		return hs;
	}
		
	boolean CheckConstraints(Edge lastRW,Edge relTriplet)
	{
				
		if((lastRW.isInverse) &&(relTriplet.Name.equals(lastRW.Name)) &&(lastRW.NoBackTwice))
		{
			return true;
		}
		else if(!(lastRW.isInverse) && (relTriplet.Name.equals(lastRW.Name)) && (lastRW.NoForwardTwice))
		{
			return true;
		}
		else if((lastRW.isInverse)&&(lastRW.Name.equals("_"+relTriplet.Name))&&(lastRW.NoForward))
		{
			return true;
		}
		else if(!(lastRW.isInverse)&&(relTriplet.Name.equals("_"+lastRW.Name))&&(lastRW.NoBack))
		{
			return true;
		}
		
		return false;
	}
	
	String CreateNewRandomWalk(String oldRandomWalk,String triplet)
	{
		HashMap<String,String> hs = SplitString(triplet);
		String s = oldRandomWalk+"("+hs.get("LastRelation") + ")"+hs.get("LastEntity");
		return s;
	}
	
	void createRandomWalks(Graph graph) throws IOException
	{
		AddStartEntity(graph.StartEntity);
		GenerateTriplets(graph.GraphEdges);
					
		for(int i=0;i<=graph.MaxRWLength;i++)
		{
			if(i==0)
				continue;
			else
			{
				HashSet <String> cloneIntermediateRW = new HashSet <String>();
				cloneIntermediateRW=(HashSet)IntermediateRandomWalks.clone();
				
				for(String s:cloneIntermediateRW)
				{
					HashMap<String,String> hIntermediate = SplitString(s);
									
					for (String s2:Storetriplets)
					{
						HashMap<String,String> hTriplet = SplitString(s2);
						if((hIntermediate.get("LastEntity")).equals(hTriplet.get("FirstEntity")))
						{
							if(hIntermediate.get("LastRelation")!=null)
							{
								Edge tripletEdge = graph.GraphEdges.get(hTriplet.get("LastRelation"));
								Edge RWLastEdge = graph.GraphEdges.get(hIntermediate.get("LastRelation"));
								if(CheckConstraints(RWLastEdge,tripletEdge))
									continue;
												
							}
							String newRW = CreateNewRandomWalk(s,s2);
							HashMap<String,String> hnewRW = SplitString(newRW);
							
							if(hnewRW.get("LastEntity").equals(graph.EndEntity))
							{
								FinalRandomWalks.add(newRW);
							}
							
							IntermediateRandomWalks.add(newRW);
							
						}
					}
					IntermediateRandomWalks.remove(s);
				}
								
			}
			
		}
		
		Predicates myPredicate = new Predicates();
		myPredicate.CreatePredicatesInAlchemyFormat(FinalRandomWalks,graph.DirectoryPath);
			
	}
	
	public static void main(String[] args) {
		// TODO Auto-generated method stub

	}

}
