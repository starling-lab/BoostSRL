package edu.iu.cs.RelationalRandomWalks;



public class Edge {

	public String Name;
	public int Edgeid;
	public Node fromNode;
	public Node ToNode;
	public boolean NoBack=false;
	public boolean NoForward = false;
	public boolean NoForwardTwice = false;
	public boolean NoBackTwice = false;
	public boolean NoInverse = false;
	public boolean isInverse = false;
	
	public Edge(String EName, int XEdgeid, Node nodefrom, Node nodeto)
	{
		this.Name = EName;
		this.Edgeid =XEdgeid; 
		this.fromNode = nodefrom;
		this.ToNode = nodeto;
	
	}
	
	public boolean canFollow(Edge r0){
		if (r0==null ) return true;
		//if (r0.NoRepeat)
			if (r0.equals(this))
				return false;	// no repetition allowed
		if (r0.NoBack)
			//if (r0.twin!=null)
				//if (r0.twin.equals(this))
					return false;	// no backward walking
		return true;
	}		
	
	
	public static void main(String[] args) {
		// TODO Auto-generated method stub

	}

}
