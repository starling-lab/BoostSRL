package edu.iu.cs.RelationalRandomWalks;

public class RelationalRandomWalks {
	Graph gr;
	
	public RelationalRandomWalks(Graph mygraph, CommandLineArguments cmdArgs)
	{
		String StartEntity;
		String EndEntity;
		String DirectoryPath;
		int MaxRWLength;
		StartEntity = cmdArgs.getStartEntity();
		EndEntity = cmdArgs.getEndEntity();
		MaxRWLength = cmdArgs.getRandomWalkLength();
		DirectoryPath = cmdArgs.getTrainDirVal();
		mygraph.MaxRWLength = MaxRWLength;
		mygraph.DirectoryPath = DirectoryPath;
				    
		if(!mygraph.GraphNodes.containsKey(StartEntity))
		{
			System.out.println("Start Entity is Not Set Correctly. "+StartEntity+" Is Not Part Of The Facts File(Input is Case Sensitive).");
			StartEntity = null;
		}
		else
		{
			System.out.println("% Start Entity Set Correctly to: "+StartEntity);
			mygraph.StartEntity = StartEntity;
		}
    
		if(!mygraph.GraphNodes.containsKey(EndEntity))
		{
			System.out.println("End Entity Is Not Set Correctly. "+EndEntity+" Is Not Part Of The Facts File(Input is Case Sensitive).");
			EndEntity=null;
		}
		else
		{
			System.out.println("% End Entity Set Correctly  to: "+EndEntity);	
			mygraph.EndEntity = EndEntity;
		}
		
		if(cmdArgs.isDefaultRandomWalkLength())
			System.out.println("% Random Walks Length Set to default: "+cmdArgs.getRandomWalkLength()+". To set it to other value, use -maxRWlen flag.");
		else
		{			
			System.out.println("% Random Walks Length Set to: " +MaxRWLength);
		}
		
		this.gr = mygraph;
	}

	public static void main(String[] args) {
	
	}
}
