package edu.wisc.cs.will.GroundRelationalRandomWalks;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
//import java.util.Collection;
import java.util.List;

import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;
import edu.wisc.cs.will.Boosting.MLN.RunBoostedMLN;
import edu.wisc.cs.will.Boosting.Utils.CommandLineArguments;
//import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.Utils.Utils;



public class RunGroundRelationalRandomWalks {
	
	static List<Clause> GroundedRandomWalks = new ArrayList<Clause>();
	
	/*static Collection<BindingList> negBLs = new ArrayList<BindingList>();
	
	public static void AddBindingforGroundedRandomWalks(Collection<BindingList> negBL){
		for(BindingList bl:negBL)
		{
			negBLs.add(bl);
		}
		
	}*/
	
	public void CollectTheGroundedRandomWalks(List<Clause> GroundingsPerClause)
	{
		for(Clause c: GroundingsPerClause)
		{
			GroundedRandomWalks.add(c);
		}
		
	}
	
	public void WriteGroundedRWtoFile(String filename)
	{
		//System.out.println("Writing the grounded Random Walks to "+filename);
		Utils.println(" "); 
		Utils.println("%  Writing the grounded Random Walks to "+filename); 
		
		File f = new File(filename);
		try {
			f.createNewFile();
			BufferedWriter bfWriter = new BufferedWriter(new FileWriter(f));
		
			for(Clause c: GroundedRandomWalks)
			{
				bfWriter.write(c+"\n");
			}
		
			bfWriter.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	//	System.out.println("Completed Writing the grounded random walks to output file"+filename);
		Utils.println(" ");
		Utils.println("% Completed Writing the grounded random walks to output file"+filename);
		Utils.println(" ");
	}
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		
		args = Utils.chopCommentFromArgs(args); 
		CommandLineArguments cmd = RunBoostedModels.parseArgs(args);
		if (cmd == null) {
			Utils.error(CommandLineArguments.getUsageString());
		}
		RunBoostedModels runClass = null;
		runClass = new RunBoostedMLN();
		if (!cmd.isGroundedRelationalRW()) {
			Utils.waitHere("Set \"-grw\"  in cmdline arguments to ensure that we intend to ground RW. Will now ground RW.");
		}
		cmd.setGroundedRelationalRW(true);
		
		if (!cmd.isLearnMLN()|| !cmd.isInferVal() ) {
			Utils.waitHere("Internally Setting\"-mln\" and \"-i\" in cmdline arguments to turn inference in MLN module on.");
		}
		
		cmd.setLearnMLN(true);
		cmd.setInferVal(true);
				
		runClass.setCmdArgs(cmd);
		try {
		    runClass.runJob();
		} catch (IOException e) {
		    e.printStackTrace();
		}
	}

}
