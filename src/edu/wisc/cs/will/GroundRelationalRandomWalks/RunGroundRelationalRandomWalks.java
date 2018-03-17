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
import edu.wisc.cs.will.Utils.check_disc;
import edu.wisc.cs.will.Utils.disc;



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
		System.out.println("Writing the grounded Random Walks to "+filename);
		
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
		System.out.println("Completed Writing the grounded random walks to output file"+filename);
	}
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		
		args = Utils.chopCommentFromArgs(args); 
		boolean disc_flag=false;
		CommandLineArguments cmd = RunBoostedModels.parseArgs(args);
		if (cmd == null) {
			Utils.error(CommandLineArguments.getUsageString());
		}
		disc discObj= new disc();
		
		/*Check for discretization*/
		
		check_disc flagObj=new check_disc();
		if (cmd.getTrainDirVal()!=null)
		{
			try {
			System.out.println("cmd.getTrainDirVal()"+cmd.getTrainDirVal());
			disc_flag=flagObj.checkflagvalues(cmd.getTrainDirVal());
			
			/*Updates the names of the training and Test file based on discretization is needed or not*/
			cmd.update_file_name(disc_flag);
//			System.out.println("Hellooooooooooooooooooooo"+cmd.get_filename());
			
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		}
		else if((cmd.getTestDirVal()!=null)) 
		{
			try {
			System.out.println("cmd.getTestDirVal()"+cmd.getTestDirVal());
			disc_flag=flagObj.checkflagvalues(cmd.getTestDirVal());
			
			/*Updates the names of the training and Test file based on discretization is needed or not*/
			cmd.update_file_name(disc_flag);
//			System.out.println("Hellooooooooooooooooooooo"+cmd.get_filename());
			
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
			
		}
		if (cmd.getTrainDirVal()!=null)
			
			{   
				File  f = new File(cmd.getTrainDirVal()+"\\"+cmd.trainDir+"_facts_disc.txt");
			    
				if(f.exists())
				 {
					f.delete();
				 }
				
			    try {
//			    	System.out.println("Hellooooooooooooooooooooo"+cmd.getTrainDirVal());
			    	if (disc_flag==true)
			    	{	
					discObj.Discretization(cmd.getTrainDirVal());
			    	}
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			    
			}
		if (cmd.getTestDirVal()!=null)
				
			{   
					
				File f = new File(cmd.getTestDirVal().replace("/","\\"+cmd.testDir+"_facts_disc.txt"));
				
				if(f.exists())
				{
					f.delete();
				}
				
				/*This module does the actual discretization step*/
			    try {
			    	if (disc_flag==true)
			    	{	
					 discObj.Discretization(cmd.getTestDirVal());
			    	} 
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			   
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
		runClass.runJob();
	}

}
