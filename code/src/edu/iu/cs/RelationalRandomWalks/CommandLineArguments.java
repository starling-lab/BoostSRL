package edu.iu.cs.RelationalRandomWalks;

import edu.wisc.cs.will.Utils.Utils;

public class CommandLineArguments {

	public CommandLineArguments() {
		super();
	}
	
	/**
	 * Steps to add new arguments
	 * 1. Define a "static final" string for the flag
	 * 2. Define a variable that is set by the flag
	 * 3. Create a getter and setter for the variable.
	 * 4. Set the value of the variable from the flags in parseArgs
	 * 5. Define a usage string in getUsageString
	 */
	
	
	public static final String argPrefix = "-";
	//public static final String learn = "l";
	
	public static final String useRandomWalks = "rw";
	private boolean learnRandomWalks=false;
	
	public static final String trainDir = "train";
	private String trainDirVal;
	
	public static final String numRWLength = "maxRWlen";
	private int MaxRWLength=6;
	private boolean DefaultLength = true;
	
	public static final String startEntity = "startentity";
	private String startentityname;
	
	public static final String endEntity = "endentity";
	private String endentityname;
	
	
	public boolean parseArgs(String[] args) {
		for (int i = 0; i < args.length; i++) {		
			if (args[i].trim().isEmpty())
				continue;
			Utils.println("args[" + i + "] = " + args[i]);
		
			if (argMatches(args[i], useRandomWalks)) {
				learnRandomWalks = true;
				continue;
			}
			if (argMatches(args[i], numRWLength)) {
				if(MaxRWLength!=Integer.parseInt(args[++i]))
					DefaultLength=false;
				MaxRWLength=Integer.parseInt(args[i]);
				continue;
			}
			
			if (argMatches(args[i], trainDir)) {
				setTrainDirVal(args[++i]);
				continue;
			}
			
			if (argMatches(args[i], startEntity)) {
				setStartEntity(args[++i]);
				continue;
			}
			
			if (argMatches(args[i], endEntity)) {
				setEndEntity(args[++i]);
				continue;
			}
			
			Utils.println("Unknown argument: " + args[i]);
			return false;
		  }	
			
		 return true;
		}

	
	public boolean argMatches(String arg, String constant) {
		if (arg.compareToIgnoreCase(argPrefix + constant) == 0)
			return true;
		return false;
	}
	/**
	 * @param trainDirVal the trainDirVal to set
	 */
	private boolean checked_trainDirVal = false;
	public void setTrainDirVal(String trainDirVal) {
		checked_trainDirVal = true;
		if (!(trainDirVal.endsWith("/") || trainDirVal.endsWith("\\"))) {  trainDirVal += "/"; }
		this.trainDirVal = trainDirVal;
	}
	
	public String getTrainDirVal() {
		if (!checked_trainDirVal && trainDirVal != null) {
			checked_trainDirVal = true;
		}
		return trainDirVal;
	}
	
	
	
	public void setStartEntity(String startentityname) {
		this.startentityname = startentityname;
	}
	
	public String getStartEntity() {
		return startentityname;
	}

	
	public void setEndEntity(String endentityname) {
		this.endentityname = endentityname;
	}
	
	public String getEndEntity() {
		return endentityname;
	}
	
	public boolean isDefaultRandomWalkLength() {
		return DefaultLength;
	}
	public int getRandomWalkLength()
	{
		return MaxRWLength;
	}
	
	
	public boolean islearnRandomWalks() {
		return learnRandomWalks;
	}
	
	public void setLearnRandomWalks(boolean learnRandomWalks) {
		this.learnRandomWalks = learnRandomWalks;
	}
	
	
	
	public static String getUsageString() {
		String result = "Usage:\n";
		
		result += argPrefix + useRandomWalks + " : Use this flag, if you want to enable Random Walks.\n";
		
		result += argPrefix + trainDir + " <Random Walks File> : Path to the file storing Random Walks Predicates and Constraints.\n";
		
		result += argPrefix + numRWLength + " <Length OF Random Walks>: Maximum Length of Each Random Walks.\n";
		
		result += argPrefix + startEntity + " <Start Entity>: Start Entity of Each Random Walks.\n";
		
		result += argPrefix + endEntity + " <End Entity>: End Entity of Each Random Walks.\n";
			
		return result;
	}
	
	
//	public static void main(String[] args) {
//		// TODO Auto-generated method stub
//
//	}

}
