package edu.iu.cs.RelationalRandomWalks;

import java.io.IOException;
import edu.wisc.cs.will.Utils.Utils;

public class RunRelationalRandomWalks {

	
	public static CommandLineArguments parseArgs(String[] args) {
		CommandLineArguments cmdArgs = new CommandLineArguments();
		if (cmdArgs.parseArgs(args)) {
			return cmdArgs;
		}
		return null;
	}

	public static void main(String[] args) throws IOException {
				
		args = Utils.chopCommentFromArgs(args); 
		CommandLineArguments cmd = RunRelationalRandomWalks.parseArgs(args);
					
		if (cmd == null) {
			Utils.error(CommandLineArguments.getUsageString());
		}
		
		Graph MyGraph = new Graph();
		MyGraph.ReadInputFile(cmd.getTrainDirVal());
		
		if (!cmd.islearnRandomWalks()) {
			Utils.waitHere("Set \"-rw\"  in cmdline arguments to ensure that we intend to learn random walks. Will now learn random walks.");
			cmd.setLearnRandomWalks(true);
		}
		
		RelationalRandomWalks MyRandomWalks = new RelationalRandomWalks(MyGraph,cmd);
	
		GenerateRandomWalks RWGeneration = new GenerateRandomWalks();
		RWGeneration.createRandomWalks(MyRandomWalks.gr);
		
	}
}
