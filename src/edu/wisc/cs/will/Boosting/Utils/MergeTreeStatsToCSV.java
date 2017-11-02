package edu.wisc.cs.will.Boosting.Utils;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;


import edu.wisc.cs.will.Boosting.RDN.InferBoostedRDN;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.StringConstant;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.Utils.Utils;

public class MergeTreeStatsToCSV {
	
	private Map<String, Double> idToProb;
	
	private Map<String, Integer> idTocounts;
	
	private FileParser parser;
	public static enum ArgLocationInTreeStats {
		LEAFID,
		PROB,
		COUNT,
		FRAC
	}
	
	public MergeTreeStatsToCSV() {
		parser = new FileParser(new HandleFOPCstrings());
		idToProb = new HashMap<String, Double>();
		idTocounts = new HashMap<String, Integer>();
	}
	
	public void mergeStatsFromFiles(String[] files, String outputCSV) {
		for (String file : files) {
			Utils.println("Merging " + file);
			addFileToStats(file);	
		}
		// Sort probabilities
		// Sort by probabilities(lowest comes first)
		Map<String, Double> sortedMap = new TreeMap<String, Double>(new InferBoostedRDN.ValueComparator(idToProb));
		sortedMap.putAll(idToProb);
		try {
			
			InferBoostedRDN.writeTreeStatsToCSV(idTocounts, sortedMap, outputCSV);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}


	private void addFileToStats(String file) {
		
		if (!Utils.fileExists(file)) {
			Utils.waitHere("addFileToStats: this file doesn't exist:\n  " + file);
			return;
		}
		List<Sentence> sentences = parser.readFOPCfile(file);
		for (Sentence sentence : sentences) {
			if (sentence instanceof Literal) {
				addLiteralToStats((Literal)sentence);
			}
		}
	}


	private void addLiteralToStats(Literal lit) {
		if (lit.predicateName.name.equals(InferBoostedRDN.RDNTreeStats)) {
			String id = ((StringConstant)lit.getArgument(ArgLocationInTreeStats.LEAFID.ordinal())).getName();
			double prob = ((NumericConstant)lit.getArgument(ArgLocationInTreeStats.PROB.ordinal())).value.doubleValue();
			int count = ((NumericConstant)lit.getArgument(ArgLocationInTreeStats.COUNT.ordinal())).value.intValue();
			if (idToProb.containsKey(id)) {
				if (Utils.diffDoubles(idToProb.get(id), prob)) {
					// Probabilities should match
					Utils.waitHere("Merging files with different probabilities: " + prob + " & " + idToProb.get(id) +" for " + id);
				} 
			} else {
				idToProb.put(id, prob);
				idTocounts.put(id,0);
			}
			idTocounts.put(id, idTocounts.get(id) + count);
		}
	}
	
	
	
	public static void main(String[] args) {
		
		// TVK: For testing
		//String outDir = "F:/WILLscratch/TestDR_v2/";
		//String prefix =  "X:/MRtestbeds/TestDR2_v2/bins/bin";
		
		// TODO - walk through the RELATION NAMES
		
		// For NFL.
		int binStart  =   0;
		int binEnd    = 499; // Since these are over the TEST corpus, these were run PER BIN (of articles) rather than PER FOLD (which is what happens when doing 10-fold CV on a train corpus).
		int modValues =   1;
		int foldsToUse =  1;
		
		String outDir          = "C:/WILLscratch/MRtestbeds/TestDR2_v2/";
		String prefix          = outDir + "bins/bin";
		String suffix1         = "/NFL/";
		String suffix2         = "/Lits1Trees25Skew10_Run1/trainOnAll/modelsLits1Trees25Skew10/testSetResults/";
		String treeStatFile1   = "testSetInferenceResults_pos_allNeg_whenModEquals";
		String treeStatFile2   = "_Lits1Trees25Skew10_Run1_testf";
		String treeStatFile3   = "_RDNtreePathStats";
		List<String> fileNames = new ArrayList<String>();
		
		String[] relationNames = {  // These are HARDWIRED IN for now so that this class can stay in WILL (which should not depend on MachineReading).
				  "gameDate_Date_NFLGame",
				  "scoringEventFG_NFLTeam_NFLGame",
				  "teamFinalScore_TeamScore_NFLTeam_NFLGame",
				  "teamFinalScore_TeamScore_NFLGame",
				  "teamFinalScore_NFLTeam",
				  "teamFinalScore_NFLGame",
				  "scoringEventFG_NFLTeam_NFLGame_ScoreEvent",
				  "gameDate_NFLGame",
				  "teamFinalScore_TeamScore_NFLTeam",
				  "homeTeamInGame_NFLTeam",
				  "teamFinalScore_TeamScore",
				  "gameLoser_NFLTeam",
				  "gameWinner_NFLTeam_NFLGame",
				  "scoringEventFG_ScoreEvent",
				  "teamInGame_NFLGame",
				  "scoringEventFG_NFLGame",
				  "gameWinner_NFLTeam",
				  "scoringEventTD_NFLGame_ScoreEvent",
				  "scoringEventFG_NFLTeam_ScoreEvent",
				  "awayTeamInGame_NFLTeam",
				  "scoringEventFG_NFLTeam",
				  "teamInGame_NFLTeam_NFLGame",
				  "scoringEventTD_NFLTeam_ScoreEvent",
				  "teamInGame_NFLTeam",
				  "scoringEventTD_NFLTeam_NFLGame",
				  "gameLoser_NFLTeam_NFLGame",
				  "homeTeamInGame_NFLTeam_NFLGame",
				  "scoringEventTD_ScoreEvent",
				  "awayTeamInGame_NFLTeam_NFLGame",
				  "scoringEventTD_NFLTeam",
				  "scoringEventTD_NFLTeam_NFLGame_ScoreEvent",
				  "gameWinner_NFLGame",
				  "homeTeamInGame_NFLGame",
				  "gameLoser_NFLGame",
				  "gameDate_Date",
				  "scoringEventTD_NFLGame",
				  "scoringEventFG_NFLGame_ScoreEvent",
				  "teamFinalScore_NFLTeam_NFLGame"
		};
		Set<Integer> skipsThisBin = new HashSet<Integer>(4);
		
		if (true) { // This is for KBP.
		
			binEnd     =    0;
			modValues  =   10;
			foldsToUse =   10;
			
			outDir        = "S:/people/Jude/MRtestbeds/TrainGeneratedTAC_Slots/Pass1Results/TACSlot/hasSpouse_person_person/Lits1Trees25Skew4_Run1/trainOnAll";
			prefix        = outDir;
			suffix1       = "/modelsLits1Trees25Skew4/testSetResults/";
			suffix2       = "";
			treeStatFile2 = "_Lits1Trees25Skew4_Run1_testf";
			String[] relationNames2 = { "" };  relationNames = relationNames2; // Work around Java shortcoming.
		} else { // This is for NFL (as are the default settings above).
			skipsThisBin.add(141);
			skipsThisBin.add(142);
			skipsThisBin.add(344);
			skipsThisBin.add(387);
		}
		
		for (int relationNumber = 0; relationNumber < relationNames.length; relationNumber++) {
			String relationName = relationNames[relationNumber];
			String suffix = suffix1 + relationName + suffix2;
			for (int i = binStart; i <= binEnd; i++) if (!skipsThisBin.contains(i)) for (int m = 0; m < modValues; m++)  for (int f = 0; f < foldsToUse; f++) {
				String fileToUse = prefix + (binStart == binEnd ? "" : i) + suffix + treeStatFile1 + m + treeStatFile2 + f + treeStatFile3 + Utils.defaultFileExtensionWithPeriod;
				Utils.ensureDirExists(fileToUse);
				fileNames.add(fileToUse);
			}
			Utils.println("\n% Have collected " + Utils.comma(fileNames) + " file names.");
			String outFile = outDir + suffix + treeStatFile1 + treeStatFile2 + treeStatFile3 + "_combined.csv";
			Utils.ensureDirExists(outFile);
			
			MergeTreeStatsToCSV merger = new MergeTreeStatsToCSV();
			merger.mergeStatsFromFiles(fileNames.toArray(new String[1]), outFile);	
			Utils.println("\n% Have written the results to:\n%  " + outFile);
			
			String homeDir = Utils.getUserHomeDir() + "/BoostedTreeStats/" + treeStatFile1 + treeStatFile2 + treeStatFile3 + "_" + 
							("".equals(relationName) ? "hasSpouse_person_person" : relationName) + // Hack to handle the fact that KBP is using different file names.
							"_combined.csv";
			Utils.copyFile(outFile, homeDir);
			Utils.println("\n% And copied to:\n%  " + homeDir);
			}
			
	}
}
