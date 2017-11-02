package edu.wisc.cs.will.Boosting.Utils;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import edu.wisc.cs.will.Boosting.RDN.RunBoostedRDN;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
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
	public static final String learn = "l";
	
	public static       int modN                            =   10; // Divide inference examples into this many bins.  THIS IS NEEDED WHEN THE SIZE OF A TESTSET IS TOO LARGE.
	protected           int doInferenceIfModNequalsThis     =   -1; // '-1' means do ALL. 
	public static final String indicatorOfModN              = "useMod";
	public static final String indicatorOfDoEveryNth        = "doWhenMod";
	
	public boolean useLockFiles = true; // Need to turn this off when using Condor. 
	
	private boolean learnVal = false;
	
	public static final String currentModelMarker   = "marker"; // Added by JWS so that repeated runs can get different markers (might want to do this for more/all files).
	public static final String currentResultsMarker = "resultsFileMarker";
	
	public static final String useMLN = "mln";
	private boolean learnMLN=false;

	public static final String useSoftM = "softm";
	private boolean SoftM=false;
	
	public static final String alphaFlag="alpha";
	private double alpha=0;
	
	public static final String betaFlag="beta";
	private double beta=0;
	
	public static final String useOCC = "occ";
	private boolean learnOCC=false;
	
	public static final String sampleOCCFlag = "dropPos";
	private double dropPos=0.0;
	
	public static final String learnMLNClauses = "mlnClause";
	private boolean learningMLNClauses=false;
	
	public static final String numMLNClauses = "numMLNClause";
	private int numberOfMLNClauses=5;
	
	public static final String maxMLNLength = "mlnClauseLen";
	private int maxMLNClauseLength=2;
	
	public static final String noTargetModes = "removeTarget";
	private boolean noTargetModesInitially = false;

	public static final String hiddenLitFlag = "hidden";
	private String hiddenStrategy = "ignore";

	public static final String hideSampleFlag = "hideProb";
	private double hiddenLitProb = -1;

	public static final String hideNegSampleFlag = "hideNegProb";
	private double hiddenNegLitProb = -1;

	public static final String outputAlchFlag = "outputFacts";
	private String outputAlchDBFile = null;

	public static final String createHiddenFlag = "createHidden";
	private boolean createHiddenFile = false;
	
	public static final String reportMissFlag = "reportHiddenEx";
	private boolean reportHiddenEx = true;
	
	public static final String rdnIterFlag = "iter";
	private int rdnIterationStep = -1;
	
	public static final String emSampleFlag = "numState";
	private int numberOfHiddenStates = -1;
	
	public static final String ignoreStateProbFlag = "noStateProb";
	private boolean ignoreStateProb = false;
	
	
	public static final String emSampleProbFlag = "emSampleProb";
	private double emSampleProb = 1;
	
	public static final String learnCurve = "lc";
	private boolean printLearningCurve = false;
	
	public static final String outName = "outSuffix";
	public String outFileSuffix = null;
	
	
	public static final String infer = "i";
	private boolean inferVal=false;

	public static final String useYap = "y";
	private boolean useYapVal=false;
	
	public static final String noBoosting = "noBoost";
	private boolean disabledBoosting=false;	
	
	public static final String trainDir = "train";
	private String trainDirVal;
	
	public static final String combineFlag = "combine";
	private boolean combineValue;

	public static final String testDir = "test";
	private String testDirVal;

	public static final String modelDir = "model";
	private String modelDirVal = null;
	
	public static final String resultsDir = "results";
	private String resultsDirVal = null;
	
	public static final String adviceFile = "advice";
	private String adviceFileVal = null;

	public static final String yapBin = "yapBin";
	private String yapBinVal = "/u/t/u/tushar/code/yap/bin/yap";

	public static final String yapBias = "yapBias";
	private String yapBiasVal = "";

	public static final String targetPred = "target";
	private Set<String> targetPredVal = null;
	
	public static final String hiddenPredFlag = "hiddenPred";
	private Set<String> hiddenPredVal = null;
	
	public static final String loadModelPredFlag = "loadPredModel";
	private Set<String> loadPredModelVal = null;
	
	
	public static final String saveModel = "save";
	private boolean saveModelVal=false;

	public static final String maxTrees = "trees";
	private int maxTreesVal=10;

	public static final String noLazybase = "noLazy";
	private boolean usingDefaultClausebase = false;
	
	public static final String autoCreateNeg = "createNeg";
	private boolean createSyntheticEgs = false;
	
	public static final String printLeafIds = "printLeafId";
	private boolean printingTreeStats = false;
	
	public static final String disableJointModel = "noJointModel";
	private boolean jointModelDisabled =false;
	
	public static final String disableChkPtFlag = "disableChkPts";
	private boolean noCheckPointing=false;

	public static final String disableAdviceFlag = "disableAdvice";
	private boolean disableAdvice = false;

	public static final String regressionFlag = "reg";
	private boolean learnRegression = false;

	public static final String probFlag = "probEx";
	private boolean learnProbExamples = false;

	
	public static final String disableMultiClassFlag = "noMulti";
	private boolean disableMultiClass = false;
	
	public static final String priorAdviceFlag = "priorAdvice";
	private String priorAdvice="advice.txt";

	public static final String maxInteriorNodeLits = "maxNodeLits";
	private int maxLiteralsInAnInteriorNodeVal = 1;

	public static final String bagOriginalExamplesKey   = "bag";
	public static final String noBagOriginalExamplesKey = "noBag";
	private boolean bagOriginalExamples = false;
	
	public static final String stepLen = "step";
	private double stepLenVal =1;
	
	public static final String sampleNegsToPosRatio = "negPosRatio";
	private double sampleNegsToPosRatioVal = 2;

	public static final String printAllEgFlag		= "printAllEgToo";
	private boolean printAllExamplesToo = false;
	
	public static final String testNegsToPosRatio = "testNegPosRatio";
	private double testNegsToPosRatioVal = -1;
	public static final String testPosString      = "testPosString"; // Allow overriding of the default.
	private String stringForTestsetPos = "pos";
	public static final String testNegString      = "testNegString"; // Allow overriding of the default.
	private String stringForTestsetNeg  = "neg";
	public static final String testFactsString    = "testFactsString"; // Allow overriding of the default.
	/*Changed for discretization*/
	private String stringForTestsetFacts = null;
	
	/*private String stringForTestsetFacts = "facts_new";*/
	public static final String testHiddenString    = "testHiddenString"; // Allow overriding of the default.
	private String stringForTestsetHidden = "hidden";
	
	public static final String treelearner = "yapTree";
	private String treelearnerVal = "/u/t/u/tushar/code/tildecrf_20091116/treelearner/treelearner.pl" ;
	
	public static final String aucPath = "aucJarPath";
	private String aucPathVal = null;
	
	public static final String modelName = "modelSuffix";
	public String modelFileVal = null;
	
	
	public static final String samplePosProb = "samplePositive";
	public double samplePosProbVal = -1.0;
	
	public static final String reweighEx = "reweigh";
	public boolean reweighExamples = false;
	
	public static final String useProbWts = "probWt";
	private boolean useProbabilityWeights = false;

        // Introduced By Navdeep Kaur
        // Used to set flag for grounded random walks
        public static final String groundedRW = "grw";
        private boolean GroundedRelationalRW = false;

	public static final String kbpllFile = "adviceFile";
	private String kbpllAdviceFile = null;
	
	public static final String adviceWts = "adviceWt";
	private double adviceWtVal = 0.5;
	
	public static final String useApproxCount = "approxCount"; // change by MD & DD for approx
	private boolean useApproxCountVal = false;
		
	public void setkbpllFiles(String files) {
		kbpllAdviceFile = files;
	}
	
	public String getkbpllFiles() {
		return kbpllAdviceFile;
	}
	
	public void setAdviceWt(String d) {
		adviceWtVal = Double.parseDouble(d);
	}
	
	public double getAdviceWt() {
		return adviceWtVal;
	}
	
	public int getDoInferenceIfModNequalsThis() {
		return doInferenceIfModNequalsThis;
	}
	public void setDoInferenceIfModNequalsThis(int doInferenceIfModNequalsThis) {
		this.doInferenceIfModNequalsThis = doInferenceIfModNequalsThis;
	}
	
	public String getAnyStringForModEquals() {
		if (doInferenceIfModNequalsThis < 0) { return ""; }
		return "whenModEquals" + doInferenceIfModNequalsThis + "_";
	}
	
	public boolean parseArgs(String[] args) {
		for (int i = 0; i < args.length; i++) {		
			if (args[i].trim().isEmpty())
				continue;
			Utils.println("args[" + i + "] = " + args[i]);
			if (argMatches(args[i], "noLockFiles")) {
				useLockFiles = false;
				continue;
			}
			else if (argMatches(args[i], "condorJWS")) { // Special-purpose code for JWS' experiments.  Currently only evaluates learned bRDN models on testsets.
				String experimentID = args[++i];
				int    condorID     = Integer.parseInt(args[++i]);
				
				// if (condorID < 70) { System.exit(0); } // Temp code to skip initial debugging runs (which might not have completed).

                int onesDigit  = (condorID        % 10);
                int tensDigit  = (condorID /   10 % 10);
                int hundsDigit = (condorID /  100 % 10);
                int thousDigit = (condorID / 1000 % 10);
                
				useLockFiles = false; // When running in Condor, lock files are dangerous since jobs can be evicted (and start anew) at any time.
				
                doInferenceIfModNequalsThis = onesDigit;
                String target = "";
                stringForTestsetPos   = "pos";
                stringForTestsetNeg   = ((tensDigit == (tensDigit / 2) * 2) ? "allNeg"      : "neg");
                stringForTestsetFacts = ((tensDigit == (tensDigit / 2) * 2) ? "factsAllNeg" : "facts");
                int    fold   = tensDigit / 2;
				switch (hundsDigit) {
					case 0: target += (thousDigit <= 0 ? "gameLoser_NFLTeamNFLGameNFLGame"  : "scoringEventTD_NFLTeamNFLGameScore"); break;
					case 1: target += (thousDigit <= 0 ? "gameWinner_NFLTeamNFLGameNFLGame" : "scoringEventFG_NFLTeamNFLGameScore"); break;
					case 2: target += "homeTeamInGame_NFLTeamNFLGame"; break;        // I. e., should do 1300 runs (0 through 1199).
					case 3: target += "awayTeamInGame_NFLTeamNFLGame"; break;
					case 4: target += "gameDate_DateNFLGame"; break;
					case 5: target += "NFLGame"; break;
					case 6: target += "NFLTeam"; break;
					case 7: target += "Date";    break;
					case 8: target += "Score";   break;
					case 9: target += "teamFinalScore_ScoreNFLTeamNFLGame"; break;
				}

				targetPredVal = new HashSet<String>();
				targetPredVal.add(target);
				
				if (modelDirVal   == null) { modelDirVal   = "/u/shavlikgroup/people/Jude/MRtestbedResults/NFL/"; }
				if (resultsDirVal == null) { resultsDirVal = modelDirVal; }
				if (testDirVal    == null) { testDirVal    = "/u/shavlikgroup/projects/MachineReading/MRtestbeds/NFL/"; }				
				
				modelDirVal   += target + "/trainf" + fold + "/models" + experimentID + "/";
				resultsDirVal += target + "/trainf" + fold + "/models" + experimentID + "/";
				testDirVal    += target + "/testf"  + fold + "/"; 				

				if (RunBoostedRDN.nameOfCurrentModel == null) { RunBoostedRDN.nameOfCurrentModel = "Run1"; }
				
				String learnFile =  modelDirVal + "bRDNs/Trees/" + target + "_Run1Tree" + (maxTreesVal - 1) + ".tree";
				if (!Utils.ensureDirExists(learnFile).exists()) {
					Utils.println("% Exiting inference because this learned model does not exist:\n " + learnFile);
					System.exit(0);
				}
				
				String inferFile = resultsDirVal + "testSetResults/testSetInferenceResults"				
											   + "_" + getExtraMarkerForFiles(true) + getStringForTestsetPos() + "_" + getStringForTestsetNeg() 
											   + "_sorted" + "_Run1" + Utils.defaultFileExtensionWithPeriod;
				if (Utils.ensureDirExists(inferFile).exists()) {
					Utils.println("% Exiting inference because this file already exists: " + inferFile);
					System.exit(0); 
				}
				
				continue;
			}			

			if (argMatches(args[i], "condorJWSlearn")) { // Special-purpose code for JWS' experiments.  Currently only evaluates learned bRDN models on testsets.
				String experimentID = args[++i];
				int    condorID     = Integer.parseInt(args[++i]);
				
				// if (condorID < 70) { System.exit(0); } // Temp code to skip initial debugging runs (which might not have completed).

                int onesDigit  = (condorID        % 10);
                int tensDigit  = (condorID /   10 % 10);
                int hundsDigit = (condorID /  100 % 10);
                int thousDigit = (condorID / 1000 % 10);
                
				useLockFiles = false; // When running in Condor, lock files are dangerous since jobs can be evicted (and start anew) at any time.
				
                String target = "";
                int    fold   = onesDigit;
                
                if (fold > 4) { System.exit(0); } // Can we use these for something? USE  TO SUPPORT TWO ALGO VARIANTS?  IF SO, CREATE 'marker' here (rather than in the calling script).

				switch (tensDigit) { // Could rewrite this to only need 60 Condor jobs ...
					case 0: target += (hundsDigit <= 0 ? "gameLoser_NFLTeamNFLGame"  : "scoringEventTD_NFLTeamNFLGameScore"); break;
					case 1: target += (hundsDigit <= 0 ? "gameWinner_NFLTeamNFLGame" : "scoringEventFG_NFLTeamNFLGameScore"); break;
					case 2: target += "homeTeamInGame_NFLTeamNFLGame"; break;        // I. e., should do 120 runs (0 through 119).
					case 3: target += "awayTeamInGame_NFLTeamNFLGame"; break;
					case 4: target += "gameDate_DateNFLGame"; break;
					case 5: target += "NFLGame"; break;
					case 6: target += "NFLTeam"; break;
					case 7: target += "Date";    break;
					case 8: target += "Score";   break;
					case 9: target += "teamFinalScore_ScoreNFLTeamNFLGame"; break;
				}

				targetPredVal = new HashSet<String>();
				targetPredVal.add(target);
				
				if (modelDirVal == null) { modelDirVal = "/u/shavlikgroup/people/Jude/MRtestbedResults/NFL/"; }	
				if (trainDirVal == null) { trainDirVal = "/u/shavlikgroup/projects/MachineReading/MRtestbeds/NFL/"; }	
				modelDirVal += target + "/trainf" + fold + "/models" + experimentID + "/";
				trainDirVal += target + "/trainf" + fold + "/"; 				
				
				if (RunBoostedRDN.nameOfCurrentModel == null) { RunBoostedRDN.nameOfCurrentModel = "Run1"; }
				
				String learnFile =  modelDirVal + "bRDNs/Trees/" + target + "_Run1Tree" + (maxTreesVal - 1) + ".tree";
				if (Utils.ensureDirExists(learnFile).exists()) {
					Utils.println("% Exiting learning because this learned model already exists:\n " + learnFile);
					System.exit(0);
				}
				
				continue;
			}

			if (argMatches(args[i], "condor")) {
				String experimentID    = args[++i];
				int    condorProcessID = Integer.parseInt(args[++i]);
				// Compute fold, run number, etc from the processID.
				int fold =     condorProcessID / 25;
				int run  = 1 + condorProcessID % 25; // Count runs from 1.
				
				useLockFiles = false; // When running in Condor, lock files are dangerous since jobs can be evicted (and start anew) at any time.
				
			//	if (run > 100) { System.exit(0); }
				
				// This is the notation used in the NFL tasks.  This code assumes that all other variables have already been set.
				String target = Utils.getIthItemInCollectionUnsafe(targetPredVal, 0);
				modelDirVal += target + "/trainf" + fold + "/models" + experimentID + "/";
				if (trainDirVal != null) { 
					trainDirVal +=      "/trainf" + fold; 
				//	trainDirVal += fold; // Notation for BC 
				//	modelDirVal += fold + "/models" + experimentID;
				}
				if (testDirVal  != null) {
					testDirVal  +=      "/testf"  + fold; 
				}
				if (RunBoostedRDN.nameOfCurrentModel == null) { RunBoostedRDN.nameOfCurrentModel = "Run"; }
				RunBoostedRDN.nameOfCurrentModel += run;
				
				if (learnVal) {
					// If LEARNING, then see if the last tree already exists.
					String learnFile = "/" + modelDirVal + "bRDNs/Trees/" + target + BoostingUtils.getLabelForCurrentModel() + "Tree" + (maxTreesVal - 1) + ".tree";
				
					if (Utils.ensureDirExists(learnFile).exists()) {
						Utils.println("% Exiting learning because this file already exists: " + learnFile);
						if (inferVal) { learnVal = false; } else { System.exit(0); } 
					}
				}
				
				if (inferVal && !learnVal) { // If learning, should always redo the inference.
					Utils.writeMe("inferFile out of date?"); // work in (and put in common location) + "_" + cmdArgs.getStringForTestsetPos() + "_" + cmdArgs.getStringForTestsetNeg() + cmdArgs.getAnyStringForModEquals()
					String inferFile = "/" + modelDirVal + "testSetResults/testSetInferenceResults" + BoostingUtils.getLabelForCurrentModel() + BoostingUtils.getLabelForResultsFileMarker() + "Trees" + maxTreesVal + Utils.defaultFileExtensionWithPeriod;
					if (Utils.ensureDirExists(inferFile).exists()) {
						Utils.println("% Exiting inference because this file already exists: " + inferFile);
						System.exit(0); 
					}
				}
				
				continue;
			}			
			if (argMatches(args[i], indicatorOfModN)) {
				modN = Integer.parseInt(args[++i]);
				continue;
			}			
			if (argMatches(args[i], indicatorOfDoEveryNth)) {
				doInferenceIfModNequalsThis = Integer.parseInt(args[++i]);
				continue;
			}			
			if (argMatches(args[i], currentModelMarker)) {
				RunBoostedRDN.nameOfCurrentModel = args[++i];
				continue;
			}			
			if (argMatches(args[i], currentResultsMarker)) {
				RunBoostedRDN.resultsFileMarker = args[++i];
				continue;
			}
			if (argMatches(args[i], useMLN)) {
				learnMLN = true;
				continue;
			}
			// Changed By Navdeep Kaur
			if (argMatches(args[i], groundedRW)) {
			        GroundedRelationalRW = true;
				continue;
			}
			
			if (argMatches(args[i], useSoftM)) {
				SoftM = true;
				continue;
			}
			
			if (argMatches(args[i], alphaFlag)) {
				alpha=Double.parseDouble(args[++i]);
				continue;
			}
	
			if (argMatches(args[i], betaFlag)) {
				beta=Double.parseDouble(args[++i]);
				continue;
			}
			
			if (argMatches(args[i], useOCC)) {
				learnOCC = true;
				continue;
			}

			if (argMatches(args[i], sampleOCCFlag)) {
				dropPos = Double.parseDouble(args[++i]);
				continue;
			}
			
			if (argMatches(args[i], learnCurve)) {
				printLearningCurve = true;
				if (isArgumentNotAFlag(args, i+1)) {
					printLearningCurve = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], disableChkPtFlag)) {
				noCheckPointing = true;
				if (isArgumentNotAFlag(args, i+1)) {
					noCheckPointing = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], printAllEgFlag)) {
				printAllExamplesToo = true;
				if (isArgumentNotAFlag(args, i+1)) {
					printAllExamplesToo = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], noTargetModes)) {
				noTargetModesInitially = true;
				if (isArgumentNotAFlag(args, i+1)) {
					noTargetModesInitially = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], hiddenLitFlag)) {
				hiddenStrategy = args[++i];
				continue;
			}
			if (argMatches(args[i], hideSampleFlag)) {
				hiddenLitProb = Double.parseDouble(args[++i]);
				continue;
			}
			if (argMatches(args[i], hideNegSampleFlag)) {
				hiddenNegLitProb = Double.parseDouble(args[++i]);
				continue;
			}
			if (argMatches(args[i], outputAlchFlag)) {
				outputAlchDBFile = args[++i];
				continue;
			}
			if (argMatches(args[i], createHiddenFlag)) {
				createHiddenFile = true;
				if (isArgumentNotAFlag(args, i+1)) {
					createHiddenFile = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			
			if (argMatches(args[i], reportMissFlag)) {
				reportHiddenEx = true;
				if (isArgumentNotAFlag(args, i+1)) {
					reportHiddenEx = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], rdnIterFlag)) {
				rdnIterationStep = Integer.parseInt(args[++i]);
				continue;
			}
			
			if (argMatches(args[i], emSampleFlag)) {
				numberOfHiddenStates = Integer.parseInt(args[++i]);
				continue;
			}
			
			if (argMatches(args[i], ignoreStateProbFlag)) {
				ignoreStateProb = true;
				if (isArgumentNotAFlag(args, i+1)) {
					ignoreStateProb = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			
			if (argMatches(args[i], emSampleProbFlag)) {
				emSampleProb = Double.parseDouble(args[++i]);
				continue;
			}
			
			if (argMatches(args[i], learnMLNClauses)) {
				learningMLNClauses = true;
				if (isArgumentNotAFlag(args, i+1)) {
					learningMLNClauses = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], numMLNClauses)) {
				numberOfMLNClauses=Integer.parseInt(args[++i]);
				continue;
			}
			if (argMatches(args[i], maxMLNLength)) {
				maxMLNClauseLength=Integer.parseInt(args[++i]);
				continue;
			}
			if (argMatches(args[i], reweighEx)) {
				reweighExamples=true;
				continue;
			}
			if (argMatches(args[i], useProbWts)) {
				useProbabilityWeights = true;
				if (isArgumentNotAFlag(args, i+1)) {
					useProbabilityWeights = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], outName)) {
				outFileSuffix = args[++i];
				continue; 
			}
			if (argMatches(args[i], learn)) {
				learnVal = true;
				if (isArgumentNotAFlag(args, i+1)) {
					learnVal = Utils.parseBoolean(args[++i]);
				}
				continue;
				
			}
			if (argMatches(args[i],combineFlag)){
				combineValue = true;
				if(isArgumentNotAFlag(args,i+1)){
					combineValue = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], infer)) {
				inferVal = true;
				if (isArgumentNotAFlag(args, i+1)) {
					inferVal = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i],combineFlag)){
				combineValue = true;
				if(isArgumentNotAFlag(args,i+1)){
					combineValue = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], useYap)) {
				useYapVal = true;
				if (isArgumentNotAFlag(args, i+1)) {
					useYapVal = Utils.parseBoolean(args[++i]);
				}
				continue;
			}		
			if (argMatches(args[i], disableJointModel)) {
				jointModelDisabled = true;
				if (isArgumentNotAFlag(args, i+1)) {
					jointModelDisabled = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], disableMultiClassFlag)) {
				disableMultiClass = true;
				if (isArgumentNotAFlag(args, i+1)) {
					disableMultiClass = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], noLazybase)) {
				usingDefaultClausebase = true;
				if (isArgumentNotAFlag(args, i+1)) {
					usingDefaultClausebase = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], autoCreateNeg)) {
				createSyntheticEgs = true;
				if (isArgumentNotAFlag(args, i+1)) {
					createSyntheticEgs = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], printLeafIds)) {
				printingTreeStats = true;
				if (isArgumentNotAFlag(args, i+1)) {
					printingTreeStats = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], bagOriginalExamplesKey)) {
				bagOriginalExamples = true;
				if (isArgumentNotAFlag(args, i+1)) {
					bagOriginalExamples = Utils.parseBoolean(args[++i]);
				}
				continue;
			}		
			if (argMatches(args[i], noBagOriginalExamplesKey)) {
				bagOriginalExamples = false;
				continue;
			}
			if (argMatches(args[i], noBoosting)) {
				disabledBoosting = true;
				if (isArgumentNotAFlag(args, i+1)) {
					disabledBoosting = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], trainDir)) {
				setTrainDirVal(args[++i]);
				continue;
			}
			if (argMatches(args[i], testDir)) {
				setTestDirVal(args[++i]);
				continue;
			}
			if (argMatches(args[i], modelDir)) {
				setModelDirVal(args[++i]);
				continue; 
			}
			if (argMatches(args[i], resultsDir)) {
				setResultsDirVal(args[++i]);
				continue; 
			}
			if (argMatches(args[i], adviceFile )) {
				setAdviceFileVal(args[++i]);
				continue; 
			}
			if (argMatches(args[i], adviceWts)) {
				setAdviceWt(args[++i]);
				continue;
			}
			if (argMatches(args[i], yapBin)) {
				yapBinVal = args[++i];
				continue;
			}
			if (argMatches(args[i], yapBias)) {
				yapBiasVal = args[++i];
				continue;
			}
			if (argMatches(args[i], targetPred)) {
				String targetStr = args[++i];
				targetPredVal = new HashSet<String>();
				targetPredVal.addAll(Arrays.asList(targetStr.split(",")));
				continue;
			}
			if (argMatches(args[i], hiddenPredFlag)) {
				String targetStr = args[++i];
				hiddenPredVal = new HashSet<String>();
				hiddenPredVal.addAll(Arrays.asList(targetStr.split(",")));
				continue;
			}
			if (argMatches(args[i], loadModelPredFlag)) {
				String targetStr = args[++i];
				loadPredModelVal = new HashSet<String>();
				loadPredModelVal.addAll(Arrays.asList(targetStr.split(",")));
				continue;
			}
			if (argMatches(args[i], saveModel)) {
				saveModelVal=true;
				if (isArgumentNotAFlag(args, i+1)) {
					saveModelVal = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], disableAdviceFlag)) {
				disableAdvice=true;
				if (isArgumentNotAFlag(args, i+1)) {
					disableAdvice = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], regressionFlag)) {
				learnRegression=true;
				if (isArgumentNotAFlag(args, i+1)) {
					learnRegression = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], probFlag)) {
				learnProbExamples=true;
				if (isArgumentNotAFlag(args, i+1)) {
					learnProbExamples = Utils.parseBoolean(args[++i]);
				}
				continue;
			}
			if (argMatches(args[i], priorAdviceFlag)) {
				priorAdvice = args[++i];
				continue;
			}
			if (argMatches(args[i], maxInteriorNodeLits)) {
				maxLiteralsInAnInteriorNodeVal=Integer.parseInt(args[++i]);
				continue;
			}
			if (argMatches(args[i], maxTrees)) {
				maxTreesVal=Integer.parseInt(args[++i]);
				continue;
			}
			if (argMatches(args[i], stepLen)) {
				stepLenVal=Double.parseDouble(args[++i]);
				continue;
			}
			if (argMatches(args[i], treelearner)) {	
				treelearnerVal = args[++i];
				continue;
			}
			if (argMatches(args[i], sampleNegsToPosRatio)) {
				sampleNegsToPosRatioVal=Double.parseDouble(args[++i]);
				continue;
			}
			if (argMatches(args[i], testNegsToPosRatio)) {
				testNegsToPosRatioVal=Double.parseDouble(args[++i]);
				continue;
			}
			if (argMatches(args[i], testPosString)) {
				stringForTestsetPos = args[++i];
				continue;
			}
			if (argMatches(args[i], testNegString)) {
				stringForTestsetNeg = args[++i];
				continue;
			}
			if (argMatches(args[i], testFactsString)) {
				stringForTestsetFacts = args[++i];
				continue;
			}
			if (argMatches(args[i], testHiddenString)) {
				stringForTestsetHidden = args[++i];
				continue;
			}
			if (argMatches(args[i], samplePosProb)) {
				samplePosProbVal=Double.parseDouble(args[++i]);
				continue;
			}
				
			if (argMatches(args[i], aucPath)) {
				aucPathVal = args[++i];
				continue;
			}			
			if (argMatches(args[i], modelName)) {
				modelFileVal = args[++i];
				continue;
			}
			if (argMatches(args[i], kbpllFile)) {
				kbpllAdviceFile = args[++i];
				continue;
			}
			if (argMatches(args[i], useApproxCount)) {
				useApproxCountVal = true;
				continue;
			}
			Utils.println("Unknown argument: " + args[i]);
			return false;
		}
		return true;
	}

	/**
	 * Returns true if there is an argument at "index" and it is not a flag. It uses startsWith("-") to determine
	 * if the next argument is a flag. So make sure to use it only for checking if boolean flags have 
	 * an argument that follows it as that would not begin with "-"
	 * @param args Arguments 
	 * @param index Position to look at 
	 * @return
	 */
	public static boolean isArgumentNotAFlag(String[] args, int index) {
		if (args.length > index) {
			if (!args[index].startsWith("-")) {
				return true;
			}
		}
		return false;
	}
	
	public static String getUsageString() {
		String result = "Usage:\n";
		
		result += argPrefix + learn + " : Use this flag, if you want to enable learning.\n";
		
		result += argPrefix + infer + " : Use this flag, if you want to enable inference.\n";
		
		result += argPrefix + useYap + " : Use this flag, if you want to use Yap for tree learning.\n";
		
		result += argPrefix + noBoosting + " : Use this flag, if you dont want to use boosting.\n";
		
		result += argPrefix + trainDir + " <Training directory> : Path to the training directory in WILL format.\n";
		
		result += argPrefix + testDir + " <Testing directory> : Path to the testing directory in WILL format.\n";
		
		result += argPrefix + modelDir + " <Model directory> : Path to the directory with the stored models[or where they will be stored].\n";
		
		result += argPrefix + yapBin + " <Yap binary> : Path to the Yap binary.\n";
		
		result += argPrefix + yapBias + " <Yap bias file> : Path to the Yap Bias file.\n";
		
		result += argPrefix + treelearner + " <TILDE treelearner file> : Path to the treelearner file.\n";
		
		result += argPrefix + targetPred + " <target predicates> : Comma separated list of predicates that need to be learned/inferred.\n";
		
		result += argPrefix + saveModel + " : Use this flag, if you want to save the learnt models.\n";
		
		result += argPrefix + maxTrees + " <Number of trees>: Number of boosting trees.\n";
		
		result += argPrefix + maxInteriorNodeLits +  " <Max number of literals at an interior node>: Max number of literals in an interior node.\n";
		
		result += argPrefix + stepLen + " <Step Length>: Default step length for functional gradient.\n";
		
		result += argPrefix + testNegsToPosRatio + " <Negative/Positive ratio>: Ratio of negatives to positive for testing.\n";
		
		return result;
	}
	
	public boolean argMatches(String arg, String constant) {
		if (arg.compareToIgnoreCase(argPrefix + constant) == 0)
			return true;
		return false;
	}

	/**
	 * @return the learnVal
	 */
	public boolean isLearnVal() {
		return learnVal;
	}
	/**
	 * @param learnVal the learnVal to set
	 */
	public void setLearnVal(boolean learnVal) {
		this.learnVal = learnVal;
	}
	
	public void update_file_name(boolean discflag){
		if (discflag==true)
		{
			stringForTestsetFacts="facts_new";
		}
		else{
			stringForTestsetFacts="facts";
		}
	}
	
	public String get_filename(){
		return stringForTestsetFacts;
	}
	
	public boolean isCombineVal(){
		return combineValue;
	}
	public void setCombineVal(boolean combineVal){
		this.combineValue = combineVal;
	}
	/**
	 * @return the inferVal
	 */
	public boolean isInferVal() {
		return inferVal;
	}
	/**
	 * @param inferVal the inferVal to set
	 */
	public void setInferVal(boolean inferVal) {
		this.inferVal = inferVal;
	}
	private boolean checked_trainDirVal = false;
	/**
	 * @return the disabledBoosting
	 */
	public boolean isDisabledBoosting() {
		return disabledBoosting;
	}


	/**
	 * @param disabledBoosting the disabledBoosting to set
	 */
	public void setDisabledBoosting(boolean disabledBoosting) {
		this.disabledBoosting = disabledBoosting;
	}


	/**
	 * @return the trainDirVal
	 */
	public String getTrainDirVal() {
		if (!checked_trainDirVal && trainDirVal != null) {
			checked_trainDirVal = true;
			//*System.out.println("I am inside if");
		}
		System.out.println(trainDirVal);
		return trainDirVal;
	}
	/**
	 * @param trainDirVal the trainDirVal to set
	 */
	public void setTrainDirVal(String trainDirVal) {
		checked_trainDirVal = true;
		if (!(trainDirVal.endsWith("/") || trainDirVal.endsWith("\\"))) {  trainDirVal += "/"; }
		this.trainDirVal = trainDirVal;
	}
	/**
	 * @return the useYapVal
	 */
	public boolean isUseYapVal() {
		return useYapVal;
	}

	/**
	 * @param useYapVal the useYapVal to set
	 */
	public void setUseYapVal(boolean useYapVal) {
		this.useYapVal = useYapVal;
	}

	private boolean checked_testDirVal = false;
	/**
	 * @return the testDirVal
	 */
	public String getTestDirVal() {
		if (!checked_testDirVal && testDirVal != null) {
			checked_testDirVal = true;
		}
		return testDirVal;
	}
	/**
	 * @param testDirVal the testDirVal to set
	 */
	public void setTestDirVal(String testDirVal) {
		checked_testDirVal = true;
		if (!(testDirVal.endsWith("/") || testDirVal.endsWith("\\"))) {  testDirVal += "/"; }
		this.testDirVal = testDirVal;
	}
	
	public boolean isLearningMLNClauses() {
		return learningMLNClauses;
	}
	public void setLearningMLNClauses(boolean learningMLNClauses) {
		this.learningMLNClauses = learningMLNClauses;
	}
	public int getNumberOfMLNClauses() {
		return numberOfMLNClauses;
	}


	public void setNumberOfMLNClauses(int numberOfMLNClauses) {
		this.numberOfMLNClauses = numberOfMLNClauses;
	}


	public boolean isPrintAllExamplesToo() {
		return printAllExamplesToo;
	}
	public void setPrintAllExamplesToo(boolean printAllExamplesToo) {
		this.printAllExamplesToo = printAllExamplesToo;
	}
	public int getMaxMLNClauseLength() {
		return maxMLNClauseLength;
	}


	public void setMaxMLNClauseLength(int maxMLNClauseLength) {
		this.maxMLNClauseLength = maxMLNClauseLength;
	}


	/**
	 * @return the hiddenStrategy
	 */
	public String getHiddenStrategy() {
		return hiddenStrategy;
	}
	/**
	 * @param hiddenStrategy the hiddenStrategy to set
	 */
	public void setHiddenStrategy(String hiddenStrategy) {
		this.hiddenStrategy = hiddenStrategy;
	}
	/**
	 * @return the reportHiddenEx
	 */
	public boolean isReportHiddenEx() {
		return reportHiddenEx;
	}
	/**
	 * @param reportHiddenEx the reportHiddenEx to set
	 */
	public void setReportHiddenEx(boolean reportHiddenEx) {
		this.reportHiddenEx = reportHiddenEx;
	}
	public boolean isPrintLearningCurve() {
		return printLearningCurve;
	}


	public void setPrintLearningCurve(boolean printLearningCurve) {
		this.printLearningCurve = printLearningCurve;
	}
	public boolean getBagOriginalExamples() {
		return bagOriginalExamples;
	}
	
	public void setBagOriginalExamples(boolean bagOriginalExamples) {
		this.bagOriginalExamples = bagOriginalExamples;
	}
	
	public boolean useCheckPointing() {
		return !noCheckPointing;
	}
	
	public void setCheckpointing(boolean val) {
		noCheckPointing = !val;
	}
	
	private boolean checked_modelDirVal = false;
	/**
	 * @return the modelDirVal
	 */
	public String getModelDirVal() {
		if (!checked_modelDirVal && modelDirVal != null) {
			checked_modelDirVal = true;
		}
		return modelDirVal;
	}
	/**
	 * @param modelDirVal the modelDirVal to set
	 */
	public void setModelDirVal(String modelDirVal) {
		checked_modelDirVal = true;
		if (!(modelDirVal.endsWith("/") || modelDirVal.endsWith("\\"))) {  modelDirVal += "/"; }
		this.modelDirVal = modelDirVal;
	}

	
	public boolean isUseProbabilityWeights() {
		return useProbabilityWeights;
	}
	public void setUseProbabilityWeights(boolean useProbabilityWeights) {
		this.useProbabilityWeights = useProbabilityWeights;
	}
	public boolean isReweighExamples() {
		return reweighExamples;
	}
	public void setReweighExamples(boolean reweighExamples) {
		this.reweighExamples = reweighExamples;
	}

	private boolean checked_resultsDirVal = false;
	/**
	 * @return the modelDirVal
	 */
	public String getResultsDirVal() {
		if (!checked_resultsDirVal && resultsDirVal != null) {
			checked_resultsDirVal = true;
		}
		return resultsDirVal;
	}
	/**
	 * @param modelDirVal the modelDirVal to set
	 */
	public void setResultsDirVal(String resultsDirVal) {
		checked_resultsDirVal = true;
		if (!(resultsDirVal.endsWith("/") || resultsDirVal.endsWith("\\"))) {  resultsDirVal += "/"; }
		this.resultsDirVal = resultsDirVal;
	}
	
	public void setAdviceFileVal(String fileName) {
		adviceFileVal = Utils.replaceWildCards(fileName);
		if (!Utils.fileExists(fileName)) {
			Utils.waitHere("This specified advice file does not exist: \n  " + adviceFileVal);
		}
	}
	
	public boolean isNoTargetModesInitially() {
		return noTargetModesInitially;
	}
	public void setNoTargetModesInitially(boolean noTargetModesInitially) {
		this.noTargetModesInitially = noTargetModesInitially;
	}
	public String getAdviceFileVal() {
		return adviceFileVal;
	}
	
	/**
	 * @return the yapBinVal
	 */
	public String getYapBinVal() {
		return yapBinVal;
	}
	/**
	 * @param yapBinVal the yapBinVal to set
	 */
	public void setYapBinVal(String yapBinVal) {
		this.yapBinVal = yapBinVal;
	}
	/**
	 * @return the yapBiasVal
	 */
	public String getYapBiasVal() {
		return yapBiasVal;
	}
	/**
	 * @param yapBiasVal the yapBiasVal to set
	 */
	public void setYapBiasVal(String yapBiasVal) {
		this.yapBiasVal = yapBiasVal;
	}
	/**
	 * @return the modelFileVal
	 */
	public String getModelFileVal() {
		return modelFileVal;
	}


	/**
	 * @param modelFileVal the modelFileVal to set
	 */
	public void setModelFileVal(String modelFileVal) {
		this.modelFileVal = modelFileVal;
	}


	/**
	 * @return the targetPredVal
	 */
	public Set<String> getTargetPredVal() {
		return targetPredVal;
	}
	/**
	 * @param targetPredVal the targetPredVal to set
	 */
	public void setTargetPredVal(Set<String> targetPredVal) {
		this.targetPredVal = targetPredVal;
	}

	/**
	 * @return the hiddenPredVal
	 */
	public Set<String> getHiddenPredVal() {
		return hiddenPredVal;
	}
	/**
	 * @param hiddenPredVal the hiddenPredVal to set
	 */
	public void setHiddenPredVal(Set<String> hiddenPredVal) {
		this.hiddenPredVal = hiddenPredVal;
	}
	/**
	 * @return the disableMultiClass
	 */
	public boolean isDisableMultiClass() {
		return disableMultiClass;
	}
	/**
	 * @param disableMultiClass the disableMultiClass to set
	 */
	public void setDisableMultiClass(boolean disableMultiClass) {
		this.disableMultiClass = disableMultiClass;
	}
	/**
	 * @return the loadPredModelVal
	 */
	public Set<String> getLoadPredModelVal() {
		return loadPredModelVal;
	}
	/**
	 * @param loadPredModelVal the loadPredModelVal to set
	 */
	public void setLoadPredModelVal(Set<String> loadPredModelVal) {
		this.loadPredModelVal = loadPredModelVal;
	}
	/**
	 * @return the learnRegression
	 */
	public boolean isLearnRegression() {
		return learnRegression;
	}
	/**
	 * @param learnRegression the learnRegression to set
	 */
	public void setLearnRegression(boolean learnRegression) {
		this.learnRegression = learnRegression;
	}
	/**
	 * @return the saveModelVal
	 */
	public boolean isSaveModelVal() {
		return saveModelVal;
	}

	/**
	 * @param saveModelVal the saveModelVal to set
	 */
	public void setSaveModelVal(boolean saveModelVal) {
		this.saveModelVal = saveModelVal;
	}

	/**
	 * @return the maxTreesVal
	 */
	public int getMaxTreesVal() {
		return maxTreesVal;
	}

	/**
	 * @param maxTreesVal the maxTreesVal to set
	 */
	public void setMaxTreesVal(int maxTreesVal) {
		this.maxTreesVal = maxTreesVal;
	}

	/**
	 * @return the defaultStepLenVal
	 */
	public double getDefaultStepLenVal() {
		return stepLenVal;
	}

	/**
	 * @param defaultStepLenVal the defaultStepLenVal to set
	 */
	public void setDefaultStepLenVal(double defaultStepLenVal) {
		this.stepLenVal = defaultStepLenVal;
	}

	/**
	 * @return the rdnIterationStep
	 */
	public int getRdnIterationStep() {
		return rdnIterationStep;
	}
	/**
	 * @param rdnIterationStep the rdnIterationStep to set
	 */
	public void setRdnIterationStep(int rdnIterationStep) {
		this.rdnIterationStep = rdnIterationStep;
	}
	/**
	 * @return the treelearnerVal
	 */
	public String getTreelearnerVal() {
		return treelearnerVal;
	}

	/**
	 * @param treelearnerVal the treelearnerVal to set
	 */
	public void setTreelearnerVal(String treelearnerVal) {
		this.treelearnerVal = treelearnerVal;
	}

	/**
	 * @return the samplePosProbVal
	 */
	public double getSamplePosProbVal() {
		return samplePosProbVal;
	}


	/**
	 * @param samplePosProbVal the samplePosProbVal to set
	 */
	public void setSamplePosProbVal(double samplePosProbVal) {
		this.samplePosProbVal = samplePosProbVal;
	}


	/**
	 * @return the sampleNegsToPosRatioVal
	 */
	public double getSampleNegsToPosRatioVal() {
		return sampleNegsToPosRatioVal;
	}

	/**
	 * @param sampleNegsToPosRatioVal the sampleNegsToPosRatioVal to set
	 */
	public void setSampleNegsToPosRatioVal(double sampleNegsToPosRatioVal) {
		this.sampleNegsToPosRatioVal = sampleNegsToPosRatioVal;
	}


	/**
	 * @return the learnOCC
	 */
	public boolean isLearnOCC() {
		return learnOCC;
	}
	/**
	 * @param learnOCC the learnOCC to set
	 */
	public void setLearnOCC(boolean learnOCC) {
		this.learnOCC = learnOCC;
	}
	/**
	 * @return the dropPos
	 */
	public double getDropPos() {
		return dropPos;
	}
	/**
	 * @param dropPos the dropPos to set
	 */
	public void setDropPos(double dropPos) {
		this.dropPos = dropPos;
	}
	/**
	 * @return the hiddenLitProb
	 */
	public double getHiddenLitProb() {
		return hiddenLitProb;
	}
	/**
	 * @param hiddenLitProb the hiddenLitProb to set
	 */
	public void setHiddenLitProb(double hiddenLitProb) {
		this.hiddenLitProb = hiddenLitProb;
	}
	/**
	 * @return the hiddenNegLitProb
	 */
	public double getHiddenNegLitProb() {
		return hiddenNegLitProb;
	}
	/**
	 * @param hiddenNegLitProb the hiddenNegLitProb to set
	 */
	public void setHiddenNegLitProb(double hiddenNegLitProb) {
		this.hiddenNegLitProb = hiddenNegLitProb;
	}
	/**
	 * @return the outputAlchDBFile
	 */
	public String getOutputAlchDBFile() {
		return outputAlchDBFile;
	}
	/**
	 * @param outputAlchDBFile the outputAlchDBFile to set
	 */
	public void setOutputAlchDBFile(String outputAlchDBFile) {
		this.outputAlchDBFile = outputAlchDBFile;
	}
	/**
	 * @return the aucPathVal
	 */
	public String getAucPathVal() {
		return aucPathVal;
	}


	/**
	 * @param aucPathVal the aucPathVal to set
	 */
	public void setAucPathVal(String aucPathVal) {
		this.aucPathVal = aucPathVal;
	}


	/**
	 * @return the testNegsToPosRatioVal
	 */
	public double getTestNegsToPosRatioVal() {
		return testNegsToPosRatioVal;
	}


	/**
	 * @param testNegsToPosRatioVal the testNegsToPosRatioVal to set
	 */
	public void setTestNegsToPosRatioVal(double testNegsToPosRatioVal) {
		this.testNegsToPosRatioVal = testNegsToPosRatioVal;
	}

	public String getStringForTestsetPos() {
		return stringForTestsetPos;
	}

	public String getExtraMarkerForFiles(boolean includeTestSkew) {
		String result = "_";
		if (stringForTestsetPos != null)            { result += stringForTestsetPos + "_"; }
		if (stringForTestsetNeg != null)            { result += stringForTestsetNeg + "_"; }
		 result += getAnyStringForModEquals();
		if (maxLiteralsInAnInteriorNodeVal >= 0)    { result += "Lits"  + maxLiteralsInAnInteriorNodeVal; }
		if (maxTreesVal                    >= 0)    { result += "Trees" + maxTreesVal; }
		if (sampleNegsToPosRatioVal        >= 0)    { result += "Skew"     + (int) sampleNegsToPosRatioVal; }
		if (includeTestSkew &&
				testNegsToPosRatioVal      >= 0)    { result += "TestSkew" + (int) testNegsToPosRatioVal; }
		return result;
	}

	public void setStringForTestsetPos(String stringForTestsetPos) {
		this.stringForTestsetPos = stringForTestsetPos;
	}
	
	/**
	 * @return the stringForTestsetHidden
	 */
	public String getStringForTestsetHidden() {
		return stringForTestsetHidden;
	}
	/**
	 * @param stringForTestsetHidden the stringForTestsetHidden to set
	 */
	public void setStringForTestsetHidden(String stringForTestsetHidden) {
		this.stringForTestsetHidden = stringForTestsetHidden;
	}
	/**
	 * @return the numberOfHiddenStates
	 */
	public int getNumberOfHiddenStates() {
		return numberOfHiddenStates;
	}
	/**
	 * @param numberOfHiddenStates the numberOfHiddenStates to set
	 */
	public void setNumberOfHiddenStates(int numberOfHiddenStates) {
		this.numberOfHiddenStates = numberOfHiddenStates;
	}
	/**
	 * @return the emSampleProb
	 */
	public double getEmSampleProb() {
		return emSampleProb;
	}
	/**
	 * @param emSampleProb the emSampleProb to set
	 */
	public void setEmSampleProb(double emSampleProb) {
		this.emSampleProb = emSampleProb;
	}
	/**
	 * @return the ignoreStateProb
	 */
	public boolean isIgnoreStateProb() {
		return ignoreStateProb;
	}
	/**
	 * @param ignoreStateProb the ignoreStateProb to set
	 */
	public void setIgnoreStateProb(boolean ignoreStateProb) {
		this.ignoreStateProb = ignoreStateProb;
	}
	public int getMaxLiteralsInAnInteriorNode() {
		return maxLiteralsInAnInteriorNodeVal;
	}
	public void setMaxLiteralsInAnInteriorNode(int maxLiteralsInAnInteriorNode) {
		this.maxLiteralsInAnInteriorNodeVal = maxLiteralsInAnInteriorNode;
	}
	
	public String getStringForTestsetNeg() {
		return stringForTestsetNeg;
	}
	
	public String getStringForTestsetFacts() {
		return stringForTestsetFacts;
	}

	public void setStringForTestsetNeg(String stringForTestsetNeg) {
		this.stringForTestsetNeg = stringForTestsetNeg;
	}
	
	/**
	 * @return the jointModelDisabled
	 */
	public boolean isJointModelDisabled() {
		return jointModelDisabled;
	}
	/**
	 * @param jointModelDisabled the jointModelDisabled to set
	 */
	public void setJointModelDisabled(boolean jointModelDisabled) {
		this.jointModelDisabled = jointModelDisabled;
	}
	public String getDirForAUCfiles(String target, WILLSetup setup) {
		// If models are being written somewhere, then also write AUC's there (this allows us to avoid writing in a dir that only contains INPUT files) - hence, multiple runs can simultaneously use the same input dir, yet write to different output dirs.
		String aucTempDirectory =  (getResultsDirVal() != null ? getResultsDirVal() : setup.getOuterLooper().getWorkingDirectory()) + "AUC/";
		if (getTargetPredVal().size() > 1) { 
			aucTempDirectory += target;
		}			
		if (getModelFileVal() != null) {
			aucTempDirectory += getModelFileVal();
		}
		Utils.ensureDirExists(aucTempDirectory);
		return aucTempDirectory;
	}
	public boolean isLearnMLN() {
		return learnMLN;
	}
	public boolean isSoftM() {
		return SoftM;
	}
	public void setLearnMLN(boolean learnMLN) {
		this.learnMLN = learnMLN;
	}

       //Changed By Navdeep Kaur
       public boolean isGroundedRelationalRW() {
	        return GroundedRelationalRW;
       }

       //Changed By Navdeep Kaur
       public void setGroundedRelationalRW(boolean GroundedRelationalRW) {
	        this.GroundedRelationalRW = GroundedRelationalRW;
       }
    
	public void setSoftM(boolean SoftM) {
		this.SoftM = SoftM;
	}
	
	public double getAlpha() {
		return alpha;
	}

	public void setAlpha(double alpha) {
		this.alpha = alpha;
	}


	public double getBeta() {
		return beta;
	}

	public void setBeta(double beta) {
		this.beta = beta;
	}

	public boolean isLearnProbExamples() {
		return learnProbExamples;
	}
	public void setLearnProbExamples(boolean learnProbExamples) {
		this.learnProbExamples = learnProbExamples;
	}
	public boolean isDisableAdvice() {
		return disableAdvice;
	}
	public void setDisableAdvice(boolean disableAdvice) {
		this.disableAdvice = disableAdvice;
	}
	public String getPriorAdvice() {
		return priorAdvice;
	}
	public void setPriorAdvice(String priorAdvice) {
		this.priorAdvice = priorAdvice;
	}
	/**
	 * @return the usingDefaultClausebase
	 */
	public boolean isUsingDefaultClausebase() {
		return usingDefaultClausebase;
	}
	/**
	 * @param usingDefaultClausebase the usingDefaultClausebase to set
	 */
	public void setUsingDefaultClausebase(boolean usingDefaultClausebase) {
		this.usingDefaultClausebase = usingDefaultClausebase;
	}
	/**
	 * @return the printingTreeStats
	 */
	public boolean isPrintingTreeStats() {
		return printingTreeStats;
	}
	/**
	 * @param printingTreeStats the printingTreeStats to set
	 */
	public void setPrintingTreeStats(boolean printingTreeStats) {
		this.printingTreeStats = printingTreeStats;
	}
	/**
	 * @return the createSyntheticEgs
	 */
	public boolean isCreateSyntheticEgs() {
		return createSyntheticEgs;
	}
	/**
	 * @param createSyntheticEgs the createSyntheticEgs to set
	 */
	public void setCreateSyntheticEgs(boolean createSyntheticEgs) {
		this.createSyntheticEgs = createSyntheticEgs;
	}
	/**
	 * @return the createHidenFile
	 */
	public boolean isCreateHiddenFile() {
		return createHiddenFile;
	}
	/**
	 * @param createHidenFile the createHidenFile to set
	 */
	public void setCreateHidenFile(boolean createHidenFile) {
		this.createHiddenFile = createHidenFile;
	}
	public void setUseApproxCountVal(boolean val)//change by MD & DD for approx
	{
		this.useApproxCountVal=val;
	}
	
	public boolean isCountApprox()
	{
		return useApproxCountVal;
	}
}
