package edu.wisc.cs.will.ILP;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.AllOfFOPC;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Theory;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.ILP.CoverageScore;
import edu.wisc.cs.will.ILP.Gleaner;
import edu.wisc.cs.will.ILP.ILPCrossValidationLoop;
import edu.wisc.cs.will.ILP.ILPSearchAction;
import edu.wisc.cs.will.ILP.ILPSearchListener;
import edu.wisc.cs.will.ILP.ILPouterLoop;
import edu.wisc.cs.will.ILP.ILPparameterSettings;
import edu.wisc.cs.will.ILP.LearnOneClause;
import edu.wisc.cs.will.ILP.OnionFilter;
import edu.wisc.cs.will.ILP.ScoreSingleClause;
import edu.wisc.cs.will.ILP.ScoreSingleClauseByAccuracy;
import edu.wisc.cs.will.ILP.TuneParametersForILP;
import edu.wisc.cs.will.ILP.TuneParametersForILP.ReasonToStopEarly;
import edu.wisc.cs.will.ResThmProver.DefaultHornClauseContext;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CondorFileReader;
import edu.wisc.cs.will.Utils.condor.CondorFileWriter;
import edu.wisc.cs.will.stdAIsearch.BestFirstSearch;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchStrategy;

/**
 *
 * @author shavlik
 *
 */

public class ExperimenterMR { // TODO - maybe this should be ExperimentWithSimulatedData?
	private  ILPouterLoop      outerLooper;
	private  LearnOneClause    learnOneClause;
	private  HornClauseContext context;
	public   Boolean           relevanceEnabled = null;

	private static String task                 = "NFL";
	private static String dataDirectory        = "/u/shavlikgroup/projects/MachineReading/MRtestbeds/" + task + "/";
	private static String resultsDirectory     = "/u/shavlikgroup/people/Jude/MRtestbedResults/"       + task + "/";
	private static String windowsResultsDir    = "J:\\Jude\\MRtestbedResults\\"                        + task + "\\";
	private static String windowsDataDirectory = "S:\\projects\\MachineReading\\MRtestbeds\\"          + task + "\\";
	
    protected String  mainWorkingDir           = dataDirectory;
    private boolean   runningInWindows         = mainWorkingDir.substring(1).startsWith(":\\"); // A sufficient hack for Windows?  TODO - need to evaluate later?
    
    // These are likely to be reset by the command-line arguments.
    public String     directory                = "./";
    public String     prefix                   = "Date";
    private int       foldInUse                = 0;
    
    private boolean           checkpointEnabled     = false;
    private long              maxTimeInMilliseconds = 3 * 24 * 60 * 60 * 1000L; // As a default, allow a max of three days (e.g., overnight plus the weekend).  This is in milliseconds, but remember that the max time, command-line argument is in seconds!
    private ReasonToStopEarly the_reasonToStopEarly = ReasonToStopEarly.useBestAccuracyToStopEarly;

    private Set<String> lessonsToSkip = new HashSet<String>(32); 
    
    private int     numberOfFolds     =   1; // <------------------
    private int     maxNodesExpanded  = 100; // This is the number of ILP rule bodies that are EXPANDED by adding literals.
    private double  thresholdForUsingTuningSets       = 0.275; // E.g., if our train set has 100 examples, once 27.5 are in use (e.g., in a learning curve), we use a tuning set.
    private double  fractionOfExamplesUsedForTuning   = 0.33;  // NOTE: set the previous value to a negative number to turn off useSingleTrainTuneSplit.
  
    private boolean useOnion       = true;
    private boolean useRRR         = false;
    private boolean flipFlopPosNeg = false;
    private String  fileExtension            = Utils.defaultFileExtension;
    private String  fileExtensionWithPeriod  = Utils.defaultFileExtensionWithPeriod;

    public OnionFilter onionFilter = null;

    private boolean overWriteOldResults = false; // Please don't change me.  If you need to change this, override it in a subclass via the setupUserOverrides() method.
        
	public  String[] lessonsToUse = {
	     "gameLoser_NFLTeamNFLGame"
		,"gameWinner_NFLTeamNFLGame"
	    ,"homeTeamInGame_NFLTeamNFLGame"
		,"awayTeamInGame_NFLTeamNFLGame"
	    ,"gameDate_DateNFLGame"
		,"scoringEventTD_NFLTeamNFLGameScore"
		,"scoringEventFG_NFLTeamNFLGameScore"
		,"teamFinalScore_ScoreNFLTeamNFLGame"
		,"NFLGame"
		,"NFLTeam"
		,"score"
		};
    
    public Theory        bestTheory;
    public CoverageScore bestTheoryTrainingScore;
    public PredicateName targetPredicateName;

	public ExperimenterMR() { }

    public void setup(String[] args) throws SearchInterrupted {
    	setup(args, false, false);
    }
    public boolean setup(String[] args, boolean onlyScanArgs, boolean skipIfTheoryFileExists) throws SearchInterrupted {
		args = Utils.chopCommentFromArgs(args);

        Utils.Verbosity defaultVerbosity = Utils.isDevelopmentRun() ? Utils.Verbosity.Developer : Utils.Verbosity.Medium;

        processFlagArguments(args);

        if (onlyScanArgs) { return false; }
        
		Utils.seedRandom(12345);

        if ( Utils.isVerbositySet() == false ){
            Utils.setVerbosity(defaultVerbosity);
        }
        
        // See if we need to make this run.  DO THIS BEFORE LOADING ALL THE FILES, SINCE THAT TAKES AWHILE.
        // TODO - check for the RESULTS file?
        if (skipIfTheoryFileExists) {
        	File theoryFile = Utils.ensureDirExists(resultsSubDir() + "_theory" + fileExtensionWithPeriod);
        	
            if (theoryFile.exists()) { 
            	Utils.println("\n% Since this theory file exists, this run will be skipped (delete or rename the file if you wish to recompute it):\n%  " + theoryFile);
          
                File resultsFile = Utils.ensureDirExists(resultsSubDir() + "_testsetResult" + fileExtensionWithPeriod);
                if (!resultsFile.exists()) {
                	waitHereUnlessCondorJob("BUT THE CORRESPONDING RESULTS FILE IS MISSING! " + resultsFile);
                	return false;
                }
				Utils.println("\n% Theory and results files already exist.");
				return false;
            }
            File resultsFile = Utils.ensureDirExists(resultsSubDir() + "_testsetResult" + fileExtensionWithPeriod);
            if (resultsFile.exists()) { 
            	Utils.println("\n% Although no theory file exists, this run will be skipped because a results file exists (delete or rename the file if you wish to recompute it):\n%  " + resultsFile);  
            	return false;
            } 
			Utils.println("\n% Neither theory nor results file exists.\n   " + theoryFile + "\n   " + resultsFile);
        }


		String[] newArgList = new String[4];
		newArgList[0] = getPosTrainExamplesFileName();
		newArgList[1] = getNegTrainExamplesFileName();
		newArgList[2] = getTrainBKfileName(); // Here we want the original (BK and facts).
		newArgList[3] = getTrainFactsFileName();

        for (int i = 0; i <= 3; i++) { Utils.println("% setup:  newArgList[i] = " + newArgList[i]);}
		if (flipFlopPosNeg) {
			String   temp = newArgList[0];
			newArgList[0] = newArgList[1];
			newArgList[1] = temp;
		}

		Utils.createDribbleFile(resultsSubDir() + "_dribble." + fileExtension);
        
		try {
            HandleFOPCstrings stringHandler = new HandleFOPCstrings(true); // OK for this to be a NEW string handler (since we might be running multiple experiments in sequence).
            stringHandler.setStringsAreCaseSensitive(true); // TODO - don't want this for non-BL tasks.   
            // We want everything new each run.
            context        = new DefaultHornClauseContext(stringHandler);
			outerLooper    = new ILPouterLoop(dataSubDir(), null, newArgList, new Gleaner(), context);  // Use null for prefix since already in directory.   
			learnOneClause = outerLooper.innerLoopTask;
			if (Utils.getSizeSafely(learnOneClause.getTargets()) < 1) { // TODO - clean this up!
				targetPredicateName = learnOneClause.getPosExamples().get(0).predicateName; // WILL CRASH IF NO POS EXAMPLES.
			} else {
				targetPredicateName = learnOneClause.targets.get(0).predicateName;
			}			
			
        } catch (IOException e) {
        	Utils.reportStackTrace(e);
			Utils.error("Error: " + e);
		}
        setupParameters();

		if (getLearnOneClause().createdSomeNegExamples) {
			Example.writeObjectsToFile(newArgList[1], getLearnOneClause().getNegExamples(), ".", "// Negative examples, including created ones.");
		}

        return true;
    }

    
    private void reportDoc(String docStringForCallToOnion, double trainsetAccuracy, double tuneSetAccuracy, double testSetAccuracy) {
        File docFile = Utils.ensureDirExists(resultsSubDir() + "_OnionDoc" + fileExtensionWithPeriod); // Use commas to separate files so can concatenate these into a *.csv file so they can be sorted in Excel.
        Utils.println("% Create this Onion documentation file: " + docFile);
    	try {
        	new CondorFileWriter(docFile, false).append("Onion" + (TuneParametersForILP.allOnionDocOnOneLine ? "," : "\n")
        										   + docStringForCallToOnion + (TuneParametersForILP.allOnionDocOnOneLine ? "," : "\n")
        										   + "    Train/Tune/Test accuracies: "
        										   + Utils.truncate(trainsetAccuracy, 4) + "/"
        										   + Utils.truncate(tuneSetAccuracy,  4) + "/"
        										   + Utils.truncate(testSetAccuracy,  4) + "\n").close();
        } catch (IOException e) {
        	Utils.waitHere("% Could not save the current Onion call's documentation string to file:\n%  " + docFile + "\n%  " + e);
        }    	
    }
    
    private void noTheoryWasLearned() {
		Utils.println("\n% The ONION was unable to find an acceptable theory.");
		// Save the theory file.
        File theoryFile = Utils.ensureDirExists(resultsSubDir() + "_theory" + fileExtensionWithPeriod);
        Utils.println("% Create this 'nothing learned' theory: " + theoryFile);
        try {
        	String theoryAsString = "NOTHING LEARNED!";
        	new CondorFileWriter(theoryFile, false).append(theoryAsString).close();
        } catch (IOException e) {
        	Utils.waitHere("% Could not save the learned theory to file:\n%  " + theoryFile + "\n%  " + e);
        }    	
        // Save the result of guessing the majority category. TODO - make this be the case 
        saveDefaultResultsToFile();
    }
    
    private void saveDefaultResultsToFile() {
    	saveResultsToFile(0.5, 0.5, 0.5);
    }
    
    private void saveResultsToFile(double trainSetScore, double tuneSetScore, double testSetScore) {
        String testSetFileName = resultsSubDir() + "_testsetResult" + fileExtensionWithPeriod;
        File   testSetFile     = Utils.ensureDirExists(testSetFileName);
        try {
        	String resultStr = prefix;
        	boolean majorityClassIsPos = false; // TO DO CONFIRM THIS.
        	// Put this in for debugging/confirmation purposes.		
        	
	        resultStr += getExperimentSecondarySignature();
        	new CondorFileWriter(testSetFile, false).append(resultStr + ", " + trainSetScore + ", " + tuneSetScore + ", " + testSetScore + "\n").close();
        } catch (IOException e) {
        	Utils.waitHere("% Could not save the testset results to file:\n%  " + testSetFile + "\n%  " + e);
        }
    }
    
    private String getExperimentSecondarySignature() { // This DOES NOT INCLUDE fractionOfTrainingExamplesToUse/probOfDroppingLiteral/probOfFlippingClassLabel/useAdvice
    	return                                                ", [thresholdForUsingTuningSets("    + 
	     Utils.truncate(thresholdForUsingTuningSets,     2) + ")/fractionOfExamplesUsedForTuning(" + // Don't put any extra commas in here!
		 Utils.truncate(fractionOfExamplesUsedForTuning, 2) + ")/maxNodesExpanded("                + 
		 maxNodesExpanded                                   + ")]";
    }
    
    
    public LearnOneClause createLearnOneClauseForLesson()  {
        try {
            String[] newArgList = new String[4];
            newArgList[0] = getPosTrainExamplesFileName();
            newArgList[1] = getNegTrainExamplesFileName();
            newArgList[2] = getTrainBKfileName();
            newArgList[3] = getTrainFactsFileName();
            for (int i = 0; i <= 3; i++) { Utils.println("  " + newArgList[i]);}
            LearnOneClause loc = new LearnOneClause(dataSubDir(), null, newArgList[0], newArgList[1], newArgList[2], newArgList[3], null, null);
            return loc;
        } catch (Exception e) {
            Utils.reportStackTrace(e);
            Utils.println("createLearnOneClauseForLesson error: " + e);
            Utils.waitHere("Unable to load lesson ILP files for lesson " + prefix + " under directory " + directory + ".");
        }
        return null;        
    }
    
    public boolean isTheoryNothingLearned(File theoryFile) {
    	BufferedReader r = null;
    	try {
    		r = new BufferedReader(new CondorFileReader(theoryFile));    	
    		String line;        
    		line = parseUntil("NOTHING LEARNED", r, null);    		
    		return line != null;
    	}
    	catch(Exception e) {    		
    	}
    	finally {
    		if ( r != null )
				try {r.close();	} catch (IOException e) {}
    	}    	
    	return false;
    }

    private String parseUntil(String string, BufferedReader r, String errorString) throws IOException {
        String line = null;
        while ((line = r.readLine()) != null) {
        	//Utils.println(line);
            if (line.contains(string) || (errorString != null && line.contains(errorString)) ) {
                return line;
            }
        }
        return null;
    }
    // For safety, test with a FRESH LearnOneClause, stringHandler, set of facts (currently reusing the same), etc.
    public CoverageScore getTestSetScore(PredicateName targetPname, Theory theory) throws IOException {
    	if (theory == null) { return null; }
        String[] newArgList = new String[4];
        newArgList[0] = getPosTestExamplesFileName();
        newArgList[1] = getNegTestExamplesFileName();
        newArgList[2] = getTestBKfileName();
        newArgList[3] = getTestFactsFileName();
        for (int i = 0; i <= 3; i++) { Utils.println("% getTestSetScore:  newArgList[i] = " + newArgList[i]);}
        if (theory.isNegated()) { theory.rewriteFlipFloppedTheory(false); } 
        LearnOneClause freshL1C      = new LearnOneClause(dataSubDir(), null, newArgList[0], newArgList[1], newArgList[2], newArgList[3], null, null);
        boolean hold = AllOfFOPC.truncateStrings;
        AllOfFOPC.truncateStrings = false;
        List<Sentence> theoryClauses = freshL1C.getParser().readFOPCstream(theory.toString()); // Reparse so we know it works in a new environment.
        AllOfFOPC.truncateStrings = hold;
        Theory         theoryAnew    = new Theory(freshL1C.getStringHandler());
        context                      = freshL1C.getContext();
        for (Sentence sentence : theoryClauses) {
        	List<Clause> clauses = sentence.convertToClausalForm();
        	for (Clause clause : clauses) {
        		if  (clause.getDefiniteClauseHead().predicateName.name.equals(targetPname.name)) {
        			theoryAnew.addMainClause(clause);  // No need to add these to the context because the getWeightedCoverage code will walk through all the main clauses.
        		}
        		else {
        			theoryAnew.addSupportingClause(clause);
            		context.assertDefiniteClause(clause);
        		}
        	}
        }
        freshL1C.setMEstimatePos(0); // M-estimates are to help avoid overfitting the training set, so not needed here (though 'error bars' would be nice).
        freshL1C.setMEstimateNeg(0);
        CoverageScore results = freshL1C.getWeightedCoverage(theoryAnew);
        // Utils.println("theory:        " + theory);
        // Utils.println("theoryClauses: " + theoryClauses);
        // Utils.println("targetPname:   " + targetPname);
        // Utils.println("theoryAnew:    " + theoryAnew);
        Utils.println("\n%getTestSetScore(" + targetPname + (theory.isNegated() ? ", flipped" : "") + ")'s performance:\n" + results.toShortString());
        return results;
    }
    
    private String dataSubDir()     { return directory        + prefix + "/trainf" + foldInUse + "/"; }
    private String resultsSubDir()  { return resultsDirectory + prefix + "/trainf" + foldInUse + "/" + prefix; }
    private String trainSubstring() { return                             "/trainf" + foldInUse + "/trainf" + foldInUse; }
    private String  testSubstring() { return                             "/testf"  + foldInUse + "/testf"  + foldInUse; }
    
    
    private String getTrainBKfileName() {
    	return directory + prefix + trainSubstring() + "_bk"    + fileExtensionWithPeriod;
    }
    private String getTrainFactsFileName() {
    	return directory + prefix + trainSubstring() + "_facts" + fileExtensionWithPeriod;
    }
    private String getPosTrainExamplesFileName() {
    	return directory + prefix + trainSubstring() + "_pos"   + fileExtensionWithPeriod;
    }    
    private String getNegTrainExamplesFileName() {
    	return directory + prefix + trainSubstring() + "_neg"   + fileExtensionWithPeriod;
    }    
    
    private String getTestBKfileName() {
    	return directory + prefix + testSubstring()  + "_bk"    + fileExtensionWithPeriod;
    }
    private String getTestFactsFileName() {
    	return directory + prefix + testSubstring()  + "_facts" + fileExtensionWithPeriod;
    }
    private String getPosTestExamplesFileName() {
    	return directory + prefix + testSubstring()  + "_pos"   + fileExtensionWithPeriod;
    }    
    private String getNegTestExamplesFileName() {
    	return directory + prefix + testSubstring()  + "_neg"   + fileExtensionWithPeriod;
    }    
    
    public void runILP() throws SearchInterrupted, IOException {
        if (outerLooper != null) { outerLooper.initialize(false); }
        long start1 = System.currentTimeMillis();
		long end1;
		try {
			if        (Utils.getSizeSafely(outerLooper.innerLoopTask.getPosExamples()) < 0) {
				reportDoc("Did not bother training, since no positive examples.", 0.5, 0.5, 0.5);
				noTheoryWasLearned(); // TODO - only works when the data is 50-50.  we need to write more generally!  Ie, make theory: head :- false
				return;
			} else if (Utils.getSizeSafely(outerLooper.innerLoopTask.getNegExamples()) < 0) {
				reportDoc("Did not bother training, since no negative examples.", 0.5, 0.5, 0.5);
				noTheoryWasLearned(); // TODO - only works when the data is 50-50.  we need to write more generally!  Ie, make theory: head :- true
				return;
			} else if (useOnion) {
				TuneParametersForILP onion = new TuneParametersForILP(outerLooper, numberOfFolds);
				onion.setUseSingleTrainTuneSplit(true);				
				
				// Utils.println("maxTimeInMilliseconds = " + maxTimeInMilliseconds);
				onion.setMaxSecondsToSpend((int) Math.min(Integer.MAX_VALUE, maxTimeInMilliseconds / 1000));
				onion.theReasonToStopEarly = the_reasonToStopEarly;
                onion.setFilter(onionFilter);
				onion.run();

				bestTheory = onion.getTheoryFromBestFold();
				Utils.println("\n% ------------------------------------------------");
				if (bestTheory == null || bestTheory.isEmpty()) {
					Utils.println("\n% The ONION was unable to find an acceptable theory.");
					noTheoryWasLearned();
					reportDoc(onion.descriptionOfOnionProcessingNeeded, 0.5, 0.5, 0.5);
				} else {
					bestTheory.collectAnyRemainingInliners();
					if (bestTheory.isNegated()) { bestTheory.rewriteFlipFloppedTheory(); }
                    bestTheoryTrainingScore       = onion.getBestFold().getTrainingCoverageScore();
                    double bestTheoryTuningScore  = getAccuracy(onion.getBestFold().getEvaluationCoverageScore());
                    CoverageScore testsetCoverage = getTestSetScore(targetPredicateName, bestTheory);
    				reportDoc(onion.descriptionOfOnionProcessingNeeded, bestTheoryTrainingScore.getAccuracy(), bestTheoryTuningScore, testsetCoverage.getAccuracy());
                    double bestTheoryTestingScore = getAccuracy(testsetCoverage); 
					Utils.println("\n\n% Best Theory Chosen by the Onion" + (bestTheory.isNegated() ? " (via Flip-Flopping)" : "") + ":");
					Utils.println(bestTheory.toPrettyString("    "));
					Utils.println("\n" + onion.getBestFold()); // was getResultsFromBestFold()
					Utils.print(  "\n\n% Chosen Parameter Settings:");
					Utils.println(onion.bestSetting.toString(true));				
	
			        // Save the theory file.
			        File theoryFile = Utils.ensureDirExists(resultsSubDir() + "_theory" + fileExtensionWithPeriod);
			        try {
			            boolean hold = AllOfFOPC.truncateStrings;
			            AllOfFOPC.truncateStrings = false;
			        	String theoryAsString = bestTheory.toPrettyString("");
			        	AllOfFOPC.truncateStrings = hold;
			        	theoryAsString += "\n/*\n\n" + onion.getBestFold() + "\n%%% Fresh TESTING Coverage Score:\n" + testsetCoverage.toLongString() + "\n\n*/\n";
			        	new CondorFileWriter(theoryFile, false).append(theoryAsString).close();
			        } catch (IOException e) {
			        	Utils.waitHere("% Could not save the learned theory to file:\n%  " + theoryFile + "\n%  " + e);
			        }
			        // Save the result score in a CSV format.
			        saveResultsToFile(getAccuracy(bestTheoryTrainingScore), bestTheoryTuningScore, bestTheoryTestingScore);
				}
				Utils.println("\n% ------------------------------------------------");
			} else {
				waitHereUnlessCondorJob("This method has mainly been tested with the (above) Onion.  So the calls below might be out of date.");
				ILPCrossValidationLoop cvLoop = new ILPCrossValidationLoop(outerLooper, numberOfFolds, 0, 0);
	            cvLoop.setFlipFlopPositiveAndNegativeExamples(flipFlopPosNeg);
	            cvLoop.setMaximumCrossValidationTimeInMillisec(maxTimeInMilliseconds);
				cvLoop.executeCrossValidation();
	        //	ILPCrossValidationResult results = cvLoop.getCrossValidationResults();
			}
		}
        catch (StackOverflowError e) {
        	Utils.reportStackTrace(e);
        	Utils.error("Something went wrong ...");
        }


		end1 = System.currentTimeMillis();
		// Use 'err' here so we see these.
		Utils.printlnErr("\n% Took "    + Utils.convertMillisecondsToTimeSpan(end1 - start1, 3) + ".");
        Utils.printlnErr(  "% Executed "  + Utils.comma(getLearnOneClause().getTotalProofsProved()) + " proofs " + String.format("in %.2f seconds (%.2f proofs/sec).", getLearnOneClause().getTotalProofTimeInNanoseconds()/1.0e9, getLearnOneClause().getAverageProofsCompletePerSecond()));
        Utils.printlnErr(  "% Performed " + Utils.comma(Unifier.getUnificationCount()) + " unifications while proving Horn clauses.");
    }
    
    private double getAccuracy(CoverageScore score) {
    	if (score == null) { return -1; }
		return score.getAccuracy();
	}
	
	private boolean isaCondorJob = false;
	private  void waitHereUnlessCondorJob(String msg) {
		if (isaCondorJob) { Utils.println(msg); } else { Utils.waitHere(msg); }
	}

    private void processFlagArguments(String[] args) throws IllegalArgumentException {
        int offset = 0;

        for (int arg = 0; arg < args.length; arg++) {
            if      (args[arg].equalsIgnoreCase("rrr") || args[arg].equalsIgnoreCase("-rrr")) {
                useRRR = true;
            }
            else if (args[arg].startsWith("offset")) {
                offset = Integer.parseInt(args[arg].substring(args[arg].indexOf("=") + 1));
            }
            else if (args[arg].startsWith("condorJWS=")) {
            	directory                = dataDirectory; // Condor needs absolute pathways.
            	runningInWindows         = mainWorkingDir.substring(1).startsWith(":\\");
            	isaCondorJob             = true && !runningInWindows;
            	if (runningInWindows) { directory  = windowsDataDirectory; resultsDirectory = windowsResultsDir; }
            	
                int condorID   = offset + Integer.parseInt(args[arg].substring(args[arg].indexOf("=") + 1));
                int onesDigit  = (condorID        % 10);
                int tensDigit  = (condorID /   10 % 10);
                int hundsDigit = (condorID /  100 % 10);
                int thousDigit = (condorID / 1000 % 10);
                
                Utils.println("% condorJWS: thousDigit=" + thousDigit + " hundsDigit=" + hundsDigit + "  tensDigit=" + tensDigit + " onesDigit=" + onesDigit);                
                
                String keeper1 = null;
                String keeper2 = null;

                foldInUse = onesDigit;
                if (foldInUse > 4) { System.exit(0); }
                
				switch (tensDigit) {
					case 0: keeper1 = "NFLGame"; keeper2 = "NFLTeam";  break;
					case 1: keeper1 = "Date";    keeper2 = "score";    break;
					case 2: keeper1 = "gameLoser_NFLTeamNFLGame";      break;
					case 3: keeper1 = "gameWinner_NFLTeamNFLGame";     break;
					case 4: keeper1 = "homeTeamInGame_NFLTeamNFLGame"; break;
					case 5: keeper1 = "awayTeamInGame_NFLTeamNFLGame"; break;
					case 6: keeper1 = "gameDate_DateNFLGame";          break;
					case 7: keeper1 = "scoringEventTD_NFLTeamNFLGameScore";  break;
					case 8: keeper1 = "scoringEventFG_NFLTeamNFLGameScore";  break;
					case 9: keeper1 = "teamFinalScore_ScoreNFLTeamNFLGame";  break;
				}
				
				if (hundsDigit > 0 && keeper2 != null) { keeper1 = keeper2; keeper2 = null; } // Can run all with 120 condor jobs.
				
                for (String str : lessonsToUse) if (!str.equalsIgnoreCase(keeper1) && !str.equalsIgnoreCase(keeper2)) {
                	lessonsToSkip.add(str);
                } 
                
            }
            else if (args[arg].equalsIgnoreCase("true") || args[arg].equalsIgnoreCase("-true")) {
                useRRR = true;
            }
            else if (args[arg].equalsIgnoreCase("false") || args[arg].equalsIgnoreCase("-false")) {
                useRRR = false;
            }
            else if (args[arg].equalsIgnoreCase("std") || args[arg].equalsIgnoreCase("-std")) {
                useRRR = false;
            }
            else if (args[arg].equalsIgnoreCase("flip") || args[arg].equalsIgnoreCase("-flip")) {
                flipFlopPosNeg = true;
            }
            else if (args[arg].startsWith("cwd=") || args[arg].startsWith("-cwd=") || args[arg].startsWith("dir=") || args[arg].startsWith("-dir=") || args[arg].startsWith("directory=") || args[arg].startsWith("-directory=")) {
            	mainWorkingDir = args[arg].substring(args[arg].indexOf("=") + 1);
            }
            else if (args[arg].startsWith("-prefix=")) {
                prefix = args[arg].substring(args[arg].indexOf("=") + 1);
            }
            else if (Utils.isaInteger(args[arg])) {
                numberOfFolds = Integer.parseInt(args[arg]);
            } // A bare number is interpreted as the number of folds.
            else if (args[arg].startsWith("-folds=")) {
                numberOfFolds = Integer.parseInt(args[arg].substring(args[arg].indexOf("=") + 1));
            }
//            else if (args[arg].startsWith("-fold=")) {
//                firstFold = Integer.parseInt(args[arg].substring(args[arg].indexOf("=") + 1));
//                lastFold = firstFold;
//            }
            else if (args[arg].equalsIgnoreCase("-checkpoint")) {
                checkpointEnabled = true;
            }
            else if (args[arg].equalsIgnoreCase("-relevance")) {
                relevanceEnabled = true;
            }
            else if (args[arg].equalsIgnoreCase("-norelevance")) {
                relevanceEnabled = false;
            }
            else if (args[arg].startsWith("-maxTime=") || args[arg].startsWith("-maxTimeInMsec=") || args[arg].startsWith("-maxTimeInMillisec=")) {
                maxTimeInMilliseconds = Integer.parseInt(args[arg].substring(args[arg].indexOf("=") + 1)) * 1000L;
            }
            else if (args[arg].startsWith("-maxTimeInSec=") || args[arg].startsWith("-maxTimeInSeconds=")) {
                maxTimeInMilliseconds = Integer.parseInt(args[arg].substring(args[arg].indexOf("=") + 1));
            }
            else if (args[arg].equalsIgnoreCase("useOnion") || args[arg].equalsIgnoreCase("-useOnion")) {
                useOnion = true;
            }
            else if (args[arg].equalsIgnoreCase("onion") || args[arg].equalsIgnoreCase("-onion")) {
                useOnion = true;
            }
            else if (args[arg].equalsIgnoreCase("noonion") || args[arg].startsWith("noOnion") || args[arg].equalsIgnoreCase("-noOnion")) {
                useOnion = false;
            }
            else if (args[arg].startsWith("-extension=") || args[arg].startsWith("extension=")) {
                fileExtension = args[arg].substring(args[arg].indexOf("=") + 1);
            }
            else {
                throw new IllegalArgumentException("Unknown argument specified: " + args[arg]);
            }
        }
    }

    private void setupParameters() {
        Gleaner gleaner = (Gleaner) getLearnOneClause().searchMonitor;
        outerLooper.directoryForGleanerFile = resultsDirectory + prefix + "/trainf" + foldInUse + "/";
        outerLooper.writeGleanerFilesToDisk = true;
        //		if (args.length > 3) { getLearnOneClause().setMinPosCoverage(Double.parseDouble(args[3])); }
        //		if (args.length > 4) { getLearnOneClause().setMinPrecision(  Double.parseDouble(args[4]));   }
        // Set some additional parameters for the inner-loop runs.
        getLearnOneClause().setMaxNodesToConsider(maxNodesExpanded); // This should be SMALLER THAN THE NEXT BECAUSE THIS IS THE NUMBER OF *POP* FROM OPEN.  I.e., it is the number of EXPANSIONS.
        getLearnOneClause().setMaxNodesToCreate(100 * maxNodesExpanded); // This is the maximum number of nodes to ADD to OPEN.  (WHAT HAPPENS WHEN THIS IS HIT?  ILP SEARCH STOPS?  I ASSUME SO.  NO NEED TO EMPTY OPEN.)
        getLearnOneClause().maxSearchDepth     = 1000;
        getLearnOneClause().verbosity          = 0;
        getLearnOneClause().maxBodyLength      = 7; // Changed by JWS for debugging purposes (feel free to edit).
        getLearnOneClause().maxNumberOfNewVars = 7;
        getLearnOneClause().maxDepthOfNewVars  = 7;
        getLearnOneClause().maxPredOccurrences = 3;
        getLearnOneClause().setMaxNegCoverage(0.4999); // Never cover more than 1/2th the negatives.  TODO - what about the 'always say neg' rule (or its equivalent)?  Assume flip-flop will handle?
        outerLooper.max_total_nodesExpanded    = 1000000;
        outerLooper.max_total_nodesCreated     =     100 * outerLooper.max_total_nodesExpanded;
        outerLooper.maxNumberOfClauses         = 2; // <-----------------------
        outerLooper.maxNumberOfCycles          = 2 * outerLooper.maxNumberOfClauses;
        getLearnOneClause().minNumberOfNegExamples = 1;
        getLearnOneClause().setMinPosCoverage(1);
        getLearnOneClause().restartsRRR = 25;
        getLearnOneClause().getStringHandler().setStarMode(TypeSpec.minusMode);
        getLearnOneClause().setMEstimatePos(0.01);
        getLearnOneClause().setMEstimateNeg(0.01);
        gleaner.reportingPeriod = 1000;
        outerLooper.setMinPrecisionOfAcceptableClause(0.5);
        //outerLooper.initialize(false); // We want to initialize this as late as possible.
        outerLooper.setCheckpointEnabled(checkpointEnabled);
        getLearnOneClause().setDumpGleanerEveryNexpansions(1000);
    }
    
    public HornClauseContext getContext() {
        if ( context == null ) {
            if ( outerLooper == null ) {
                context = new DefaultHornClauseContext();
            }
            else {
                context = getLearnOneClause().getContext();
            }
        }
        return context;
    }


    public boolean isOverWriteOldResults() {
        return overWriteOldResults;
    }

    public void setOverWriteOldResults(boolean overWriteOldResults) {
        if ( overWriteOldResults == true ) {
            Utils.warning("Overriding 'overWriteOldResults' to true.  I hope you know what you are doing.");
        }
        this.overWriteOldResults = overWriteOldResults;
    }

    public LearnOneClause getLearnOneClause() {
        return learnOneClause;
    }
        
    public void setupUserOverrides() {

    }

    /** Free any objects that are being held by Experimenter but aren't needed...
     *
     */
    private void cleanup() {

        Utils.println("% Freeing memory after runILP: outLooper = null, learnOneClause = null, context = null, bestTheory = null, bestTheoryTrainingScore = null.");

        outerLooper    = null;
        learnOneClause = null;
        context        = null;

        // We might want to keep these.
        bestTheory              = null;
        bestTheoryTrainingScore = null;
        targetPredicateName     = null;
    }

    public static void mainJWS(String[] args) throws SearchInterrupted, IOException {
    	mainJWS(args, false);
    }
	/**
	 * @param args
	 * @throws SearchInterrupted
	 * @throws IOException 
	 */

    public static void mainJWS(String[] args, boolean calledFromWindows) throws SearchInterrupted, IOException {
        ExperimenterMR main = new ExperimenterMR();
        mainJWS(args, calledFromWindows, main);
    }

	public static void mainJWS(String[] args, boolean calledFromWindows, ExperimenterMR main) throws SearchInterrupted, IOException {
		Utils.doNotCreateDribbleFiles  = true;  // Be sure to notice the NOT.
		Utils.doNotPrintToSystemDotOut = false; // Ditto.

		long start = System.currentTimeMillis();

		if (calledFromWindows) { 
			main.mainWorkingDir   = windowsDataDirectory;
			resultsDirectory      = windowsResultsDir;
			main.runningInWindows = true;
		} else {
			main.mainWorkingDir   = dataDirectory;
			main.runningInWindows = false;
		}
		///////////////////////////
		
		// Set for the default run (i.e., if there are no arguments).
		main.maxTimeInMilliseconds = 6 * 60 * 60 * 1000; // This is for any ONE task (but over ALL Onion layers for that task).

		main.processFlagArguments(args);
        main.setupUserOverrides();
        for (String str : main.lessonsToUse) if (!str.isEmpty() && !main.lessonsToSkip.contains(str)) {			
        	main.prefix    = str;
        	main.directory = main.mainWorkingDir;
			String[] theseArgs = new String[1]; // Have set useOnion=true elsewhere, but force it here?  If not, we still something to send to setup, even if just an empty list.
			theseArgs[0]   = "-onion"; // Turn on variables that we want.  TODO - should this be done earlier so callers can overwrite or should we force it?
			
			main.processFlagArguments(theseArgs);
			boolean continueThisRun = main.setup(theseArgs, false, true);
			Utils.println("% continueThisRun=" + continueThisRun + " overWriteOldResults=" + main.overWriteOldResults + " lessonsToSkip: " + main.lessonsToSkip + "\n\n% *****\n% ");
			if (!continueThisRun) { main.cleanup(); continue; }
			main.runILP();
			main.cleanup();
        }
		// Use 'err' here so we see these.
		Utils.printlnErr("\n\n%  DONE!  Took " + Utils.convertMillisecondsToTimeSpan(System.currentTimeMillis() - start, 3) + " overall."); 
	}
	
	// Let's always leave this AFTER all the special versions so new users can easily find it.
    public static void mainDefault(String[] args) throws SearchInterrupted, IOException {
		ExperimenterMR main = new ExperimenterMR();
		main.setup(args);
		main.runILP();
    }
    
    public static void main(String[] rawArgs) throws SearchInterrupted, IOException { // TODO - catch the IOException closer to its source ...
    	String[] args = Utils.chopCommentFromArgs(rawArgs);
		if (args.length > 0) for (int i = 0; i < args.length; i++) {
			Utils.println("% MAIN: arg[" + i + "] = " + args[i]);
		}// waitHereUnlessCondorJob();
		
	//	String userName = Utils.getUserName();	waitHereUnlessCondorJob("user name = " + userName);
		if (false) { mainJWS(args,true); }
		else       { mainDefault(args);  }
	}

    public class RecordActiveAdviceSearchListener implements ILPSearchListener {
        ILPparameterSettings currentOnionSettings = null;
        int currentFold;

        public ILPSearchAction onionLayerStarting(TuneParametersForILP onion, ILPparameterSettings onionLayer) {
            currentOnionSettings = onionLayer;
            return ILPSearchAction.PERFORM_LOOP;
        }

        public void onionLayerFinished(TuneParametersForILP onion, ILPparameterSettings onionLayer) {
        }

        public ILPSearchAction crossValidationFoldStarting(ILPCrossValidationLoop cvLoop, int fold) {
            return ILPSearchAction.PERFORM_LOOP;
        }

        public void crossValidationFoldFinished(ILPCrossValidationLoop cvLoop, int fold) {
            this.currentFold = fold;

        }

        public ILPSearchAction outerLoopStarting(ILPouterLoop outerLoop) {
            return ILPSearchAction.PERFORM_LOOP;
        }

        public void outerLoopFinished(ILPouterLoop outerLoop) {
        }

        public ILPSearchAction innerLoopStarting(LearnOneClause learnOneClause) {
            return ILPSearchAction.PERFORM_LOOP;
        }

        public void innerLoopFinished(LearnOneClause learnOneClause) {

        }

    }
}
