/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.ILP;

import java.io.File;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.Utils.condor.CondorFileWriter;

import java.io.FileNotFoundException;
import java.io.IOException;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Theory;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.ResThmProver.DefaultHornClauseContext;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.BestFirstSearch;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchStrategy;
import java.io.FileWriter;

/**
 *
 * @author twalker
 */
public final class ILPMain {

    public ILPouterLoop outerLooper;

    private LearnOneClause learnOneClause;

    public HornClauseContext context;

    public int numberOfFolds = 1;

    public String directory;

    public String prefix = null;

    public int firstFold = 0;

    public int lastFold = -1;

    public boolean checkpointEnabled = false;

    private long maxTimeInMilliseconds = 3 * 24 * 60 * 60 * 1000L; // As a default, allow a max of three days (e.g., overnight plus the weekend).  This is in milliseconds, but remember that the max time, command-line argument is in seconds!

    public boolean useRRR = false;

    public boolean flipFlopPosNeg = false;

    public boolean lowerCaseMeansVariable = false; // TODO - allow user to specify this.

    public String fileExtension = Utils.defaultFileExtension;

    boolean useOnion = true;

    public Boolean relevanceEnabled = true;

    public OnionFilter onionFilter = null;

    private static final String testBedsPrefix = "../Testbeds/"; // But DO include the backslash here.

    public Theory bestTheory = null;

    public CoverageScore bestTheoryTrainingScore = null;

    public ILPMain() {
    }

    public void setup(String... args) throws SearchInterrupted {
        args = Utils.chopCommentFromArgs(args);

        Utils.Verbosity defaultVerbosity = Utils.isDevelopmentRun() ? Utils.Verbosity.Developer : Utils.Verbosity.Medium;

        processFlagArguments(args);

        Utils.seedRandom(12345);

        if (Utils.isVerbositySet() == false) {
            Utils.setVerbosity(defaultVerbosity);
        }

        if (lastFold == -1) {
            lastFold = numberOfFolds - 1;
        }

        boolean partialRun = (firstFold != 0 && lastFold != numberOfFolds - 1);

        setupDirectoryAndPrefix(args);

        String[] newArgList = new String[4];
        newArgList[0] = directory + "/" + prefix + "_pos." + fileExtension;
        newArgList[1] = directory + "/" + prefix + "_neg." + fileExtension;
        newArgList[2] = directory + "/" + prefix + "_bk." + fileExtension;
        newArgList[3] = directory + "/" + prefix + "_facts." + fileExtension;

        if (flipFlopPosNeg) {
            String temp = newArgList[0];
            newArgList[0] = newArgList[1];
            newArgList[1] = temp;
        }

        Utils.createDribbleFile(directory + "/" + prefix + "_dribble" + (useRRR ? "_rrr" : "") + (flipFlopPosNeg ? "_flipFlopped" : "") + (partialRun ? "_fold" + firstFold + "to" + lastFold : "") + "." + fileExtension);
        //	Utils.waitHere(directory + prefix + "_dribble" + (useRRR ? "_rrr" : "") + (flipFlopPosNeg ? "_flipFlopped" : "") + (partialRun ? "_fold" + firstFold + "to" + lastFold : "" ) + "." + fileExtension);

        try {
            //	HandleFOPCstrings stringHandler = new HandleFOPCstrings(lowerCaseMeansVariable);
            if (context == null) {
                context = new DefaultHornClauseContext();
            }
            outerLooper = new ILPouterLoop(directory, prefix, newArgList, new Gleaner(), context);
        } catch (IOException e) {
            Utils.reportStackTrace(e);
            Utils.error("File not found: " + e.getMessage());
        }
        setupParameters();

        if (getLearnOneClause().createdSomeNegExamples) {
            Example.writeObjectsToFile(newArgList[1], getLearnOneClause().getNegExamples(), ".", "// Negative examples, including created ones.");
        }

        setupRelevance();
    }

    public void runILP() throws SearchInterrupted {

        outerLooper.initialize(false);

        long start1 = System.currentTimeMillis();
        long end1;

        if (useOnion) {
            TuneParametersForILP onion = new TuneParametersForILP(outerLooper, numberOfFolds);
            onion.setFilter(onionFilter);
            // Utils.println("maxTimeInMilliseconds = " + maxTimeInMilliseconds);
            onion.setMaxSecondsToSpend((int) Math.min(Integer.MAX_VALUE, maxTimeInMilliseconds / 1000));
            onion.run();
            bestTheory = onion.getTheoryFromBestFold();
            Utils.println("\n% ------------------------------------------------");
            if (bestTheory == null) {
                Utils.println("\n% The ONION was unable to find an acceptable theory.");
            }
            else {
                Utils.println("\n\n% Best Theory Chosen by the Onion:");
                Utils.println(bestTheory.toPrettyString("    "));
                Utils.println("\n" + onion.getResultsFromBestFold());

                if (onion.bestSetting != null) {
                    Utils.print("\n\n% Chosen Parameter Settings:");
                    Utils.println(onion.bestSetting.toString(true));
                }

                CrossValidationFoldResult bestFold = onion.getBestFold();

                if (bestFold != null) {
                    bestTheoryTrainingScore = bestFold.getTrainingCoverageScore();
                }
            }
            Utils.println("\n% ------------------------------------------------");
        }
        else {
            ILPCrossValidationLoop cvLoop = new ILPCrossValidationLoop(outerLooper, numberOfFolds, firstFold, lastFold);
            cvLoop.setFlipFlopPositiveAndNegativeExamples(flipFlopPosNeg);
            cvLoop.setMaximumCrossValidationTimeInMillisec(maxTimeInMilliseconds);
            cvLoop.executeCrossValidation();
            //	ILPCrossValidationResult results = cvLoop.getCrossValidationResults();
        }

        end1 = System.currentTimeMillis();
        Utils.println("\n% Took " + Utils.convertMillisecondsToTimeSpan(end1 - start1, 3) + ".");
        Utils.println("% Executed " + Utils.comma(getLearnOneClause().getTotalProofsProved()) + " proofs " + String.format("in %.2f seconds (%.2f proofs/sec).", getLearnOneClause().getTotalProofTimeInNanoseconds() / 1.0e9, getLearnOneClause().getAverageProofsCompletePerSecond()));
        Utils.println("% Performed " + Utils.comma(Unifier.getUnificationCount()) + " unifications while proving Horn clauses.");
    }

    public void writeLearnedTheory(String prologueString) {

        if (bestTheory != null) {
            if (directory != null && prefix != null) {
                File theoryFile = new File(directory, prefix + "_theory.txt");
                try {
                    String theoryAsString = prologueString + bestTheory.toPrettyString("") + "\n";

                    new CondorFileWriter(theoryFile).append(theoryAsString).close();
                } catch (IOException except) {
                    Utils.printlnErr("Could not save the learned theory to a file: " + except.toString() + ".");
                }
            }
        }
    }

    private void processFlagArguments(String[] args) throws IllegalArgumentException {
        // Allow these three to come in any order.
        for (int arg = 1; arg < args.length; arg++) {
            if (args[arg].equalsIgnoreCase("rrr") || args[arg].startsWith("-rrr")) {
                useRRR = true;
            }
            else if (args[arg].equalsIgnoreCase("true") || args[arg].startsWith("-true")) {
                useRRR = true;
            }
            else if (args[arg].equalsIgnoreCase("false") || args[arg].startsWith("-false")) {
                useRRR = false;
            }
            else if (args[arg].equalsIgnoreCase("std") || args[arg].startsWith("-std")) {
                useRRR = false;
            }
            else if (args[arg].startsWith("flip") || args[arg].startsWith("-flip")) {
                flipFlopPosNeg = true;
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
            else if (args[arg].startsWith("-fold=")) {
                firstFold = Integer.parseInt(args[arg].substring(args[arg].indexOf("=") + 1));
                lastFold = firstFold;
            }
            else if (args[arg].equals("-checkpoint")) {
                checkpointEnabled = true;
            }
            else if (args[arg].equals("-relevance")) {
                relevanceEnabled = true;
            }
            else if (args[arg].equals("-norelevance")) {
                relevanceEnabled = false;
            }
            else if (args[arg].startsWith("-maxTime=")) {
                int i = Integer.parseInt(args[arg].substring(args[arg].indexOf("=") + 1));
                if (i <= 0) {
                    maxTimeInMilliseconds = Long.MAX_VALUE;
                }
                else {
                    maxTimeInMilliseconds = i * 1000L;
                }
            }
            else if (args[arg].startsWith("useOnion") || args[arg].equalsIgnoreCase("-useOnion")) {
                useOnion = true;
            }
            else if (args[arg].startsWith("onion") || args[arg].equalsIgnoreCase("-onion")) {
                useOnion = true;
            }
            else if (args[arg].startsWith("noonion") || args[arg].startsWith("noOnion") || args[arg].equalsIgnoreCase("-noOnion")) {
                useOnion = false;
            }
            else if (args[arg].startsWith("-") == false) {
                fileExtension = args[1];
            }
            else {
                throw new IllegalArgumentException("Unknown argument specified: " + args[arg]);
            }
        }
    }

    private void setupDirectoryAndPrefix(String[] args) throws IllegalArgumentException {
        // LearnOnClause performs the inner loop of ILP.
        directory = args[0];
        File dir = new CondorFile(directory);
        if (dir.isDirectory() == false) {
            dir = new CondorFile(testBedsPrefix + directory);
        }
        if (dir.isDirectory() == false) {
            throw new IllegalArgumentException("Unable to find problem directory '" + directory + "'.");
        }
        directory = dir.getPath();
        if (prefix == null) {
            prefix = dir.getName();
        }
        if (prefix.endsWith("/")) {
            prefix = prefix.substring(0, prefix.length() - 1);
        }
    }

    private void setupParameters() {
        Gleaner gleaner = (Gleaner) getLearnOneClause().searchMonitor;
        outerLooper.writeGleanerFilesToDisk = true;
        //		if (args.length > 3) { getLearnOneClause().setMinPosCoverage(Double.parseDouble(args[3])); }
        //		if (args.length > 4) { getLearnOneClause().setMinPrecision(  Double.parseDouble(args[4]));   }
        // Set some additional parameters for the inner-loop runs.
        maxTimeInMilliseconds = 12 * 60 * 60 * 1000; // This is for any ONE task (but over ALL Onion layers for that task).
        getLearnOneClause().setMaxNodesToConsider(10000); // <-----------------------
        getLearnOneClause().setMaxNodesToCreate(100000);
        getLearnOneClause().maxSearchDepth = 1000;
        getLearnOneClause().verbosity = 0;
        getLearnOneClause().maxBodyLength = 4; // Changed by JWS for debugging purposes (feel free to edit).
        getLearnOneClause().maxNumberOfNewVars = 6;
        getLearnOneClause().maxDepthOfNewVars = 6;
        getLearnOneClause().maxPredOccurrences = 6;
        outerLooper.max_total_nodesExpanded = 100000; // <-----------------------
        outerLooper.max_total_nodesCreated = 10 * outerLooper.max_total_nodesExpanded;
        outerLooper.maxNumberOfClauses = 2; // <-----------------------
        outerLooper.maxNumberOfCycles = 2 * outerLooper.maxNumberOfClauses;
        getLearnOneClause().minNumberOfNegExamples = 1;
        getLearnOneClause().setMinPosCoverage(1);
        getLearnOneClause().restartsRRR = 25;
        getLearnOneClause().stringHandler.setStarMode(TypeSpec.plusMode);
        getLearnOneClause().setMEstimatePos(0.01); // <-----------------------
        getLearnOneClause().setMEstimateNeg(0.01); // <-----------------------
        gleaner.reportingPeriod = 1000;
        outerLooper.setMinPrecisionOfAcceptableClause(0.5);// <-----------------------
        //outerLooper.initialize(false); // We want to initialize this as late assert possible.
        outerLooper.setCheckpointEnabled(checkpointEnabled);
        getLearnOneClause().setDumpGleanerEveryNexpansions(1000);
    }

    private void setupRelevance() throws SearchInterrupted {
        if (isRelevanceEnabled()) {
            try {
                File file = getRelevanceFile();
                getLearnOneClause().setRelevanceFile(file);
                getLearnOneClause().setRelevanceEnabled(true);
            } catch (FileNotFoundException fileNotFoundException) {
                throw new SearchInterrupted("Relevance File '" + getRelevanceFile() + "' not found:\n  " + fileNotFoundException);
            } catch (IllegalStateException illegalStateException) {
                throw new SearchInterrupted(illegalStateException);
            }
        }
        else {
            getLearnOneClause().setRelevanceEnabled(false);
        }
    }

    public HornClauseContext getContext() {
        if (context == null) {
            if (outerLooper == null) {
                context = new DefaultHornClauseContext();
            }
            else {
                context = getLearnOneClause().getContext();
            }
        }

        return context;
    }

    public boolean isRelevanceEnabled() {
        return relevanceEnabled == null ? getRelevanceFile().exists() : relevanceEnabled;
    }

    public void setRelevanceEnabled(Boolean relevanceEnabled) {
        this.relevanceEnabled = relevanceEnabled;
    }

    public boolean isRelevanceEnableSet() {
        return relevanceEnabled != null;
    }

    public File getRelevanceFile() {
        File relevanceFile = new CondorFile(directory + "/" + prefix + "_bkRel." + fileExtension);

        return relevanceFile;
    }

    public LearnOneClause getLearnOneClause() {
        return outerLooper.innerLoopTask;
    }

    public Theory getBestTheory() {
        return bestTheory;
    }

    public static void mainJWS(String[] args) throws SearchInterrupted, IOException {
        //	Experimenter.mainJWS(args);
        ExperimenterMR.mainJWS(args);
    }

    public static void main(String[] args) throws SearchInterrupted, IOException {
        String userName = Utils.getUserName();
        //	waitHereUnlessCondorJob("user name = " + userName);
        if ("shavlik".equals(userName)) {
            mainJWS(args);
            System.exit(0);
        } // IF YOU ADD AN ENTRY, BE SURE TO USE *ELSE* OTHERWISE mainDefault will also be called.
        else if ("twalker".equals(userName)) {
            mainJWS(args);
            System.exit(0);
        }
        //	else if ("kunapg".equals( userName)) { mainGK( args);  System.exit(0); }
        //  else if () { mainYOU(args); }
        else {
            mainDefault(args);
        }
    }

    /**
     * @param args
     * @throws SearchInterrupted
     */
    public static void mainDefault(String[] args) throws SearchInterrupted {
        ILPMain main = new ILPMain();
        main.setup(args);
        main.runILP();
    }
}
