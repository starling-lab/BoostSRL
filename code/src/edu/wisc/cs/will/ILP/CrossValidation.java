///*
// * To change this template, choose Tools | Templates
// * and open the template in the editor.
// */
//
package edu.wisc.cs.will.ILP; // The Eclipse JAR code complains if this is a file of only comments.
//
//import edu.wisc.cs.will.DataSetUtils.Example;
//import edu.wisc.cs.will.FOPC.Theory;
//import edu.wisc.cs.will.Utils.Stopwatch;
//import edu.wisc.cs.will.Utils.Utils;
//import edu.wisc.cs.will.Utils.condor.CondorFile;
//import edu.wisc.cs.will.Utils.condor.CondorFileInputStream;
//import edu.wisc.cs.will.Utils.condor.CondorFileOutputStream;
//import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
//import java.io.BufferedInputStream;
//import java.io.BufferedOutputStream;
//import java.io.File;
//import java.io.IOException;
//import java.io.InputStream;
//import java.io.InvalidClassException;
//import java.io.ObjectInputStream;
//import java.io.ObjectOutputStream;
//import java.io.OutputStream;
//import java.io.StreamCorruptedException;
//import java.util.Iterator;
//import java.util.List;
//import java.util.Set;
//import java.util.TreeSet;
//import java.util.zip.GZIPInputStream;
//import java.util.zip.GZIPOutputStream;
//
///**
// *
// * @author twalker
// */
public class CrossValidation { } // The Eclipse JAR code complains if this is a file of only comments.
//
//    private ILPLoop ilpLoop;
//
//    private CrossValidationResult crossValidationResult;
//
//    private int numberOfFolds;
//
//    private CrossValidationExampleSets crossValidationExampleSets;
//
//    /** Creates an ILPCrossValidationLoop with <code>numberOfFolds</code> folds.
//     *
//     * This constructor will create a full cross-validation run.  When executeCrossValidation() is called,
//     * all folds will be run.
//     *
//     * The allPositiveExample and allNegativeExample sets will be obtained from the onion, permuted randomly,
//     * and split into the appropriate number of folds.
//     *
//     * @param onion onion to use during the search.  This should be the same for all folds.
//     * @param numberOfFolds Number of folds to run.
//     */
//    public CrossValidation(ILPLoop ilpLoop, int numberOfFolds) {
//        this(ilpLoop, numberOfFolds, null);
//    }
//
//    /** Creates an ILPCrossValidationLoop with <code>numberOfFolds</code> folds
//     * and sets this loop to run fold <code>firstFoldToRun</code> through <code>lastFoldToRun</code>.
//     *
//     * This constructor will create a full cross-validation run.  When executeCrossValidation() is called, only
//     * folds from firstFoldToRun to lastFoldToRun will be run.  Folds are indexed from 0.
//     *
//     * @param ilpLoop onion to use during the search.  This should be the same for all folds.
//     * @param numberOfFolds Number of folds to run.
//     * @param ilpCrossValidationExampleSets Collection of examples to use for cross validation.
//     * @param firstFoldToRun
//     * @param lastFoldToRun
//     */
//    public CrossValidation(ILPLoop ilpLoop, int numberOfFolds, CrossValidationExampleSets ilpCrossValidationExampleSets) {
//
//        if (numberOfFolds < 1) {
//            throw new IllegalArgumentException("You must run at least a single fold.");
//        }
//
//        this.ilpLoop = ilpLoop;
//    }
//
//    public void executeCrossValidation() throws SearchInterrupted {
//
//        initialize();
//
//        for (int currentFold = 0; currentFold <= numberOfFolds; currentFold++) {
//                executeCrossValidationForFold(currentFold);
//        }
//    }
//
//    /** Creates a CrossValidationFoldResult object and scores the training/testing sets.
//     *
//     * @param currentFold
//     * @param theory
//     * @param gleaner
//     * @return
//     */
//    private CrossValidationFoldResult createCVFoldResult(int fold, Theory theory, Gleaner gleaner) {
//        CrossValidationFoldResult result = new CrossValidationFoldResult(fold, theory, gleaner);
//
//        CoverageScore cs;
//
//        List<Example> positiveExamples = getPositiveEvaluationExamplesForFold(fold);
//        List<Example> negativeativeExamples = getNegativeEvaluationExamplesForFold(fold);
//        if ((positiveExamples != null && positiveExamples.size() > 0) || (negativeativeExamples != null && negativeativeExamples.size() > 0)) {
//            cs = ilpLoopState.getWeightedCoverage(theory, positiveExamples, negativeativeExamples);
//            result.setEvaluationCoverageScore(cs);
//        }
//
//        positiveExamples = getPositiveTrainingExamplesForFold(fold);
//        negativeativeExamples = getNegativeTrainingExamplesForFold(fold);
//        if ((positiveExamples != null && positiveExamples.size() > 0) || (negativeativeExamples != null && negativeativeExamples.size() > 0)) {
//            cs = ilpLoopState.getWeightedCoverage(theory, positiveExamples, negativeativeExamples);
//            result.setTrainingCoverageScore(cs);
//        }
//
//        positiveExamples = getAllPositiveExamples();
//        negativeativeExamples = getAllNegativeExamples();
//        if ((positiveExamples != null && positiveExamples.size() > 0) || (negativeativeExamples != null && negativeativeExamples.size() > 0)) {
//            cs = ilpLoopState.getWeightedCoverage(theory, positiveExamples, negativeativeExamples);
//            result.setAllExamplesCoverageScore(cs);
//        }
//
//        return result;
//    }
//
//    private void executeCrossValidationForFold(int currentFold) throws SearchInterrupted {
//
//        boolean isFoldComplete = isFoldCompleted(currentFold);
//
//        if (isFoldComplete == false) {
//
//            if (LearnOneClause.debugLevel > -10) {
//                Utils.println("\n% Initializing fold " + Utils.comma(currentFold) + ".");
//            }
//
//            Stopwatch s = new Stopwatch();
//
//            // Safe the state of the outer loop so we can replace it later.
//            // We do this just in case someone else is relying on the outer loop
//            // not changing during cross validation.
//            TuneParametersForILPState originalState = ilpLoopState.getonionState();
//            List<Example> originalPositiveExamples = ilpLoopState.getPositiveExamples();
//            List<Example> originalNegativeExamples = ilpLoopState.getNegativeExamples();
//            List<Example> originalEvalSetPositiveExamples = ilpLoopState.getEvalSetPositiveExamples();
//            List<Example> originalEvalSetNegativeExamples = ilpLoopState.getEvalSetNegativeExamples();
//
//            TuneParametersForILPState onionStateForThisFold = getTuneParametersForILPStateForFold(currentFold);
//
//            // Set the state of the TuneParametersForILP to be the onionState for this fold...
//            // We will lose the existing other loop state, but that is okay.  Either
//            // a copy has been stored in the cvState or it was read in as part of a
//            // restart.  In any case, the verifyCVState should have checked that
//            // it was okay to swap these...
//            ilpLoopState.setonionState(onionStateForThisFold);
//            ilpLoopState.setPositiveExamples(getPositiveTrainingExamplesForFold(currentFold));
//            ilpLoopState.setNegativeExamples(getNegativeTrainingExamplesForFold(currentFold));
//            ilpLoopState.setEvalSetPositiveExamples(getPositiveEvaluationExamplesForFold(currentFold));
//            ilpLoopState.setEvalSetNegativeExamples(getNegativeEvaluationExamplesForFold(currentFold));
//
//            // Make sure we create a new Gleaner, so we have results just for this fold...
//            ilpLoopState.setGleaner(new Gleaner());
//
//            if (getMaximumCrossValidationTimeInMillisec() != Long.MAX_VALUE) {
//                ilpLoopState.setMaximumClockTimeInMillisec(getMaximumCrossValidationTimeInMillisec() / getNumberOfFolds());
//            }
//            else {
//                ilpLoopState.setMaximumClockTimeInMillisec(Long.MAX_VALUE);
//            }
//
//            if (LearnOneClause.debugLevel > -10) {
//                Utils.println("%   Number of positive TRAIN examples = " + Utils.comma(ilpLoopState.getPositiveExamples()) + ".");
//                Utils.println("%   Number of negativeative TRAIN examples = " + Utils.comma(ilpLoopState.getNegativeExamples()) + ".");
//                //jws3      Utils.println("%   Number of positive TUNE  examples = " + Utils.comma(onion.getTuneSetPositiveExamples()) + ".");
//                //      Utils.println("%   Number of negativeative TUNE  examples = " + Utils.comma(onion.getTuneSetNegativeExamples()) + ".");
//                Utils.println("%   Number of positive EVAL  examples = " + Utils.comma(ilpLoopState.getEvalSetPositiveExamples()) + ".");
//                Utils.println("%   Number of negativeative EVAL  examples = " + Utils.comma(ilpLoopState.getEvalSetNegativeExamples()) + ".");
//            }
//
//            // Wrap this the run in a try-catch so that the finally clause can restore the
//            // onion to pre-CV values regardless of the outcome of the search.
//            try {
//                setupAdvice(ilpLoopState);
//
//                    Theory theory = ilpLoopState.executeonion();
//
//                    theory.setNegativeated(getFlipFlopPositiveAndNegativeativeExamples());
//
//                    if (LearnOneClause.debugLevel > -10) {
//                        Utils.println(String.format("\n%% Finished fold %d (%.2fs):", currentFold, s.getTotalTimeInSeconds()));
//                        Utils.println("\n" + ilpLoopState.reportSearchStats());
//                        Utils.println("\n% " + ilpLoopState.getLearnedTheory().toPrettyString("% "));
//                    }
//
//                    // Grab the gleaner from the innerLoop.
//                    // Not, we don't want to save the gleaner we created a couple lines
//                    // above since the onion may have restored a different gleaner
//                    // from a saved checkpoint file.
//                    Gleaner gleaner = ilpLoopState.getGleaner();
//
//                    // If onion didn't throw an exception, lets assume everything worked.
//                    // We can add a check later...
//                    CrossValidationFoldResult result = createCVFoldResult(currentFold, theory, gleaner);
//                    setFoldResult(currentFold, result);
//
//                    // Delete the checkpoint since we know that this fold is done and
//                    // it won't be needed anymore...
//                    if (filesystemUseEnabled) {
//                        // Write the result out to disk.  This is how we will know that a run is complete in the
//                        // future...
//                        writeResult(result);
//
//                        ilpLoopState.deleteCheckpoint();
//                    }
//
//                    ilpLoopState.innerLoopTask.fireonionFinished(ilpLoopState);
//
//            } catch (IOException ioe) {
//                // Hmmm...there was a problem saving the search...that is probably a bad thing...
//                // Let's throw an exception...
//                throw new SearchInterrupted("Error occurred while attempting to save cross validation results for fold " + currentFold + ": " + ioe.toString());
//            } finally {
//                // Put back the state no matter what happened during the outer loop search...
//                ilpLoopState.setonionState(originalState);
//                ilpLoopState.setPositiveExamples(originalPositiveExamples);
//                ilpLoopState.setNegativeExamples(originalNegativeExamples);
//                ilpLoopState.setEvalSetPositiveExamples(originalEvalSetPositiveExamples);
//                ilpLoopState.setEvalSetNegativeExamples(originalEvalSetNegativeExamples);
//
//                unsetAdvice(ilpLoopState);
//            }
//        }
//        else if (filesystemUseEnabled) {
//            // We will read in the fold results here, so that we can do early stopping if desired.
//            try {
//                CrossValidationFoldResult result = readResultsForFold(currentFold);
//                setFoldResult(currentFold, result);
//            } catch (IOException ioe) {
//            }
//        }
//    }
//
//    /** Consolidates all of the fold results.
//     *
//     * This is normally called by the process that ran the first fold of the cross-validation,
//     * but could be called separately if necessary.
//     *
//     * If called separately, use the initializeAndConsolidateCrossValidationResults() method
//     * since there is some initialization that has to occur before this will work.
//     *
//     * This method will block waiting for all the runs to finish.
//     *
//     * @throws SearchInterrupted A SearchInterrupted message will be throw if something bad
//     * occurs during consolidation.  Most likely this will be the result of an IO error
//     * during the reading of the results.
//     */
//    protected void consolidateCrossValidationResults() throws SearchInterrupted {
//
//        if (filesystemUseEnabled == false) {
//            throw new IllegalStateException("Filesystem Use disabled.  Cannot consolidate CV results.");
//        }
//        else {
//            try {
//                waitForAllFoldsToFinish();
//
//                readAllFoldResults();
//
//                writeFinalReport();
//
//                if (removeFoldResultFilesAfterConsolidation) {
//                    removeResultFiles();
//                }
//
//            } catch (IOException ex) {
//                throw new SearchInterrupted(ex);
//            }
//        }
//    }
//
//    /** Waits for all the Runs to Finish.
//     *
//     * This just checks that runs are finished.  It does not actually
//     * load the runs.
//     *
//     * This will block until all the runs are completed.
//     */
//    private void waitForAllFoldsToFinish() {
//
//        TreeSet<Integer> unfinishedFolds = new TreeSet<Integer>();
//
//        for (int fold = 0; fold < getNumberOfFolds(); fold++) {
//            unfinishedFolds.add(fold);
//        }
//
//        while (unfinishedFolds.isEmpty() == false) {
//            for (Iterator<Integer> it = unfinishedFolds.iterator(); it.hasNext();) {
//                int fold = it.next();
//
//                if (isFoldCompleted(fold)) {
//                    it.remove();
//                }
//            }
//
//            if (unfinishedFolds.isEmpty() == false) {
//                if (filesystemUseEnabled == false) {
//                    throw new IllegalStateException("Filesystem storage is disabled.  However, one or more folds are not complete.  This should not happen.");
//                }
//
//                Utils.println(Utils.getPrettyString("Waiting for fold", "to finish.  Will check again in 30 seconds.", unfinishedFolds));
//                try {
//                    Thread.sleep(30000);
//                } catch (InterruptedException ex) {
//                }
//            }
//        }
//    }
//
//    /** Reads the results of all folds.
//     *
//     * The results will be placed in the results array and can be accessed
//     * via the getResults() method.
//     *
//     * This method assumes that all of the results exist and are on disk.
//     * If they aren't, it will result in a IOException when the missing
//     * fold is read.  The waitForAllFoldsToFinish() method can be used to
//     * wait for the completion of runs.
//     *
//     * @throws IOException An IOException will be throw if the results for one of the
//     * folds does not exist.
//     */
//    public void readAllFoldResults() throws IOException {
//        if (filesystemUseEnabled == false) {
//            throw new IllegalStateException("Attempting to read fold results from disk while filesystem storage is disabled.");
//        }
//        else {
//            boolean done = false;
//            int maxTries = 3;
//            int tries = 0;
//
//            while (!done && tries < maxTries) {
//                done = true;
//
//                for (int fold = 0; fold < getNumberOfFolds(); fold++) {
//                    if (getFoldResult(fold) == null) {
//
//                        try {
//                            CrossValidationFoldResult result = readResultsForFold(fold);
//
//                            if (result.getFold() != fold) {
//                                throw new RuntimeException("The results file for fold " + fold + " appears to hold results from fold " + result.getFold() + " instead.  This shouldn't happen.");
//                            }
//
//                            setFoldResult(fold, result);
//                        } catch (StreamCorruptedException sce) {
//                            // The stream is corrupt.  This probably means that the file
//                            // is in the process of being read.
//                            Utils.println("The results for fold " + fold + " appears to be corrupted.  It may be in the process of writing.");
//                            done = false;
//                        }
//                    }
//                }
//
//                tries++;
//
//                if (done == false && tries < maxTries) {
//                    // One or more folds is corrupt, probably being written by a different process.
//                    // Lets wait if we can.
//                    Utils.println("One or more result files were corrupt.  Will attempt to read again in 30 seconds. " + (maxTries - tries) + " attempts remaining.");
//                    try {
//                        Thread.sleep(30000);
//                    } catch (InterruptedException ex) {
//                    }
//                }
//            }
//
//            if (!done) {
//                // Crap, we didn't get all of the runs...
//                // This really shouldn't have happened.
//                Set<Integer> unfinishedRuns = new TreeSet<Integer>();
//                for (int i = 0; i < getNumberOfFolds(); i++) {
//                    if (getFoldResult(i) == null) {
//                        unfinishedRuns.add(i);
//                    }
//                }
//
//                String err = Utils.getPrettyString("Fold", " are corrupt and unreadable.  They should probably be delete and rerun.", unfinishedRuns);
//                throw new RuntimeException(err);
//            }
//        }
//    }
//
//    private void removeResultFiles() {
//
//        if (filesystemUseEnabled) {
//            for (int fold = 0; fold < getNumberOfFolds(); fold++) {
//                File f = new CondorFile(ilpLoopState.getResultFileNameForFold(fold));
//                if (f.exists()) {
//                    f.delete();
//                }
//            }
//
//            File f = getCVStateFile();
//            if (f.exists()) {
//                f.delete();
//            }
//        }
//    }
//
//    /** Initializes the CrossValidation and consolidates the results.
//     *
//     *
//     * @throws SearchInterrupted
//     */
//    public void initializeAndConsolidateCrossValidationResults() throws SearchInterrupted {
//        try {
//            initialize();
//        } catch (IOException ioe) {
//            throw new SearchInterrupted("Something unexpected happened while initializing crossValidation: " + ioe.toString());
//        } catch (IncongruentSavedStateException isse) {
//            throw new SearchInterrupted("Error while restoring cross validation saved state: " + isse.toString() + "\n"
//                    + "This probably means that the saved state (" + getCVStateFile() + ") should be removed and the "
//                    + "search restarted.");
//        }
//
//        consolidateCrossValidationResults();
//    }
//
//    /** Indicates this run should consolidate everything.
//     *
//     * Theortically, you could have a run whose only job was to consolidate
//     * the results.  For now, just make the guy who did the first run the
//     * consolidator.
//     *
//     * @return
//     */
//    private boolean isConsolidator() {
//        return firstFoldToRun == 0;
//    }
//
//    private boolean isFoldCompleted(int currentFold) {
//
//        if (getFoldResult(currentFold) != null) {
//            // We have a fold result in memory, so it is definitely completed
//            return true;
//        }
//
//        // Doesn't exist in memory, so check the disk...
//        if (filesystemUseEnabled) {
//            File f = new CondorFile(ilpLoopState.getResultFileNameForFold(currentFold));
//            if (f.exists()) {
//                return true;
//            }
//        }
//
//        return false;
//    }
//
//    private void initialize() throws IOException, IncongruentSavedStateException {
//
//        ILPCrossValidationState savedCVState = null;
//
//        if (firstFoldToRun == 0) {
//            savedCVState = readCVState(false);
//
//            if (savedCVState == null) {
//                savedCVState = initializeCVState();
//                writeCVState(savedCVState);
//            }
//        }
//        else {
//            savedCVState = readCVState(true);
//        }
//
//        verifyCVState(savedCVState);
//        mergeCVState(savedCVState);
//    }
//
//    private ILPCrossValidationState readCVState(boolean waitForCreation) {
//
//        ILPCrossValidationState readState = null;
//
//        if (filesystemUseEnabled) {
//
//            File cvStateFile = getCVStateFile();
//
//
//            int tries = 0;
//            int maxTries = 10;
//
//            while (tries == 0 || (waitForCreation && tries < maxTries && readState == null)) {
//
//                if (cvStateFile.exists()) {
//                    ObjectInputStream ois = null;
//                    InputStream is = null;
//                    try {
//                        is = new CondorFileInputStream(cvStateFile);
//
//                        if (cvStateFile.getName().endsWith(".gz")) {
//                            is = new GZIPInputStream(is);
//                        }
//
//                        ois = new ILPObjectInputStream(new BufferedInputStream(is), ilpLoopState.innerLoopTask.stringHandler, ilpLoopState.innerLoopTask);
//
//                        readState = (ILPCrossValidationState) ois.readObject();
//
//                    } catch (InvalidClassException ex) {
//                        throw new RuntimeException("The cross validation state on the disk is not longer compatible with the current WILL "
//                                + "codebase.  Please remove the state file \"" + cvStateFile + "\" and restart all runs.");
//                    } catch (ClassNotFoundException ex) {
//                        throw new RuntimeException("Odd Error reading cross validation state. This probably shouldn't have happened.", ex);
//                    } catch (IOException ex) {
//                    } finally {
//                        try {
//                            if (ois != null) {
//                                ois.close();
//                            }
//                            else if (is != null) {
//                                is.close();
//                            }
//                        } catch (IOException ex) {
//                        }
//                    }
//
//                }
//
//                if (readState == null && waitForCreation) {
//                    Utils.println("Waiting for fold 0 to create cross validation state file \"" + cvStateFile + "\"...");
//                    try {
//                        Thread.sleep(30000);
//                    } catch (InterruptedException interruptedException) {
//                    }
//                }
//
//                tries++;
//            }
//
//            if (waitForCreation && readState == null) {
//                throw new IllegalStateException("Non-main CV loop didn't find CV state file after " + maxTries + ".  Quiting.");
//            }
//        }
//
//        return readState;
//    }
//
//    /** Initialized the
//     *
//     * Previously, this actually created a new state based on the existing cvState that
//     * was created during the constructor.  However, since it was a direct clone
//     * and all we did here was setup examples, it didn't really make sense to do
//     * that anymore.
//     *
//     * Not, this is still only called by the fold 0 cross-validation process.  If there are
//     * other cross-validation processes (for parallel execution), their cvState will be
//     * replaced by the fold 0 one saved to disk.
//     */
//    private ILPCrossValidationState initializeCVState() {
//        if (getILPCrossValidationExampleSets() == null) {
//            CrossValidationExampleSets ilpcves = new CrossValidationExampleSets(getNumberOfFolds(), ilpLoopState.getPositiveExamples(), ilpLoopState.getNegativeExamples());
//            setILPCrossValidationExampleSets(ilpcves);
//        }
//
//        return cvState;
//    }
//
//    /**
//     * @return the onion
//     */
//    protected TuneParametersForILP getOnion() {
//        return ilpLoopState;
//    }
//
//    /**
//     * @param onion the onion to set
//     */
//    protected void setOnion(TuneParametersForILP onion) {
//        this.ilpLoopState = onion;
//    }
//
//    public int getNumberOfFolds() {
//        return getNumberOfFolds();
//    }
//
//    /** Sets the CrossValidationResult for fold.
//     *
//     * @param fold
//     * @param result
//     * @throws IllegalStateException
//     */
//    protected void setFoldResult(int fold, CrossValidationFoldResult result) throws IllegalStateException {
//        if (crossValidationResult == null) {
//            crossValidationResult = new CrossValidationResult(getNumberOfFolds());
//        }
//
//        crossValidationResult.setFoldResult(fold, result);
//    }
//
//    /** Returns the CrossValidationResult for fold, null if that fold is not currently stored.
//     *
//     * Only the run doing the consolidation of all the fold stores this information.  Other runs
//     * never need it.
//     *
//     * @param fold
//     * @return
//     * @throws IllegalStateException
//     */
//    protected CrossValidationFoldResult getFoldResult(int fold) throws IllegalStateException {
//        if (crossValidationResult == null) {
//            return null;
//        }
//
//        return crossValidationResult.getFoldResult(fold);
//    }
//
//    /** Returns the Consolidated results for the Cross Validation.
//     *
//     * If the runs aren't finished or this isn't the consolidator of the
//     * runs, this may only be the partial results.
//     *
//     * @return The (positivesibly partial) cross validation results.
//     */
//    public CrossValidationResult getCrossValidationResults() {
//
//        if (crossValidationResult == null) {
//            crossValidationResult = new CrossValidationResult(getNumberOfFolds());
//        }
//
//        return crossValidationResult;
//    }
//
//    public CrossValidationExampleSets getILPCrossValidationExampleSets() {
//        return getILPCrossValidationExampleSets();
//    }
//
//    /** Writes the final report.
//     *
//     * At this point, getResult() should return an CrossValidationResult for each
//     * individual fold.  Just loop through the folds and build your report.
//     *
//     * If removeFoldResultsAfterConsolidation is false, you can test this by rerunning a cross validation
//     * repeatedly.  The first time will create all the files.  After just this will be run.
//     *
//     * removeFoldResultsAfterConsolition should probably default to true once the bugs have been worked out.
//     */
//    protected void writeFinalReport() {
//
//        if (LearnOneClause.debugLevel > -10) {
//            for (int i = 0; i < getNumberOfFolds(); i++) {
//                Utils.println("% Fold " + i + " Theory: ");
//                Utils.println(getFoldResult(i).getTheory().toPrettyString("  "));
//                Utils.println("");
//            }
//        }
//
//        CrossValidationResult results = getCrossValidationResults();
//        Utils.println("\n% TRAINING Set Average Weighted Coverage:");
//        Utils.println(results.getAverageTrainingCoverageScore() + "\n");
//
//        CoverageScore cs = results.getAverageEvaluationCoverageScore();
//        if (cs != null) {
//            Utils.println("\n% TESTING Set Average Weighted Coverage:");
//            Utils.println(cs.toString() + "\n");
//        }
//    }
//
//
//}
