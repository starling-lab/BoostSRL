/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.ILP.LearnOneClause;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Theory;
import edu.wisc.cs.will.Utils.Stopwatch;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.File;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.Utils.condor.CondorFileInputStream;
import edu.wisc.cs.will.Utils.condor.CondorFileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InvalidClassException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.OutputStream;
import java.io.StreamCorruptedException;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.zip.GZIPInputStream;
import java.util.zip.GZIPOutputStream;

/** Cross Validation.
 *
 * <p><B>Set edu.wisc.cs.will.ILP.readmeCheckpointingAndCrossValidating.txt
 * for up to date usage information.</b></p>
 *
 * <p>Cross-validation is now supported by WILL.</p>
 *
 * <p>You can use cross-validation by creating a ILPouterLoop, then
 * passing that outerLoop to a new ILPCrossValidationLoop object.
 * Then you can do the cross-validation by calling
 * ILPCrossValidationLoop.executeCrossValidation().  Alternatively,
 * if you are using ILPouterLoop as your main, you can just specify
 * the number of folds to run at the end of the normal command line.</p>
 *
 * <p>It is always safe to call executeCrossValidation() with a cross
 * validation loop, instead of using the ILPouterLoop.executeOuterLoop().
 * If the number of folds is set to 1, executeCrossValidation() calls
 * ILPouterLoop.executeOuterLoop() without any extra overhead.</p>
 *
 * <p>If the number of folds is greater than 1, the cross validation loop
 * will partition the positive and negative examples and then execute the
 * outer loop for each fold with the appropriate examples.</p>
 *
 * <p>It is possible to split the work of a cross-validation run across
 * multiple processors or machines.  Each processor/machine can be assigned
 * one or more folds to work on.</p>
 *
 * <p>The instances that is assigned fold 0 will setup the initial state
 * and will collate the results after all of the fold have finished.  If
 * you are using ILPouterLoop as your main, there is now a -fold option
 * to specify the fold to work on.  That parameter will only result in the
 * indicated fold being processed.  If you need a single process to work on
 * multiple folds, there isn't a command-line option right now, but you can use
 * the appropriate ILPCrossValidationLoop constructor to specify it.</p>
 *
 * <p> As folds are finished, there results are written to disk in the working
 * directory.  If a process fails to complete it's folds, it can be restarted
 * and only the unfinished folds will be run.</p>
 *
 * <p> Caveat:  Do not assign multiple processors or machine to fold 0.  It will
 * probably work, but two or more of the processes might do the example
 * permutation and splitting, which would be bad.  If this becomes a problem,
 * I can probably get a locking mechanism in place, but it will be a bit of a hack.</p>
 *
 * <p> Caveat:  There is no way to disable saving the cross-validation state
 * and finished folds to disk.  These file are how the separate processes
 * communicate.  If this is a problem (say, because BL doesn't allow us disk
 * access), I can relax this constraint.  However, we will be limited to
 * running all folds in a single process.</p>
 *
 * <p> Caveat:  Since files are saved to disk, the caveat concerning parameter
 * changes from above apply to cross-validation also.  If you change parameters
 * for a run, make sure you clean up the cross-validation state and fold result
 * files.  Otherwise, some of the results will most likely be from previous
 * parameter settings.</p>
 *
 * @author twalker
 */
public class ILPCrossValidationLoop {

    /*
     * starting cross validation fold
     *
     * finished cross validation fold
     *
     * getWeightedCoverage(theory, posEx, negEx)
     *
     * getState
     *
     * getPosExamples
     *
     * getNegExamples
     *
     * getEvalSetPos
     * getEvalSetNeg
     *
     * setState
     *
     * setPos
     *
     * setNeg
     *
     * setEvalPos
     *
     * setEvalNeg
     *
     * setGleaner
     *
     * setMaximumClock
     *
     * executeLoop
     *
     * reportSearchStats
     *
     * getLearnedTheory
     *
     * getGleaner
     *
     * setAdvice
     *
     * unsetAdvice
     *
     *
     *
     *
     *
     *
     */

    private int firstFoldToRun;

    private int lastFoldToRun;

    private boolean filesystemUseEnabled = false;

    private boolean removeTemporaryFilesAfterCompletion = true;

    private boolean removeFoldResultFilesAfterConsolidation = false;

    private CrossValidationLoopState cvState;

    private ILPouterLoop outerLoop;

    private CrossValidationResult crossValidationResult;

    /** Creates an ILPCrossValidationLoop with <code>numberOfFolds</code> folds.
     *
     * This constructor will create a full cross-validation run.  When executeCrossValidation() is called,
     * all folds will be run.
     *
     * The allPosExample and allNegExample sets will be obtained from the outerLoop, permuted randomly,
     * and split into the appropriate number of folds.
     *
     * @param outerLoop OuterLoop to use during the search.  This should be the same for all folds.
     * @param numberOfFolds Number of folds to run.
     */
    public ILPCrossValidationLoop(ILPouterLoop outerLoop, int numberOfFolds) {
        this(outerLoop, numberOfFolds, null, 0, numberOfFolds - 1);
    }

    /** Creates an ILPCrossValidationLoop with <code>numberOfFolds</code> folds and the specified ILPCrossValidationExamples.
     *
     * This constructor will create a full cross-validation run.  When executeCrossValidation() is called,
     * all folds 0 to numberOfFolds-1 will be run.
     *
     * If ilpCrossValidationExampleSets is non-null, it should be fully setup with all positive and negative
     * examples as well as fold data sets.
     *
     * If ilpCrossValidationExampleSets, the examples will be obtained from the outer loop.
     *
     * @param outerLoop OuterLoop to use during the search.  This should be the same for all folds.
     * @param numberOfFolds Number of folds to run.
     * @param ilpCrossValidationExampleSets Example sets to use during cross validation.
     */
    public ILPCrossValidationLoop(ILPouterLoop outerLoop, int numberOfFolds, CrossValidationExampleSets ilpCrossValidationExampleSets) {
        this(outerLoop, numberOfFolds, ilpCrossValidationExampleSets, 0, numberOfFolds - 1);
    }

    /** Creates an ILPCrossValidationLoop with <code>numberOfFolds</code> folds
     * and sets this loop to run fold <code>firstFoldToRun</code> through <code>lastFoldToRun</code>.
     *
     * This constructor will create a full cross-validation run.  When executeCrossValidation() is called, only
     * folds from firstFoldToRun to lastFoldToRun will be run.  Folds are indexed from 0.
     *
     * The allPosExample and allNegExample sets will be obtained from the outerLoop, permuted randomly,
     * and split into the appropriate number of folds.
     *
     * @param outerLoop OuterLoop to use during the search.  This should be the same for all folds.
     * @param numberOfFolds Number of folds to run.
     * @param firstFoldToRun
     * @param lastFoldToRun
     */
    public ILPCrossValidationLoop(ILPouterLoop outerLoop, int numberOfFolds, int firstFoldToRun, int lastFoldToRun) {
        this(outerLoop, numberOfFolds, null, firstFoldToRun, lastFoldToRun);
    }

    /** Creates an ILPCrossValidationLoop with <code>numberOfFolds</code> folds
     * and sets this loop to run fold <code>firstFoldToRun</code> through <code>lastFoldToRun</code>.
     *
     * This constructor will create a full cross-validation run.  When executeCrossValidation() is called, only
     * folds from firstFoldToRun to lastFoldToRun will be run.  Folds are indexed from 0.
     *
     * @param outerLoop OuterLoop to use during the search.  This should be the same for all folds.
     * @param numberOfFolds Number of folds to run.
     * @param ilpCrossValidationExampleSets Collection of examples to use for cross validation.
     * @param firstFoldToRun
     * @param lastFoldToRun
     */
    public ILPCrossValidationLoop(ILPouterLoop outerLoop, int numberOfFolds, CrossValidationExampleSets ilpCrossValidationExampleSets, int firstFoldToRun, int lastFoldToRun) {
        if (numberOfFolds == -1) {
            // Assume they want 1 fold...
            numberOfFolds = 1;
            firstFoldToRun = 0;
            lastFoldToRun = 0;
        }

        if (numberOfFolds < 1) {
            throw new IllegalArgumentException("You must run at least a single fold.");
        }

        if (firstFoldToRun < 0) {
            throw new IllegalArgumentException("The firstFoldToRun must be \u2265 0 and < numberOfFolds.");
        }

        if (lastFoldToRun < firstFoldToRun) {
            throw new IllegalArgumentException("The lastFoldToRun must \u2265 firstFoldToRun.");
        }

        if (lastFoldToRun > numberOfFolds - 1) {
            throw new IllegalArgumentException("The lastFoldToRun must be < numberOfFolds.");
        }

        this.outerLoop = outerLoop;
        this.cvState = new CrossValidationLoopState(outerLoop.getOuterLoopState(), numberOfFolds, ilpCrossValidationExampleSets); // Temporary state info...replaced below...

        this.firstFoldToRun = firstFoldToRun;
        this.lastFoldToRun = lastFoldToRun;

        if (numberOfFolds == 1) {
            setFilesystemUseEnabled(false); // Don't use the file system, by default, when we are doing only a single fold.
        }
    }

    public void executeCrossValidation() throws SearchInterrupted {

        try {
            initializeState();
        } catch (IOException ioe) {
            throw new SearchInterrupted("Something unexpected happened while initializing crossValidation: " + ioe.toString());
        } catch (IncongruentSavedStateException isse) {
            throw new SearchInterrupted("Error while restoring cross validation saved state: " + isse.toString() + "\n"
                    + "This probably means that the saved state (" + getCVStateFile() + ") should be removed and the "
                    + "search restarted.");
        }

        // Okay everything should be setup...
        // Lets do this thing.
        StoppingCondition<ILPCrossValidationLoop> stoppingCondition = getEarlyStoppingCondition();

            for (int currentFold = firstFoldToRun; currentFold <= lastFoldToRun; currentFold++) {

                ILPSearchAction action = outerLoop.innerLoopTask.fireCrossValidationFoldStarting(this, currentFold);

                if (action == ILPSearchAction.PERFORM_LOOP) {

                    executeCrossValidationForFold(currentFold);

                    if (currentFold != lastFoldToRun - 1 && stoppingCondition != null && stoppingCondition.isStoppingConditionMet(this)) {
                        throw new EarlyStoppingConditionMet();
                    }

                    outerLoop.innerLoopTask.fireCrossValidationFoldFinished(this, currentFold);
                }
                else if (action == ILPSearchAction.SKIP_ITERATION) {
                    Utils.println("ILPSearchListener skipped cross-validation fold " + currentFold + ".");
                }
                else {
                    Utils.println("ILPSearchListener terminated cross-validation prior to fold " + currentFold + ".");
                    throw new SearchInterrupted("ILPSearchListener terminated cross-validation prior to fold " + currentFold + ".");
                }
            }

        if (isConsolidator() && filesystemUseEnabled) {
            // since we did the first run, let's do the consolidation of results...
            consolidateCrossValidationResults();

            // Clean up the disk files, if they exist...
            if (removeTemporaryFilesAfterCompletion) {
                removeResultFiles();
            }
        }

    }

    /** Creates a CrossValidationFoldResult object and scores the training/testing sets.
     *
     * @param currentFold
     * @param theory
     * @param gleaner
     * @return
     */
    private CrossValidationFoldResult createCVFoldResult(int fold, Theory theory, Gleaner gleaner) {
        CrossValidationFoldResult result = new CrossValidationFoldResult(fold, theory, gleaner);

        CoverageScore cs;

        List<Example> positiveExamples = cvState.getPositiveEvaluationExamplesForFolds(fold);
        List<Example> negativeExamples = cvState.getNegativeEvaluationExamplesForFolds(fold);
        if ((positiveExamples != null && positiveExamples.size() > 0) || (negativeExamples != null && negativeExamples.size() > 0)) {
            cs = outerLoop.getWeightedCoverage(theory, positiveExamples, negativeExamples);
            result.setEvaluationCoverageScore(cs);
        }

        positiveExamples = cvState.getPositiveTrainingExamplesForFolds(fold);
        negativeExamples = cvState.getNegativeTrainingExamplesForFolds(fold);
        if ((positiveExamples != null && positiveExamples.size() > 0) || (negativeExamples != null && negativeExamples.size() > 0)) {
            cs = outerLoop.getWeightedCoverage(theory, positiveExamples, negativeExamples);
            result.setTrainingCoverageScore(cs);
        }

        positiveExamples = cvState.getAllPositiveExamples();
        negativeExamples = cvState.getAllNegativeExamples();
        if ((positiveExamples != null && positiveExamples.size() > 0) || (negativeExamples != null && negativeExamples.size() > 0)) {
            cs = outerLoop.getWeightedCoverage(theory, positiveExamples, negativeExamples);
            result.setAllExamplesCoverageScore(cs);
        }

        return result;
    }

    private void executeCrossValidationForFold(int currentFold) throws SearchInterrupted {

        boolean isFoldComplete = isFoldCompleted(currentFold);

        if (isFoldComplete == false) {

            if (LearnOneClause.debugLevel > -10) {
                Utils.println("\n% Initializing fold " + Utils.comma(currentFold) + ".");
            }

            Stopwatch s = new Stopwatch();

            // Safe the state of the outer loop so we can replace it later.
            // We do this just in case someone else is relying on the outer loop
            // not changing during cross validation.
            ILPouterLoopState originalState = outerLoop.getOuterLoopState();
            List<Example> originalPosExamples = outerLoop.getPosExamples();
            List<Example> originalNegExamples = outerLoop.getNegExamples();
            List<Example> originalEvalSetPosExamples = outerLoop.getEvalSetPosExamples();
            List<Example> originalEvalSetNegExamples = outerLoop.getEvalSetNegExamples();

            ILPouterLoopState outerLoopStateForThisFold = cvState.getILPOuterLoopStateForFold(currentFold);

            // Set the state of the ILPouterLoop to be the outerLoopState for this fold...
            // We will lose the existing other loop state, but that is okay.  Either
            // a copy has been stored in the cvState or it was read in as part of a
            // restart.  In any case, the verifyCVState should have checked that
            // it was okay to swap these...
            outerLoop.setOuterLoopState(outerLoopStateForThisFold);
            outerLoop.setPosExamples(cvState.getPositiveTrainingExamplesForFolds(currentFold));
            outerLoop.setNegExamples(cvState.getNegativeTrainingExamplesForFolds(currentFold));
            outerLoop.setEvalSetPosExamples(cvState.getPositiveEvaluationExamplesForFolds(currentFold));
            outerLoop.setEvalSetNegExamples(cvState.getNegativeEvaluationExamplesForFolds(currentFold));

            // Make sure we create a new Gleaner, so we have results just for this fold...
            outerLoop.setGleaner(new Gleaner());

            if (getMaximumCrossValidationTimeInMillisec() != Long.MAX_VALUE) {
                outerLoop.setMaximumClockTimeInMillisec(getMaximumCrossValidationTimeInMillisec() / getNumberOfFolds());
            }
            else {
                outerLoop.setMaximumClockTimeInMillisec(Long.MAX_VALUE);
            }

            if (LearnOneClause.debugLevel > -10) {
                Utils.println("%   Number of positive TRAIN examples = " + Utils.comma(outerLoop.getPosExamples()) + ".");
                Utils.println("%   Number of negative TRAIN examples = " + Utils.comma(outerLoop.getNegExamples()) + ".");
                //jws3      Utils.println("%   Number of positive TUNE  examples = " + Utils.comma(outerLoop.getTuneSetPosExamples()) + ".");
                //      Utils.println("%   Number of negative TUNE  examples = " + Utils.comma(outerLoop.getTuneSetNegExamples()) + ".");
                Utils.println("%   Number of positive EVAL  examples = " + Utils.comma(outerLoop.getEvalSetPosExamples()) + ".");
                Utils.println("%   Number of negative EVAL  examples = " + Utils.comma(outerLoop.getEvalSetNegExamples()) + ".");
            }

            // Wrap this the run in a try-catch so that the finally clause can restore the 
            // outerLoop to pre-CV values regardless of the outcome of the search.
            try {
                setupAdvice(outerLoop);

                    Theory theory = outerLoop.executeOuterLoop();

                    theory.setNegated(getFlipFlopPositiveAndNegativeExamples());

                    if (LearnOneClause.debugLevel > -10) {
                        Utils.println(String.format("\n%% Finished fold %d (%.2fs):", currentFold, s.getTotalTimeInSeconds()));
                        Utils.println("\n" + outerLoop.reportSearchStats());
                        Utils.println("\n% " + outerLoop.getLearnedTheory().toPrettyString("% "));
                    }

                    // Grab the gleaner from the innerLoop.
                    // Not, we don't want to save the gleaner we created a couple lines
                    // above since the outerLoop may have restored a different gleaner
                    // from a saved checkpoint file.
                    Gleaner gleaner = outerLoop.getGleaner();

                    // If outerLoop didn't throw an exception, lets assume everything worked.
                    // We can add a check later...
                    CrossValidationFoldResult result = createCVFoldResult(currentFold, theory, gleaner);
                    setFoldResult(currentFold, result);

                    // Delete the checkpoint since we know that this fold is done and
                    // it won't be needed anymore...
                    if (filesystemUseEnabled) {
                        // Write the result out to disk.  This is how we will know that a run is complete in the
                        // future...
                        writeResult(result);

                        outerLoop.deleteCheckpoint();
                    }

                    outerLoop.innerLoopTask.fireOuterLoopFinished(outerLoop);
                
            } catch (IOException ioe) {
                // Hmmm...there was a problem saving the search...that is probably a bad thing...
                // Let's throw an exception...
                throw new SearchInterrupted("Error occurred while attempting to save cross validation results for fold " + currentFold + ": " + ioe.toString());
            } finally {
                // Put back the state no matter what happened during the outer loop search...
                outerLoop.setOuterLoopState(originalState);
                outerLoop.setPosExamples(originalPosExamples);
                outerLoop.setNegExamples(originalNegExamples);
                outerLoop.setEvalSetPosExamples(originalEvalSetPosExamples);
                outerLoop.setEvalSetNegExamples(originalEvalSetNegExamples);

                unsetAdvice(outerLoop);
            }
        }
        else if (filesystemUseEnabled) {
            // We will read in the fold results here, so that we can do early stopping if desired.
            try {
                CrossValidationFoldResult result = readResultsForFold(currentFold);
                setFoldResult(currentFold, result);
            } catch (IOException ioe) {
            }
        }
    }

    /** Consolidates all of the fold results.
     *
     * This is normally called by the process that ran the first fold of the cross-validation,
     * but could be called separately if necessary.
     *
     * If called separately, use the initializeAndConsolidateCrossValidationResults() method
     * since there is some initialization that has to occur before this will work.
     *
     * This method will block waiting for all the runs to finish.
     *
     * @throws SearchInterrupted A SearchInterrupted message will be throw if something bad
     * occurs during consolidation.  Most likely this will be the result of an IO error
     * during the reading of the results.
     */
    protected void consolidateCrossValidationResults() throws SearchInterrupted {

        if (filesystemUseEnabled == false) {
            throw new IllegalStateException("Filesystem Use disabled.  Cannot consolidate CV results.");
        }
        else {
            try {
                waitForAllFoldsToFinish();

                readAllFoldResults();

                writeFinalReport();

                if (removeFoldResultFilesAfterConsolidation) {
                    removeResultFiles();
                }

            } catch (IOException ex) {
                throw new SearchInterrupted(ex);
            }
        }
    }

    /** Waits for all the Runs to Finish.
     *
     * This just checks that runs are finished.  It does not actually
     * load the runs.
     *
     * This will block until all the runs are completed.
     */
    private void waitForAllFoldsToFinish() {

        TreeSet<Integer> unfinishedFolds = new TreeSet<Integer>();

        for (int fold = 0; fold < getNumberOfFolds(); fold++) {
            unfinishedFolds.add(fold);
        }

        while (unfinishedFolds.isEmpty() == false) {
            for (Iterator<Integer> it = unfinishedFolds.iterator(); it.hasNext();) {
                int fold = it.next();

                if (isFoldCompleted(fold)) {
                    it.remove();
                }
            }

            if (unfinishedFolds.isEmpty() == false) {
                if (filesystemUseEnabled == false) {
                    throw new IllegalStateException("Filesystem storage is disabled.  However, one or more folds are not complete.  This should not happen.");
                }

                Utils.println(Utils.getPrettyString("Waiting for fold", "to finish.  Will check again in 30 seconds.", unfinishedFolds));
                try {
                    Thread.sleep(30000);
                } catch (InterruptedException ex) {
                }
            }
        }
    }

    /** Reads the results of all folds.
     *
     * The results will be placed in the results array and can be accessed
     * via the getResults() method.
     *
     * This method assumes that all of the results exist and are on disk.
     * If they aren't, it will result in a IOException when the missing
     * fold is read.  The waitForAllFoldsToFinish() method can be used to
     * wait for the completion of runs.
     *
     * @throws IOException An IOException will be throw if the results for one of the
     * folds does not exist.
     */
    public void readAllFoldResults() throws IOException {
        if (filesystemUseEnabled == false) {
            throw new IllegalStateException("Attempting to read fold results from disk while filesystem storage is disabled.");
        }
        else {
            boolean done = false;
            int maxTries = 3;
            int tries = 0;

            while (!done && tries < maxTries) {
                done = true;

                for (int fold = 0; fold < getNumberOfFolds(); fold++) {
                    if (getFoldResult(fold) == null) {

                        try {
                            CrossValidationFoldResult result = readResultsForFold(fold);

                            if (result.getFold() != fold) {
                                throw new RuntimeException("The results file for fold " + fold + " appears to hold results from fold " + result.getFold() + " instead.  This shouldn't happen.");
                            }

                            setFoldResult(fold, result);
                        } catch (StreamCorruptedException sce) {
                            // The stream is corrupt.  This probably means that the file
                            // is in the process of being read.
                            Utils.println("The results for fold " + fold + " appears to be corrupted.  It may be in the process of writing.");
                            done = false;
                        }
                    }
                }

                tries++;

                if (done == false && tries < maxTries) {
                    // One or more folds is corrupt, probably being written by a different process.
                    // Lets wait if we can.
                    Utils.println("One or more result files were corrupt.  Will attempt to read again in 30 seconds. " + (maxTries - tries) + " attempts remaining.");
                    try {
                        Thread.sleep(30000);
                    } catch (InterruptedException ex) {
                    }
                }
            }

            if (!done) {
                // Crap, we didn't get all of the runs...
                // This really shouldn't have happened.
                Set<Integer> unfinishedRuns = new TreeSet<Integer>();
                for (int i = 0; i < getNumberOfFolds(); i++) {
                    if (getFoldResult(i) == null) {
                        unfinishedRuns.add(i);
                    }
                }

                String err = Utils.getPrettyString("Fold", " are corrupt and unreadable.  They should probably be delete and rerun.", unfinishedRuns);
                throw new RuntimeException(err);
            }
        }
    }

    private void removeResultFiles() {

        if (filesystemUseEnabled) {
            for (int fold = 0; fold < getNumberOfFolds(); fold++) {
                File f = new CondorFile(outerLoop.getResultFileNameForFold(fold));
                if (f.exists()) {
                    f.delete();
                }
            }

            File f = getCVStateFile();
            if (f.exists()) {
                f.delete();
            }
        }
    }

    /** Initializes the CrossValidationLoop and consolidates the results.
     *
     *
     * @throws SearchInterrupted
     */
    public void initializeAndConsolidateCrossValidationResults() throws SearchInterrupted {
        try {
            initializeState();
        } catch (IOException ioe) {
            throw new SearchInterrupted("Something unexpected happened while initializing crossValidation: " + ioe.toString());
        } catch (IncongruentSavedStateException isse) {
            throw new SearchInterrupted("Error while restoring cross validation saved state: " + isse.toString() + "\n"
                    + "This probably means that the saved state (" + getCVStateFile() + ") should be removed and the "
                    + "search restarted.");
        }

        consolidateCrossValidationResults();
    }

    /** Indicates this run should consolidate everything.
     *
     * Theortically, you could have a run whose only job was to consolidate
     * the results.  For now, just make the guy who did the first run the
     * consolidator.
     *
     * @return
     */
    private boolean isConsolidator() {
        return firstFoldToRun == 0;
    }

    private boolean isFoldCompleted(int currentFold) {

        if (getFoldResult(currentFold) != null) {
            // We have a fold result in memory, so it is definitely completed
            return true;
        }

        // Doesn't exist in memory, so check the disk...
        if (filesystemUseEnabled) {
            File f = new CondorFile(outerLoop.getResultFileNameForFold(currentFold));
            if (f.exists()) {
                return true;
            }
        }

        return false;
    }

    private void initializeState() throws IOException, IncongruentSavedStateException {

        CrossValidationLoopState savedCVState = null;

        if (firstFoldToRun == 0) {
            savedCVState = readCVState(false);

            if (savedCVState == null) {
                savedCVState = initializeCVState();
                writeCVState(savedCVState);
            }
        }
        else {
            savedCVState = readCVState(true);
        }

        verifyCVState(savedCVState);
        mergeCVState(savedCVState);
    }

    private CrossValidationLoopState readCVState(boolean waitForCreation) {

        CrossValidationLoopState readState = null;

        if (filesystemUseEnabled) {

            File cvStateFile = getCVStateFile();


            int tries = 0;
            int maxTries = 10;

            while (tries == 0 || (waitForCreation && tries < maxTries && readState == null)) {

                if (cvStateFile.exists()) {
                    ObjectInputStream ois = null;
                    InputStream is = null;
                    try {
                        is = new CondorFileInputStream(cvStateFile);

                        if (cvStateFile.getName().endsWith(".gz")) {
                            is = new GZIPInputStream(is);
                        }

                        ois = new ILPObjectInputStream(new BufferedInputStream(is), outerLoop.innerLoopTask.stringHandler, outerLoop.innerLoopTask);

                        readState = (CrossValidationLoopState) ois.readObject();

                    } catch (InvalidClassException ex) {
                        throw new RuntimeException("The cross validation state on the disk is not longer compatible with the current WILL "
                                + "codebase.  Please remove the state file \"" + cvStateFile + "\" and restart all runs.");
                    } catch (ClassNotFoundException ex) {
                        throw new RuntimeException("Odd Error reading cross validation state. This probably shouldn't have happened.", ex);
                    } catch (IOException ex) {
                    } finally {
                        try {
                            if (ois != null) {
                                ois.close();
                            }
                            else if (is != null) {
                                is.close();
                            }
                        } catch (IOException ex) {
                        }
                    }

                }

                if (readState == null && waitForCreation) {
                    Utils.println("Waiting for fold 0 to create cross validation state file \"" + cvStateFile + "\"...");
                    try {
                        Thread.sleep(30000);
                    } catch (InterruptedException interruptedException) {
                    }
                }

                tries++;
            }

            if (waitForCreation && readState == null) {
                throw new IllegalStateException("Non-main CV loop didn't find CV state file after " + maxTries + ".  Quiting.");
            }
        }

        return readState;
    }

    /** Initialized the CVState.
     *
     * Previously, this actually created a new state based on the existing cvState that
     * was created during the constructor.  However, since it was a direct clone
     * and all we did here was setup examples, it didn't really make sense to do
     * that anymore.
     *
     * Not, this is still only called by the fold 0 cross-validation process.  If there are
     * other cross-validation processes (for parallel execution), their cvState will be
     * replaced by the fold 0 one saved to disk.
     */
    private CrossValidationLoopState initializeCVState() {
        if (cvState.getILPCrossValidationExampleSets() == null) {
            CrossValidationExampleSets ilpcves = new CrossValidationExampleSets(getNumberOfFolds(), outerLoop.getPosExamples(), outerLoop.getNegExamples());
            cvState.setILPCrossValidationExampleSets(ilpcves);
        }

        return cvState;
    }

    /** Merges the saved CVState into our existing cvState.
     *
     * This merges the two CVStates.  In a perfect world, the two states should be exactly
     * the same, parameter-wise.  verifyCVState() should confirm this.  If your parameters settings
     * are getting lost when resuming saved runs, it probably means you should be checking those settings
     * and starting the search over when things aren't the same.
     *
     * @param savedCVState
     */
    private void mergeCVState(CrossValidationLoopState savedCVState) {
        // We might be smarter about this, but for now,
        // just replace the initial state with the saved state
        // with a little jigging around with the ILPOuterLoop saved
        // objects.
        cvState = savedCVState;
    }

    private void writeCVState(CrossValidationLoopState cvStateToSave) throws IOException {

        if (filesystemUseEnabled) {
            OutputStream os = null;
            ObjectOutputStream oos = null;
            try {
                if (firstFoldToRun != 0) {
                    throw new IllegalStateException("Only the primary run (run containing fold 0) should save the CVState.");
                }
                File cvStateFile = getCVStateFile();
                os = new CondorFileOutputStream(cvStateFile);
                if (cvStateFile.getName().endsWith(".gz")) {
                    os = new GZIPOutputStream(os);
                }

                oos = new ObjectOutputStream(new BufferedOutputStream(os));

                oos.writeObject(cvStateToSave);
            } finally {
                try {
                    if (oos != null) {
                        oos.close();
                    }
                    else if (os != null) {
                        os.close();
                    }
                } catch (IOException ex) {
                }
            }
        }
    }

    private void verifyCVState(CrossValidationLoopState savedCVState) throws IncongruentSavedStateException {
        if (savedCVState == null) {
            throw new IncongruentSavedStateException("SavedCVState is null.  This shouldn't happen");
        }

        // Compare the saved state against the current cvState (which was just temporary to store initial settings).
        savedCVState.checkStateCongruency(cvState);
    }

    private File getCVStateFile() {
        String workingDirectory = getOuterLoop().getWorkingDirectory();
        String extendedPrefix = getOuterLoop().getExtendedPrefix();
        return new CondorFile(workingDirectory, extendedPrefix + ".cvState.gz");
    }

    /**
     * @return the outerLoop
     */
    protected ILPouterLoop getOuterLoop() {
        return outerLoop;
    }

    /**
     * @param outerLoop the outerLoop to set
     */
    protected void setOuterLoop(ILPouterLoop outerLoop) {
        this.outerLoop = outerLoop;
    }

    public int getNumberOfFolds() {
        return cvState.getNumberOfFolds();
    }

    /** Reads a single result.
     *
     * @param fold
     * @return
     * @throws IOException
     */
    protected CrossValidationFoldResult readResultsForFold(int fold) throws IOException {

        if (filesystemUseEnabled == false) {
            throw new IllegalStateException("Attempting to read fold results from disk while filesystem storage is disabled.");
        }

        File resultsFile = new CondorFile(outerLoop.getResultFileNameForFold(fold));
        ObjectInputStream ois = null;
        InputStream is = null;
        try {
            is = new CondorFileInputStream(resultsFile);

            if (resultsFile.getName().endsWith(".gz")) {
                is = new GZIPInputStream(is);
            }

            ois = new ILPObjectInputStream(new BufferedInputStream(is), outerLoop.innerLoopTask.stringHandler, outerLoop.innerLoopTask);

            return (CrossValidationFoldResult) ois.readObject();

        } catch (InvalidClassException ex) {
            throw new RuntimeException("The cross validation results file is not longer compatible with the current WILL "
                    + "codebase.  Please remove the results file \"" + resultsFile + "\" and restart all runs.");
        } catch (ClassNotFoundException ex) {
            throw new RuntimeException("Odd Error reading cross validation state. This probably shouldn't have happened.", ex);
        } finally {
            try {
                if (ois != null) {
                    ois.close();
                }
                else if (is != null) {
                    is.close();
                }
            } catch (IOException ex) {
            }
        }
    }

    protected void writeResult(CrossValidationFoldResult result) throws IOException {

        if (filesystemUseEnabled == false) {
            throw new IllegalStateException("Attempting to write fold results from disk while filesystem storage is disabled.");
        }
        else {
            OutputStream os = null;
            ObjectOutputStream oos = null;
            try {
                File resultsFile = new CondorFile(outerLoop.getResultFileNameForFold(result.getFold()));
                os = new CondorFileOutputStream(resultsFile);
                if (resultsFile.getName().endsWith(".gz")) {
                    os = new GZIPOutputStream(os);
                }

                oos = new ObjectOutputStream(new BufferedOutputStream(os));

                oos.writeObject(result);
            } finally {
                try {
                    if (oos != null) {
                        oos.close();
                    }
                    else if (os != null) {
                        os.close();
                    }
                } catch (IOException ex) {
                }
            }
        }
    }

    /** Sets the CrossValidationResult for fold.
     *
     * @param fold
     * @param result
     * @throws IllegalStateException
     */
    protected void setFoldResult(int fold, CrossValidationFoldResult result) throws IllegalStateException {
        if (crossValidationResult == null) {
            crossValidationResult = new CrossValidationResult(getNumberOfFolds());
        }

        crossValidationResult.setFoldResult(fold, result);
    }

    /** Returns the CrossValidationResult for fold, null if that fold is not currently stored.
     *
     * Only the run doing the consolidation of all the fold stores this information.  Other runs
     * never need it.
     *
     * @param fold
     * @return
     * @throws IllegalStateException
     */
    protected CrossValidationFoldResult getFoldResult(int fold) throws IllegalStateException {
        if (crossValidationResult == null) {
            return null;
        }

        return crossValidationResult.getFoldResult(fold);
    }

    /** Returns the Consolidated results for the Cross Validation.
     *
     * If the runs aren't finished or this isn't the consolidator of the
     * runs, this may only be the partial results.
     *
     * @return The (possibly partial) cross validation results.
     */
    public CrossValidationResult getCrossValidationResults() {

        if (crossValidationResult == null) {
            crossValidationResult = new CrossValidationResult(getNumberOfFolds());
        }

        return crossValidationResult;
    }

    /**
     * @return the removeFoldResultsAfterConsolidation
     */
    public boolean isRemoveFoldResultsAfterConsolidation() {
        return removeFoldResultFilesAfterConsolidation;
    }

    /**
     * @param removeFoldResultsAfterConsolidation the removeFoldResultsAfterConsolidation to set
     */
    public void setRemoveFoldResultsAfterConsolidation(boolean removeFoldResultsAfterConsolidation) {
        this.removeFoldResultFilesAfterConsolidation = removeFoldResultsAfterConsolidation;
    }

    public CrossValidationExampleSets getILPCrossValidationExampleSets() {
        return cvState.getILPCrossValidationExampleSets();
    }

    public void setEarlyStoppingCondition(StoppingCondition<ILPCrossValidationLoop> earlyStoppingCondition) {
        cvState.setEarlyStoppingCondition(earlyStoppingCondition);
    }

    public StoppingCondition<ILPCrossValidationLoop> getEarlyStoppingCondition() {
        return cvState.getEarlyStoppingCondition();
    }

    /** Writes the final report.
     *
     * At this point, getResult() should return an CrossValidationResult for each
     * individual fold.  Just loop through the folds and build your report.
     *
     * If removeFoldResultsAfterConsolidation is false, you can test this by rerunning a cross validation
     * repeatedly.  The first time will create all the files.  After just this will be run.
     *
     * removeFoldResultsAfterConsolition should probably default to true once the bugs have been worked out.
     */
    protected void writeFinalReport() {

        if (LearnOneClause.debugLevel > -10) {
            for (int i = 0; i < getNumberOfFolds(); i++) {
                Utils.println("% Fold " + i + " Theory: ");
                Utils.println(getFoldResult(i).getTheory().toPrettyString("  "));
                Utils.println("");
            }
        }

        CrossValidationResult results = getCrossValidationResults();
        Utils.println("\n% TRAINING Set Average Weighted Coverage:");
        Utils.println(results.getAverageTrainingCoverageScore() + "\n");

        CoverageScore cs = results.getAverageEvaluationCoverageScore();
        if (cs != null) {
            Utils.println("\n% TESTING Set Average Weighted Coverage:");
            Utils.println(cs.toString() + "\n");
        }
    }

    /**
     * @return the removeCheckpointFileAfterCompletion
     */
    public boolean getRemoveTemporaryFilesAfterCompletion() {
        return removeTemporaryFilesAfterCompletion;
    }

    /**
     * @param removeTemporaryFilesAfterCompletion the removeCheckpointFileAfterCompletion to set
     */
    public void setRemoveTemporaryFilesAfterCompletion(boolean removeTemporaryFilesAfterCompletion) {
        this.removeTemporaryFilesAfterCompletion = removeTemporaryFilesAfterCompletion;
    }

    /**
     * @return the filesystemUseEnabled
     */
    public boolean isFilesystemUseEnabled() {
        return filesystemUseEnabled;
    }

    /**
     * @param filesystemUseEnabled the filesystemUseEnabled to set
     */
    public void setFilesystemUseEnabled(boolean filesystemUseEnabled) {

        if (filesystemUseEnabled == false && (firstFoldToRun != 0 || lastFoldToRun != getNumberOfFolds() - 1)) {
            throw new IllegalArgumentException("The Cross-Validation loop is configured to run only a partial set of folds.  Filesystem must be enabled with this setting.");
        }

        this.filesystemUseEnabled = filesystemUseEnabled;
    }

    public void setFlipFlopPositiveAndNegativeExamples(boolean flipFlopPositiveAndNegativeExamples) {
        //	Utils.println("% ILPCrossValidationLoop: flipFlopPosAndNegExamples = " + flipFlopPositiveAndNegativeExamples);
        cvState.setFlipFlopPositiveitiveAndNegativeativeExamples(flipFlopPositiveAndNegativeExamples);
    }

    public boolean getFlipFlopPositiveAndNegativeExamples() {
        return cvState.getFlipFlopPositiveitiveAndNegativeativeExamples();
    }

    public void setMaximumCrossValidationTimeInMillisec(long maximumCrossValidationTimeInMillisec) {
        cvState.setMaximumCrossValidationTimeInMillisec(maximumCrossValidationTimeInMillisec);
    }

    public long getMaximumCrossValidationTimeInMillisec() {
        return cvState.getMaximumCrossValidationTimeInMillisec();
    }

    private void setupAdvice(ILPouterLoop outerLooper) {
        if (outerLooper.innerLoopTask.isRelevanceEnabled()) {
            ActiveAdvice activeAdvice = outerLooper.innerLoopTask.getAdviceProcessor().processAdvice(outerLooper.innerLoopTask.getCurrentRelevanceStrength(), outerLooper.getPosExamples(), outerLooper.getNegExamples());
            setActiveAdvice(outerLooper, activeAdvice);
        }
    }

    protected void unsetAdvice(ILPouterLoop outerLooper) {
        if (getActiveAdvice(outerLooper) != null) {
            outerLooper.innerLoopTask.getAdviceProcessor().retractRelevanceAdvice();
            setActiveAdvice(outerLooper, null);
        }
    }

    public ActiveAdvice getActiveAdvice(ILPouterLoop outerLooper) {
        return outerLooper.innerLoopTask.getActiveAdvice();
    }

    public void setActiveAdvice(ILPouterLoop outerLooper, ActiveAdvice activeAdvice) {
        outerLooper.innerLoopTask.setActiveAdvice(activeAdvice);
    }

}
