/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.Utils.Utils;

import java.io.Serializable;
import java.util.List;

/**
 *
 * @author twalker
 */
@SuppressWarnings("serial")
public class CrossValidationLoopState implements Serializable {

    private ILPouterLoopState outerLoopState;

    private int numberOfFolds = -1; // Initialize to illegal value so we know it has been set.

    private CrossValidationExampleSets ilpCrossValidationExampleSets;

    private StoppingCondition<ILPCrossValidationLoop> earlyStoppingCondition = null;

    private long maximumCrossValidationTimeInMillisec = Long.MAX_VALUE;

    /** Stores the flipFlip examples values.
     *
     * This is also stored in the ilpCrossValidationExampleSets.  However, since that
     * may be null when this is set, we store a copy of the value here.
     *
     * If this value is null, then it passes through to the ilpCrossValidationExampleSets
     * to get the actual value.  The only time this shouldn't be null is when there isn't
     * an examples set set current.
     */
    private Boolean flipFlopValueHolder = null;

    /**
     *
     * @param outerLoopState
     * @param numberOfFolds
     * @param earlyStoppingCondition
     */
    public CrossValidationLoopState(ILPouterLoopState outerLoopState, int numberOfFolds, StoppingCondition<ILPCrossValidationLoop> earlyStoppingCondition) {
        this.outerLoopState = outerLoopState.clone();
        setNumberOfFolds(numberOfFolds);
        this.earlyStoppingCondition = earlyStoppingCondition;
    }

    /** Creates a CrossValidationLoopState with the given outerLoopState, numberOfFolds and example collection.
     *
     * If the example collection is non-null, it is assumed that the examples and fold data are already
     * setup.
     *
     * @param outerLoopState
     * @param numberOfFolds
     * @param ilpCrossValidationExampleSets Collection of examples along with fold data.
     */
    public CrossValidationLoopState(ILPouterLoopState outerLoopState, int numberOfFolds, CrossValidationExampleSets ilpCrossValidationExampleSets) {
        this.outerLoopState = outerLoopState.clone();
        setNumberOfFolds(numberOfFolds);
        setILPCrossValidationExampleSets(ilpCrossValidationExampleSets);
    }

    /** Checks to make sure that the two state objects belong to the same search.
     *
     * When loading checkpoint information, we need to make sure that the state
     * information saved to disk belongs to the same ILP run as the one currently
     * being performed.
     *
     * If this method throws an IncongruentSavedStateException, this state is probably
     * from a different search.
     *
     * This code resembled equals code and performs approximately the same function.
     * However, I renamed it to make it explicit what it is doing.
     *
     * @param savedCVState
     * @throws IncongruentSavedStateException
     */
    protected void checkStateCongruency(CrossValidationLoopState savedCVState) throws IncongruentSavedStateException {

        // Check that the number of folds was the same...
        if (numberOfFolds != savedCVState.numberOfFolds) {
            throw new IncongruentSavedStateException("Saved cross-validation state configured with incorrect number of folds. " +
                    "Expected = " + numberOfFolds + ".  Found = " + savedCVState.numberOfFolds + ".");
        }
        
        // For now just check that the other loop is consistent...
        getOuterLoopState().checkStateCongruency(savedCVState.outerLoopState);

        if ( getILPCrossValidationExampleSets() != null && savedCVState.getILPCrossValidationExampleSets() != null) {
            getILPCrossValidationExampleSets().checkStateCongruency(savedCVState.getILPCrossValidationExampleSets());
        }

        if (earlyStoppingCondition != savedCVState.earlyStoppingCondition && (earlyStoppingCondition == null || earlyStoppingCondition.equals(savedCVState.earlyStoppingCondition) == false)) {
            throw new IncongruentSavedStateException("Saved cross-validation early stopping criteria does not matter configured.  (Make sure your early stopping criteria class implements equals() correctly.");
        }
    }

    /** Creates an ILPouterLoop object which can be used to run a single fold.
     *
     * This object is just a copy of the CrossValidation outerloop with the
     * positiveitive and Negativeative examples set appropriately for this fold.
     *
     * @param fold
     * @return
     */
    protected ILPouterLoopState getILPOuterLoopStateForFold(int fold) {
        ILPouterLoopState newState = outerLoopState.clone();
        newState.setCurrentFold(fold);

        return newState;
    }

    /**
     * @return the outerLoopState
     */
    public ILPouterLoopState getOuterLoopState() {
        return outerLoopState;
    }

    /**
     * @param outerLoopState the outerLoopState to set
     */
    public void setOuterLoopState(ILPouterLoopState outerLoopState) {
        this.outerLoopState = outerLoopState;
    }

    /**
     * @return the numberOfFolds
     */
    public int getNumberOfFolds() {
        return numberOfFolds;
    }

    /**
     * @param numberOfFolds the numberOfFolds to set
     */
    public final void setNumberOfFolds(int numberOfFolds) {

        if ( numberOfFolds <= 0 ) {
            throw new IllegalArgumentException("Number of folds must be >= 1.");
        }

        if (numberOfFolds != this.numberOfFolds) {
            if (this.numberOfFolds != -1) {
                throw new IllegalStateException("The number of folds has already been set.  Once set, it cannot be changed.");
            }

            this.numberOfFolds = numberOfFolds;
        }
    }

    /**
     * @return the ilpCrossValidationExamples
     */
    public CrossValidationExampleSets getILPCrossValidationExampleSets() {
        return ilpCrossValidationExampleSets;
    }

    /**
     * @param ilpCrossValidationExamples the ilpCrossValidationExamples to set
     */
    public final void setILPCrossValidationExampleSets(CrossValidationExampleSets ilpCrossValidationExamples) {
        if (this.ilpCrossValidationExampleSets != ilpCrossValidationExamples) {

            if ( ilpCrossValidationExamples != null && ilpCrossValidationExamples.getNumberOfFolds() != numberOfFolds ) {
                throw new IllegalArgumentException("The CV examples sets must have the same number of folds as the Cross Validation loop.  " +
                        "CVLoop folds = " + getNumberOfFolds() + ".  Collection folds = " + ilpCrossValidationExamples.getNumberOfFolds() + "." );
            }

            this.ilpCrossValidationExampleSets = ilpCrossValidationExamples;

            if ( this.ilpCrossValidationExampleSets != null &&  flipFlopValueHolder != null ) {
                this.ilpCrossValidationExampleSets.setFlipFlopPositiveitiveAndNegativeativeExamples(flipFlopValueHolder);

                flipFlopValueHolder = null;
            }
            
        }
    }

    private void createCrossValidaitonExampleSets() {
        if ( ilpCrossValidationExampleSets == null ) {
            ilpCrossValidationExampleSets = new CrossValidationExampleSets(numberOfFolds);
        }
    }

    public void setPositiveTrainingExamplesForFold(int fold, List<Example> positiveTrainingExamplesForFolds) {
        createCrossValidaitonExampleSets();
        ilpCrossValidationExampleSets.setPositiveTrainingExamplesForFold(fold, positiveTrainingExamplesForFolds);
    }

    public void setPositiveTestingExamplesForFold(int fold, List<Example> positiveTestingExamplesForFolds) {
        createCrossValidaitonExampleSets();
        ilpCrossValidationExampleSets.setPositiveEvaluationExamplesForFold(fold, positiveTestingExamplesForFolds);
    }

    public void setNegativeTrainingExamplesForFold(int fold, List<Example> NegativeTrainingExamplesForFolds) {
        createCrossValidaitonExampleSets();
        ilpCrossValidationExampleSets.setNegativeTrainingExamplesForFold(fold, NegativeTrainingExamplesForFolds);
    }

    public void setNegativeEvaluationExamplesForFold(int fold, List<Example> NegativeEvaluationExamplesForFolds) {
        createCrossValidaitonExampleSets();
        ilpCrossValidationExampleSets.setNegativeEvaluationExamplesForFold(fold, NegativeEvaluationExamplesForFolds);
    }

    public void setAllPositiveExamples(List<Example> allPositiveExamples) {
        createCrossValidaitonExampleSets();
        ilpCrossValidationExampleSets.setAllPositiveExamples(allPositiveExamples);
    }

    public void setAllNegativeExamples(List<Example> allNegativeExamples) {
        createCrossValidaitonExampleSets();
        ilpCrossValidationExampleSets.setAllNegativeExamples(allNegativeExamples);
    }

    public List<Example> getPositiveTrainingExamplesForFolds(int fold) {

        if ( ilpCrossValidationExampleSets == null ) throw new IllegalStateException("The cross-validation example sets have not been set.");

        return ilpCrossValidationExampleSets.getPositiveTrainingExamplesForFold(fold);
    }


    public List<Example> getPositiveEvaluationExamplesForFolds(int fold) {

        if ( ilpCrossValidationExampleSets == null ) throw new IllegalStateException("The cross-validation example sets have not been set.");

        return ilpCrossValidationExampleSets.getPositiveEvaluationExamplesForFold(fold);
    }

    public List<Example> getNegativeTrainingExamplesForFolds(int fold) {

        if ( ilpCrossValidationExampleSets == null ) throw new IllegalStateException("The cross-validation example sets have not been set.");

        return ilpCrossValidationExampleSets.getNegativeTrainingExamplesForFold(fold);
    }

    public List<Example> getNegativeEvaluationExamplesForFolds(int fold) {

        if ( ilpCrossValidationExampleSets == null ) throw new IllegalStateException("The cross-validation example sets have not been set.");

        return ilpCrossValidationExampleSets.getNegativeEvaluationExamplesForFold(fold);
    }

    public List<Example> getAllPositiveExamples() {

        if ( ilpCrossValidationExampleSets == null ) throw new IllegalStateException("The cross-validation example sets have not been set.");

        return ilpCrossValidationExampleSets.getAllPositiveExamples();
    }

    public List<Example> getAllNegativeExamples() {

        if ( ilpCrossValidationExampleSets == null ) throw new IllegalStateException("The cross-validation example sets have not been set.");

        return ilpCrossValidationExampleSets.getAllNegativeExamples();
    }

    /**
     * @return the earlyStoppingCondition
     */
    public StoppingCondition<ILPCrossValidationLoop> getEarlyStoppingCondition() {
        return earlyStoppingCondition;
    }

    /**
     * @param earlyStoppingCondition the earlyStoppingCondition to set
     */
    public void setEarlyStoppingCondition(StoppingCondition<ILPCrossValidationLoop> earlyStoppingCondition) {
        this.earlyStoppingCondition = earlyStoppingCondition;
    }

    /**
     * @return the flipFlopPositiveitiveAndNegativeativeExamples
     */
    public boolean getFlipFlopPositiveitiveAndNegativeativeExamples() {
        if (flipFlopValueHolder == null) {
            if ( ilpCrossValidationExampleSets != null ) {
                return ilpCrossValidationExampleSets.getFlipFlopPositiveitiveAndNegativeativeExamples();
            }
            else {
                return false;
            }
        }
        else {
            return flipFlopValueHolder;
        }
    }

    /**
     * @param flipFlopPositiveitiveAndNegativeativeExamples the flipFlopPositiveitiveAndNegativeativeExamples to set
     */
    public void setFlipFlopPositiveitiveAndNegativeativeExamples(boolean flipFlopPositiveitiveAndNegativeativeExamples) {

        if ( this.flipFlopValueHolder == null || this.flipFlopValueHolder != flipFlopPositiveitiveAndNegativeativeExamples ) {
            if ( this.ilpCrossValidationExampleSets != null ) {
                this.ilpCrossValidationExampleSets.setFlipFlopPositiveitiveAndNegativeativeExamples(flipFlopPositiveitiveAndNegativeativeExamples);

            	this.flipFlopValueHolder = null;
            }
            else {
            	this.flipFlopValueHolder = flipFlopPositiveitiveAndNegativeativeExamples;
            }
            
        }
    //  Utils.println("% CrossValidationLoopState: flipFlopPositiveAndNegativeExamples = " + flipFlopPositiveitiveAndNegativeativeExamples);
        outerLoopState.setFlipFlopPosAndNegExamples(flipFlopPositiveitiveAndNegativeativeExamples); // Add by JWS 12/8/09.
    }

    /**
     * @return the maximumCrossValidationTime
     */
    public long getMaximumCrossValidationTimeInMillisec() {
        return maximumCrossValidationTimeInMillisec;
    }

    /**
     * @param maximumCrossValidationTimeInMillisec the maximumCrossValidationTime to set
     */
    public void setMaximumCrossValidationTimeInMillisec(long maximumCrossValidationTimeInMillisec) {
    	if (maximumCrossValidationTimeInMillisec < 0) { Utils.waitHere("Should not have a Negativeative value: setMaximumCrossValidationTimeInMillisec = " + maximumCrossValidationTimeInMillisec); }
        this.maximumCrossValidationTimeInMillisec = Math.max(0, maximumCrossValidationTimeInMillisec);
    }


}
