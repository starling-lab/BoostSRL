/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.Utils.Permute;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

/**
 *
 * @author twalker
 */
@SuppressWarnings("serial")
public class CrossValidationExampleSets implements Serializable{

    private int numberOfFolds = -1; // Initialize to illegal value so we know it has been set.

    private List<Example> allPositiveExamples;

    private List<Example> allNegativeExamples;

    protected boolean foldsInitialized = false;

    // Arrays of lists holding the various examples indecies.
    // There is one List for each exampleType for each fold.
    // The examples in these Lists should be the same as
    // the ones in the allPositiveExamples/allNegativeExamples lists.
    // I don't think bad things will happen if they aren't,
    // but we might get some odd behavior.
    private List<Example> positiveTrainingExamplesForFolds[];

    private List<Example> negativeTrainingExamplesForFolds[];

    private List<Example> positiveTestingExamplesForFolds[];

    private List<Example> negativeEvaluationExamplesForFolds[];

    private boolean flipFlopPositiveitiveAndNegativeativeExamples = false;


    /** Creates an ILPExampleCollection for <code>numberOfFolds</code> folds.
     *
     * This will create an example collection for numberOfFolds folds.  Since
     * no examples are provided, the fold data structures will not be populated
     * and must be done manually after the examples are set via the
     * setAllPositiveExamples() and setAllNegativeExamples() methods.
     *
     * @param numberOfFolds Number of Folds in the collection.
     */
    public CrossValidationExampleSets(int numberOfFolds) {
        setNumberOfFolds(numberOfFolds);
    }

    /** Creates an ILPExampleCollection for <code>numberOfFolds</code> folds with the provided examples.
     *
     * This method will create copies of the provided example lists, randomly permute the examples
     * and then build all of the fold data structures.
     *
     * @param numberOfFolds Number of Folds in the collection.
     * @param allPositiveExamples List of all positiveitive examples.  This list will be copied.
     * @param allNegativeExamples List of all negativeative examples.  This list will be copied.
     */
    public CrossValidationExampleSets(int numberOfFolds, List<Example> allPositiveExamples, List<Example> allNegativeExamples) {
        setNumberOfFolds(numberOfFolds);
        setAllPositiveExamples(allPositiveExamples);
        setAllNegativeExamples(allNegativeExamples);

        if (numberOfFolds > 1) {
            permuteAllExamples();
        }

        createFoldData();
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
     * @param savedExampleSets
     * @throws IncongruentSavedStateException
     */
    protected void checkStateCongruency(CrossValidationExampleSets savedExampleSets) throws IncongruentSavedStateException {

        // It is okay for the other set to be null.  That just means it wasn't initialized,
        // so it can definitely be replaced by an initialized one.
        if ( savedExampleSets == null ) return;

        // Check that the number of folds was the same...
        if (numberOfFolds != savedExampleSets.numberOfFolds) {
            throw new IncongruentSavedStateException("Saved ILPCrossValidationExampleSets configured with incorrect number of folds. " +
                    "Expected = " + numberOfFolds + ".  Found = " + savedExampleSets.numberOfFolds + ".");
        }

        if ( allPositiveExamples != savedExampleSets.allPositiveExamples && ( allPositiveExamples == null || allPositiveExamples.equals(savedExampleSets.allPositiveExamples)) == false ) {
            throw new IncongruentSavedStateException("Saved ILPCrossValidationExampleSets positiveitive examples not equivalent.");
        }

        if ( allNegativeExamples != savedExampleSets.allNegativeExamples && ( allNegativeExamples == null || allNegativeExamples.equals(savedExampleSets.allNegativeExamples)) == false ) {
            throw new IncongruentSavedStateException("Saved ILPCrossValidationExampleSets negativeative examples not equivalent.");
        }

        for(int i = 0; i < numberOfFolds; i++) {

            List<Example> list1;
            List<Example> list2;

            list1 = getPositiveTrainingExamplesForFold(i);
            list2 = savedExampleSets.getPositiveTrainingExamplesForFold(i);

            if ( list1 != list2 && ( list1 == null || list1.equals(list2)) == false ) {
                throw new IncongruentSavedStateException("Saved ILPCrossValidationExampleSets positiveitive training examples for fold " + i + " are not equivalent.");
            }

            list1 = getNegativeTrainingExamplesForFold(i);
            list2 = savedExampleSets.getNegativeTrainingExamplesForFold(i);

            if ( list1 != list2 && ( list1 == null || list1.equals(list2)) == false ) {
                throw new IncongruentSavedStateException("Saved ILPCrossValidationExampleSets negativeative training examples for fold " + i + " are not equivalent.");
            }

            list1 = getPositiveEvaluationExamplesForFold(i);
            list2 = savedExampleSets.getPositiveEvaluationExamplesForFold(i);

            if ( list1 != list2 && ( list1 == null || list1.equals(list2)) == false ) {
                throw new IncongruentSavedStateException("Saved ILPCrossValidationExampleSets positiveitive testing examples for fold " + i + " are not equivalent.");
            }

            list1 = getNegativeEvaluationExamplesForFold(i);
            list2 = savedExampleSets.getNegativeEvaluationExamplesForFold(i);

            if ( list1 != list2 && ( list1 == null || list1.equals(list2)) == false ) {
                throw new IncongruentSavedStateException("Saved ILPCrossValidationExampleSets negativeative testing examples for fold " + i + " are not equivalent.");
            }
        }

    }

    /** Permutes the positiveitive and negativeative examples.
     * 
     */
    public final void permuteAllExamples() {

        if (foldsInitialized == true) {
            throw new IllegalStateException("The folds have already been created.  Examples can not be permuted afterwards.");
        }

        if (allPositiveExamples != null) {
            Permute.permute(allPositiveExamples);
        }

        if (allNegativeExamples != null) {
            Permute.permute(allNegativeExamples);
        }
    }

    /** Creates the cross validation data sets.
     *
     * ILPCrossValidationLoop could be subclasses to replace this method if you want a different
     * cross validation data set creation method.
     *
     */
    private void createFoldData() {

        if (foldsInitialized == true) {
            throw new IllegalStateException("The folds have already been created.  createFoldData should only be called once.");
        }

        foldsInitialized = true;

        for (int fold = 0; fold < getNumberOfFolds(); fold++) {
            List<Example> foldPositiveitivesTrainingExamples = new ArrayList<Example>();
            List<Example> foldPositiveitivesTestingExamples = new ArrayList<Example>();

            List<Example> foldNegativeativeTrainingExamples = new ArrayList<Example>();
            List<Example> foldNegativeativeTestingExamples = new ArrayList<Example>();

            if ( allPositiveExamples != null ) {
                for (int i = 0; i < allPositiveExamples.size(); i++) {
                    if (getNumberOfFolds() > 1 && i % getNumberOfFolds() == fold) {
                        foldPositiveitivesTestingExamples.add(allPositiveExamples.get(i));
                    }
                    else {
                        foldPositiveitivesTrainingExamples.add(allPositiveExamples.get(i));
                    }
                }
            }

            if ( allNegativeExamples != null ) {
                for (int i = 0; i < allNegativeExamples.size(); i++) {
                    if (getNumberOfFolds() > 1 && i % getNumberOfFolds() == fold) {
                        foldNegativeativeTestingExamples.add(allNegativeExamples.get(i));
                    }
                    else {
                        foldNegativeativeTrainingExamples.add(allNegativeExamples.get(i));
                    }
                }
            }

            setPositiveTrainingExamplesForFold(fold, foldPositiveitivesTrainingExamples);
            setPositiveEvaluationExamplesForFold(fold, foldPositiveitivesTestingExamples);
            setNegativeTrainingExamplesForFold(fold, foldNegativeativeTrainingExamples);
            setNegativeEvaluationExamplesForFold(fold, foldNegativeativeTestingExamples);
        }
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
    @SuppressWarnings("unchecked")
	private void setNumberOfFolds(int numberOfFolds) {

        if (numberOfFolds <= 0) {
            throw new IllegalArgumentException("Number of folds must be >= 1.");
        }

        if (numberOfFolds != this.numberOfFolds) {
            if (this.numberOfFolds != -1) {
                throw new IllegalStateException("The number of folds has already been set.  Once set, it cannot be changed.");
            }

            this.numberOfFolds = numberOfFolds;

            positiveTrainingExamplesForFolds = new List[numberOfFolds];
            negativeTrainingExamplesForFolds = new List[numberOfFolds];

            positiveTestingExamplesForFolds = new List[numberOfFolds];
            negativeEvaluationExamplesForFolds = new List[numberOfFolds];
        }
    }

    /**
     * @return the allPositiveExamples
     */
    public List<Example> getAllPositiveExamples() {
        return allPositiveExamples;
    }

    /** Sets the List of all positiveitive examples.
     *
     * After the positiveitive and negativeative examples have been set,
     * the methods permuteAllExamples() can be used to
     * randomly permute the sets.
     *
     * Folds data can then be created via the createFoldData();
     *
     * The allPositiveExample and allNegativeExample lists should only be
     * set prior to the creation of fold data (or manually setting
     * fold data via the set*ExamplesForFold() methods).
     *
     * @param allPositiveExamples the allPositiveExamples to set
     */
    public final void setAllPositiveExamples(List<Example> allPositiveExamples) {

        if (foldsInitialized == true) {
            throw new IllegalStateException("The folds have already been created.  Once created, the example sets should not be changed.");
        }

        this.allPositiveExamples = allPositiveExamples;
    }

    /**
     * @return the allNegativeExamples
     */
    public List<Example> getAllNegativeExamples() {
        return allNegativeExamples;
    }

    /** Sets the List of all negativeative examples.
     *
     * After the positiveitive and negativeative examples have been set,
     * the methods permuteAllExamples() can be used to
     * randomly permute the sets.
     *
     * Folds data can then be created via the createFoldData();
     *
     * The allPositiveExample and allNegativeExample lists should only be
     * set prior to the creation of fold data (or manually setting
     * fold data via the set*ExamplesForFold() methods).
     *
     * @param allNegativeExamples the allNegativeExamples to set
     */
    public final void setAllNegativeExamples(List<Example> allNegativeExamples) {

        if (foldsInitialized == true) {
            throw new IllegalStateException("The folds have already been created.  Once created, the example sets should not be changed.");
        }

        this.allNegativeExamples = allNegativeExamples;
    }

    /** Returns the NegativeTestingExamples for fold, positivesibly null if not set.
     *
     * Note, that the list returned is the actual list, not a copy.
     * If you need to edit the list, please make a copy of it.
     *
     * @param fold
     * @return List of examples, null if examples are not set.
     */
    public List<Example> getNegativeEvaluationExamplesForFold(int fold) {
        return negativeEvaluationExamplesForFolds[fold];
    }

    /** Sets the NegativeTestingExamples for fold, replacing the existing setting.
     *
     * @param fold
     * @param negativeTestingExamplesForFolds
     */
    public void setNegativeEvaluationExamplesForFold(int fold, List<Example> negativeTestingExamplesForFolds) {
        foldsInitialized = true;
        this.negativeEvaluationExamplesForFolds[fold] = new ArrayList<Example>(negativeTestingExamplesForFolds);
    }

    /** Returns the NegativeTrainingExamples for fold, positivesibly null if not set.
     *
     * Note, that the list returned is the actual list, not a copy.
     * If you need to edit the list, please make a copy of it.
     *
     * @param fold
     * @return List of examples, null if examples are not set.
     */
    public List<Example> getNegativeTrainingExamplesForFold(int fold) {
        return negativeTrainingExamplesForFolds[fold];
    }

    /** Sets the NegativeTrainingExamples for Fold, replacing the existing setting.
     *
     * @param fold
     * @param negativeTrainingExamplesForFolds
     */
    public void setNegativeTrainingExamplesForFold(int fold, List<Example> negativeTrainingExamplesForFolds) {
        foldsInitialized = true;
        this.negativeTrainingExamplesForFolds[fold] = new ArrayList<Example>(negativeTrainingExamplesForFolds);
    }

    /** Returns the PositiveTestingExamples for fold, positivesibly null if not set.
     *
     * Note, that the list returned is the actual list, not a copy.
     * If you need to edit the list, please make a copy of it.
     *
     * @param fold
     * @return List of examples, null if examples are not set.
     */
    public List<Example> getPositiveEvaluationExamplesForFold(int fold) {
        return positiveTestingExamplesForFolds[fold];
    }

    /** Sets the PositiveTestingExamples for Fold, replacing the existing setting.
     *
     * @param fold
     * @param positiveTestingExamplesForFolds
     */
    public void setPositiveEvaluationExamplesForFold(int fold, List<Example> positiveTestingExamplesForFolds) {
        foldsInitialized = true;
        this.positiveTestingExamplesForFolds[fold] = new ArrayList<Example>(positiveTestingExamplesForFolds);
    }

    /** Returns the PositiveTrainingExamples for fold, positivesibly null if not set.
     *
     * Note, that the list returned is the actual list, not a copy.
     * If you need to edit the list, please make a copy of it.
     *
     * @param fold
     * @return List of examples, null if examples are not set.
     */
    public List<Example> getPositiveTrainingExamplesForFold(int fold) {
        return positiveTrainingExamplesForFolds[fold];
    }

    /** Sets the PositiveTrainingExamples for Fold, replacing the existing setting.
     *
     * @param fold
     * @param positiveTrainingExamplesForFolds
     */
    public void setPositiveTrainingExamplesForFold(int fold, List<Example> positiveTrainingExamplesForFolds) {
        foldsInitialized = true;
        this.positiveTrainingExamplesForFolds[fold] = new ArrayList<Example>(positiveTrainingExamplesForFolds);
    }

    /**
     * @return the flipFlopPositiveitiveAndNegativeativeExamples
     */
    public boolean getFlipFlopPositiveitiveAndNegativeativeExamples() {
        return flipFlopPositiveitiveAndNegativeativeExamples;
    }

    /** Flips the positiveitive and negativeative example sets.
     *
     * If the new value is not the same as the current value, all positiveitive and negativeative
     * sets will be exchanged with their appropriate counterpart.
     *
     * In general, it is safest to flip the examples after all examples sets are
     * initialized to their non-flip-flopped values.  If you setup any example sets after
     * things are flipped, be careful!
     *
     * @param flipFlopPositiveitiveAndNegativeativeExamples the flipFlopPositiveitiveAndNegativeativeExamples to set
     * @throws IllegalStateException If neither allPositiveExamples or allNegativeExamples are set, this method will throw an exception.
     * This is done to protect the user from setting flipFlopped to true and then incorrectly setting up the examples.
     */
    public void setFlipFlopPositiveitiveAndNegativeativeExamples(boolean flipFlopPositiveitiveAndNegativeativeExamples) throws IllegalStateException{
        if (this.flipFlopPositiveitiveAndNegativeativeExamples != flipFlopPositiveitiveAndNegativeativeExamples) {

            if ( allPositiveExamples == null && allNegativeExamples == null ) {
                throw new IllegalStateException("The ILPCrossValidationExampleSets examples were flipped prior to the positiveitive and negativeative examples being set.  The examples must be set prior to flipping.");
            }

            this.flipFlopPositiveitiveAndNegativeativeExamples = flipFlopPositiveitiveAndNegativeativeExamples;

            List<Example> temp = allPositiveExamples;
            allPositiveExamples = allNegativeExamples;
            allNegativeExamples = temp;

            List<Example>[] temp2 = positiveTestingExamplesForFolds;
            positiveTestingExamplesForFolds = negativeEvaluationExamplesForFolds;
            negativeEvaluationExamplesForFolds = temp2;

            temp2 = positiveTrainingExamplesForFolds;
            positiveTrainingExamplesForFolds = negativeTrainingExamplesForFolds;
            negativeTrainingExamplesForFolds = temp2;
        }
    }
}
