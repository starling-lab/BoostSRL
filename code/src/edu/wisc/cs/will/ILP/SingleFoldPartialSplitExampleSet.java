/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.Utils.Utils;
import java.util.ArrayList;
import java.util.List;

/**
 *
 * @author twalker
 */
public class SingleFoldPartialSplitExampleSet extends CrossValidationExampleSets {

    /**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	public  double firstTrainExample  = -1; // These are FRACTIONS of the full set.
    public  double lastTrainExample   = -1;
    public  double firstEvalExample   = -1;
    public  double lastEvalExample    = -1;

    public SingleFoldPartialSplitExampleSet(List<Example> allPosExamples, List<Example> allNegExamples, double firstTrainExample, double lastTrainExample, double firstEvalExample, double lastEvalExample) {
        this(firstTrainExample, lastTrainExample, firstEvalExample, lastEvalExample);

        setAllPositiveExamples(allPosExamples);
        setAllNegativeExamples(allNegExamples);
        createFoldData();
    }

    public SingleFoldPartialSplitExampleSet(double firstTrainExample, double lastTrainExample, double firstEvalExample, double lastEvalExample) {
        super(1);

        this.firstTrainExample = firstTrainExample;
        this.lastTrainExample  = lastTrainExample;
        this.firstEvalExample  = firstEvalExample;
        this.lastEvalExample   = lastEvalExample;
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
            List<Example> foldPositivesTrainingExamples = new ArrayList<Example>();
            List<Example> foldPositivesEvalExamples     = new ArrayList<Example>();

            List<Example> foldNegativesTrainingExamples = new ArrayList<Example>();
            List<Example> foldNegativesEvalExamples     = new ArrayList<Example>();

            int exNumber;

            exNumber = 0;
            for (Example example : getAllPositiveExamples()) {
                if ( putThisExampleInThisTrainFold(exNumber++, getAllPositiveExamples().size())) {
                    foldPositivesTrainingExamples.add(example);
                }
                else if ( putThisExampleInThisEvalFold(exNumber, getAllPositiveExamples().size())) {
                	foldPositivesEvalExamples.add(example);
                }
            }

            exNumber = 0;
            for (Example example : getAllNegativeExamples()) {
                if ( putThisExampleInThisTrainFold(exNumber++, getAllNegativeExamples().size())) {
                    foldNegativesTrainingExamples.add(example);
                }
                else if ( putThisExampleInThisEvalFold(exNumber, getAllNegativeExamples().size())) {
                    foldNegativesEvalExamples.add(example);
                }
            }

            Utils.println("% CV Example setup (single fold):");

            Utils.println("%  Train in ["  + Utils.truncate(firstTrainExample, 2) + "," + Utils.truncate(lastTrainExample, 2)
            			+ "] and Test in(" + Utils.truncate(firstEvalExample,  2) + "," + Utils.truncate(lastEvalExample,  2) +"].");
            Utils.println("%  |posTRAIN| = " + Utils.getSizeSafely(foldPositivesTrainingExamples) + " examples");
            Utils.println("%  |negTRAIN| = " + Utils.getSizeSafely(foldNegativesTrainingExamples));
            Utils.println("%  |posEval|  = " + Utils.getSizeSafely(foldPositivesEvalExamples));
            Utils.println("%  |negEval|  = " + Utils.getSizeSafely(foldNegativesEvalExamples));
       //   Utils.waitHere("[" + firstTrainExample + "," + lastTrainExample + "] [" + firstEvalExample + ", " + lastEvalExample + "]");
            
            
            if (Utils.getSizeSafely(foldNegativesEvalExamples) + Utils.getSizeSafely(foldPositivesEvalExamples) < 1) {
            	Utils.println("\n% NOTE: Since there are no Eval examples, the TRAINING examples will also be used for that task.");
            	foldPositivesEvalExamples.addAll(foldPositivesTrainingExamples);
            	foldNegativesEvalExamples.addAll(foldNegativesTrainingExamples);
            }

            setPositiveTrainingExamplesForFold(  fold, foldPositivesTrainingExamples);
            setPositiveEvaluationExamplesForFold(fold, foldPositivesEvalExamples);
            setNegativeTrainingExamplesForFold(  fold, foldNegativesTrainingExamples);
            setNegativeEvaluationExamplesForFold(fold, foldNegativesEvalExamples);
            
        }
    }

    private boolean putThisExampleInThisTrainFold(int exNumber, int totalNumberOfExamples) {
    	if (firstTrainExample >= 0.0) {
    		return exNumber >= firstTrainExample * totalNumberOfExamples && exNumber < lastTrainExample * totalNumberOfExamples; 
    	}
		return false;
    }    
    private boolean putThisExampleInThisEvalFold(int exNumber, int totalNumberOfExamples) {        
    	if (firstEvalExample >= 0.0) {
    		return exNumber >= firstEvalExample   * totalNumberOfExamples && exNumber < lastEvalExample  * totalNumberOfExamples;
    	}
		return false;
    	
    }

   
}
