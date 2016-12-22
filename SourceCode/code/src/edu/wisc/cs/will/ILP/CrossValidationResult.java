/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.Utils.Utils;
import java.util.Comparator;

/**
 *
 * @author twalker
 */
public class CrossValidationResult {

    private CoverageScore averageTrainingCoverageScore;
    private CoverageScore averageEvaluationCoverageScore;

    private int numberOfFolds;

    private CrossValidationFoldResult[] foldResults;

    public CrossValidationResult(int numberOfFolds) {
        this.numberOfFolds = numberOfFolds;
        foldResults = new CrossValidationFoldResult[numberOfFolds];
    }

    public CrossValidationFoldResult getFoldResult(int fold) {
        return foldResults[fold];
    }

    public void setFoldResult(int fold, CrossValidationFoldResult foldResult) {
        foldResults[fold] = foldResult;

        invalidateCoverageScores();
    }

    public CrossValidationFoldResult[] getFoldResults() {
        return foldResults;
    }

    protected void invalidateCoverageScores() {
        setAverageEvaluationCoverageScore(null);
        setAverageTrainingCoverageScore(  null);
    }

    /**
     * @return the averageTrainingCoverageScore
     */
    public CoverageScore getAverageTrainingCoverageScore() {
        calculateAverageTrainingCoverageScore();

        return averageTrainingCoverageScore;
    }

    /**
     * @param averageTrainingCoverageScore the averageTrainingCoverageScore to set
     */
    private void setAverageTrainingCoverageScore(CoverageScore averageTrainingCoverageScore) {
        this.averageTrainingCoverageScore = averageTrainingCoverageScore;
    }

    /**
     * @return the averageTestingCoverageScore
     */
    public CoverageScore getAverageEvaluationCoverageScore() {
        calculateAverageEvaluationCoverageScore();

        return averageEvaluationCoverageScore;
    }

    /**
     * @param averageEvaluationCoverageScore the averageTestingCoverageScore to set
     */
    private void setAverageEvaluationCoverageScore(CoverageScore averageEvaluationCoverageScore) {
        this.averageEvaluationCoverageScore = averageEvaluationCoverageScore;
    }

    private void calculateAverageTrainingCoverageScore() {
        if (averageTrainingCoverageScore == null) {
            double tp = 0;
            double tn = 0;
            double fp = 0;
            double fn = 0;

            double fnMEst = 0;
            double fpMEst = 0;

            int foldCount = 0;

            for (int i = 0; i < foldResults.length; i++) {
                CrossValidationFoldResult foldResult = foldResults[i];

                if (foldResult != null) {
                    foldCount ++;

                    CoverageScore score = foldResult.getTrainingCoverageScore();

                    if (score != null) {
                    	tp += score.getTruePositives();
                    	tn += score.getTrueNegatives();
                    	fp += score.getFalsePositives();
                    	fn += score.getFalseNegatives();

                    	fnMEst += score.getFalseNegativeMEstimate();
                    	fpMEst += score.getFalsePositiveMEstimate();
                    } /*else { // Call everything NEGATIVE.  TODO - need #pos and #neg
                    	tp += 0;
                    	tn += 100; // THIS IS INCORRECT! JWSJWSJWS
                    	fp += 0;
                    	fn += 100;
                    		
                    	fnMEst += 0.01;
                    	fpMEst += 0;
                    } */
                }
            }

            averageTrainingCoverageScore = new CoverageScore(tp/foldCount, fp/foldCount, tn/foldCount, fn/foldCount, fnMEst/foldCount, fpMEst/foldCount);
        }
    }

    private void calculateAverageEvaluationCoverageScore() {
        if (averageEvaluationCoverageScore == null) {
            double tp = 0;
            double tn = 0;
            double fp = 0;
            double fn = 0;

            double fnMEst = 0;
            double fpMEst = 0;

            int foldCount = 0;

            for (int i = 0; i < foldResults.length; i++) {
                CrossValidationFoldResult foldResult = foldResults[i];

                if (foldResult != null) {
                    

                    CoverageScore score = foldResult.getEvaluationCoverageScore();

                    if ( score != null ) {
                        foldCount ++;
                        tp += score.getTruePositives();
                        tn += score.getTrueNegatives();
                        fp += score.getFalsePositives();
                        fn += score.getFalseNegatives();

                        fnMEst += score.getFalseNegativeMEstimate();
                        fpMEst += score.getFalsePositiveMEstimate();
                    }
                }
            }

            if ( foldCount > 0 ) {
                averageEvaluationCoverageScore = new CoverageScore(tp/foldCount, fp/foldCount, tn/foldCount, fn/foldCount, fnMEst/foldCount, fpMEst/foldCount);
            }
        }
    }

    public double getAverageTrainingAccuracy() {
        CoverageScore score = getAverageTrainingCoverageScore();

        if (score == null) {
            return Double.NaN;
        }
        else {
            return score.getAccuracy();
        }
    }

    public double getAverageTestingAccuracy() {
        CoverageScore score = getAverageEvaluationCoverageScore();

        if (score == null) {
            return Double.NaN;
        }
        else {
            return score.getAccuracy();
        }
    }

    public double getAverageAccuracy() {
        double v = getAverageTestingAccuracy();

        if (Double.isNaN(v)) {
            v = getAverageTrainingAccuracy();
        }

        return v;
    }

    public double getAverageTrainingPrecision() {
        CoverageScore score = getAverageTrainingCoverageScore();

        if (score == null) {
            return Double.NaN;
        }
        else {
            return score.getPrecision();
        }
    }

    public double getAverageTestingPrecision() {
        CoverageScore score = getAverageEvaluationCoverageScore();

        if (score == null) {
            return Double.NaN;
        }
        else {
            return score.getPrecision();
        }
    }

    public double getAveragePrecision() {
        double v = getAverageTestingPrecision();

        if (Double.isNaN(v)) {
            v = getAverageTrainingPrecision();
        }

        return v;
    }

    public double getAverageTrainingRecall() {
        CoverageScore score = getAverageTrainingCoverageScore();

        if (score == null) {
            return Double.NaN;
        }
        else {
            return score.getRecall();
        }
    }

    public double getAverageTestingRecall() {
        CoverageScore score = getAverageEvaluationCoverageScore();

        if (score == null) {
            return Double.NaN;
        }
        else {
            return score.getRecall();
        }
    }

    public double getAverageRecall() {
        double v = getAverageTestingRecall();

        if (Double.isNaN(v)) {
            v = getAverageTrainingRecall();
        }

        return v;
    }

    public double getAverageTrainingFBeta(double beta) {
        CoverageScore score = getAverageTrainingCoverageScore();

        if (score == null) {
            return Double.NaN;
        }
		return score.getFBeta(beta);
    }


    public double getAverageTestingFBeta() {
    	return getAverageTestingFBeta(1.0); 
    }
    public double getAverageTestingFBeta(double beta) {
        CoverageScore score = getAverageEvaluationCoverageScore();

        if (score == null) {
            return Double.NaN;
        }
		return score.getFBeta(beta);
    }

    public double getAverageFBeta() {
    	return getAverageFBeta(1.0); 
    }
    public double getAverageFBeta(double beta) {
        CoverageScore score = getAverageEvaluationCoverageScore();

        if (score == null) {
            score = getAverageTrainingCoverageScore();
        }

        if ( score == null ) {
            return Double.NaN;
        }
		return score.getFBeta(beta);
    }

    public int getCompletedFoldCount() {
        int count = 0;
        for (int i = 0; i < foldResults.length; i++) {
            if ( foldResults[i] != null ) {
                count++;
            }

        }
        return count;
    }

    public boolean isCrossValidationComplete() {
        return getCompletedFoldCount() == numberOfFolds;
    }

    /**
     * @return the numberOfFolds
     */
    public int getNumberOfFolds() {
        return numberOfFolds;
    }

    
    public String toShortString() {
        StringBuilder sb = new StringBuilder();

        CoverageScore cs;

        sb.append("% Folds = ").append(getNumberOfFolds());

        cs = getAverageTrainingCoverageScore();
        if ( cs != null ) {
            sb.append(", Train: ").append(cs.toShortString());
        }
        cs = getAverageEvaluationCoverageScore();
        if ( cs != null ) {
            sb.append(", Test: ").append(cs.toShortString());
        }
        return sb.toString();
    }

    public String toLongString() {
                StringBuilder sb = new StringBuilder();

        CoverageScore cs;

        sb.append("%%% Cross-Validation Average Scores [Folds = ").append(getNumberOfFolds()).append("]:\n\n");

        cs = getAverageTrainingCoverageScore();
        if ( cs != null ) {
            sb.append("%%% Average TRAINING Coverage Score:\n").append(cs.toLongString());
        }
        cs = getAverageEvaluationCoverageScore();
        if ( cs != null ) {
            sb.append("%%% Average TESTING[Trevor should rename or drop this] Coverage Score:\n").append(cs.toLongString());
        }
        return sb.toString();
    }

    @Override
    public String toString() {
        return toShortString();
    }

    /** Returns the FoldResults with the best Accuracy across all examples.
     *
     * The coverage score used to compare the fold results is based upon all
     * of the examples in the positive and negative sets.  If you would like
     * to get the best overall, you can pass a more specific comparator into
     * the getBestOrverallFold(Comparator&ltILPCVFoldResult&gt foldComparator)
     * method.
     *
     * @return FoldResults with the best Accuracy across all examples.
     */
    public CrossValidationFoldResult getBestOverallFoldByAccuracy() {
        return getBestOverallFold(CoverageScore.ascendingAccuracyComparator);
    }

    public CrossValidationFoldResult getBestOverallFoldByF1() {
        return getBestOverallFold(CoverageScore.ascendingF1Comparator);
    }
    
    /** Returns the best FoldResults across all examples as determined by the comparator.
     *
     * The comparator must be a CoverageScore comparator.  The CoverageScore
     * class many of the common comparison, such as accuracy, precision, etc.
     *
     * The coverage score used to compare the fold results is based upon all
     * of the examples in the positive and negative sets.  If you would like
     * to get the best overall, you can pass a more specific comparator into
     * the getBestOrverallFold(Comparator&ltILPCVFoldResult&gt foldComparator)
     * method.
     *
     * @param coverageScoreComparator CoverageScore comparator used to order the
     * fold results.  The coverage score compared is based upon all examples,
     * not just the evaluation test.
     * 
     * @return FoldResults with the best coverage score across all examples as determined by the comparator.
     */
    public CrossValidationFoldResult getBestOverallFold(final Comparator<CoverageScore> coverageScoreComparator) {

        Comparator<CrossValidationFoldResult> foldComparator = new Comparator<CrossValidationFoldResult>() {

            public int compare(CrossValidationFoldResult o1, CrossValidationFoldResult o2) {
                return coverageScoreComparator.compare(o1.getAllExamplesCoverageScore(), o2.getAllExamplesCoverageScore());
            }
        };

        return getBestOrverallFold(foldComparator);
    }

    /** Returns the best FoldResults as determined by the comparator.
     *
     * This method allows for maximum configurability with regards to how to
     * compare folds.  See getBestOverallFoldByAccuracy() and
     * getBestOverallFold(final Comparator<CoverageScore> coverageScoreComparator)
     * for simplier calling patterns.
     *
     * @param foldComparator Comparator used to order the fold results.
     * @return FoldResults with the best score as determined by the comparator.
     */
    public CrossValidationFoldResult getBestOrverallFold(Comparator<CrossValidationFoldResult> foldComparator) {
        CrossValidationFoldResult best = Utils.argmax(foldComparator, foldResults);

        return best;
    }



}
