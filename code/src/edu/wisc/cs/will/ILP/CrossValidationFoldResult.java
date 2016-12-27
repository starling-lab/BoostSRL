/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.FOPC.Theory;
import java.io.Serializable;

/**
 *
 * @author twalker
 */
@SuppressWarnings("serial")
public class CrossValidationFoldResult implements Serializable {
    private int     fold;
    private Theory  theory;
    private Gleaner gleaner;

    private CoverageScore trainingCoverageScore    = null;
    private CoverageScore evaluationCoverageScore  = null;
    private CoverageScore allExamplesCoverageScore = null;

    public CrossValidationFoldResult(int fold, Theory theory, Gleaner gleaner) {
        this.fold = fold;
        this.theory = theory;
        this.gleaner = gleaner;
    }

    /**
     * @return the gleaner
     */
    public Gleaner getGleaner() {
        return gleaner;
    }

    /**
     * @param gleaner the gleaner to set
     */
    public void setGleaner(Gleaner gleaner) {
        this.gleaner = gleaner;
    }

    /**
     * @return the theory
     */
    public Theory getTheory() {
        return theory;
    }

    /**
     * @param theory the theory to set
     */
    public void setTheory(Theory theory) {
        if (this.theory != theory) {

            this.theory = theory;

            invalidateCoverageScores();
        }
    }

    protected void invalidateCoverageScores() {
        trainingCoverageScore = null;
        evaluationCoverageScore = null;
    }

    /**
     * @return the fold
     */
    public int getFold() {
        return fold;
    }

    /**
     * @param fold the fold to set
     */
    public void setFold(int fold) {
        this.fold = fold;
    }

    /**
     * @return the trainingCoverageScore
     */
    public CoverageScore getTrainingCoverageScore() {

        return trainingCoverageScore;
    }

    /**
     * @param trainingCoverageScore the trainingCoverageScore to set
     */
    public void setTrainingCoverageScore(CoverageScore trainingCoverageScore) {
        this.trainingCoverageScore = trainingCoverageScore;
    }

    /**
     * @return the testingCoverageScore
     */
    public CoverageScore getEvaluationCoverageScore() {
        return evaluationCoverageScore;
    }
    
    /**
     * @param testingCoverageScore the testingCoverageScore to set
     */
    public void setEvaluationCoverageScore(CoverageScore evaluationCoverageScore) {
        this.evaluationCoverageScore = evaluationCoverageScore;
    }

    /**
     * @return the allExamplesCoverageScore
     */
    public CoverageScore getAllExamplesCoverageScore() {
        return allExamplesCoverageScore;
    }

    /**
     * @param allExamplesCoverageScore the allExamplesCoverageScore to set
     */
    public void setAllExamplesCoverageScore(CoverageScore allExamplesCoverageScore) {
        this.allExamplesCoverageScore = allExamplesCoverageScore;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        CoverageScore cs;

        sb.append("Cross-Validation Fold Result (Fold #").append(getFold()).append("):\n\n");

        sb.append(getTheory().toString()).append("\n");

        cs = getTrainingCoverageScore();
        if ( cs != null ) {
            sb.append("\n%%% TRAINING-SET Coverage Score:\n").append(cs.toLongString()).append("\n");
        }
        cs = getEvaluationCoverageScore();
        if ( cs != null ) {
            sb.append("\n%%% EVALUATION-SET Coverage Score:\n").append(cs.toLongString()).append("\n");
        }

        cs = getAllExamplesCoverageScore();
        if ( cs != null ) {
            sb.append("\n%%% All Examples Coverage Score:\n").append(cs.toLongString()).append("\n");
        }

        return sb.toString();
    }




}
