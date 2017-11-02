/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Theory;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 *
 * @author twalker
 */
public class DefaultLoopState implements ILPLoopState, Cloneable {

    private List<Example> positiveExamples;

    private List<Example> negativeExamples;

    private long maximumTimeInSeconds;

    private Theory learnedTheory;

    private CoverageScore coverageScore;

    /**
     * @return the positiveExamples
     */
    public List<Example> getPositiveExamples() {
        return positiveExamples;
    }

    /**
     * @param positiveExamples the positiveExamples to set
     */
    public void setPositiveExamples(List<Example> positiveExamples) {
        this.positiveExamples = positiveExamples;
    }

    /**
     * @return the negativeExamples
     */
    public List<Example> getNegativeExamples() {
        return negativeExamples;
    }

    /**
     * @param negativeExamples the negativeExamples to set
     */
    public void setNegativeExamples(List<Example> negativeExamples) {
        this.negativeExamples = negativeExamples;
    }

    /**
     * @return the maximumTimeInSeconds
     */
    public long getMaximumTimeInSeconds() {
        return maximumTimeInSeconds;
    }

    /**
     * @param maximumTimeInSeconds the maximumTimeInSeconds to set
     */
    public void setMaximumTimeInSeconds(long maximumTimeInSeconds) {
        this.maximumTimeInSeconds = maximumTimeInSeconds;
    }

    /**
     * @return the learnedTheory
     */
    public Theory getLearnedTheory() {
        return learnedTheory;
    }

    /**
     * @param learnedTheory the learnedTheory to set
     */
    public void setLearnedTheory(Theory learnedTheory) {
        this.learnedTheory = learnedTheory;
    }

    /**
     * @return the coverageScore
     */
    public CoverageScore getCoverageScore() {
        return coverageScore;
    }

    /**
     * @param coverageScore the coverageScore to set
     */
    public void setCoverageScore(CoverageScore coverageScore) {
        this.coverageScore = coverageScore;
    }

    public DefaultLoopState copy() {
        try {
            DefaultLoopState copy = clone();

            return copy;
        } catch (CloneNotSupportedException ex) {
        }

        return null;
    }

    protected DefaultLoopState clone() throws CloneNotSupportedException {
        return (DefaultLoopState) super.clone();
    }
}
