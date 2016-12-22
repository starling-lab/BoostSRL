/*
 * CoverageScore.java
 *
 * Created on December 3, 2007, 9:04 AM
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.Utils.Utils;
import java.io.Serializable;
import java.util.Comparator;

/**
 *
 * @author twalker
 */
@SuppressWarnings("serial")
public class CoverageScore implements Serializable {

    public final static Comparator<CoverageScore> ascendingAccuracyComparator = new AccuracyComparator(true);
    public final static Comparator<CoverageScore> descendingAccuracyComparator = new AccuracyComparator(false);
    public final static Comparator<CoverageScore> ascendingPrecisionComparator = new PrecisionComparator(true);
    public final static Comparator<CoverageScore> descendingPrecisionComparator = new PrecisionComparator(false);
    public final static Comparator<CoverageScore> ascendingRecallComparator = new RecallComparator(true);
    public final static Comparator<CoverageScore> descendingRecallComparator = new RecallComparator(false);
    public final static Comparator<CoverageScore> ascendingF1Comparator = new F1Comparator(true);
    public final static Comparator<CoverageScore> descendingF1Comparator = new F1Comparator(false);

    private double truePositives  = 0;
    private double falsePositives = 0;
    private double trueNegatives  = 0;
    private double falseNegatives = 0;
    private double falseNegativeMEstimate = 0;
    private double truePositiveMEstimate  = 0;
    private double falsePositiveMEstimate = 0;
    private double trueNegativeMEstimate  = 0;

    /** Creates a new instance of CoverageScore */
    public CoverageScore() {
    }

    /** Creates a new instance of CoverageScore.
     *
     * @param tp True Positives (possibly weighted).
     * @param fp False Positives (possibly weighted).
     * @param tn True Negatives (possibly weighted).
     * @param fn False Negatives (possibly weighted).
     * @param falseNegativeMEstimate False negative mEstimate used when calculating precision/recall/F score.
     * @param falsePositiveMEstimate False positive mEstimate used when calculating precision/recall/F score.
     */
    public CoverageScore(double tp, double fp, double tn, double fn, double falseNegativeMEstimate, double falsePositiveMEstimate) {
        setCounts(tp, fp, tn, fn);
        this.falseNegativeMEstimate = falseNegativeMEstimate;
        this.falsePositiveMEstimate = falsePositiveMEstimate;
    }

    /** Creates a new instance of CoverageScore.
     *
     * This form of the constructor sets the mEstimates to 0.
     *
     * @param tp True Positives (possibly weighted).
     * @param fp False Positives (possibly weighted).
     * @param tn True Negatives (possibly weighted).
     * @param fn False Negatives (possibly weighted).
     */
    public CoverageScore(double tp, double fp, double tn, double fn) {
        this(tp, fp, tn, fn, 0, 0);
    }

    public void setCounts(double tp, double fp, double tn, double fn) {
        this.setTruePositives( tp);
        this.setFalseNegatives(fn);
        this.setFalsePositives(fp);
        this.setTrueNegatives( tn);
    }

    public double getPrecision() {
        return Utils.getPrecision(truePositives + truePositiveMEstimate, falsePositives + falsePositiveMEstimate);
    }

    public double getRecall() {
        return Utils.getRecall(truePositives + truePositiveMEstimate, falseNegatives + falseNegativeMEstimate);
    }

    public double getAccuracy() {
        return Utils.getAccuracy(truePositives + truePositiveMEstimate, falsePositives + falsePositiveMEstimate, trueNegatives + trueNegativeMEstimate, falseNegatives + falseNegativeMEstimate);
    }

    public double getF1() {
        return Utils.getF1(truePositives + truePositiveMEstimate, falsePositives + falsePositiveMEstimate, falseNegatives + falseNegativeMEstimate);
    }

    public double getFBeta(double beta) {
        return Utils.getFBeta(beta, truePositives + trueNegativeMEstimate, falsePositives + falsePositiveMEstimate, falseNegatives + falseNegativeMEstimate);
    }

    public String toShortString() {
        boolean nonInteger = (trueNegatives != Math.floor(trueNegatives) || truePositives != Math.floor(truePositives) || falseNegatives != Math.floor(falseNegatives) || falsePositives != Math.floor(falsePositives));

        if (nonInteger) {
            return String.format("%% [TP=%.2f, FP=%.2f, TN=%.2f, FN=%.2f, A=%.2f, P=%.2f, R=%.2f, F1=%.2f]", truePositives, falsePositives, trueNegatives, falseNegatives, getAccuracy(), getPrecision(), getRecall(), getF1());
        } else {
            return String.format("%% [TP=%d, FP=%d, TN=%d, FN=%d, A=%.2f, P=%.2f, R=%.2f, F1=%.2f]", (int) truePositives, (int) falsePositives, (int) trueNegatives, (int) falseNegatives, getAccuracy(), getPrecision(), getRecall(), getF1());
        }
    }

    public String toLongString() {
        StringBuilder sb = new StringBuilder();

        double maxValue = Utils.max(trueNegatives, truePositives, falseNegatives, falsePositives);


        int columnWidth = 6;

        boolean nonInteger = (trueNegatives != Math.floor(trueNegatives) || truePositives != Math.floor(truePositives) || falseNegatives != Math.floor(falseNegatives) || falsePositives != Math.floor(falsePositives));

        if (maxValue > 0 && Double.isInfinite(maxValue) == false && Double.isNaN(maxValue) == false) {
            columnWidth = Math.max((int) Math.ceil(Math.log10(maxValue)) + 2 + (nonInteger ? 3 : 0), columnWidth);
        }

        sb.append(String.format("%% %" + ((21 + 3 * columnWidth) / 2) + "s\n", "Actual"));
        sb.append(String.format("%% %9s%" + columnWidth + "s%" + columnWidth + "s%" + columnWidth + "s\n", "", "Pos", "Neg", "Total"));
        sb.append(String.format("%% %9s%" + columnWidth + (nonInteger ? ".2" : ".0") + "f%" + columnWidth + (nonInteger ? ".2" : ".0") +
                "f%" + columnWidth + (nonInteger ? ".2" : ".0") + "f\n", "Model Pos", truePositives, falsePositives, truePositives + falsePositives));
        sb.append(String.format("%% %9s%" + columnWidth + (nonInteger ? ".2" : ".0") + "f%" + columnWidth + (nonInteger ? ".2" : ".0") +
                "f%" + columnWidth + (nonInteger ? ".2" : ".0") + "f\n", "Neg", falseNegatives, trueNegatives, falseNegatives + trueNegatives));
        sb.append(String.format("%% %9s%" + columnWidth + (nonInteger ? ".2" : ".0") + "f%" + columnWidth + (nonInteger ? ".2" : ".0") +
                "f\n", "Total", truePositives + falseNegatives, falsePositives + trueNegatives));

        if (falseNegativeMEstimate != 0 || truePositiveMEstimate != 0 || falsePositiveMEstimate != 0 || trueNegativeMEstimate != 0) {
            sb.append("\n");
            if (truePositiveMEstimate != 0) {
                sb.append(String.format("%% True  Pos mEst  = %.4f\n", truePositiveMEstimate));
            }
            if (falsePositiveMEstimate != 0) {
                sb.append(String.format("%% False Pos mEst  = %.4f\n", falsePositiveMEstimate));
            }
            if (trueNegativeMEstimate != 0) {
                sb.append(String.format("%% True  Neg mEst  = %.4f\n", trueNegativeMEstimate));
            }
            if (falseNegativeMEstimate != 0) {
                sb.append(String.format("%% False Neg mEst  = %.4f\n", falseNegativeMEstimate));
            }
        }

        sb.append("\n");

        sb.append(String.format("%% Accuracy  = %.4f\n", getAccuracy()));
        sb.append(String.format("%% Precision = %.4f\n", getPrecision()));
        sb.append(String.format("%% Recall    = %.4f\n", getRecall()));
        sb.append(String.format("%% F(1)      = %.4f",   getF1()));

        return sb.toString();
    }

    @Override
    public String toString() {
        return toLongString();
    }



    /**
     * Increment true positives by add
     * @param add
     */
    public void addToTruePositive(double add) {
    	truePositives += add;
    }
    
    /**
     * Increment false positives by add
     * @param add
     */
    public void addToFalsePositive(double add) {
    	falsePositives += add;
    }
    
    /**
     * Increment true negatives by add
     * @param add
     */
    public void addToTrueNegative(double add) {
    	trueNegatives += add;
    }
    
    /**
     * Increment false negatives by add
     * @param add
     */
    public void addToFalseNegative(double add) {
    	falseNegatives += add;
    }
    
    

    /**
     * @return the truePositives
     */
    public double getTruePositives() {
        return truePositives;
    }

    /**
     * @param truePositives the truePositives to set
     */
    public void setTruePositives(double truePositives) {
        this.truePositives = truePositives;
    }

    /**
     * @return the falsePositives
     */
    public double getFalsePositives() {
        return falsePositives;
    }

    /**
     * @param falsePositives the falsePositives to set
     */
    public void setFalsePositives(double falsePositives) {
        this.falsePositives = falsePositives;
    }

    /**
     * @return the trueNegatives
     */
    public double getTrueNegatives() {
        return trueNegatives;
    }

    /**
     * @param trueNegatives the trueNegatives to set
     */
    public void setTrueNegatives(double trueNegatives) {
        this.trueNegatives = trueNegatives;
    }

    /**
     * @return the falseNegatives
     */
    public double getFalseNegatives() {
        return falseNegatives;
    }

    /**
     * @param falseNegatives the falseNegatives to set
     */
    public void setFalseNegatives(double falseNegatives) {
        this.falseNegatives = falseNegatives;
    }

    public static void main(String[] args) {

        CoverageScore score;

        score = new CoverageScore(100, 200, 12, 30);
        System.out.println(score.toString() + "\n\n");

        score = new CoverageScore(100.23, 232200.11, 12.43, 30.22);
        System.out.println(score.toString() + "\n\n");

        score = new CoverageScore(1, 1, 1, 1, 1, 1);
        System.out.println(score.toString() + "\n\n");

        score = new CoverageScore(100, 0, 0, 0, 1, 1);
        System.out.println(score.toString() + "\n\n");
    }

    /**
     * @return the truePositiveMEstimate
     */
    public double getTruePositiveMEstimate() {
        return truePositiveMEstimate;
    }

    /**
     * @param truePositiveMEstimate the truePositiveMEstimate to set
     */
    public void setTruePositiveMEstimate(double truePositiveMEstimate) {
        this.truePositiveMEstimate = truePositiveMEstimate;
    }

    /**
     * @return the falsePositiveMEstimate
     */
    public double getFalsePositiveMEstimate() {
        return falsePositiveMEstimate;
    }

    /**
     * @param falsePositiveMEstimate the falsePositiveMEstimate to set
     */
    public void setFalsePositiveMEstimate(double falsePositiveMEstimate) {
        this.falsePositiveMEstimate = falsePositiveMEstimate;
    }

    /**
     * @return the falseNegativeMEstimate
     */
    public double getFalseNegativeMEstimate() {
        return falseNegativeMEstimate;
    }

    /**
     * @param falseNegativeMEstimate the falseNegativeMEstimate to set
     */
    public void setFalseNegativeMEstimate(double falseNegativeMEstimate) {
        this.falseNegativeMEstimate = falseNegativeMEstimate;
    }

    /**
     * @return the trueNegativeMEstimate
     */
    public double gettrueNegativeMEstimate() {
        return trueNegativeMEstimate;
    }

    /**
     * @param trueNegativeMEstimate the trueNegativeMEstimate to set
     */
    public void settrueNegativeMEstimate(double trueNegativeMEstimate) {
        this.trueNegativeMEstimate = trueNegativeMEstimate;
    }

    public static class AccuracyComparator implements Comparator<CoverageScore> {
        private int ascending = 1;

        public AccuracyComparator(boolean ascending) {
            this.ascending = ascending ? 1 : -1;
        }

        public int compare(CoverageScore o1, CoverageScore o2) {
            double v1 = o1.getAccuracy();
            double v2 = o2.getAccuracy();

            if ( Double.isNaN(v1) && Double.isNaN(v2) == false ) {
                return -1 * ascending;
            }
            else if ( Double.isNaN(v1) == false && Double.isNaN(v2) ) {
                return 1 * ascending;
            }
            if ( Double.isNaN(v1) && Double.isNaN(v2) ) {
                return 0;
            }
            else {
                return (int)Math.signum(v1-v2) * ascending;
            }
        }
    }

    public static class PrecisionComparator implements Comparator<CoverageScore> {
        private int ascending = 1;

        public PrecisionComparator(boolean ascending) {
            this.ascending = ascending ? 1 : -1;
        }

        public int compare(CoverageScore o1, CoverageScore o2) {
            double v1 = o1.getPrecision();
            double v2 = o2.getPrecision();

            if ( Double.isNaN(v1) && Double.isNaN(v2) == false ) {
                return -1 * ascending;
            }
            else if ( Double.isNaN(v1) == false && Double.isNaN(v2) ) {
                return 1 * ascending;
            }
            if ( Double.isNaN(v1) && Double.isNaN(v2) ) {
                return 0;
            }
            else {
                return (int)Math.signum(v1-v2) * ascending;
            }
        }
    }

    public static class RecallComparator implements Comparator<CoverageScore> {
        private int ascending = 1;

        public RecallComparator(boolean ascending) {
            this.ascending = ascending ? 1 : -1;
        }

        public int compare(CoverageScore o1, CoverageScore o2) {
            double v1 = o1.getRecall();
            double v2 = o2.getRecall();

            if ( Double.isNaN(v1) && Double.isNaN(v2) == false ) {
                return -1 * ascending;
            }
            else if ( Double.isNaN(v1) == false && Double.isNaN(v2) ) {
                return 1 * ascending;
            }
            if ( Double.isNaN(v1) && Double.isNaN(v2) ) {
                return 0;
            }
            else {
                return (int)Math.signum(v1-v2) * ascending;
            }
        }
    }

    public static class FBetaComparator implements Comparator<CoverageScore> {
        private int ascending = 1;
        private double beta;

        public FBetaComparator(double beta, boolean ascending) {
            this.beta = beta;
            this.ascending = ascending ? 1 : -1;
        }

        public int compare(CoverageScore o1, CoverageScore o2) {
            double v1 = o1.getFBeta(beta);
            double v2 = o2.getFBeta(beta);

            if ( Double.isNaN(v1) && Double.isNaN(v2) == false ) {
                return -1 * ascending;
            }
            else if ( Double.isNaN(v1) == false && Double.isNaN(v2) ) {
                return 1 * ascending;
            }
            if ( Double.isNaN(v1) && Double.isNaN(v2) ) {
                return 0;
            }
            else {
                return (int)Math.signum(v1-v2) * ascending;
            }
        }
    }

    public static class F1Comparator extends FBetaComparator {

        public F1Comparator(boolean ascending) {
            super(1, ascending);
        }
    }
}
