/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.RelevanceStrength;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.Utils.MapOfLists;

/**
 *
 * @author twalker
 */
public class RelevantFeatureInformation implements RelevantInformation, Cloneable {

    Example example;

    boolean relevanceFromPositiveExample = true;

    private PredicateNameAndArity predicateNameAndArity;

    private RelevanceStrength relevanceStrength;

    public RelevantFeatureInformation(Example example, PredicateNameAndArity predicateNameAndArity, RelevanceStrength relevanceStrength) {
        this.example = example;
        this.predicateNameAndArity = predicateNameAndArity;
        this.relevanceStrength = relevanceStrength;
    }

    @Override
    public String toString() {
        return toString("");
    }

    @Override
    public Example getExample() {
        return example;
    }

    public boolean isRelevanceFromPositiveExample() {
        return relevanceFromPositiveExample;
    }

    public void setRelevanceFromPositiveExample(boolean positive) {
        this.relevanceFromPositiveExample = positive;
    }

    @Override
    public boolean isEquivalentUptoVariableRenaming(RelevantInformation info) {

        boolean result = false;

        if (info instanceof RelevantFeatureInformation) {
            RelevantFeatureInformation that = (RelevantFeatureInformation) info;
            result = this.getPredicateNameAndArity().equals(that.getPredicateNameAndArity());
        }

        return result;
    }

    @Override
    public RelevantFeatureInformation getGeneralizeRelevantInformation() {
        return this;
    }

    /**
     * @return the relevanceStrength
     */
    public RelevanceStrength getRelevanceStrength() {
        return relevanceStrength;
    }

    /**
     * @param relevanceStrength the relevanceStrength to set
     */
    public void setRelevanceStrength(RelevanceStrength relevanceStrength) {
        this.relevanceStrength = relevanceStrength;
    }

    @Override
    public boolean prove(HornClauseContext context) {

        return relevanceFromPositiveExample;

    }

    /**
     * @return the predicateNameAndArity
     */
    public PredicateNameAndArity getPredicateNameAndArity() {
        return predicateNameAndArity;
    }

    /**
     * @param predicateNameAndArity the predicateNameAndArity to set
     */
    public void setPredicateNameAndArity(PredicateNameAndArity predicateNameAndArity) {
        this.predicateNameAndArity = predicateNameAndArity;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final RelevantFeatureInformation other = (RelevantFeatureInformation) obj;
        if (this.example != other.example && (this.example == null || !this.example.equals(other.example))) {
            return false;
        }
        if (this.relevanceFromPositiveExample != other.relevanceFromPositiveExample) {
            return false;
        }
        if (this.predicateNameAndArity != other.predicateNameAndArity && (this.predicateNameAndArity == null || !this.predicateNameAndArity.equals(other.predicateNameAndArity))) {
            return false;
        }
        if (this.relevanceStrength != other.relevanceStrength) {
            return false;
        }
        return true;
    }

    public boolean subsumes(RelevantInformation that) {
        return false;
    }

    @Override
    public int hashCode() {
        int hash = 7;
        hash = 67 * hash + (this.example != null ? this.example.hashCode() : 0);
        hash = 67 * hash + (this.relevanceFromPositiveExample ? 1 : 0);
        hash = 67 * hash + (this.predicateNameAndArity != null ? this.predicateNameAndArity.hashCode() : 0);
        hash = 67 * hash + (this.relevanceStrength != null ? this.relevanceStrength.hashCode() : 0);
        return hash;
    }

    public String toString(String prefix) {
        return prefix + example + " : " + getPredicateNameAndArity() + ", " + getRelevanceStrength();
    }

    public RelevantFeatureInformation copy() {
        try {
            return clone();
        } catch (CloneNotSupportedException ex) {
            return null;
        }
    }

    protected RelevantFeatureInformation clone() throws CloneNotSupportedException {
        RelevantFeatureInformation newRCI = (RelevantFeatureInformation) super.clone();
        return newRCI;
    }

    public boolean isValidAdvice(AdviceProcessor ap) {
        //Set<PredicateNameAndArity> usedPredicate =
        return true;
    }

    public RelevantFeatureInformation getSimplified(HornClauseContext context, MapOfLists<PredicateNameAndArity, Clause> supportClauses) {
        return this;
    }
}
