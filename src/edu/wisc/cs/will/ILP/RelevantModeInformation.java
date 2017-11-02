/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.ConnectedSentence;
import edu.wisc.cs.will.FOPC.ConnectiveName;
import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.visitors.Inliner;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.RelevanceStrength;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.Utils.MapOfLists;
import java.util.ArrayList;
import java.util.List;

/**
 *
 * @author twalker
 */
public class RelevantModeInformation implements RelevantInformation, Cloneable {

    Example example;

    boolean relevanceFromPositiveExample;

    Literal mode;

    private RelevanceStrength relevanceStrength;

    public RelevantModeInformation(Example example, boolean relevanceFromPositiveExample, Literal mode, RelevanceStrength relevanceStrength) {
        this.example = example;
        this.relevanceFromPositiveExample = relevanceFromPositiveExample;
        this.mode = mode;
        this.relevanceStrength = relevanceStrength;
    }

    @Override
    public String toString(String prefix) {
        return prefix + example + " : " + mode + ", " + getRelevanceStrength();
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

        if (info instanceof RelevantModeInformation) {
            RelevantModeInformation that = (RelevantModeInformation) info;
            result = this.mode.equals(that.mode);
        }

        return result;
    }

    @Override
    public RelevantModeInformation getGeneralizeRelevantInformation() {
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

    public PredicateNameAndArity getPredicateNameAndArity() {
        return mode.getPredicateNameAndArity();
    }

    List<Term> getSignature() {
        List<Term> signature = new ArrayList<Term>();
        for (int i = 0; i < mode.getArity(); i++) { // TREVOR: this is probably ok since we only have 'flat' Examples, but there is (possibly) more robust code.  See how I did it for the negation-by-failure stuff.  JWS  TODO
            signature.add(mode.getStringHandler().getStringConstant("constant"));
        }
        return signature;
    }

    List<TypeSpec> getTypeSpecs() {
        return mode.getTypeSpecs();
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final RelevantModeInformation other = (RelevantModeInformation) obj;
        if (this.example != other.example && (this.example == null || !this.example.equals(other.example))) {
            return false;
        }
        if (this.relevanceFromPositiveExample != other.relevanceFromPositiveExample) {
            return false;
        }
        if (this.mode != other.mode && (this.mode == null || !this.mode.equals(other.mode))) {
            return false;
        }
        if (this.relevanceStrength != other.relevanceStrength) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        int hash = 7;
        hash = 43 * hash + (this.example != null ? this.example.hashCode() : 0);
        hash = 43 * hash + (this.relevanceFromPositiveExample ? 1 : 0);
        hash = 43 * hash + (this.mode != null ? this.mode.hashCode() : 0);
        hash = 43 * hash + (this.relevanceStrength != null ? this.relevanceStrength.hashCode() : 0);
        return hash;
    }


    public RelevantModeInformation copy() {
        try {
            return clone();
        } catch (CloneNotSupportedException ex) {
            return null;
        }
    }

    protected RelevantModeInformation clone() throws CloneNotSupportedException {
        RelevantModeInformation newRCI = (RelevantModeInformation) super.clone();
        return newRCI;
    }

    public boolean isValidAdvice(AdviceProcessor ap) {
        //Set<PredicateNameAndArity> usedPredicate =
        return true;
    }

    public ConnectedSentence getSentence(HornClauseContext context) {
        List<DefiniteClause> clauses = context.getClausebase().getAssertions(getPredicateNameAndArity());

        ConnectedSentence result = null;

        if ( clauses != null && clauses.isEmpty() == false) {
            if ( clauses.size() == 1) {
                Clause theClause = clauses.get(0).getDefiniteClauseAsClause();
                result = theClause.asConnectedSentence();
            }
            else {

                Sentence s = null;

                BindingList bl = new BindingList();

                Literal firstHead = null;

                for (DefiniteClause definiteClause : clauses) {
                    Clause aClause = definiteClause.getDefiniteClauseAsClause();
                    Literal head = aClause.getDefiniteClauseHead();

                    if ( firstHead == null) {
                        firstHead = head;
                        s = context.getStringHandler().getClause(null, aClause.getNegativeLiterals());
                    }
                    else {
                        // This probably won't work...but I have no examples of when it
                        // will fail, so whatever...
                        bl = Unifier.UNIFIER.unify(firstHead, head, bl);
                        aClause = aClause.applyTheta(bl);
                        s = context.getStringHandler().getConnectedSentence(s, ConnectiveName.OR, context.getStringHandler().getClause(null, aClause.getNegativeLiterals()));
                    }
                }

                result = context.getStringHandler().getConnectedSentence(s, ConnectiveName.IMPLIES, firstHead);
            }

        }

        return result;
    }

    public RelevantModeInformation getSimplified(HornClauseContext context, MapOfLists<PredicateNameAndArity, Clause> supportClauses) {
        return this;
    }

    public boolean subsumes(RelevantInformation that) {
        return false;
    }


    
    
}
