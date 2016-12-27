/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.RelevanceStrength;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.Utils.MapOfLists;

/**
 *
 * @author twalker
 */
public interface RelevantInformation {
    public Example getExample();
    public RelevanceStrength getRelevanceStrength();
    public boolean isRelevanceFromPositiveExample();
    public void setRelevanceFromPositiveExample(boolean positive);

    public boolean isEquivalentUptoVariableRenaming(RelevantInformation info);
    public abstract RelevantInformation getGeneralizeRelevantInformation();

    public boolean prove(HornClauseContext context);

    public String toString(String prefix);

    public RelevantInformation copy();

    public boolean isValidAdvice(AdviceProcessor ap);

    public boolean subsumes(RelevantInformation that);

    /** Returns a simplified version of the relevant information.
     *
     *
     * @param context
     * @param supportClauses
     * @return
     */
    RelevantInformation getSimplified(HornClauseContext context, MapOfLists<PredicateNameAndArity, Clause> supportClauses);
}
