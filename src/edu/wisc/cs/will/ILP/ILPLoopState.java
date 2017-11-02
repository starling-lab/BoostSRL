/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Theory;
import java.util.List;

/**
 *
 * @author twalker
 */
public interface ILPLoopState {

    public List<Example> getPositiveExamples();

    public List<Example> getNegativeExamples();

    public void setMaximumTimeInSeconds(long seconds);

    public Theory getLearnedTheory();

    public CoverageScore getCoverageScore();

    public ILPLoopState copy();
}
