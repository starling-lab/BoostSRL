/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ILP;

import java.util.EventListener;

/**
 *
 * @author twalker
 */
public interface ILPSearchListener extends EventListener {

    public ILPSearchAction onionLayerStarting(TuneParametersForILP onion, ILPparameterSettings onionLayer);
    public void onionLayerFinished(TuneParametersForILP onion, ILPparameterSettings onionLayer);

    public ILPSearchAction crossValidationFoldStarting(ILPCrossValidationLoop cvLoop, int fold);
    public void crossValidationFoldFinished(ILPCrossValidationLoop cvLoop, int fold);

    public ILPSearchAction outerLoopStarting(ILPouterLoop outerLoop);
    public void outerLoopFinished(ILPouterLoop outerLoop);

    public ILPSearchAction innerLoopStarting(LearnOneClause learnOneClause);
    public void innerLoopFinished(LearnOneClause learnOneClause);

}
