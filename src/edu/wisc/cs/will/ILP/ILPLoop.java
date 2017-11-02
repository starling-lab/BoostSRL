/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ILP;

/**
 *
 * @author twalker
 */
public interface ILPLoop {
    
     public ILPLoopState getState();

     public ILPLoopState setState();

     public void executeLoop(ILPLoopState state);

     public void setAdvice(ActiveAdvice advice);

     public void unsetAdvice();

     public String reportSearchStats();
}
