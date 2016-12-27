/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.visitors.ElementPositionVisitor.ElementPositionData;

/**
 *
 * @author twalker
 */
public interface ElementPositionListener<T extends ElementPositionData> {
    /** Informs the listener that the element position is being visited.
     *
     * @param s
     * @return True indicates the element position visitor should stop visiting.
     */
    public boolean visiting(Sentence s, T data);
    
    /** Informs the listener that the element position is being visited.
     *
     * @param s
     * @return True indicates the element position visitor should stop visiting.
     */
    public boolean visiting(Term t, T data);
}
