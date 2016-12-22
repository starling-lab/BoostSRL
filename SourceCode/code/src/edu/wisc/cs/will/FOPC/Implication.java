/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC;

/**
 *
 * @author twalker
 */
public interface Implication {
    public Sentence getAntecedent() throws IllegalStateException ;
    public Sentence getConsequence() throws IllegalStateException;
}
