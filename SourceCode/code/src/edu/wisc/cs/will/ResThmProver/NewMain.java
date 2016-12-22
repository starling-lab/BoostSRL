/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.BindingList;

/**
 *
 * @author twalker
 */
public class NewMain {

    /**
     * @param args the command line arguments
     */
    public static void main(String[] args) {
        // TODO code application logic here
//        Utils.setVerbosity(Utils.Verbosity.High);
//        Utils.appendString(new CondorFile("/tmp/lockTest"), "Hello");


        UserHornClauseProver prover = new UserHornClauseProver();

        prover.assertDefiniteClause("likes(a,b).");
        prover.assertDefiniteClause("likes(a,c).");

        BindingList bl1 = prover.prove("likes(a,X).");
        System.out.println(bl1);
        BindingList bl2 = prover.prove("findAll(X, likes(a,X), L).");
        System.out.println(bl2);
        
    }

}
