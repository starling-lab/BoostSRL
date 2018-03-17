/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.ResThmProver.DefaultHornClauseContext;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import java.util.List;

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

        HornClauseContext context = new DefaultHornClauseContext();

        FileParser parser = context.getFileParser();

        parser.parsingWithNamedArguments = true;
        parser.stringHandler.setStringsAreCaseSensitive(true);
        parser.stringHandler.cleanFunctionAndPredicateNames = false;


        List<Sentence> sentences = parser.readFOPCstream("Utter(name=Utter_1892, addressee=Student(name=theStudent), utterance=RelevantRelationship(arg1=SameAs(arg1=theResult, arg2=8.333333333333334E_4)));");

        for (Sentence sentence : sentences) {
            System.out.println(sentence);
        }
    }

}
