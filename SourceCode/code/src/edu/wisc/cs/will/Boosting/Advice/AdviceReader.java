/**
 *  Reads advice file for rules that should form the initial model for RFGB
 *  Reads from advice.txt in the WILL folder
 */
package edu.wisc.cs.will.Boosting.Advice;

import java.util.ArrayList;
import java.util.List;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author tkhot
 *
 */
public class AdviceReader {
	
	FileParser parser  			=	null;
	HornClauseContext context 	=	null;
	HandleFOPCstrings handler	=	null;
	
	public AdviceReader(FileParser parser, HornClauseContext context, HandleFOPCstrings handler) {
		this.parser = parser;
		this.context = context;
		this.handler = handler;
	}
	
	
	/***
	 * Reads advice from the file. Modes and bk rules are added to the background knowledge.
	 * Horn clauses with weights are added to the advice. 
	 * @param file Read this file
	 * @param advice add to this advice.
	 */
	public void readAdviceFromFile(String file, List<Sentence> advice) {
		if (advice == null) {
			Utils.error("Initialize the list for advice");
		}
		if (!Utils.fileExists(file)) {
			Utils.waitHere("Advice file not present at: " + file);
		}
		Utils.println("File: " + file + " used for loading advice");
		List<Sentence> sentences = parser.readFOPCfile(file);
		List<Sentence> nonAdviceBk = new ArrayList<Sentence>();
		for (Sentence sentence : sentences) {
			if (sentence.getWeightOnSentence() != Sentence.defaultWeight) {
				Utils.println("Found advice: " + sentence);
				advice.add(createRegressionClause(sentence));
			} else {
				nonAdviceBk.add(sentence);
			}
		}
		
		// Assert all non-advice bk 
		context.assertSentences(nonAdviceBk);
	}


	private Sentence createRegressionClause(Sentence sentence) {
		double weight  = sentence.getWeightOnSentence();
		sentence.setWeightOnSentence();
		Clause clause = sentence.asClause();
		if (!clause.isDefiniteClause()) {
			Utils.error("Advice must be horn clause.");
		}
		Literal head = clause.posLiterals.get(0);
		head.addArgument(handler.getNumericConstant(weight));
		return clause;
	}
}
