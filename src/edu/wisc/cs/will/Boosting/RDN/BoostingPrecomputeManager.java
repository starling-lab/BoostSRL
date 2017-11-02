package edu.wisc.cs.will.Boosting.RDN;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.Reader;
import java.util.ArrayList;
import java.util.List;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.ILP.Precompute;
import edu.wisc.cs.will.ResThmProver.HornClauseProverChildrenGenerator;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CondorFileReader;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

public class BoostingPrecomputeManager {

		private WILLSetup setup;
		
		public BoostingPrecomputeManager(WILLSetup setup) {
			this.setup = setup;
		}
		
		
		public void recomputeFactsFor(PredicateName pName, boolean overwritePrecomputeFileIfExists) {
			Precompute precomputer = new Precompute();
			precomputer.alwaysRecreatePrecomputeFiles = true;
			FileParser parser = setup.getInnerLooper().getParser();
			for (int i = 0; i < parser.getNumberOfPrecomputeFiles(); i++) {
				List<Sentence> precomputeThese = parser.getSentencesToPrecompute(i); // Note that this is the set of ALL precompute's encountered during any file reading.
				precomputeThese = filterSentencesWithHead(precomputeThese, pName);
				if (Utils.getSizeSafely(precomputeThese) > 0) {
				//	 Utils.println("Have " + Utils.getSizeSafely(precomputeThese) + " sentences to precompute (i=" + i + ").");
					try {
						String precomputeFileNameToUse = "recomputed" + Utils.defaultFileExtensionWithPeriod;
						// The method below will check if the precompute file already exists, and if so, will simply return unless overwritten.
						precomputer.processPrecomputeSpecifications(overwritePrecomputeFileIfExists,
																    setup.getContext().getClausebase(),
																	precomputeThese, precomputeFileNameToUse);
						addToFacts(precomputeFileNameToUse, true); // Load the precomputed file.
					}
					catch (SearchInterrupted e) {
						Utils.reportStackTrace(e);
						Utils.error("Problem in recomputeFactsFor.");
					}
				}
			} //Utils.waitHere("after precomputing");
		}
	
		
		private List<Sentence> filterSentencesWithHead(List<Sentence> sentences,
									PredicateName pName) {
			List<Sentence> acceptedSentences = new ArrayList<Sentence>();
			for (Sentence sentence : sentences) {
				List<Clause> clauses = sentence.convertToClausalForm();
				if (clauses == null) {
					continue;
				}
				// Take each clause
				for (Clause clause : clauses) {
					if (!clause.isDefiniteClause()) { 
						Utils.error("Can only precompute Horn ('definite' actually) clauses.  You provided: '" + sentence + "'."); 
					}

					PredicateName headPredName = clause.posLiterals.get(0).predicateName;
					// This clause should be precomputed
					if(headPredName.equals(pName)) {
						acceptedSentences.add(sentence);
						break;
					}
				}
				
			}
			return acceptedSentences;
		}


		private List<Sentence> readFacts(Reader factsReader, String readerDirectory) {
			return readFacts(factsReader, readerDirectory, false);
		}
		private List<Sentence> readFacts(Reader factsReader, String readerDirectory, boolean okIfNoFacts) {
			if (factsReader == null && okIfNoFacts) { return null; }
			List<Sentence> sentences = null;
			try {
				sentences = setup.getInnerLooper().getParser().readFOPCreader(factsReader, readerDirectory); // TODO - should get the DIR of the facts file.
			}
			catch (IOException e) {
				Utils.reportStackTrace(e);
				Utils.error("Problem encountered reading  facts: " + factsReader);
			}
			if (okIfNoFacts && sentences == null) { return null; }
			if (sentences == null) { Utils.error("There are no facts in: " + factsReader); }
			return sentences;
		}

		private void addToFacts(String factsFileName, boolean okIfNoFacts) {
			try {
				File factsFile = Utils.ensureDirExists(factsFileName);
				addToFacts(new CondorFileReader(factsFile), factsFile.getParent(), okIfNoFacts);
			}
			catch (FileNotFoundException e) {
				Utils.reportStackTrace(e);
				Utils.error("Cannot find this file: " + factsFileName);
			}
		}
		private void addToFacts(Reader factsReader, String readerDirectory, boolean okIfNoFacts) {
			List<Sentence> moreFacts = readFacts(factsReader, readerDirectory, okIfNoFacts);
			if (moreFacts == null) { return; }
			//Utils.println("% Read an additional " + Utils.comma(moreFacts) + " facts from " + factsReader + ".");
			addFacts(moreFacts);
		}
		protected void addFacts(List<Sentence> newFacts) {
			setup.getContext().assertSentences(newFacts);
		}
		
	
}
