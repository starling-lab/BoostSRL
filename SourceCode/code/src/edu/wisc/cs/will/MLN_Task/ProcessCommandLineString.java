/**
 * 
 */
package edu.wisc.cs.will.MLN_Task;

import java.io.IOException;
import java.io.StringReader;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Theory;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.Utils.Utils;

/**
 
 Commands

    -dir directoryName // Use this as a prefix to all file names.  Should end with a slash.
    -dribble           // Create a 'dribble' file of the output printed to the screen.
    -it                // Use interactive mode.
    
    -cwa    true or false  // Use the closed-world assumption.
    -noCWA  pNameArityList // NEVER  apply CWA on these predicate names and arities (e.g., p/2, q/3).
    -yesCWA pNameArityList // ALWAYS apply CWA on these predicate names and arities (e.g., p/2, q/3).

    -theory fileName // File of clauses.  Can also contain modes, ranges, etc.
    -modes  fileName // File of modes, ranges, etc. (but not clauses).

    -qf fileName     // The file of query ground literals.
    -hf fileName     // The file of hidden ground literals.
    -pf fileName     // The file of positive ground literals.
    -nf fileName     // The file of negative ground literals.

    -qs list         // The comma-separated list of query ground literals.
    -hs list         // The comma-separated list of hidden ground literals.
    -ps list         // The comma-separated list of positive ground literals.
    -ns list         // The comma-separated list of negative ground literals.

    -q  pNameArityList // The comma-separated list of query  predicate names and arities (e.g., p/2, q/3).
    -h  pNameArityList // The comma-separated list of hidden predicate names and arities (e.g., p/2, q/3).
    -p  pNameArityList // The comma-separated list of pos-evidence predicate names and arities (e.g., p/2, q/3).
    -n  pNameArityList // The comma-separated list of pos-evidence predicate names and arities (e.g., p/2, q/3).

   // These are for INFERENCE.
    -bf              // Use brute-force inference.
    -gibbs           // Use Gibbs sampling for inference.
    -ms              // Use the MC-SAT algorithm for inference.
    -temp double     // Temperature for simulated annealing.
    -prob double     // Probability for Walk SAT.

    -maxSteps                int // For MCMC.
    -maxBurninSteps          int // For MCMC.
    -maxNumBlockCombinations int // ??
    -numStepsAfterSoln       int // For Sample SAT.
    -numSATstarts            int // For SAT.
    -numSATstepsPerStart     int // For SAT.
    
   // These are for WEIGHT LEARNING.
    -vp              // Use voted perceptron.
    -pscg            // Use conjugate gradient.
    -perGcOn         // TURN ON  the per-grounded clause learning rates.
    -perGcOff        // TURN OFF the per-grounded clause learning rates
    -printgc         // Set print1normGradient_discrimLearning = true.

    -numSteps        // Number of learning steps.
    -ciw             // Method for initializing weights of clauses.  One of: {ALL_ZERO, RANDOM, LOG_COUNTS_RATIO}
    -toe             // Type of estimation for Voted Perceptron.  One of: {SAT, MCMC, PSEUDO_LIKELIHOOD}
   
    -lambda          // The lambda in conjugate gradient.
    -eta             // The eta in conjugate gradient.
    -VPnumSATstarts  // These four have self-documenting names.
    -VPnumSATstepsPerStart
    -VPnumMCMCstepsPerIter
    -PSCGnumMCMCstepsPerIter
    
   // These are for STRUCTURE LEARNING.
   

 * @author shavlik
 *
 */
public class ProcessCommandLineString {
	private static final int debugLevel  = 0;
	
	public  static final int BRUTE_FORCE = 0;
	public  static final int GIBBS       = 1;
	public  static final int MC_SAT      = 2;
	public  static final int DEFAULT_INFERENCE_ALGO = MC_SAT;	
	
	private HandleFOPCstrings stringHandler;
	private FileParser        parser;
	private MLN_Task          task;
	
	public int     inferenceAlgo = DEFAULT_INFERENCE_ALGO;
	public boolean useCWA        = true;
	public boolean interactive   = false;

	// For inference.
	public int     burninSteps           = Integer.MIN_VALUE;
	public int     maxMCMCSteps          = Integer.MIN_VALUE;	
	public int     numberMCMCtrials      = Integer.MIN_VALUE;
	public int     numbStarts_SAT        = Integer.MIN_VALUE;
	public int     numbStepsPerStart_SAT = Integer.MIN_VALUE;
	public int     maxNumStepsAfterSoln_sampleSAT = Integer.MIN_VALUE;
	public double  temperatureSA         = Double.NaN;
	public double  probOfWalkSAT         = Double.NaN;
	
	// For weight learning.
	public int    numLearningSteps                         = Integer.MIN_VALUE;
	public int    numStepsPerStart_MCSAT                   = Integer.MIN_VALUE;
	public int    numStarts_votedPerceptron                = Integer.MIN_VALUE;
	public int    numStepsPerStart_votedPerceptron         = Integer.MIN_VALUE;
	public int    numMCMCstepsPerIteration_votedPerceptron = Integer.MIN_VALUE;
	public int    numMCMCstepsPerIteration_PSCG            = Integer.MIN_VALUE;
	public int    numStarts_MCSAT                          = Integer.MIN_VALUE;
	public double lambda_PSCG                              = Double.NaN;
	public double eta_votedPerceptron                      = Double.NaN;
	public String learningAlgo                             = null;
	public String typeOfEstimation_votedPerceptron         = null;
	public String typeOfInitialWeights_discrimLearning     = null;
	public String useDifferentEtas_votedPerceptron         = null;
	public String print1normGradient_discrimLearning       = null;
	
	public int     maxNumCombinations_block = Block.maxNumCombinations_default;  // TODO - figure this out and pass this one around


	/**
	 * 
	 */
	public ProcessCommandLineString(HandleFOPCstrings stringHandler, FileParser parser, MLN_Task task) {
		this.stringHandler = stringHandler;
		this.parser        = parser;
		this.task          = task;
	}


	public void processOptions(String[] options) {
		int index = 0;
		Set<PredNameArityPair> queryPredNames    = null;
		Set<PredNameArityPair> hiddenPredNames   = null;
		Set<PredNameArityPair> posEvidPredName   = null;
		Set<PredNameArityPair> negEvidPredName   = null;
		Set<PredNameArityPair> yesCWA_PredNames  = null;
		Set<PredNameArityPair>  noCWA_PredNames  = null;
		Set<Literal>           queryLiterals     = null;
		Set<Literal>           hiddenLiterals    = null;
		Set<Literal>           posEvidence       = null;
		Set<Literal>           negEvidence       = null;
		Set<GroundLiteral>     posQueries        = null; // These are the positive and negative (if any) labels for training.
		Set<GroundLiteral>     negQueries        = null;
		String                 directory         = "";
		boolean                createDribbleFile = false;
		while (index < options.length) {
			if (index == options.length - 1) {
				if (!options[index].equalsIgnoreCase("-dribble") && !options[index].equalsIgnoreCase("-bf")   && !options[index].equalsIgnoreCase("-gibbs")   && !options[index].equalsIgnoreCase("-ms")       && !options[index].equalsIgnoreCase("-it") &&
					!options[index].equalsIgnoreCase("-vp")      && !options[index].equalsIgnoreCase("-pscg") && !options[index].equalsIgnoreCase("-perGcOn") && !options[index].equalsIgnoreCase("-perGcOff") && !options[index].equalsIgnoreCase("-printgc"))				
					Utils.error("No value was entered for " + options[index]);
			}
			if (options[index].equalsIgnoreCase("-dir")) {
				index++;
				directory = options[index];
				if (createDribbleFile) { Utils.createDribbleFileInDirectory(directory); createDribbleFile = false; }				
			} else if (options[index].equalsIgnoreCase("-dribble")) {
				index++;
				if (directory.equals("")) { createDribbleFile = true; } // Create at end if no directory yet.
				else { Utils.createDribbleFileInDirectory(directory); } // Create as soon as possible, so that all output can be grabbed.
				//Utils.waitHere("Starting a dribble!  directory = " + directory);
			} else if (options[index].equalsIgnoreCase("-theory")) { // The input mln file.  Clauses should be in here.  OK to also add modes and ranges.
				index++;
				List<Sentence> sentences = parser.readFOPCfile(directory + options[index], false);
				Theory theory = new Theory(stringHandler, sentences);
				if (theory == null || Utils.getSizeSafely(theory.getClauses()) < 1) { Utils.error("Read ZERO clauses from " + directory + options[index]); }
				task.setAllClauses(theory.getClauses());				
				if (debugLevel > 2) for (Clause clause : theory.getClauses()) { Utils.println("%  Read this clause: '" + clause + "' from " + directory + options[index]); }
				if (debugLevel > 0) { Utils.println("%  Read " + Utils.comma(theory.getClauses()) + " clauses from " + directory + options[index]); }
			} else if (options[index].equalsIgnoreCase("-modes")) { // It is fine if background information (e.g., modes and ranges) is in a separate file.
				index++;
				List<Sentence> sentences = parser.readFOPCfile(directory + options[index], false);
				Theory theory = new Theory(stringHandler, sentences);
				if (theory != null && Utils.getSizeSafely(theory.getClauses()) > 0) { Utils.error("Should NOT read any clauses from " + directory + options[index]); }
			} else if (options[index].equalsIgnoreCase("-pf")) { // The file of positive ground literals.
				index++;
				List<Sentence> sentences = parser.readFOPCfile(directory + options[index], false);
				Theory theory = new Theory(stringHandler, sentences);
				List<Clause> clauses = theory.getClauses();
				if (Utils.getSizeSafely(clauses) < 1) { Utils.error("Read no clauses from " + directory + options[index]); }
				if (posEvidPredName != null)          { Utils.error("Already have posEvidPredName from '-e' and have encountered '-dp'"); }
				if (posEvidence     != null)          { Utils.error("Already have posEvidence and have encountered another '-dp'"); }
				posEvidence = new HashSet<Literal>(4);
				for (Clause clause : clauses) {
					if (Utils.getSizeSafely(clause.posLiterals) > 1) { Utils.error("Too many positive literals in this clause: " + clause); }
					if (Utils.getSizeSafely(clause.posLiterals) < 1) { Utils.error( "Too few positive literals in this clause: " + clause); }
					if (Utils.getSizeSafely(clause.negLiterals) > 0) { Utils.error( "Should not have any NEGATIVE literals in this clause: " + clause); }
					Literal lit = clause.posLiterals.get(0);
					posEvidence.add(lit);
				}
				Utils.println("% Have read " + Utils.comma(posEvidence.size()) + " pos-evidence literals from " + Utils.comma(clauses.size()) + " clauses.");
			} else if (options[index].equalsIgnoreCase("-nf")) { // The file of negative ground literals.
				index++;
				List<Sentence> sentences = parser.readFOPCfile(directory + options[index], false);
				Theory theory = new Theory(stringHandler, sentences);
				List<Clause> clauses = theory.getClauses();
				if (Utils.getSizeSafely(clauses) < 1) { Utils.error("Read no clauses from " + directory + options[index]); }
				if (posEvidPredName != null)          { Utils.error("Already have posEvidPredName from '-e' and have encountered '-dp'"); }
				if (negEvidence     != null)          { Utils.error("Already have negEvidence and have encountered another '-dn'"); }
				negEvidence = new HashSet<Literal>(4);
				for (Clause clause : clauses) {
					if (Utils.getSizeSafely(clause.posLiterals) > 1) { Utils.error("Too many positive literals in this clause: " + clause); }
					if (Utils.getSizeSafely(clause.posLiterals) < 1) { Utils.error( "Too few positive literals in this clause: " + clause); }
					if (Utils.getSizeSafely(clause.negLiterals) > 0) { Utils.error( "Should not have any NEGATIVE literals in this clause: " + clause); }
					Literal lit = clause.negLiterals.get(0);
					negEvidence.add(lit);
				}
				Utils.println("% Have read " + Utils.comma(negEvidence.size()) + " neg-evidence literals from " + Utils.comma(clauses.size()) + " clauses.");
			}
			else if (options[index].equalsIgnoreCase("-q")) { // The list of queryPredNames.  Note: user must also supply arities, e.g. p/2
				index++;
				String[] tokens = options[index].split(",");
				if (queryLiterals  != null) { Utils.error("Already have queryLiterals from '-qf' or '-qs' and have encountered '-q'"); }
				if (queryPredNames != null) { Utils.error("Already have queryPredNames and have encountered another '-q'"); }
				queryPredNames = new HashSet<PredNameArityPair>(4);
				for (int i = 0; i < tokens.length; i++) {
					String[] items = tokens[i].split("/");
					queryPredNames.add(new PredNameArityPair(stringHandler.getPredicateName(items[0]), Integer.valueOf(items[1])));
				}
			}
			else if (options[index].equalsIgnoreCase("-h")) { // The list of hiddenPredNames.  Note: user must also supply arities, e.g. p/2
				index++;
				String[] tokens = options[index].split(",");
				if (hiddenLiterals  != null) { Utils.error("Already have hiddenLiterals from '-hf' or '-hs' and have encountered '-h'"); }
				if (hiddenPredNames != null) { Utils.error("Already have hiddenPredNames and have encountered another '-h'"); }
				hiddenPredNames = new HashSet<PredNameArityPair>(4);
				for (int i = 0; i < tokens.length; i++) {
					String[] items = tokens[i].split("/");
					hiddenPredNames.add(new PredNameArityPair(stringHandler.getPredicateName(items[0]), Integer.valueOf(items[1])));
				}
			} else if (options[index].equalsIgnoreCase("-p")) { // The list of (positive) EvidPredName.  Note: user must also supply arities, e.g. p/2
				index++;
				String[] tokens = options[index].split(",");
				if (posEvidence     != null) { Utils.error("Already have posEvidence from '-pf' and have encountered '-p'"); }
				if (posEvidPredName != null) { Utils.error("Already have posEvidPredName and have encountered another '-p'"); }
				posEvidPredName = new HashSet<PredNameArityPair>(4);
				for (int i = 0; i < tokens.length; i++) {
					String[] items = tokens[i].split("/");
					posEvidPredName.add(new PredNameArityPair(stringHandler.getPredicateName(items[0]), Integer.valueOf(items[1])));
				}
			} else if (options[index].equalsIgnoreCase("-e")) { // The list of (negative) EvidPredName.  Note: user must also supply arities, e.g. p/2
				index++;
				String[] tokens = options[index].split(",");
				if (negEvidence     != null) { Utils.error("Already have negEvidence from '-nf' and have encountered '-n'"); }
				if (negEvidPredName != null) { Utils.error("Already have negativeEvidPredName and have encountered another '-n'"); }
				negEvidPredName = new HashSet<PredNameArityPair>(4);
				for (int i = 0; i < tokens.length; i++) {
					String[] items = tokens[i].split("/");
					negEvidPredName.add(new PredNameArityPair(stringHandler.getPredicateName(items[0]), Integer.valueOf(items[1])));
				}
			} else if (options[index].equalsIgnoreCase("-qf")) { // A file containing query ground literals.
				index++;
				List<Sentence> sentences = parser.readFOPCfile(directory + options[index], false);
				Theory theory = new Theory(stringHandler, sentences);
				if (queryPredNames != null) { Utils.error("Already have queryPredNames from '-q' and have encountered '-qf'"); }
				if (queryLiterals  != null) { Utils.error("Already have queryLiterals and have encountered '-qf'"); }
				queryLiterals  = new HashSet<Literal>(4);
				for (Clause clause : theory.getClauses()) {	
					Literal lit = clause.posLiterals.get(0);			
					queryLiterals.add(lit);
				}
			} else if (options[index].equalsIgnoreCase("-qs")) { // Command-line way of giving specific query literals.
				index++;
				String queryStr = formatLine(options[index]);				
				List<Sentence> sentences = null;
				if (queryPredNames != null) { Utils.error("Already have queryPredNames from '-q' and have encountered '-qs'"); }
				if (queryLiterals  != null) { Utils.error("Already have queryLiterals and have encountered '-qs'"); }
				try {
					sentences = parser.readFOPCreader(new StringReader(queryStr), null); // Fine no directory here since processing a string.
				} catch (IOException e) { Utils.error("Couldn't form string reader of: " + options[index]);}
				Theory theory = new Theory(stringHandler, sentences);
				for (Clause clause : theory.getClauses()) {	
					Literal lit = clause.posLiterals.get(0);		
					queryLiterals.add(lit);
				}
			} else if (options[index].equalsIgnoreCase("-hf")) { // A file containing hidden ground literals.
				index++;
				List<Sentence> sentences = parser.readFOPCfile(directory + options[index], false);
				Theory theory = new Theory(stringHandler, sentences);
				if (hiddenPredNames != null) { Utils.error("Already have hiddenPredNames from '-h' and have encountered '-hf'"); }
				if (hiddenLiterals  != null) { Utils.error("Already have hiddenLiterals and have encountered '-hf'"); }
				hiddenLiterals  = new HashSet<Literal>(4);
				for (Clause clause : theory.getClauses()) {	
					Literal lit = clause.posLiterals.get(0);			
					hiddenLiterals.add(lit);
				}
			} else if (options[index].equalsIgnoreCase("-hs")) { // Command-line way of giving specific hidden literals.
				index++;
				String queryStr = formatLine(options[index]);				
				List<Sentence> sentences = null;
				if (hiddenPredNames != null) { Utils.error("Already have hiddenPredNames from '-h' and have encountered '-hs'"); }
				if (hiddenLiterals  != null) { Utils.error("Already have hiddenLiterals and have encountered '-hs'"); }
				try {
					sentences = parser.readFOPCreader(new StringReader(queryStr), null); // Fine no directory here since processing a string.
				} catch (IOException e) { Utils.error("Couldn't form string reader of: " + options[index]);}
				Theory theory = new Theory(stringHandler, sentences);
				for (Clause clause : theory.getClauses()) {	
					Literal lit = clause.posLiterals.get(0);		
					hiddenLiterals.add(lit);
				}
			} else if (options[index].equalsIgnoreCase("-pos")) { // The queries that are TRUE.
				index++;
				List<Sentence> sentences = parser.readFOPCfile(directory + options[index], false);
				Theory theory = new Theory(stringHandler, sentences);
				List<Clause> clauses = theory.getClauses();
				if (Utils.getSizeSafely(clauses) < 1) { Utils.error("Read no clauses from " + directory + options[index]); }
				if (posQueries != null) { Utils.error("Already have posQueries and have encountered another '-pos'"); }
				posQueries = new HashSet<GroundLiteral>(4);
				for (Clause clause : clauses) {
					if (Utils.getSizeSafely(clause.posLiterals) > 1) { Utils.error("Too many positive literals in this clause: " + clause); }
					if (Utils.getSizeSafely(clause.posLiterals) < 1) { Utils.error("Too few positive literals in this clause: "  + clause); }
					if (Utils.getSizeSafely(clause.negLiterals) > 0) { Utils.error("Should not have any NEGATIVE literals in this clause: " + clause); }
					Literal lit = clause.posLiterals.get(0);
					posQueries.add(new GroundLiteral(lit));
				}
				Utils.println("% Have read " + Utils.comma(posQueries.size()) + " pos-query literals from " + Utils.comma(clauses.size()) + " clauses.");
			} else if (options[index].equalsIgnoreCase("-neg")) { // The queries that are FALSE.
				index++;
				List<Sentence> sentences = parser.readFOPCfile(directory + options[index], false);
				Theory theory = new Theory(stringHandler, sentences);
				List<Clause> clauses = theory.getClauses();
				if (Utils.getSizeSafely(clauses) < 1) { Utils.error("Read no clauses from " + directory + options[index]); }
				if (negQueries != null) { Utils.error("Already have negQueries and have encountered another '-neg'"); }
				negQueries = new HashSet<GroundLiteral>(4);
				for (Clause clause : clauses) {
					if (Utils.getSizeSafely(clause.posLiterals) > 1) { Utils.error("Too many positive literals in this clause: " + clause); }
					if (Utils.getSizeSafely(clause.posLiterals) < 1) { Utils.error("Too few positive literals in this clause: "  + clause); }
					if (Utils.getSizeSafely(clause.negLiterals) > 0) { Utils.error("Should not have any NEGATIVE literals in this clause: " + clause); }
					Literal lit = clause.posLiterals.get(0);
					negQueries.add(new GroundLiteral(lit));
				}
				Utils.println("% Have read " + Utils.comma(negQueries.size()) + " neg-query literals from " + Utils.comma(clauses.size()) + " clauses.");
				
			} else if (options[index].equalsIgnoreCase("-maxSteps")) {
				index++;
				try {
					maxMCMCSteps = Integer.parseInt(options[index]);
				} catch (NumberFormatException e) {
					Utils.error("Value of maxSteps \"" + options[index] + "\" is not an integer.");
				}				
			} else if (options[index].equalsIgnoreCase("-maxBurninSteps")) {
				index++;
				try {
					burninSteps = Integer.parseInt(options[index]);
				} catch (NumberFormatException e) {
					Utils.error("Value of maxBurninSteps \"" + options[index] + "\" is not an integer.");
				}
			} else if (options[index].equalsIgnoreCase("-maxNumBlockCombinations")) {
				index++;
				int maxNumCombinations = Block.maxNumCombinations_default;
				try {
					maxNumCombinations = Integer.parseInt(options[index]);
				} catch (NumberFormatException e) {
					Utils.error("Value of maxNumBlockCombinations \"" + options[index] + "\" is not an integer.");
				}
				maxNumCombinations_block = maxNumCombinations;
				Utils.waitHere("Not yet fully implemented!");
			} else if (options[index].equalsIgnoreCase("-it")) {
				interactive = true;
			} else if (options[index].equalsIgnoreCase("-bf") || options[index].equalsIgnoreCase("-brute") || options[index].equalsIgnoreCase("-bruteForce") || options[index].equalsIgnoreCase("-exact")) {
				inferenceAlgo = BRUTE_FORCE;
			} else if (options[index].equalsIgnoreCase("-gibbs")) {
				inferenceAlgo = GIBBS;
			} else if (options[index].equalsIgnoreCase("-ms") || options[index].equalsIgnoreCase("-mc")    || options[index].equalsIgnoreCase("-mcSat")) {
				inferenceAlgo = MC_SAT;
			} else if (options[index].equalsIgnoreCase("-temp")) {
				index++;
				try {
					temperatureSA = Double.parseDouble(options[index]);
				} catch (NumberFormatException e) {
					Utils.error("Value of temp \"" + options[index] + "\" is not an integer.");
				}
			} else if (options[index].equalsIgnoreCase("-prob")) {
				index++;				
				try {
					probOfWalkSAT = Math.max(0.0, Math.min(1.0, Double.parseDouble(options[index])));		
				} catch (NumberFormatException e) {
					Utils.error("Value of p \"" + options[index] + "\" is not an double.");
				}		
			} else if (options[index].equalsIgnoreCase("-numStepsAfterSoln")) {
				index++;
				try {
				maxNumStepsAfterSoln_sampleSAT = Integer.parseInt(options[index]);
				} catch (NumberFormatException e) {
					Utils.error("Value of numStepsAfterSoln \"" + options[index] + "\" is not an integer.");
				}
			} else if (options[index].equalsIgnoreCase("-numSATstarts")) {
				index++;
				try {
					numbStarts_SAT        = Integer.parseInt(options[index]);
				} catch (NumberFormatException e) {
					Utils.error("Value of numSATstarts \"" + options[index] + "\" is not an integer.");
				}
			} else if (options[index].equalsIgnoreCase("-numSATstepsPerStart")) {
				index++;
				try {
					numbStepsPerStart_SAT = Integer.parseInt(options[index]);
				} catch (NumberFormatException e) {
					Utils.error("Value of numSATstepsPerStart \"" + options[index] + "\" is not an integer.");
				}
			} else if (options[index].equalsIgnoreCase("-numSteps")) {
				index++;
				try {
					numLearningSteps = Integer.parseInt(options[index]);
				} catch (NumberFormatException e) {
					Utils.error("Value of numLearningSteps \"" + options[index] + "\" is not an integer.");
				}
			} else if (options[index].equalsIgnoreCase("-cwa")) {	// Closed-world assumption.
				index++;
				String cwa = options[index];
				cwa.toLowerCase();
				if      (cwa.equalsIgnoreCase("true"))  { useCWA = true;  }
				else if (cwa.equalsIgnoreCase("false")) { useCWA = false; }
				else Utils.error("Invalid closed world-assumption value: " + options[index]);
			} else if (options[index].equalsIgnoreCase("-noCWA")) {
				index++;
				String[] tokens = options[index].split(",");
				if (noCWA_PredNames == null) { noCWA_PredNames = new HashSet<PredNameArityPair>(4); } // OK to call multiple times.
				for (int i = 0; i < tokens.length; i++) {
					String[] items = tokens[i].split("/");
					noCWA_PredNames.add(new PredNameArityPair(stringHandler.getPredicateName(items[0]), Integer.valueOf(items[1])));
				}
			} else if (options[index].equalsIgnoreCase("-yesCWA")) {
				index++;
				String[] tokens = options[index].split(",");
				if (yesCWA_PredNames == null) { yesCWA_PredNames = new HashSet<PredNameArityPair>(4); } // OK to call multiple times.
				for (int i = 0; i < tokens.length; i++) {
					String[] items = tokens[i].split("/");
					yesCWA_PredNames.add(new PredNameArityPair(stringHandler.getPredicateName(items[0]), Integer.valueOf(items[1])));
				}
			} else if (options[index].equalsIgnoreCase("-ciw")) { // Clause initial weights.
				index++;
				String assignInitWeights = options[index];
				if      (assignInitWeights.equalsIgnoreCase("zero"))   { typeOfInitialWeights_discrimLearning = assignInitWeights; }
				else if (assignInitWeights.equalsIgnoreCase("random")) { typeOfInitialWeights_discrimLearning = assignInitWeights; }
				else if (assignInitWeights.equalsIgnoreCase("lcr"))    { typeOfInitialWeights_discrimLearning = assignInitWeights; }
				else { Utils.error("Unknown -ciw value: " + assignInitWeights); }
			} else if (options[index].equalsIgnoreCase("-toe")) {
				index++;
				String typeOfEst = options[index];
				if      (typeOfEst.equalsIgnoreCase("sat"))  { typeOfEstimation_votedPerceptron = typeOfEst; }
				else if (typeOfEst.equalsIgnoreCase("mcmc")) { typeOfEstimation_votedPerceptron = typeOfEst; }
				else if (typeOfEst.equalsIgnoreCase("pl"))   { typeOfEstimation_votedPerceptron = typeOfEst; }
				else { Utils.error("Unknown -toe value: " + typeOfEst); }
			} else if (options[index].equalsIgnoreCase("-perGcOn"))  { // TURN ON  the per-ground clause learning rates.
				useDifferentEtas_votedPerceptron = "true";				
			} else if (options[index].equalsIgnoreCase("-perGcOff")) { // TURN OFF the per-ground clause learning rates (provide both, in case default value changes).
				useDifferentEtas_votedPerceptron = "false";				
			} else if (options[index].equalsIgnoreCase("-vp")) {
				learningAlgo = "VP";
			} else if (options[index].equalsIgnoreCase("-pscg")) {
				learningAlgo = "PSCG";
			} else if (options[index].equalsIgnoreCase("-printgc")) {
				print1normGradient_discrimLearning = "true";
			} else if (options[index].equalsIgnoreCase("-numSATstarts")) {
				index++;
				try {
					numStarts_MCSAT = Integer.parseInt(options[index]);
				} catch (NumberFormatException e) {
					Utils.error("Value of numSATstarts \"" + options[index] + "\" is not an integer.");
				}
			} else if (options[index].equalsIgnoreCase("-numSATstepsPerStart")) {
				index++;
				try {
					numStepsPerStart_MCSAT = Integer.parseInt(options[index]);
				} catch (NumberFormatException e) {
					Utils.error("Value of numSATstepsPerStart \"" + options[index] + "\" is not an integer.");
				}
			} else if (options[index].equalsIgnoreCase("-VPnumSATstarts")) {
				index++;
				try {
					numStarts_votedPerceptron = Integer.parseInt(options[index]);
				} catch (NumberFormatException e) {
					Utils.error("Value of VPnumSATstarts \"" + options[index] + "\" is not an integer.");
				}
			} else if (options[index].equalsIgnoreCase("-VPnumSATstepsPerStart")) {
				index++;
				try {
					numStepsPerStart_votedPerceptron = Integer.parseInt(options[index]);
				} catch (NumberFormatException e) {
					Utils.error("Value of VPnumSATstepsPerStart \"" + options[index] + "\" is not an integer.");
				}
			} else if (options[index].equalsIgnoreCase("-VPnumMCMCstepsPerIter")) {
				index++;
				try {
					numMCMCstepsPerIteration_votedPerceptron = Integer.parseInt(options[index]);
				} catch (NumberFormatException e) {
					Utils.error("Value of VPnumMCMCstepsPerIter \"" + options[index] + "\" is not an integer.");
				}
			} else if (options[index].equalsIgnoreCase("-PSCGnumMCMCstepsPerIter")) {
				index++;
				try {
					numMCMCstepsPerIteration_PSCG = Integer.parseInt(options[index]);
				} catch (NumberFormatException e) {
					Utils.error("Value of PSCGnumMCMCstepsPerIter \"" + options[index] + "\" is not an integer.");
				}
			} else if (options[index].equalsIgnoreCase("-lambda")) {
				index++;
				try {
					lambda_PSCG = Double.parseDouble(options[index]);
				} catch (NumberFormatException e) {
					Utils.error("Value of lambda \"" + options[index] + "\" is not a double.");
				}
			} else if (options[index].equalsIgnoreCase("-eta")) {
				index++;
				try {
					eta_votedPerceptron = Double.parseDouble(options[index]);
				} catch (NumberFormatException e) {
					Utils.error("Value of eta \"" + options[index] + "\" is not an double.");
				}
			} else {
				Utils.error("Unknown argument: " + options[index]);
			}
			index++;
		}

		if (createDribbleFile) { Utils.createDribbleFileInDirectory(directory);  }
		if (posEvidence     != null) { task.setPosEvidenceLiterals(posEvidence); }
		if (negEvidence     != null) { task.setNegEvidenceLiterals(negEvidence); }
		if (queryLiterals   != null) { task.setQueryLiterals(queryLiterals);     } 
		if (queryPredNames  != null) { task.setQueryPredNames(queryPredNames);   }
		if (hiddenLiterals  != null) { task.setHiddenLiterals(hiddenLiterals);   }
		if (hiddenPredNames != null) { task.setHiddenPredNames(hiddenPredNames); }
		if (posEvidPredName != null) { task.setPosEvidencePredNames(posEvidPredName); }
		if (negEvidPredName != null) { task.setNegEvidencePredNames(negEvidPredName); }
		if (posQueries      != null) { task.setQueryLiteralsForTraining(posQueries, true);  }
		if (negQueries      != null) { task.setQueryLiteralsForTraining(negQueries, false); }
		if (yesCWA_PredNames!= null) { task.setYesCWApredNames(yesCWA_PredNames); }
		if ( noCWA_PredNames!= null) { task.setNoCWApredNames(  noCWA_PredNames); }
		task.setClosedWorldAssumption(useCWA);
	}
	
	public String formatLine(String line) {
		String[] tokens = line.split(",");
		int numLeftParen  = 0;
		int numRightParen = 0;
		String formatLine = "";
		for (String token : tokens) {
			formatLine = formatLine.concat(token);
			numLeftParen  += numOccurrencesOf(token, '(');
			numRightParen += numOccurrencesOf(token, ')');
			if (numLeftParen == numRightParen) { formatLine = formatLine.concat(" ; "); }
			else                               { formatLine = formatLine.concat(" , "); }
		}
		Utils.println(formatLine);
		return formatLine;
	}
	
	private int numOccurrencesOf(String str, char c) {
		int count = 0;
		for (int i = 0; i < str.length(); i++) {
			if (str.charAt(i) == c) { count++; }
		}
		return count;
	}
	
	// If some variable was not set, return the caller's default.  NOTE: buggy if an integer is set by the user to MIN_VALUE!
	public int choose(int callersDefault, int thisValue) {
		if (thisValue == Integer.MIN_VALUE) { return callersDefault; }
		return thisValue;
	}
	public double choose(double callersDefault, double thisValue) {
		if (Double.isNaN(thisValue)) { return callersDefault; }
		return thisValue;
	}

}
