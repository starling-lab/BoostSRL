package edu.wisc.cs.will.MLN_StructureLearning;

import java.io.File;  import edu.wisc.cs.will.Utils.condor.CondorFile;
import java.io.FileNotFoundException;
import edu.wisc.cs.will.Utils.condor.CondorFileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.naming.spi.DirectoryManager;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.ConnectedSentence;
import edu.wisc.cs.will.FOPC.ConnectiveName;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Theory;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.FOPC.UniversalSentence;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.ILP.Gleaner;
import edu.wisc.cs.will.ILP.ILPouterLoop;
import edu.wisc.cs.will.ILP.ScoreSingleClause;
import edu.wisc.cs.will.ILP.ScoreSingleClauseByAccuracy;
import edu.wisc.cs.will.MLN_Inference.AllOfInference;
import edu.wisc.cs.will.MLN_Inference.BruteForceInference;
import edu.wisc.cs.will.MLN_Inference.GibbsInference;
import edu.wisc.cs.will.MLN_Inference.Inference;
import edu.wisc.cs.will.MLN_Task.GroundLiteral;
import edu.wisc.cs.will.MLN_Task.GroundedMarkovNetwork;
import edu.wisc.cs.will.MLN_Task.MLN_Task;
import edu.wisc.cs.will.MLN_Task.MLNreductionProblemTooLargeException;
import edu.wisc.cs.will.MLN_Task.PredNameArityPair;
import edu.wisc.cs.will.MLN_Task.TimeStamp;
import edu.wisc.cs.will.MLN_WeightLearning.DiscriminativeWeightLearning;
import edu.wisc.cs.will.MLN_WeightLearning.PSCG;
import edu.wisc.cs.will.MLN_WeightLearning.VotedPerceptron;
import edu.wisc.cs.will.ResThmProver.HornClauseProver;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.BestFirstSearch;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchStrategy;


public class LearnDiscriminantMLNs {
	public  static final int    debugLevel           = 1;

	private static final int    VOTED_PERCEPTRON     = 0;
	private static final int    PSCG_ALG             = 1;
	private static final String defaultFileExtension = "txt";          // Do NOT include the '.' here.
	// My (JWS) new location for the WILL code: C:\\eclipse-workspace\\WILL
	// Testbeds are here:                       C:\\eclipse-workspace\\Testbeds
	private static final String testBedsPrefix       = "../Testbeds/MLNs/"; // But DO include the backslash here.
	
	private HandleFOPCstrings   stringHandler;
	private Unifier             unifier;
	private HornClauseProver    prover;
	private Collection<Clause>  clauses;
	private ILPouterLoop        outerLooper;
	
	private MLN_Task                task;
	private GroundedMarkovNetwork  groundedMarkovNetwork;
	
	private Set<Literal>            queryLiterals;  // We will remove DUPLICATES from these, since Sets(even though strictly speaking they should lead to multiple proofs and then be counted in ILP and MLN calculations).
	private Set<Literal>            hiddenLiterals; // Do NOT apply the closed-world assumption to these.
	private Set<Literal>            posEvidenceLiterals;
	private Set<Literal>            negEvidenceLiterals;
	private boolean                 readInTrainingLiterals = true;
	private Set<GroundLiteral>      posQueryLiterals; // These are the TRAINING values.
	private Set<GroundLiteral>      negQueryLiterals;
	private Set<PredNameArityPair>  queryPredNames; // These need to be SETs so that duplicates are not added.
	private Set<PredNameArityPair>  posEvidencePredNames;
	private Set<PredNameArityPair>  negEvidencePredNames;
	private Set<PredNameArityPair>  hiddenPredNames;  // Do NOT apply the closed-world assumption to these.
	private List<PredNameArityPair> yesCWA_PredNames; // Can override CWA on specific cases.
	private List<PredNameArityPair>  noCWA_PredNames;
	
	private boolean                 closedWorldAssumption = true;	
	private Map<GroundLiteral,String>     queryLabels; // The string associated with a query will be reported when the probability of each query is reported.

	private TimeStamp               timeStamp = new TimeStamp("LearnDiscriminantMLNs");
	
	public LearnDiscriminantMLNs() {
	}
	
	public void setUpILP(String workingDir, String[] requiredFiles) {	
		SearchStrategy    strategy = new BestFirstSearch();
		ScoreSingleClause scorer   = new ScoreSingleClauseByAccuracy();
		try {
			outerLooper = new ILPouterLoop(workingDir, requiredFiles);
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Problem encountered when setting up ILP learner: " + e);
		}
		stringHandler = outerLooper.innerLoopTask.getStringHandler();
		unifier       = outerLooper.innerLoopTask.getUnifier();
		prover        = new HornClauseProver(stringHandler); // We only need this for standard usage, rather than ILP-specific usage, so create directly.
		outerLooper.maxNumberOfCycles = 10;
		outerLooper.innerLoopTask.discardIfBestPossibleScoreOfNodeLessThanBestSeenSoFar = true;
        //outerLooper.innerLoopTask.requireThatAllRequiredHeadArgsAppearInBody = true;
        outerLooper.innerLoopTask.stopIfPerfectClauseFound = false; // Still want the best of the perfect clauses (and the branch-and-bound stuff) should filter out all others.
        outerLooper.innerLoopTask.setMinPosCoverage(1);
        outerLooper.innerLoopTask.setMinPrecision(0.5999);
        outerLooper.innerLoopTask.createCacheFiles = false;
        outerLooper.innerLoopTask.useCachedFiles   = false;
        outerLooper.innerLoopTask.setMEstimatePos(0.25);
        outerLooper.innerLoopTask.setMEstimateNeg(0.25);
        outerLooper.innerLoopTask.minNumberOfNegExamples      =     10;
        outerLooper.innerLoopTask.maxBodyLength               =     10;
        outerLooper.innerLoopTask.maxNumberOfNewVars          =     25;
        outerLooper.innerLoopTask.maxDepthOfNewVars           =     25;
        outerLooper.innerLoopTask.maxPredOccurrences          =      5;
        outerLooper.innerLoopTask.setMaxNodesToCreate(1000);
		outerLooper.innerLoopTask.setMaxNodesToConsider(100);
        outerLooper.innerLoopTask.maxResolutionsPerClauseEval =1000000;
    	Gleaner gleaner = (Gleaner) outerLooper.innerLoopTask.searchMonitor;
        gleaner.reportingPeriod = 100; 
	}
	
	public Theory learnILPTheory(boolean useRRR, String gleanerFileName, String checkpointFileName){
		Theory theory = null;
		try {
			outerLooper.initialize(false);
            outerLooper.setCheckpointFileName(checkpointFileName);
            outerLooper.setGleanerFileName(gleanerFileName);
            outerLooper.setRRR(useRRR);

			outerLooper.executeOuterLoop();
			theory = outerLooper.produceFinalTheory();
		} catch (SearchInterrupted e) {
			Utils.reportStackTrace(e);
    		Utils.error("Problem encountered when learning an ILP theory.");
		}
		return theory;
	}
	
	private void addToQueryPnameArity(Literal lit) {
		if (queryPredNames == null) { queryPredNames = new HashSet<PredNameArityPair>(4); }
		PredNameArityPair  pair = new PredNameArityPair(lit.predicateName, lit.numberArgs());
		queryPredNames.add(pair);
	}
	public void preprocessLearnedClausesForMLNweightLearning(Theory theory, boolean examplesBecomeQueryPnameArity) {
		// Get positive and negative examples and add them to the set of ground literals
		List<Example> posExamples = (readInTrainingLiterals ? outerLooper.innerLoopTask.getPosExamples() : null);
		List<Example> negExamples = (readInTrainingLiterals ? outerLooper.innerLoopTask.getNegExamples() : null);
		Iterable<Literal> facts      = outerLooper.innerLoopTask.getFacts();
		if (posExamples != null) for (Example currExample : posExamples){
			GroundLiteral gLitPos = new GroundLiteral(currExample);
			if (examplesBecomeQueryPnameArity) {
				addToQueryPnameArity(currExample);
			} else {
				if (queryLiterals == null) { queryLiterals = new HashSet<Literal>(4); }
				queryLiterals.add(currExample);
			}
			if (posQueryLiterals == null) { posQueryLiterals = new HashSet<GroundLiteral>(4);        }
			if (queryLabels      == null) { queryLabels      = new HashMap<GroundLiteral,String>(4); }
			queryLabels.put(gLitPos, " // Positive example #" + Utils.comma(1 + queryLabels.size()) + ".");
			posQueryLiterals.add(gLitPos);
		} else if (readInTrainingLiterals) { Utils.error("No positive examples found!"); }
		if (negExamples != null) for (Example currExample : negExamples) {
			GroundLiteral gLitNeg = new GroundLiteral(currExample);
			if (examplesBecomeQueryPnameArity) {
				addToQueryPnameArity(currExample);
			} else {
				if (queryLiterals == null) { queryLiterals = new HashSet<Literal>(4); }
				queryLiterals.add(currExample);
			}
			if (negQueryLiterals == null) { negQueryLiterals = new HashSet<GroundLiteral>(4);        }
			if (queryLabels      == null) { queryLabels      = new HashMap<GroundLiteral,String>(4); }
			queryLabels.put(gLitNeg, " // Negative example #" + Utils.comma(1 + queryLabels.size()) + ".");
			negQueryLiterals.add(gLitNeg); // Might not need to add them here either, but OK to do so.
		} else if (readInTrainingLiterals) { Utils.error("No negative examples found!"); }
		for (Sentence currFact : facts) /* if (!currFact.predicateName.name.equals("taughtBy")) */ {
			//currLiteral.setValueOnly(true);
			if (currFact instanceof Literal) { 
				if (posEvidenceLiterals == null) { posEvidenceLiterals =  new HashSet<Literal>(4); }
				posEvidenceLiterals.add((Literal) currFact); 
			}
			else if (currFact instanceof ConnectedSentence && ((ConnectedSentence) currFact).getSentenceB() instanceof Literal && ConnectiveName.isaNOT(((ConnectedSentence) currFact).getConnective().name)) {
				if (negEvidenceLiterals == null) { negEvidenceLiterals =  new HashSet<Literal>(4); }
				negEvidenceLiterals.add((Literal) ((ConnectedSentence) currFact).getSentenceB());  // Have NOT(p(1)).
			}
			else if (currFact instanceof UniversalSentence && ((UniversalSentence) currFact).body instanceof Literal) {
				if (posEvidenceLiterals == null) { posEvidenceLiterals =  new HashSet<Literal>(4); }
				posEvidenceLiterals.add((Literal) ((UniversalSentence) currFact).body); // Have ForAll p(x).
			} // In the test below, should really check that 'sentenceB' is an instance of Literal.  TODO
			else if (currFact instanceof UniversalSentence && ((UniversalSentence) currFact).body instanceof ConnectedSentence && ConnectiveName.isaNOT(((ConnectedSentence) ((UniversalSentence) currFact).body).getConnective().name)) {
				if (negEvidenceLiterals == null) { negEvidenceLiterals =  new HashSet<Literal>(4); }
				negEvidenceLiterals.add((Literal) ((ConnectedSentence) ((UniversalSentence) currFact).body).getSentenceB()); // Have ForAll NOT(p(x)).
			} else { Utils.error("Expecting something like NOT(p(x)) but got: " + currFact); }
		}

		/*hiddenPredNames     = new HashSet<PredNameArityPair>(1);
		PredicateName pName = stringHandler.getPredicateName("course");
		PredNameArityPair pNameArityPair = new PredNameArityPair(pName, 2);
		hiddenPredNames.add(pNameArityPair); */
		int maxEvidenceSize = 1000000000;
		int maxQueriesSize  = 1000000000;
		int maxHiddensSize  = 1000000000;
	    if (Utils.getSizeSafely(posEvidenceLiterals) > maxEvidenceSize) { Utils.println("\n*** WARNING: limiting |positive evidence| = "  + Utils.comma(maxEvidenceSize) + " (was " + Utils.comma(posEvidenceLiterals.size()) + ")."); Utils.randomlyRemoveThisManyItems(posEvidenceLiterals, posEvidenceLiterals.size() - maxEvidenceSize); }
	    if (Utils.getSizeSafely(negEvidenceLiterals) > maxEvidenceSize) { Utils.println("\n*** WARNING: limiting |negative evidence| = "  + Utils.comma(maxEvidenceSize) + " (was " + Utils.comma(negEvidenceLiterals.size()) + ")."); Utils.randomlyRemoveThisManyItems(negEvidenceLiterals, negEvidenceLiterals.size() - maxEvidenceSize); }
		if (Utils.getSizeSafely(queryLiterals)       > maxQueriesSize)  { Utils.println("\n*** WARNING: limiting |queryLits| = "          + Utils.comma(maxQueriesSize)  + " (was " + Utils.comma(queryLiterals.size())       + ")."); Utils.randomlyRemoveThisManyItems(queryLiterals,       queryLiterals.size()       - maxQueriesSize);  }
		if (Utils.getSizeSafely(hiddenLiterals)      > maxHiddensSize)  { Utils.println("\n*** WARNING: limiting |hiddenLits| = "         + Utils.comma(maxHiddensSize)  + " (was " + Utils.comma(hiddenLiterals.size())      + ")."); Utils.randomlyRemoveThisManyItems(hiddenLiterals,      hiddenLiterals.size()      - maxHiddensSize);  }
		if (debugLevel > 0) { Utils.println("\n% Sizes: |positive evidence| = " + Utils.comma(Utils.getSizeSafely(posEvidenceLiterals)) + ", |negative evidence| = " + Utils.comma(Utils.getSizeSafely(negEvidenceLiterals)) + ", |queries| = " + Utils.comma(Utils.getSizeSafely(queryLiterals)) + ", and |hiddens| = " + Utils.comma(Utils.getSizeSafely(hiddenLiterals))); }
		// Get the list of query predicate names and the evidence predicate names from the clauses learned in the theory.
		clauses = (theory == null ? null : theory.getClauses());
		//Utils.println("Clauses: " + clauses);
	}
	
	public void createReducedMarkovLogicNetwork(String workingdirectory) {
		long   start = System.currentTimeMillis();
		long   end;
		double timeTaken;
		
		task = new MLN_Task(stringHandler, unifier, prover, clauses, queryLiterals, queryPredNames, posEvidenceLiterals, posEvidencePredNames, negEvidenceLiterals, negEvidencePredNames, hiddenLiterals, hiddenPredNames, closedWorldAssumption);
		task.setWorkingDirectory(workingdirectory);
		if (posQueryLiterals != null) { posQueryLiterals = task.setQueryLiteralsForTraining(posQueryLiterals, true);  }
		if (negQueryLiterals != null) { negQueryLiterals = task.setQueryLiteralsForTraining(negQueryLiterals, false); }
		if (yesCWA_PredNames != null) { task.setYesCWApredNames(yesCWA_PredNames); }
		if ( noCWA_PredNames != null) { task.setNoCWApredNames(  noCWA_PredNames); }
		end       = System.currentTimeMillis();
		timeTaken = (end - start) / 1000.0;
		Utils.println("\n%       Took " + Utils.truncate(timeTaken, 3) + " seconds to create the MLN_Task instance.");

		start = System.currentTimeMillis();
		groundedMarkovNetwork = task.createReducedNetwork();
		end       = System.currentTimeMillis();
		timeTaken = (end - start) / 1000.0;
		Utils.println("\n%       Took " + Utils.truncate(timeTaken, 3) + " seconds to create the reduced MarkovLogicNetwork instance.");
	}
	
	public Collection<Clause> learnMLNWeights(int learningAlgo, int numLearningSteps) {
		DiscriminativeWeightLearning discriminativeWgtLearner = null;


		long   start = System.currentTimeMillis();
		long   end;
		double timeTaken;		
		groundedMarkovNetwork.setWeightsLearnt(false);
		switch(learningAlgo) {
		case VOTED_PERCEPTRON: 
			discriminativeWgtLearner = new VotedPerceptron(groundedMarkovNetwork, numLearningSteps);
			break;
		case PSCG_ALG: 
			discriminativeWgtLearner = new PSCG(           groundedMarkovNetwork, numLearningSteps);
			break;
		}
		Collection<Clause> weightedClauses =  null;
		// int steps = 168000 / numLearningSteps;
		// for (int i=0; i < steps; i++) {
		 	// discriminativeWgtLearner.updateMissingLiterals();
		    weightedClauses = discriminativeWgtLearner.learn(timeStamp);
		// }
		groundedMarkovNetwork.setWeightsLearnt(true);
		end       = System.currentTimeMillis();
		timeTaken = (end - start) / 1000.0;
		Utils.println("\n%   Took " + Utils.truncate(timeTaken, 3) + " seconds to perform weight learning.");
		if (debugLevel > 0) { discriminativeWgtLearner.print(); }
		return weightedClauses;
	}
	
	private void writeNegExamplesFile(String directory, String fileExtension) {
		String fileName = testBedsPrefix + directory + "/" + directory + "_neg." + fileExtension;
		List<Example> negExamples = outerLooper.innerLoopTask.getNegExamples();

        try {
            CondorFileOutputStream outStream = new CondorFileOutputStream(fileName);
            PrintStream    printStream = new PrintStream(outStream, false); // No auto-flush (can slow down code).
            int counter = 1;
            for (Example ex : negExamples) { printStream.println(ex + ". // Negative Example #" + Utils.comma(counter++) + ".  Provenance: " + ex.provenance); }
            printStream.close();
            outStream.close();
        } catch (FileNotFoundException e) {
			Utils.reportStackTrace(e);
            Utils.error("Unable to successfully open this file for writing: " + fileName + ".  Error message: " + e.getMessage());
        } catch (IOException e) {
			Utils.reportStackTrace(e);
            Utils.error("I/O exception when writing to: " + fileName + ".  Error message: " + e.getMessage());
		}
	}

	
	/**
	 * @param args
	 * @throws SearchInterrupted 
	 */
	public static void main(String[] args) throws SearchInterrupted {
		args = Utils.chopCommentFromArgs(args);
		long   startAll = System.currentTimeMillis();
		long   start    = startAll;
		long   end;
		double timeTaken, timeTakenSinceStartAll;

		Utils.println("\n\n% **** STARTING THE TIMERS HERE *****"); 

		LearnDiscriminantMLNs ilpWL = new LearnDiscriminantMLNs();
		String[] newArgList    = new String[5];
		String   directory     = args[0];
		String   fileExtension = (args.length > 1 ? args[1] : defaultFileExtension);
		String   dirForFacts        = (args.length > 2 ? args[2] : ""); // Allows one to vary the facts for experiments.  Eg:   uw-cse   txt    uw-cse_facts50/   uw-cse_facts_50_1
		String   fileNameForFacts   = (args.length > 3 ? args[3] : directory + "_facts");
		String   fileNameForDribble         = testBedsPrefix + directory + "/" + (args.length > 3 ? dirForFacts + args[3] + "_" : "");
		String   workingDirectoryForResults = testBedsPrefix + directory + "/" + (args.length > 3 ? dirForFacts + args[3] + "_" : "");

		// Utils.waitHere("System.getProperties() = " + System.getProperties());		
		ilpWL.readInTrainingLiterals = true; //// <--------------------------------------

		//TODO - automatically add the slash to dirForFacts if missing

		//Utils.createDribbleFileInDirectory(testBedsPrefix + directory);		
		Utils.createDribbleFile(fileNameForDribble + "dribbleLearnDiscrimMLN.txt");

		newArgList[0] = (ilpWL.readInTrainingLiterals ? testBedsPrefix + directory + "/" + directory   + "_pos." + fileExtension : null);
		newArgList[1] = (ilpWL.readInTrainingLiterals ? testBedsPrefix + directory + "/" + directory   + "_neg." + fileExtension : null);
		newArgList[2] =                                 testBedsPrefix + directory + "/" + directory   + "_bk."  + fileExtension;
		newArgList[3] =                                 testBedsPrefix + directory + "/" + dirForFacts + fileNameForFacts + "." + fileExtension; // TODO - if we want scatterplots to go to the specified facts dir, will need to tweak the command-line args (eg, break into args) and pass this info to the MLN_Task.
		ilpWL.setUpILP(testBedsPrefix + directory + "/" , newArgList);
		ilpWL.stringHandler.precompute_file_prefix = testBedsPrefix +  directory + "/";

		// Override defaults on a testbed-by-testbed basis.
		if (directory.equalsIgnoreCase("advised")      || directory.equalsIgnoreCase("advised_small") || 
				directory.equalsIgnoreCase("uw-cse")   || directory.equalsIgnoreCase("smoking_new")   || 
				directory.equalsIgnoreCase("citeseer") || directory.equalsIgnoreCase("concussion")    ||
				directory.equalsIgnoreCase("cora")) {
			ilpWL.outerLooper.maxNumberOfCycles = 3;
			ilpWL.outerLooper.innerLoopTask.discardIfBestPossibleScoreOfNodeLessThanBestSeenSoFar = true;
			//ilpWL.outerLooper.innerLoopTask.requireThatAllRequiredHeadArgsAppearInBody = true;
			ilpWL.outerLooper.innerLoopTask.stopIfPerfectClauseFound = false; // Still want the best of the perfect clauses (and the branch-and-bound stuff) should filter out all others.
			ilpWL.outerLooper.innerLoopTask.setMinPosCoverage(0.20);
			ilpWL.outerLooper.innerLoopTask.setMinPrecision(0.5999);
			ilpWL.outerLooper.innerLoopTask.createCacheFiles = false;
			ilpWL.outerLooper.innerLoopTask.useCachedFiles   = false;
			ilpWL.outerLooper.innerLoopTask.setMEstimatePos(1);
			ilpWL.outerLooper.innerLoopTask.setMEstimateNeg(1);
			ilpWL.outerLooper.innerLoopTask.usingWorldStates = false; // CHANGE IF WORKING ON PLANNING TASKS.
			ilpWL.outerLooper.innerLoopTask.minNumberOfNegExamples      =  1000;
			ilpWL.outerLooper.innerLoopTask.fractionOfImplicitNegExamplesToKeep = 1.01;
			ilpWL.outerLooper.innerLoopTask.maxBodyLength               =      7;
			ilpWL.outerLooper.innerLoopTask.maxNumberOfNewVars          =      5;
			ilpWL.outerLooper.innerLoopTask.maxDepthOfNewVars           =      5;
			ilpWL.outerLooper.innerLoopTask.maxPredOccurrences          =      5;
			ilpWL.outerLooper.innerLoopTask.setMaxNodesToCreate(10000);
			ilpWL.outerLooper.innerLoopTask.setMaxNodesToConsider(1000);
			ilpWL.outerLooper.innerLoopTask.maxResolutionsPerClauseEval =1000000;
			Gleaner gleaner = (Gleaner) ilpWL.outerLooper.innerLoopTask.searchMonitor;
			gleaner.reportingPeriod = 1000; 
			ilpWL.stringHandler.numberOfLiteralsPerRowInPrintouts = 10;
			ilpWL.stringHandler.useFastHashCodeForLiterals = false;
		}

		String gleanerFileName;
		String checkpointFileName;
		boolean useRRR = false;
		if (useRRR) {
			gleanerFileName    = testBedsPrefix + directory + "/gleanerRRR." + fileExtension;
			checkpointFileName = testBedsPrefix + directory + "/checkpointRRR.chkpt";
		}
		else {
			gleanerFileName    = testBedsPrefix + directory + "/gleanerStd." + fileExtension;
			checkpointFileName = testBedsPrefix + directory + "/checkpointStd.chkpt";
		}
		ilpWL.outerLooper.innerLoopTask.setDirectoryName(testBedsPrefix + directory);

		String fileName1 = testBedsPrefix + directory + "/learnedILP_theory."        + fileExtension;
		String fileName2 = testBedsPrefix + directory + "/" + directory + "_theory." + fileExtension;
		File       file1 = new CondorFile(fileName1);
		File       file2 = new CondorFile(fileName2);
		boolean usingILPtheory      = true;
		boolean clausesTheoryReadIn = true;

		// See if an ILP theory has been cached.  If not, create one and cache it (so we can focus on testing the MLN portion).
		Theory theoryToUseWithMLNs;
		if (file1.exists()) {
			Collection<Sentence> oldTheory = ilpWL.outerLooper.innerLoopTask.getParser().readFOPCfile(fileName1);
			theoryToUseWithMLNs = new Theory(ilpWL.stringHandler, oldTheory, ilpWL.outerLooper.innerLoopTask.getInlineManager());
			int numberOfClauses = Utils.getSizeSafely(theoryToUseWithMLNs.getClauses());
			Utils.println("\n% Have read " + numberOfClauses + " clauses from '" + file1 + "'.");
			// [gets printed below] Utils.println(theoryToUseWithMLNs.toString()); //Utils.waitHere("Using ILP theory = " + usingILPtheory);
			int negExCountBefore = Utils.getSizeSafely(ilpWL.outerLooper.innerLoopTask.getNegExamples());
			ilpWL.outerLooper.innerLoopTask.initialize(false); // Needed if we want to compute the coverage of the clauses on the examples.
			int negExCountAfter  = Utils.getSizeSafely(ilpWL.outerLooper.innerLoopTask.getNegExamples());
			if (negExCountAfter != negExCountBefore) { 
				Utils.println("% Negative examples created: |negExamples| = " + Utils.comma(negExCountBefore) + " BEFORE and |negExamples| = " + Utils.comma(negExCountAfter) + " AFTER initialization.");
				ilpWL.writeNegExamplesFile(directory, fileExtension);
			}
		} else if (file2.exists()) {
			usingILPtheory = false;
			Collection<Sentence> oldTheory = ilpWL.outerLooper.innerLoopTask.getParser().readFOPCfile(fileName2);
			theoryToUseWithMLNs = new Theory(ilpWL.stringHandler, oldTheory, ilpWL.outerLooper.innerLoopTask.getInlineManager());
			int numberOfClauses = Utils.getSizeSafely(theoryToUseWithMLNs.getClauses());
			Utils.println("\n% Have read " + numberOfClauses + " clauses from '" + file2 + "'.");
			// [gets printed below] Utils.println(theoryToUseWithMLNs.toString()); //Utils.waitHere("Using ILP theory = " + usingILPtheory);
			int negExCountBefore = Utils.getSizeSafely(ilpWL.outerLooper.innerLoopTask.getNegExamples());
			ilpWL.outerLooper.innerLoopTask.initialize(false);
			int negExCountAfter  = Utils.getSizeSafely(ilpWL.outerLooper.innerLoopTask.getNegExamples());
			Utils.println("\n% Have read " + 
					Utils.comma(ilpWL.outerLooper.innerLoopTask.getPosExamples()) + " positive and " +
					Utils.comma(ilpWL.outerLooper.innerLoopTask.getNegExamples()) + 
					" negative examples from '" + testBedsPrefix + directory + "'.");			
			if (negExCountAfter != negExCountBefore) { 
				Utils.println("% Negative examples created: |negExamples| = " + Utils.comma(negExCountBefore) + " BEFORE and |negExamples| = " + Utils.comma(negExCountAfter) + " AFTER initialization.");
				ilpWL.writeNegExamplesFile(directory, fileExtension); 
			}
		} else { Utils.waitHere("SHOULD NOT GET HERE IN THE CURRENT TESTING " + fileName1 + " " + fileName2);
		theoryToUseWithMLNs = ilpWL.learnILPTheory(useRRR, gleanerFileName, checkpointFileName);
		clausesTheoryReadIn = false;
		if (theoryToUseWithMLNs != null && theoryToUseWithMLNs.getClauses() != null) {
			CondorFileOutputStream outStream = null;
			try {
				outStream = new CondorFileOutputStream(fileName1);
			} catch (FileNotFoundException e) {
				Utils.reportStackTrace(e);
				Utils.error("Something went wrong reading " + fileName1);
			}
			PrintStream printStream = new PrintStream(outStream, false); // (Don't) Request auto-flush (can slow down code).
			printStream.println(theoryToUseWithMLNs.toPrettyString("   "));
		}
		}

		// File containing the hidden literals - e.g. ../Testbeds/uw-cse/uw-cse_hiddenl.txt
		String   hiddenLiteralFile = testBedsPrefix + directory + "/" + dirForFacts + directory + "_hiddenl.txt";
		ilpWL.readHiddenLiterals(hiddenLiteralFile);

		if (theoryToUseWithMLNs == null || theoryToUseWithMLNs.getClauses() == null) {
			Utils.println("% Since no theory learned, no need to learn MLN weights."); // TODO - could learn weights on all the features as 'singletons.'
		} else {
			if (debugLevel > 0) { Utils.println("\n% The " + Utils.getSizeSafely(theoryToUseWithMLNs.getClauses()) + (clausesTheoryReadIn ? " Provided" : " Learned") + " Clause(s):\n"); }
			int counter = 1;
			for (Clause c : theoryToUseWithMLNs.getClauses()) {
				if (debugLevel > 0) { Utils.println("% Clause #" + counter++ + ":  " + c.toPrettyString("%      ", Integer.MAX_VALUE)); }
				if (usingILPtheory) {
					int coveragePOS = ilpWL.outerLooper.innerLoopTask.collectPosExamplesCovered(c, false);
					int coverageNEG = ilpWL.outerLooper.innerLoopTask.collectNegExamplesCovered(c, true);
					int totalPOS    = Utils.getSizeSafely(ilpWL.outerLooper.innerLoopTask.getPosExamples());
					int totalNEG    = Utils.getSizeSafely(ilpWL.outerLooper.innerLoopTask.getNegExamples());
					Utils.println("%  Stats: " + coveragePOS + " of " + totalPOS + " pos and " + coverageNEG + " of " + totalNEG + " neg examples covered.\n");
				}
			}

			end       = System.currentTimeMillis();
			timeTaken = (end - start) / 1000.0;
			timeTakenSinceStartAll =  (end - startAll) / 1000.0;
			Utils.println("\n%   Took " + Utils.truncate(timeTaken, 3) + " seconds to reach 'preprocessLearnedClausesForMLNweightLearning' (" + Utils.truncate(timeTakenSinceStartAll, 3) + " since overall start).");

			Utils.println("\n\n% **** STARTING THE 'overall start' TIMER HERE (i.e., after files have been read) *****");
			startAll = System.currentTimeMillis();

			start = System.currentTimeMillis();
			ilpWL.preprocessLearnedClausesForMLNweightLearning(theoryToUseWithMLNs, true);
			end       = System.currentTimeMillis();
			timeTaken = (end - start) / 1000.0;
			timeTakenSinceStartAll = (end - startAll) / 1000.0;
			Utils.println("\n%   Took " + Utils.truncate(timeTaken, 3) + " seconds to complete 'preprocessLearnedClausesForMLNweightLearning' (" + Utils.truncate(timeTakenSinceStartAll, 3) + " since overall start).");

			start = System.currentTimeMillis();
			ilpWL.createReducedMarkovLogicNetwork(workingDirectoryForResults);
			end       = System.currentTimeMillis();
			timeTaken = (end - start) / 1000.0;
			timeTakenSinceStartAll = (end - startAll) / 1000.0;
			Utils.println("\n%   Took " + Utils.truncate(timeTaken, 3) + " seconds to reduce the provided MLN (" + Utils.truncate(timeTakenSinceStartAll, 3) + " since overall start).  [" + workingDirectoryForResults + "]");


			start = System.currentTimeMillis();
			boolean doingLazyInference = ilpWL.groundedMarkovNetwork.prepareForInference(ilpWL.timeStamp); 
			end       = System.currentTimeMillis();
			timeTaken = (end - start) / 1000.0;
			timeTakenSinceStartAll = (end - startAll) / 1000.0;
			Utils.println("\n%   Took " + Utils.truncate(timeTaken, 3) + " seconds to" + (doingLazyInference ? " prepare for lazy inference" : " fully ground the reduced MarkovNetwork instance") + " (" + Utils.truncate(timeTakenSinceStartAll, 3) + " since overall start).");
			ilpWL.groundedMarkovNetwork.task.getCountOfCanonicalGroundLiterals();
			ilpWL.groundedMarkovNetwork.getCountOfUniqueGroundClauses();

			if (false) { // TODO call BEFORE and AFTER weight training, and save both versions.
				start = System.currentTimeMillis();
				Inference inferenceInstance; // Note: Infer.java is for command-line calls.
				inferenceInstance = new BruteForceInference(ilpWL.groundedMarkovNetwork); 
			//	inferenceInstance = new MCSATInference(ilpWL.groundedMarkovNetwork, AllOfInference.prior_for_being_true_default);
				try {
					inferenceInstance.findQueryState(ilpWL.task.getQueryLiterals(), ilpWL.task.makeQueryLabelsCanonical(ilpWL.queryLabels));
				} catch (MLNreductionProblemTooLargeException e) {
					Utils.reportStackTrace(e);
					Utils.error("Encountered problems with inference.");
				}
				end       = System.currentTimeMillis();
				timeTaken = (end - start) / 1000.0;
				timeTakenSinceStartAll =  (end - startAll) / 1000.0;
				Utils.println("Took " + Utils.truncate(timeTaken, 3) + " seconds to complete scoring the training examples (" + Utils.truncate(timeTakenSinceStartAll, 3) + " since overall start).");
				inferenceInstance.displayOutput();
				double meanCrossEntropy = inferenceInstance.reportOnTheseExamples(ilpWL.posQueryLiterals, ilpWL.negQueryLiterals, 1000, 100);
			}
			// Uncomment to use inference for different number of learning steps
		//	for (int s = 100; s <=1000; s += 100) {
				int s = 200;
				if (false) {
					start = System.currentTimeMillis();
					boolean useVP = true;
					Collection<Clause> weightedClauses = ilpWL.learnMLNWeights(
							useVP ? VOTED_PERCEPTRON :  PSCG_ALG,
									useVP ? s :  s);
					Utils.println("% For steps: " + s);
					Utils.println("\n% The Weighted Clause(s):");
					for (Clause c : weightedClauses) {
						Utils.println("%   " + c.toPrettyString("%     ", Integer.MAX_VALUE));
					}
					end       = System.currentTimeMillis();
					timeTaken = (end - start) / 1000.0;
					timeTakenSinceStartAll =  (end - startAll) / 1000.0;
					Utils.println("Took " + Utils.truncate(timeTaken, 3) + " seconds to complete 'learnMLNWeights' (" + Utils.truncate(timeTakenSinceStartAll, 3) + " since overall start).");
				}

				if (true) { // TODO call BEFORE and AFTER weight training, and save both versions.
					Utils.println("%% After Weight Learning");
					start = System.currentTimeMillis();
					Inference inferenceInstance; // Note: Infer.java is for command-line calls.
					inferenceInstance = new BruteForceInference(ilpWL.groundedMarkovNetwork); 
				//	inferenceInstance = new MCSATInference(ilpWL.groundedMarkovNetwork, AllOfInference.prior_for_being_true_default);
					// Use Gibbs Inference
					 inferenceInstance = new GibbsInference(ilpWL.groundedMarkovNetwork, AllOfInference.prior_for_being_true_default);
					try {
						inferenceInstance.findQueryState(ilpWL.task.getQueryLiterals(), ilpWL.task.makeQueryLabelsCanonical(ilpWL.queryLabels));
					} catch (MLNreductionProblemTooLargeException e) {
						Utils.reportStackTrace(e);
						Utils.error("Encountered problems with inference.");
					}
					end       = System.currentTimeMillis();
					timeTaken = (end - start) / 1000.0;
					timeTakenSinceStartAll =  (end - startAll) / 1000.0;
					Utils.println("Took " + Utils.truncate(timeTaken, 3) + " seconds to complete scoring the training examples (" + Utils.truncate(timeTakenSinceStartAll, 3) + " since overall start).");
					inferenceInstance.displayOutput();
					double meanCrossEntropy = inferenceInstance.reportOnTheseExamples(ilpWL.posQueryLiterals, ilpWL.negQueryLiterals, 1000, 100);
					inferenceInstance.cleanupSampleGenerator();
					Utils.println("%ENTROPY: " + s + ":" + meanCrossEntropy);
				}
			}
		//}
	}

	private void readHiddenLiterals(String hlFileName) {
		// TODO Auto-generated method stub
		FileParser parser = new FileParser(stringHandler);
		List<Sentence> sentences = parser.readFOPCfile(hlFileName, true);
		if (sentences == null) return;
		Theory theory = new Theory(stringHandler, sentences);
		if (hiddenPredNames != null) { Utils.error("Already have hiddenPredNames"); }
		if (hiddenLiterals  != null) { Utils.error("Already have hiddenLiterals"); }
		hiddenLiterals  = new HashSet<Literal>(4);
		for (Clause clause : theory.getClauses()) {	
			Literal lit = clause.posLiterals.get(0);			
			hiddenLiterals.add(lit);
		}
	}

}
