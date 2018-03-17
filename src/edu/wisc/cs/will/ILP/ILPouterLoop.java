/**
 * Notes:
 * 
 *  isaStack: need to label ALL examples in each world
 *            maybe have 2-3 worlds, with 1-2 blocks in each
 *            and all (most?) data labeled
 *  
 *  me TODO
 *     make sure ok if NO negs can be created (eg, since all data is labelled)
 *      - hand edit file
 *      why isnt isablock(X) :- support(X, Y)?
 *      
 *      small penalty for 'unused' vars?
 *      
 *      clean up printing of rules?
 * 
 * 
 * 
 */
package edu.wisc.cs.will.ILP;

import java.io.File;  import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.Utils.condor.CondorFileInputStream;
import java.io.FileNotFoundException;
import edu.wisc.cs.will.Utils.condor.CondorFileOutputStream;
import edu.wisc.cs.will.Utils.condor.CondorFileReader;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.io.Reader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.zip.GZIPInputStream;
import java.util.zip.GZIPOutputStream;

import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.RDN.RunBoostedRDN;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.DataSetUtils.RegressionExample;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Theory;
import edu.wisc.cs.will.FOPC.TreeStructuredTheory;
import edu.wisc.cs.will.FOPC.TreeStructuredTheoryInteriorNode;
import edu.wisc.cs.will.FOPC.TreeStructuredTheoryLeaf;
import edu.wisc.cs.will.FOPC.TreeStructuredTheoryNode;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.ILP.Regression.BranchStats;
import edu.wisc.cs.will.ResThmProver.DefaultHornClauseContext;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.Utils.MessageType;
import edu.wisc.cs.will.Utils.NamedReader;
import edu.wisc.cs.will.Utils.Stopwatch;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.VectorStatistics;
import edu.wisc.cs.will.stdAIsearch.BestFirstSearch;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchMonitor;
import edu.wisc.cs.will.stdAIsearch.SearchResult;
import edu.wisc.cs.will.stdAIsearch.SearchStrategy;
import java.io.BufferedReader;
import java.util.Arrays;

/**
 * @author shavlik
 *
 * 
 *
 * VERSION 0.1 of the Wisconsin Inductive Logic Learner (WILL) system (name subject to change :-)
 *
 *	This class provides a mechanism for performing the traditional outer loop of ILP algorithms.
 *	The basic process is as follows:
 * 		1) do a standard ILP run
 * 		2) repeat using some new seed(s) examples until some stopping criteria met
 * 		3) return a set of clauses (a 'theory') as the final 'model'
 * 
 *  Some properties of this ILP algorithm:
 *      1) examples can be weighted
 *      2) both standard ILP heuristic search and a random-sampling method (RRR) can be performed
 *      3) the Gleaner idea (see Gleaner.java) is used to keep not only the best rule for iteration, but also the best rule per interval of recall (eg, the best rule whose recall is between 0.50 and 0,.55).
 *      4) on each cycle, multiple seed examples can be specified; a node (ie, a possible clause) needs to satisfy some fraction of the pos seeds and no more than some fraction of the negative seeds.  
 *      5) during successive iterations of the outer ILP loop, the pos examples can be down weighted and the covered neg examples can be up weighted (eg, a boosting-like mechanism, though the code currently does not compute the wgts defined by the boosting algo, but that would be a straightforward extension).
 *      6) implementation detail: in the inner loop, each node records the examples REJECTED at this node (this means that on any path to a node, examples are stored at no more than one node)
 *      7) hash tables (Java's hash maps, actually) are used for efficiency (eg, compared to linear lookups in lists)
 *      8) currently this code does NOT construct a "bottom clause" - instead if uses the multiple seed idea mentioned above to guide the search of candidate clauses
 *      9) no Prolog is needed; everything needed is provided in a set of Java projects (of course this means the code is slower than, say, Aleph+YAP Prolog, but computers get faster every year :-)
 *     10) as in Aleph and other ILP systems, arguments are typed (eg, 'human' and 'dog') to help control search; in this code the typing is hierarchical.
 *     11) as in Aleph, there is the ability for users to define prune(node), by which the user can cut off search trees.  Related to this is the built-in capability to process "intervals" such as isInThisInterval(1, value, 5).  If the previous literal is already in a clause, there is no need to add isInThisInterval(2, value, 4), since the latter will always be true given the former.  Similarly, there is no need to include isInThisInterval(7, value, 9) since it will always be false.  See PruneILPsearchTree.java for more detials. 
 * 
 * 	Note that with Gleaner as the searchMonitor, can create a theory from just one std ILP run.
 *	In this code, each std ILP run has its own Gleaner data structure, plus one Gleaner stores the best over ALL iterations.  
 *  Several different ways of returning a theory are provided (to do), as are various ways of stopping the outer loop.
 *  
 *  No support for this code is promised nor implied.  Suggestions and bug fixes may be sent to shavlik@cs.wisc.edu but please do not expect a reply.
 *  
 *  This code was heavily influenced by experience with Ashwin Srinivasan's Aleph (www.comlab.ox.ac.uk/oucl/research/areas/machlearn/Aleph/)
 *
 *  to do: count resolutions in theorem proving and throw if some max-value exceeded?
 *         add bottom clause code?
 */
public class ILPouterLoop implements GleanerFileNameProvider {
	public  static final String systemName = "WILL"; // See comment above for explanation.
   
	public  LearnOneClause innerLoopTask;  // LearnOnClause performs the inner loop of ILP.

	/** The state of the outer loop.
     *
     * Everything that should be checkpointed goes inside the ILPouterLoopState.  Variables
     * defined in ILPouterLoop will not be checkpointed.
     *
     */
	private ILPouterLoopState outerLoopState;

	private String workingDirectory;
   
    // The weight on covered example functionality was not compatible with the
    // new example weighting system.  If this functionality is needed we will have
    // to reimplement using a different approach than previously.  -Trevor
	//public  double         weightOnCoveredPosExample     =   1.0;  // When an already-covered example is covered by a new clause, this is the weight on it (should be in [0-1] but need only be non-negative) during the next iteration of the ILP inner loop.
	//public  double         weightOnCoveredNegExample     =   1.0;  // If this or the above is 0, then it means "do not count" this example in precision, etc.  Could also use, say, Boosting to weight the examples.

    public  int            maxNumberOfCycles             = 100;   // Call the inner loop at most this many times.
	public  int            maxNumberOfClauses            = 100;   // Same as above EXCEPT only counts if a clause was learned.
	public  double         minFractionOfPosCoveredToStop = 0.90;  // Stop when this fraction of the positive examples are covered by some acceptable clause.
	public  int            max_total_nodesExpanded       = Integer.MAX_VALUE;
	public  int            max_total_nodesCreated        = Integer.MAX_VALUE;
    public  int            numberPosSeedsToUse           = 1;
	public  int            numberNegSeedsToUse           = 0;
	
	public  double         minimalAcceptablePrecision    = 0.0; // If these cannot be met, even if the next clause learned covers ALL uncovered positive and covers NO negatives, then abort.
	public  double         minimalAcceptableRecall       = 0.0;
	public  double         minimalAcceptableAccuracy     = 0.0;
	public  double         minimalAcceptableF1           = 0.0; // TODO - handle F(beta).

    ///////////////////////////////////////////////////////////////////
	// Parameters that are used when learning tree-structured theories.
    public  boolean        learningTreeStructuredTheory        = false;
    public  boolean        sortTreeStructedNodesByMeanScore    = true; // If false, then sort by TOTAL score of the examples reaching that node.
    private int            maxNumberOfLiteralsAtAnInteriorNode =  2; // In calls to LearnOneClause, this is how much we are allowed to extend the current clause.  Initially it is the max body length, but since recursive calls extend the clause at the parent, we need to add this much to the current number of literals on the path to the current node (not counting the length of the tests that evaluate to false, i.e., for the FALSE branches).
    private int            maxTreeDepthInLiterals              = 25; // This is the sum of literals at all the nodes in a path from root to leaf, not just the number of interior nodes.
    private int			   maxTreeDepthInInteriorNodes         =  5; // Maximum height/depth of the tree in terms of interior nodes in the tree. NOTE: One node in the tree may have multiple literals.
    private String         prefixForExtractedRules             = "";
    private String         postfixForExtractedRules            = "";
    private boolean		   learnMLNTheory					   = false;	
    private boolean        learnMultiValPredicates             = false;
    private boolean 	   learnOCCTree						   = false;
    ///////////////////////////////////////////////////////////////////
    
	public  boolean        writeGleanerFilesToDisk       = false; // Write 'gleaner' files periodically.
	private String         gleanerFileName               = null;  // Please don't use this directly.  Null indicates the use of a default value.
	private String         gleanerFileNameFlipFlopped    = null;  // Put the gleaner results for the flip-flopped case here.
	private Gleaner        gleaner                       = null;  // These two hold on to gleaners when we do flip-flops.  The gleaner is 'really' stored in LearnOneClause.
	private Gleaner        gleanerFlipFlopped            = null;
    private String         annotationForRun              = null;

	private boolean        checkpointEnabled             = false; // Write 'gleaner' files periodically.
	private String         checkpointFileName            = null;  // Please don't use this directly.  Null indicates the use of a default value.
	private String         checkpointFileNameFlipFlopped = null;

	// All of the fields below are now in the ILPouterLoopState object.
	// Any information needed to restart a run in the middle (from the chkpt)
    // must reside in the ILPouterLoopState object.
	//
	// There are accessors for all of these variable. For example, to get and set
	// numberOfCycles, there is now a getNumberOfCycles() and
	// setNumberOfCycles().
	// However, if you still want to access this variable directly, you can use
	// 'outerLoopState.numberOfCycles'.

	// private Set<Example> negExamplesUsedAsSeeds;

	// The following assist N-fold cross validation.
	// private int numberOfFolds = 1;

	// private Gleaner[] gleaners;
	// private Theory[] theories;
    // private String currentGleanerFileName = null;
	private List<Example> evalSetPosExamples = new ArrayList<Example>(1);
	private List<Example> evalSetNegExamples = new ArrayList<Example>(1);
//	private List<Example> allPosExamples;
//	private List<Example> allNegExamples;

	// These two allow one to randomly select a subset of the modes for each cycle.  (Added by JWS 6/24/10.)
	private Set<PredicateNameAndArity> holdBodyModes;
	public double randomlySelectWithoutReplacementThisManyModes = -1; // If in (0, 1), then is a FRACTION of the modes. If negative, then do not sample.	

    public boolean waitWhenBodyModesAreEmpty = true;

    private ActiveAdvice createdActiveAdvice = null;

	public ILPouterLoop(String workingDir, String[] args, SearchStrategy strategy, ScoreSingleClause scorer) throws IOException {
		this(workingDir, null, args, strategy, scorer, new Gleaner(), new DefaultHornClauseContext(new HandleFOPCstrings()), false, false);
	}
    public ILPouterLoop(String workingDir, String[] args) throws IOException {
        this(workingDir, null, args, new Gleaner(), new HandleFOPCstrings());
    }
    public ILPouterLoop(String workingDir, String[] args, HandleFOPCstrings stringHandler) throws IOException {
        this(workingDir, null, args, new Gleaner(), stringHandler);
    }

    public ILPouterLoop(String workingDir, String[] args, HornClauseContext context) throws IOException {
        this(workingDir, null, args, new Gleaner(), context);
    }

    public ILPouterLoop(String workingDir, String prefix, String[] args, SearchMonitor monitor, HandleFOPCstrings stringHandler) throws IOException {
        this(workingDir, prefix, args, monitor, new DefaultHornClauseContext(stringHandler));
    }

    public ILPouterLoop(String workingDir, String prefix, String[] args, SearchMonitor monitor, HandleFOPCstrings stringHandler, boolean deferLoadingExamples) throws IOException {
        this(workingDir, prefix, args, monitor, new DefaultHornClauseContext(stringHandler), deferLoadingExamples);
    }

    public ILPouterLoop(String workingDir, String prefix, String[] args, 
    					SearchStrategy strategy, ScoreSingleClause scorer, SearchMonitor monitor, 
    	                HornClauseContext context, boolean useRRR, boolean deferLoadingExamples) throws IOException {
        this(workingDir, prefix, 
                getBufferedReaderFromString(ILPouterLoop.getInputArgWithDefaultValue(args, 0, "pos.txt")),
                getBufferedReaderFromString(ILPouterLoop.getInputArgWithDefaultValue(args, 1, "neg.txt")),
                getBufferedReaderFromString(ILPouterLoop.getInputArgWithDefaultValue(args, 2, "bk.txt")),
                getBufferedReaderFromString(ILPouterLoop.getInputArgWithDefaultValue(args, 3, "facts.txt")),
                strategy, scorer, monitor, context, useRRR, deferLoadingExamples);
    }

    public ILPouterLoop(String workingDir, String prefix, String[] args, SearchMonitor monitor, HornClauseContext context) throws IOException {
        this(workingDir, prefix, args, monitor, context, false);
    }

    public ILPouterLoop(String workingDir, String prefix, String[] args, SearchMonitor monitor, HornClauseContext context, boolean deferLoadingExamples) throws IOException {
        this(workingDir, prefix,
                getBufferedReaderFromString(ILPouterLoop.getInputArgWithDefaultValue(args, 0, "pos.txt")),
                getBufferedReaderFromString(ILPouterLoop.getInputArgWithDefaultValue(args, 1, "neg.txt")),
                getBufferedReaderFromString(ILPouterLoop.getInputArgWithDefaultValue(args, 2, "bk.txt")),
                getBufferedReaderFromString(ILPouterLoop.getInputArgWithDefaultValue(args, 3, "facts.txt")),
                monitor, context, deferLoadingExamples);

        if (args.length >= 5) {
            this.innerLoopTask.setRelevanceFile(args[4]);
        }
    }

    public ILPouterLoop(String workingDir, String prefix, Reader posExamplesReader, Reader negExamplesReader, Reader backgroundReader, Reader factsReader, SearchMonitor monitor, HandleFOPCstrings stringHandler) {
                        this(workingDir, prefix, posExamplesReader, negExamplesReader, backgroundReader, factsReader, monitor, new DefaultHornClauseContext(stringHandler, new FileParser(stringHandler, workingDir)), false);
    }
    public ILPouterLoop(String workingDir, String prefix, Reader posExamplesReader, Reader negExamplesReader, Reader backgroundReader, Reader factsReader,
		    			SearchMonitor monitor, HornClauseContext context, boolean deferLoadingExamples) {
    	this(workingDir, prefix, posExamplesReader, negExamplesReader, backgroundReader, factsReader,
    		 new BestFirstSearch(), new ScoreSingleClauseByAccuracy(), monitor, context, false, false);
    }
	public ILPouterLoop(String workingDir, String prefix, Reader posExamplesReader, Reader negExamplesReader, Reader backgroundReader, Reader factsReader,
					    SearchStrategy strategy, ScoreSingleClause scorer, SearchMonitor monitor, HornClauseContext context, boolean useRRR, boolean deferLoadingExamples) {

       outerLoopState = new ILPouterLoopState();
       
       setWorkingDirectory(workingDir);

       if ( prefix == null ) {
            // Oops, prefix was null.  This just means we probably used the shorter constructors.
            // Just extract it from the working directory name.
            prefix = new CondorFile(workingDirectory).getName();
        }

        setPrefix(prefix);

		if (LearnOneClause.debugLevel >= 0) { Utils.println("\n% Welcome to the " + systemName + " ILP/SRL systems.\n"); }

        // LearnOneClause performs the inner loop of ILP.
		// TODO maybe we should send in the full outer loop instance (ie, this).

		innerLoopTask = new LearnOneClause(workingDir, prefix, posExamplesReader, negExamplesReader, backgroundReader, factsReader, strategy, scorer, monitor, context, deferLoadingExamples);
		
		if (outerLoopState.isFlipFlopPosAndNegExamples()) {
			Utils.writeMe("This needs to be debugged.");
			innerLoopTask.flipFlopPosAndNegExamples();
		}
		
//		if (numberOfFolds > 1) {
//			gleaners = new Gleaner[numberOfFolds];
//			theories = new Theory[ numberOfFolds];
//		}
	      
        if (monitor instanceof Gleaner) {
            setGleaner((Gleaner) monitor);
        }
        else if (monitor != null) {
            Utils.waitHere("The Search Monitor is not an instance of Gleaner: " + monitor);
        } 

        setRRR(useRRR);
	}
	
	private String getFoldInfoString() {
		if (getCurrentFold() == -1) { return ""; }
		return "_fold" + getCurrentFold();
	}

    public void setCurrentFold(int currentFold) {
        outerLoopState.setCurrentFold(currentFold);
    }

    public int getCurrentFold() {
        return outerLoopState.getCurrentFold();
    }
	
	private static BufferedReader getBufferedReaderFromString(String string) throws IOException {
		if (string == null) { return null; }
		return new NamedReader(new CondorFileReader(string), string);
	}
	
	// Needed to get around need that "constructor call must be the first statement in a constructor."
	private static String getInputArgWithDefaultValue(String[] args, int N, String defaultString) {
		Utils.println("\n% getInputArgWithDefaultValue: args=" + Arrays.asList(args).toString() + "\n%  for N=" + N + ": args[N]=" + args[N]);
		return (args.length < (N + 1) ? defaultString : args[N]);
	}

	// In standard ILP, there are two common ways of dealing with previously covered positive examples: count them 100% or not at all.
	// This method allows those two settings to be chosen.  Notice that the default values above might differ from either of these two.
    //
	public void countPreviouslyCoveredExamples(boolean countThem) {
        throw new UnsupportedOperationException("This functionality has been removed.  See comments in variable declaration section");
//		if (countThem) {
//			weightOnCoveredPosExample = 1.0;
//			weightOnCoveredNegExample = 1.0;
//		}
//		else {
//			weightOnCoveredPosExample = 0.0;
//			weightOnCoveredNegExample = 1.0; // Still want to be penalized for covering them (though one might argue that if one rule covers it is is WORSE for another to do so, since a 'voting' method cannot overcome this false positive as easily).
//		}
	}

	// Set the sequence of positive seeds to use. This only allows for ONE positive seed per inner-loop invocation.
	// When the list is exhausted, seeds are randomly selected.
	public void setSequenceOfSeedsToUse(int[] posSeedIndices, boolean ifSeedAlreadyCoveredSkipOverIt) {
		  setPosSeedIndicesToUse(posSeedIndices);
		  setIndexIntoPosSeedArray(0);
		  setLengthPosSeedArray(getPosSeedIndicesToUse().length);
	}

	public void setMinFractionOfPosToCoverWithTheory(double fraction) {
		if (fraction <= 0.0 || fraction > 1.0) {
			Utils.error("Fraction (" + fraction + ") must be in (0,1].");
		}
		minFractionOfPosCoveredToStop = fraction;
	}

	public void setMaxNumberOfInnerLoopCycles(int count) {
		if (count <= 0) {
			Utils.error("Count (" + count + ") must be a positive integer.");
		}
		maxNumberOfCycles = count;
	}

	public void setMinPosCoverageOfAcceptableClause(int count) {
		if (count < 0) {
			Utils.error("Count (" + count + ") must be a non-negative integer.");
		}
		  innerLoopTask.setMinPosCoverage(count);
	}

	public void setMinPrecisionOfAcceptableClause(double precision) {
		if (precision < 0.0 || precision > 1.0) {
			Utils.error("Min precision (" + precision + ") must be in [0,1].");
		}
		innerLoopTask.setMinPrecision(precision);
	}
	public double getMinPrecisionOfAcceptableClause() {
		return innerLoopTask.getMinPrecision();
	}

	public void setMaxRecallOfAcceptableClause(double recall) {
		if (recall < 0.0 || recall > 1.0) {
			Utils.error("Max recall (" + recall + ") must be in [0,1].");
		}
		innerLoopTask.setMaxRecall(recall);
	}
	public double getMaxRecallOfAcceptableClause() {
		return innerLoopTask.getMaxRecall();
	}

	public void setMaxBodyLength(int maxBodyLength) {
		if (maxBodyLength < 0) {
			Utils.error("Length (" + maxBodyLength + ") must be a non-negative integer.");
		}
		// Recall that in tree-structured runs, the length of all parent nodes is also included here.
		innerLoopTask.maxBodyLength = Math.min(maxBodyLength, learningTreeStructuredTheory ? maxTreeDepthInLiterals : Integer.MAX_VALUE);
	 //	Utils.waitHere("setMaxBodyLength = " + innerLoopTask.maxBodyLength + "  maxBodyLength = " + maxBodyLength + "  learningTreeStructuredTheory = " + learningTreeStructuredTheory);
	}

	private boolean isaGoodPosSeed(int index) { // If good, then set it as the positive seed to use.
		if (index < 0 || index >= getNumberOfPosExamples()) {
			return false;
		} // Simply skip over indices that are out of bounds.
		Example chosenExample = innerLoopTask.getPosExamples().get(index);
		if ((innerLoopTask.allowPosSeedsToBeReselected || getSeedPosExamplesUsed() == null || !getSeedPosExamplesUsed().contains(chosenExample)) && // Make sure that this wasn't previously a seed.
			!getCoveredPosExamples().contains(chosenExample)) { // Make sure this is an uncovered seed.
			int[] posSeeds = new int[1];
			posSeeds[0] = index;
			if (LearnOneClause.debugLevel > -10) { Utils.println(MessageType.ILP_OUTERLOOP, "% Have selected pos example #" + Utils.comma(index) + " as the next seed: " + chosenExample); }
			innerLoopTask.selectTheseSeedsByIndex(posSeeds, null, getSeedPosExamplesUsed(), getSeedNegExamplesUsed()); // Use no negative seeds.
			return true;
		}
		return false;
	}
		
	private boolean collectMultipleSeeds() {
		if (numberPosSeedsToUse < 1) { numberPosSeedsToUse = 1; }
		if (numberNegSeedsToUse < 0) { numberNegSeedsToUse = 0; }
		
		// TODO - figure out how to report wrt to the flip-flop state.
		if (numberPosSeedsToUse > getNumberOfPosExamples()) { Utils.warning("% Have only " + Utils.comma(getNumberOfPosExamples()) + " positive examples, so cannot choose " + Utils.comma(numberPosSeedsToUse) + " of them."); }
		if (numberNegSeedsToUse > getNumberOfNegExamples()) { Utils.warning("% Have only " + Utils.comma(getNumberOfNegExamples()) + " negative examples, so cannot choose " + Utils.comma(numberNegSeedsToUse) + " of them."); }
		
		numberPosSeedsToUse = Math.min(numberPosSeedsToUse, getNumberOfPosExamples());
		numberNegSeedsToUse = Math.min(numberNegSeedsToUse, getNumberOfNegExamples());
		
		int[] posSeeds = new int[numberPosSeedsToUse];
		int[] negSeeds = new int[numberNegSeedsToUse];
		
		int posCounter = 0;
		int negCounter = 0;
		Set<Integer> posChosen = new HashSet<Integer>(4);
		Set<Integer> negChosen = new HashSet<Integer>(4);
		
		// Could be really slow if selecting nearly all of the examples, but we're limiting this to 10X tries, so don't worry about it.
		if (innerLoopTask.allowPosSeedsToBeReselected) {
			int counter = 0; // Put a limit on the number of cycles here.
			while (posCounter < numberPosSeedsToUse && counter++ < 10 * numberPosSeedsToUse) {
				int index = Utils.random0toNminus1(getNumberOfPosExamples());
				if (!posChosen.contains(index)) {
					posChosen.add(index);
					posSeeds[posCounter++] = index;
				}
			}			
		}
		// It still looking, grab in order.
		if (posCounter < numberPosSeedsToUse) {
			int i = 0;
			// Use the 1.1 to handle the case of not getting enough due to sampling effects.  This fraction is ratio of SEEDS_NEEDED over SEEDS_TO_SELECT_FROM.
			double fraction = 1.1 * (numberPosSeedsToUse - posCounter) / (double) (innerLoopTask.getPosExamples().size() - getCoveredPosExamples().size() - posCounter);
			for (Example pos : innerLoopTask.getPosExamples()) { // Would be nice to more cleanly randomly walk through the examples, but after the first cycle, will at least skip those already covered.
				if (Utils.random() < fraction && !getCoveredPosExamples().contains(pos) && !posChosen.contains(i)) {
					posChosen.add(i);
					posSeeds[posCounter++] = i;
					if (posCounter >= numberPosSeedsToUse) { break; }
				}
				i++;
			}
		}
		
		if (innerLoopTask.allowNegSeedsToBeReselected) {
			int counter = 0;
			while (negCounter < numberNegSeedsToUse && counter++ < 10 * numberNegSeedsToUse) {
				int index = Utils.random0toNminus1(getNumberOfNegExamples());
				if (!negChosen.contains(index)) {
					negChosen.add(index);
					negSeeds[posCounter++] = index;
				}
			}			
		}
		if (negCounter < numberNegSeedsToUse) {
			int i = 0; // See comment above.
			double fraction = 1.1 * (numberNegSeedsToUse - negCounter) / (double) (innerLoopTask.getNegExamples().size() - outerLoopState.getNegExamplesUsedAsSeeds().size() - negCounter);
			for (Example neg : innerLoopTask.getNegExamples()) {
				if (Utils.random() < fraction && !getNegExamplesUsedAsSeeds().contains(neg) && !negChosen.contains(i)) {
					negChosen.add(i);
					negSeeds[negCounter++] = i;
					getNegExamplesUsedAsSeeds().add(neg); // TODO - when done using all the negative seeds, should reset to use all again. 
					if (negCounter >= numberNegSeedsToUse) { break; }
				}
				i++;
			}
		}
		// If arrays still not full, shorten them.
		if (posCounter < numberPosSeedsToUse) {
			int[] posSeedsShorter = new int[Math.max(0, posCounter)];
            System.arraycopy(posSeeds, 0, posSeedsShorter, 0, posCounter);
			posSeeds = posSeedsShorter;
		}
		if (negCounter < numberNegSeedsToUse) {
			int[] negSeedsShorter = new int[Math.max(0, negCounter)];
            System.arraycopy(negSeeds, 0, negSeedsShorter, 0, negCounter);
			negSeeds = negSeedsShorter;
			   getNegExamplesUsedAsSeeds().clear(); // If ran short on negative seeds, allow old ones to be used again (BUG: should add more now, but live with one cycle with a shortage of negative seeds).
		}
		if (LearnOneClause.debugLevel > -1) {
			int maxToPrint = 100;
			if (posSeeds.length > 0) { Utils.print("\n% Have these " + Utils.comma(posSeeds.length) + " positive seeds:"); for (int i = 0; i < Math.min(maxToPrint, posSeeds.length); i++) Utils.print(" " + posSeeds[i]); if (posSeeds.length > maxToPrint) Utils.println(" ..."); else Utils.println(""); }
			if (negSeeds.length > 0) { Utils.print("\n% Have these " + Utils.comma(negSeeds.length) + " negative seeds:"); for (int i = 0; i < Math.min(maxToPrint, negSeeds.length); i++) Utils.print(" " + negSeeds[i]); if (negSeeds.length > maxToPrint) Utils.println(" ..."); else Utils.println(""); }
		}
		innerLoopTask.selectTheseSeedsByIndex(posSeeds, negSeeds, false, getSeedPosExamplesUsed(), getSeedNegExamplesUsed()); // OK if reused (e.g., if not covered or if a negative seed).
		return (posCounter > 0); // Need at least one positive seed.
	}

    /** Executes the outer ILP loop.
     *
     * This will attempt to find one or more clauses that cover the positive and
     * negative examples.  executeOuterLoop will completely reset the search and
     * start from scratch.
     *
     * @return The learned theory.
     * @throws edu.wisc.cs.will.stdAIsearch.SearchInterrupted Thrown if the search is interrupted prior
     * to completion.
     */
	public Theory executeOuterLoop() throws SearchInterrupted {
        resetAll();
        ILPSearchAction action = innerLoopTask.fireOuterLoopStarting(this);

        if (action == ILPSearchAction.PERFORM_LOOP) {

            // Try to resume the run in the middle if there is a checkpoint file...
            if (isCheckpointEnabled()) {
                boolean checkpointSuccessful = readCheckpoint();
                if ( checkpointSuccessful ) {
                    Utils.println("\nRestarting ILP Outer loop from state in checkpoint file " + getCheckpointFileName() + "...");
                }
            }

            setupAdvice();

            // If no body modes, no need to run.
            if (Utils.getSizeSafely(innerLoopTask.bodyModes) < 1) {
                if ( waitWhenBodyModesAreEmpty ) {
                    Utils.waitHere("Have no body modes.");
                }
                else {
                    Utils.warning("Have no body modes.");
                }
                return new Theory(innerLoopTask.getStringHandler());
            }

            boolean stoppedBecauseNoMoreSeedsToTry         = false;
            boolean stoppedBecauseTreeStructuredQueueEmpty = false;

            if (learningTreeStructuredTheory && outerLoopState.queueOfTreeStructuredLearningTasksIsEmpty()) {
                stoppedBecauseTreeStructuredQueueEmpty = true;
                Utils.waitHere("Have learningTreeStructuredTheory=true but stack of tasks is empty (or equal to null).");
            }

            if (LearnOneClause.debugLevel > 1) {
                reportOuterLooperStatus("\n% STARTING executeOuterLoop()");
                //Utils.waitHere();
            }

            SingleClauseNode savedBestNode = null; // When learning tree-structured models, we need to remember the node learned at the parent.
            long start = 0;
            boolean foundUncoveredPosSeed = false;
            while (!stoppedBecauseNoMoreSeedsToTry && !stoppedBecauseTreeStructuredQueueEmpty &&
                   getNumberOfLearnedClauses()  < maxNumberOfClauses &&
                   getNumberOfCycles()          < maxNumberOfCycles  &&
                   getFractionOfPosCovered()    < minFractionOfPosCoveredToStop &&
                   getTotal_nodesConsidered()   < max_total_nodesExpanded &&
                   getTotal_nodesCreated()      < max_total_nodesCreated  &&
                   getClockTimeUsedInMillisec() < getMaximumClockTimeInMillisec() &&
                   canStillMeetPrecisionRecallAccuracyF1specs(false)              &&
                   true
                   ) {

                start = System.currentTimeMillis();
                if (learningTreeStructuredTheory) {
                    //Utils.println("% innerLoopTask.resetAllForReal(before calling): " + Utils.reportSystemInfo());
                    innerLoopTask.resetAllForReal(); // Clear OPEN and CLOSED (and other things).
                    //Utils.println("% innerLoopTask.resetAllForReal(after calling):  " + Utils.reportSystemInfo());
                    outerLoopState.setCurrentTreeLearningTask(outerLoopState.popQueueOfTreeStructuredLearningTasks()); // Set in outerloopState class instead of here?
                    savedBestNode = outerLoopState.getCurrentTreeLearningTask().getCreatingNode();
                    clearSeedPosExamplesUsed();
                    clearSeedNegExamplesUsed();
                    innerLoopTask.setPosExamples(   outerLoopState.getCurrentTreeLearningTask().getPosExamples()); // Need to do these AFTER the setMinPosCoverage since that might be a fraction.
                    innerLoopTask.setNegExamples(   outerLoopState.getCurrentTreeLearningTask().getNegExamples());
                    innerLoopTask.setMinPosCoverage(outerLoopState.getOverallMinPosWeight()); // Even when we have fewer examples, we want the minPosWeight to be that from the first call.
                    
                    if (savedBestNode != null) { // Have to recompute this because the examples have changed.
                        Utils.println("\n% Working on expanding this node: '" + savedBestNode + "'");
                        ((LearnOneClause)savedBestNode.task).currentStartingNode = savedBestNode.getStartingNodeForReset(); // Only setting this while resetting the score for savedBestNode.
                        savedBestNode.resetAssumingAllExamplesCovered();
                        savedBestNode.setDontAddMeToOPEN(false);
                        innerLoopTask.scorer.scoreThisNode(savedBestNode);
                        setMaxBodyLength(Math.min(maxTreeDepthInLiterals, savedBestNode.bodyLength() + maxNumberOfLiteralsAtAnInteriorNode));
                    } else {
                        setMaxBodyLength(Math.min(maxTreeDepthInLiterals, maxNumberOfLiteralsAtAnInteriorNode));
                    }
                    if (savedBestNode != null) {
                   // 	Utils.waitHere("Setting starting node as:" + savedBestNode.getClause());
                    }
                    innerLoopTask.currentStartingNode = savedBestNode;
                }

                setNumberOfCycles( getNumberOfCycles() + 1 );

                Stopwatch stopwatch = new Stopwatch();

                if (LearnOneClause.debugLevel > 1) { Utils.println(MessageType.ILP_OUTERLOOP,"\n% ********************\n% Outer Loop Iteration #" + Utils.comma(getNumberOfCycles()) + " with strategy=" + (isRRR() ? "RRR" : "heuristic") + " (created a total of " + Utils.comma(getTotal_nodesCreated()) + " clauses so far and explored " + Utils.comma(getTotal_nodesConsidered()) + ")"); }
                if (LearnOneClause.debugLevel > 1 && getMaximumClockTimeInMillisec() < Long.MAX_VALUE) {
                                                   // Use 'err' here so we see these.
                                                   Utils.printlnErr(MessageType.ILP_OUTERLOOP,"%  The outer looper (iteration #" + Utils.comma(getNumberOfCycles()) + ") has been running " + Utils.convertMillisecondsToTimeSpan(getClockTimeUsedInMillisec()) + " and has " + Utils.convertMillisecondsToTimeSpan(getMaximumClockTimeInMillisec() - getClockTimeUsedInMillisec()) + " remaining."); }
                if (LearnOneClause.debugLevel > 1) { Utils.println(MessageType.ILP_OUTERLOOP,"%  [Min precision = " + Utils.truncate(innerLoopTask.minPrecision, 3) + ", (weighted) " + (innerLoopTask.regressionTask ? "minPosCov" : "minCover") + " = " + Utils.truncate(innerLoopTask.getMinPosCoverage(), 2) + (innerLoopTask.regressionTask ? "" : ", and (weighted) maxNegCov = " + Utils.truncate(innerLoopTask.getMaxNegCoverage(), 2)) + "]\n% ********************"); }

                if (true) { // WE NEED TO PICK A NEW SET OF SEEDS EACH TIME SINCE SEEDS CHOSEN AT THE ROOT WILL FOLLOW VARIOUS PATHS THROUGH THE TREE.  if (!foundUncoveredPosSeed || !learningTreeStructuredTheory) { // If tree-structured task, we want to use the same seeds for the full tree (otherwise maybe no [new] seeds reach the current interior node).
                    // Specify the specific seeds to use if requested.
                    foundUncoveredPosSeed = false;
                    if (numberPosSeedsToUse > 1 || numberNegSeedsToUse > 0) { foundUncoveredPosSeed = collectMultipleSeeds(); }

                    while (!foundUncoveredPosSeed && getPosSeedIndicesToUse() != null && getIndexIntoPosSeedArray() < getLengthPosSeedArray()) {
                            int index = getPosSeedIndicesToUse()[getIndexIntoPosSeedArray()]; // Increment the counter so that walking down this array.
                            setIndexIntoPosSeedArray(getIndexIntoPosSeedArray()+1);
                            foundUncoveredPosSeed = isaGoodPosSeed(index);
                    }

                    // Otherwise randomly select one positive seed be used.
                    int tries = 0;
                    while (!foundUncoveredPosSeed && tries++ < 1000) { // 1000 might be low if a very large number of pos ex's, but if hard to find, grabbing seeds in numerical order (next step) should be fine.
                        int index = Utils.random0toNminus1(getNumberOfPosExamples());
                        foundUncoveredPosSeed = isaGoodPosSeed(index);
                    }
                    // If still no luck, walk through in order until an uncovered seed is found. Should always be able to find an uncovered seed because we know fraction covered less than 1.0 ...
                    if (!foundUncoveredPosSeed) {
                        int randomOffset = Utils.random0toNminus1(getNumberOfPosExamples());  // Start at a random location in the array, and do a "wrap around" walk through the values.
                        for (int index = 0; index < getNumberOfPosExamples(); index++) {
                            int indexToUse = (randomOffset + index)	% getNumberOfPosExamples();
                            foundUncoveredPosSeed = isaGoodPosSeed(indexToUse);
                            if (LearnOneClause.debugLevel > 2) { Utils.println("  considering pos seed #" + indexToUse + ": acceptability=" + foundUncoveredPosSeed); }
                            if (foundUncoveredPosSeed) { break; }
                        }
                    }
                }

                if (!foundUncoveredPosSeed) { // Since there is a minimum coverage on the best clause, some seeds won't be covered and we might run out of seeds before meeting some other termination criterion.
                    stoppedBecauseNoMoreSeedsToTry = true;
                } else {
                    // Do the ILP inner loop.
                    //    First clear Gleaner and set up a new Gleaner set (i.e., will keep best rules PER CYCLE).
                    Gleaner theGleaner = (Gleaner) innerLoopTask.searchMonitor;
                    theGleaner.clearBestNode();

                    innerLoopTask.caller     = this;
                    innerLoopTask.callerName = "outerLoop #" + getNumberOfCycles() + getFoldInfoString();
                    theGleaner.setCurrentMarker(innerLoopTask.callerName);
                    if (!learningTreeStructuredTheory) { innerLoopTask.stringHandler.resetVarCounters(); } // When learning a tree-structured theory, we need a consistent set of variables.
                    innerLoopTask.checkIfAcceptableClausePossible();

                    if (getMaximumClockTimeInMillisec() < Long.MAX_VALUE) {
                        double denominator = 1.0; // If there is a time limit, leave some for later cycles, but allow at least 25% of the time for this one.
                        if (maxNumberOfCycles > 1 && getMaximumClockTimeInMillisec() != Long.MAX_VALUE) { denominator = Math.max(1.0, Math.min(4.0, maxNumberOfCycles / (1 + getNumberOfCycles()))); }
                        long innerLoopTimeLimit = (long) (getTimeAvailableInMillisec() / denominator);
                        if (LearnOneClause.debugLevel > 1) { Utils.printlnErr("%  The inner looper is being allocated " + Utils.convertMillisecondsToTimeSpan(innerLoopTimeLimit) + "."); }
                        innerLoopTask.setMaximumClockTimePerIterationInMillisec(innerLoopTimeLimit);
                    } else {
                        innerLoopTask.setMaximumClockTimePerIterationInMillisec(getMaximumClockTimeInMillisec());
                    }

                    ((ChildrenClausesGenerator) innerLoopTask.childrenGenerator).countOfPruningDueToVariantChildren = 0;

                    // If we are going to be sampling the modes, make a copy of the full set.  AND RESET WHEN DONE.
                    if (randomlySelectWithoutReplacementThisManyModes > 0 && holdBodyModes == null) {
                        holdBodyModes = innerLoopTask.getBodyModes();

                        if (randomlySelectWithoutReplacementThisManyModes < 1) { // Interpret as a FRACTION.  TODO - should we keep the fraction?  Seems not worth the trouble.
                            randomlySelectWithoutReplacementThisManyModes = Math.round(randomlySelectWithoutReplacementThisManyModes * Utils.getSizeSafely(holdBodyModes));
                        }
                    }
                    if (randomlySelectWithoutReplacementThisManyModes > 0 && randomlySelectWithoutReplacementThisManyModes  < Utils.getSizeSafely(holdBodyModes)) {
                        Set<PredicateNameAndArity> newSetOfBodyModes = new HashSet<PredicateNameAndArity>((int) randomlySelectWithoutReplacementThisManyModes);
                        int bodyModeSize = Utils.getSizeSafely(holdBodyModes);
                        // If we are getting almost all of the body nodes, we really should make a copy then DELETE entries until small enough.  TODO.
                        int counter = 0;
                        while (Utils.getSizeSafely(newSetOfBodyModes) < randomlySelectWithoutReplacementThisManyModes ) {
                            int                   index = Utils.random0toNminus1(bodyModeSize);
                            PredicateNameAndArity pName = Utils.getIthItemInCollectionUnsafe(holdBodyModes, index);

                            newSetOfBodyModes.add(pName); // If a duplicate, won't be added.
                            if (++counter > 10 * randomlySelectWithoutReplacementThisManyModes) { Utils.waitHere("Stuck in an infinite loop?  randomlySelectWithoutReplacementThisManyModes=" + Utils.comma(randomlySelectWithoutReplacementThisManyModes)); counter = 0; }
                        }
                        innerLoopTask.setBodyModes(newSetOfBodyModes);
                    }

                    // If we are learning a tree-structured theory, then we continue where we left off.
                    if (isRRR()) {
                        innerLoopTask.performRRRsearch(learningTreeStructuredTheory ? savedBestNode : null);
                    } else {
                        SearchResult sr = innerLoopTask.performSearch(learningTreeStructuredTheory ? savedBestNode : null);
                        innerLoopTask.needToCheckTheAdviceProcessor = false; // No need to do this at least until this "outer looper" is done.
                        if (false) { Utils.println("Search result: " + sr); }
                    }

                    // Utils.println(innerLoopTask.reportSearchStats());
                    // Want limits on (and statistics about) the full ILP search as well.
                    setTotal_nodesConsidered(getTotal_nodesConsidered() + innerLoopTask.getNodesConsidered());
                    setTotal_nodesCreated(   getTotal_nodesCreated()    + innerLoopTask.getNodesCreated());
                    setTotal_nodesNotAddedToOPENsinceMaxScoreTooLow(    getTotal_nodesNotAddedToOPENsinceMaxScoreTooLow()     + innerLoopTask.nodesNotAddedToOPENsinceMaxScoreTooLow);
                    setTotal_nodesRemovedFromOPENsinceMaxScoreNowTooLow(getTotal_nodesRemovedFromOPENsinceMaxScoreNowTooLow() + innerLoopTask.nodesRemovedFromOPENsinceMaxScoreNowTooLow);
                    setTotal_countOfPruningDueToVariantChildren(getTotal_countOfPruningDueToVariantChildren() + ((ChildrenClausesGenerator) innerLoopTask.childrenGenerator).countOfPruningDueToVariantChildren);
                    // Report what happened (TODO have an output 'results' file).
                    SingleClauseNode bestNode = theGleaner.bestNode;
                    
                    Utils.println("\n% The best node found: " + bestNode); // TEMP
                    
                    if (bestNode != null && bestNode != savedBestNode) { // Also need to check to make sure we didn't simply return the previous root when doing tree-structured learning.
                        Utils.println("\n% The best node found: " + bestNode);
                        List<Example> coveredPosExamplesThisCycle = innerLoopTask.collectPosExamplesCovered(bestNode);
                        List<Example> coveredNegExamplesThisCycle = innerLoopTask.collectNegExamplesCovered(bestNode);
                        int newlyCoveredPosExamples = 0;
                        int newlyCoveredNegExamples = 0;
                        int coveredPosExamplesCount = Utils.getSizeSafely(coveredPosExamplesThisCycle);
                        int coveredNegExamplesCount = Utils.getSizeSafely(coveredNegExamplesThisCycle);

                        if (coveredPosExamplesCount > 0) {
                            for (Example ex : coveredPosExamplesThisCycle) {
                                // Utils.println("   covered pos: " + ex);
                                if (!getCoveredPosExamples().contains(ex)) {
                                    if (!learningTreeStructuredTheory) { // When learning trees we don't need to count coverings by possibly overlapping rules.
                                        getCoveredPosExamples().add(ex);
                                        setNumberOfPosExamplesCovered(getNumberOfPosExamplesCovered() + 1); // An awkward way to increment ...
                                    }
                                    newlyCoveredPosExamples++;
                                }
                            }
                        }
                        if (coveredNegExamplesCount > 0) {
                            for (Example ex : coveredNegExamplesThisCycle) {
                                // Utils.println(" covered neg: " + ex);
                                if (!getCoveredNegExamples().contains(ex)) {
                                    if (!learningTreeStructuredTheory) {  // See comment above.
                                        getCoveredNegExamples().add(ex);
                                        setNumberOfNegExamplesCovered(getNumberOfNegExamplesCovered() + 1); // An awkward way to increment ...
                                    }
                                    newlyCoveredNegExamples++;
                                }
                            }
                        }

                        // The following line of code allowed covered examples to be reweighted on the fly during theory search.
                        //
                        // While an interesting idea, there are all sorts of problems the way you implemented it
                        // (even in the old map-based weight implementation), the biggest being that you never retain
                        // their original weights, so post-learning scoring would have been wacky.  Covered examples
                        // would have been down weighted in the final coverage scores...this could happen on both
                        // negative and positive examples, so it would be hard to say exactly what the effect would
                        // be, but it wouldn't have been the expected final score.
                        //
                        // I am commenting it out for now, but we can re-implement later if desired.
                        // -Trevor

                        //innerLoopTask.setExampleWeights((Utils.diffDoubles(weightOnCoveredPosExample, 1.0) ? getCoveredPosExamples() : null),
                        //					              (Utils.diffDoubles(weightOnCoveredNegExample, 1.0) ? getCoveredNegExamples() : null));

                        if (coveredPosExamplesCount < 1) {
                            Utils.warning("Have a bestNode that covers no positive examples.  That shouldn't happen.  Best node = " + bestNode);
                        }
                        setNumberOfLearnedClauses(getNumberOfLearnedClauses() + 1);
                        Clause newClause = new LearnedClause(innerLoopTask, bestNode, getNumberOfCycles(),
                                                             getNumberOfPosExamplesCovered(), coveredPosExamplesCount, newlyCoveredPosExamples,
                                                             getNumberOfPosExamples(), getNumberOfNegExamplesCovered(),  coveredNegExamplesCount,
                                                             newlyCoveredNegExamples, getNumberOfNegExamples());

                        if (learningTreeStructuredTheory) {
                            if (!innerLoopTask.constantsAtLeaves) { Utils.error("Have not yet implemented constantsAtLeaves = false."); }

                            if (LearnOneClause.debugLevel > 1) {
                                Utils.println("\n% New full clause: "  + newClause);
                                Utils.println("\n% New LOCAL clause: " + bestNode.getLocallyAddedClause() + "\n");
                            }

                            TreeStructuredLearningTask       currentTask  = outerLoopState.getCurrentTreeLearningTask();
                            TreeStructuredTheoryInteriorNode interiorNode = currentTask.getNode();
                            interiorNode.setSearchNodeThatLearnedTheClause(bestNode); // Be sure to set this before the next call.
                            interiorNode.setNodeTestFromFullNodeTest(newClause);
                            // Set the task used to learn this node.
                            bestNode.setStartingNodeForReset(innerLoopTask.currentStartingNode);
                            if (LearnOneClause.debugLevel > -1) {
                                Utils.println("\n% Expanding node at Level " + interiorNode.getLevel() + " with score = " + Utils.truncate(currentTask.getScore(), 3) + ".\n% Will extend: " + interiorNode.getSearchNodeThatLearnedTheClause());
                            }

                            boolean atMaxDepth = (interiorNode.getLevel() >= maxTreeDepthInInteriorNodes);
                            
                            TreeStructuredTheoryNode trueBranch;
                            TreeStructuredTheoryNode falseBranch;
                            boolean goodEnoughFitTrueBranch  = atMaxDepth || bestNode.acceptableScoreTrueBranch( outerLoopState.maxAcceptableNodeScoreToStop);
                            boolean goodEnoughFitFalseBranch = atMaxDepth || bestNode.acceptableScoreFalseBranch(outerLoopState.maxAcceptableNodeScoreToStop);

                            List<Example> trueBranchPosExamples  = null;
                            List<Example> falseBranchPosExamples = null;
                            List<Example> trueBranchNegExamples  = null;
                            List<Example> falseBranchNegExamples = null;

                            double wgtedCountTrueBranchPos  = 0.0;
                            double wgtedCountTrueBranchNeg  = 0.0;
                            double wgtedCountFalseBranchPos = 0.0;
                            double wgtedCountFalseBranchNeg = 0.0;

                            List<Example> posEx = currentTask.getPosExamples();
                            List<Example> negEx = currentTask.getNegExamples();

                            // Since we are collecting 'extra labels' for leaf nodes, we need always to collect examples.
                            if (posEx != null) {
                                trueBranchPosExamples  = (false && goodEnoughFitTrueBranch  ? null : new ArrayList<Example>(8));
                                falseBranchPosExamples = (false && goodEnoughFitFalseBranch ? null : new ArrayList<Example>(8));
                                for (Example ex : posEx) {
                                    if (bestNode.matchesThisExample(ex, true)) {
                                        if (true || !goodEnoughFitTrueBranch)  { trueBranchPosExamples.add(ex);  }
                                        wgtedCountTrueBranchPos += ex.getWeightOnExample();
                                    } else {
                                        if (true || !goodEnoughFitFalseBranch) { falseBranchPosExamples.add(ex); }
                                        wgtedCountFalseBranchPos += ex.getWeightOnExample();
                                    }
                                }
                            }
                            // Since we are collecting 'extra labels' for leaf nodes, we need always to collect examples.
                            if (negEx != null) {
                                trueBranchNegExamples  = (false && goodEnoughFitTrueBranch  ? null : new ArrayList<Example>(8));
                                falseBranchNegExamples = (false && goodEnoughFitFalseBranch ? null : new ArrayList<Example>(8));
                                for (Example ex : negEx) {
                                    if (bestNode.matchesThisExample(ex, false)) {
                                        if (true || !goodEnoughFitTrueBranch)  { trueBranchNegExamples.add(ex);  }
                                        wgtedCountTrueBranchNeg += ex.getWeightOnExample();
                                    } else {
                                        if (true || !goodEnoughFitFalseBranch) { falseBranchNegExamples.add(ex); }
                                        wgtedCountFalseBranchNeg += ex.getWeightOnExample();
                                    }
                                }
                            }

                            if (false && !atMaxDepth) {
                                Utils.println("getOverallMinPosWeight() = " + outerLoopState.getOverallMinPosWeight());
                                Utils.println("goodEnoughFitTrueBranch  = " + goodEnoughFitTrueBranch);
                                Utils.println("goodEnoughFitFalseBranch = " + goodEnoughFitFalseBranch);
                                Utils.println("wgtedCountTrueBranchPos  = " + wgtedCountTrueBranchPos);
                                Utils.println("wgtedCountTrueBranchNeg  = " + wgtedCountTrueBranchNeg);
                                Utils.println("wgtedCountFalseBranchPos = " + wgtedCountFalseBranchPos);
                                Utils.println("wgtedCountFalseBranchNeg = " + wgtedCountFalseBranchNeg);
                            }
                            /*
            				for (Example eg : bestNode.posExamplesThatFailedHere) {
            					Utils.println("Negs: " + ((RegressionRDNExample)eg).toPrettyString());
            				}
            				for (Example eg : ((LearnOneClause)bestNode.task).getPosExamples()) {
            					Utils.println("Pos: " + ((RegressionRDNExample)eg).toPrettyString());
            				}*/
                            double meanTrue = 0;
                            double[] meanVecTrue = null;
                            
                            if (learnMLNTheory) {
                            	meanTrue = bestNode.mlnRegressionForTrue();
                            } else {
                            	if (!learnOCCTree) {
                            		meanTrue = bestNode.meanIfTrue();
                            	} else {
                            		meanTrue = 1;
                            		for (Boolean b : interiorNode.returnBoolPath()) {
										meanTrue = 10*meanTrue + (b?1:0);
									}
                            		meanTrue = 10*meanTrue + 1;
                            		//meanTrue = 1;
                            	}
                            }
                            
                            if (learnMultiValPredicates) {
                            	meanVecTrue = bestNode.meanVectorIfTrue();
                            	if (meanVecTrue == null) {
                            		Utils.error("No mean vector on true branch!!");
                            	}
                            }
                            // We use 2.1 * getMinPosCoverage() here since we assume each branch needs to have getMinPosCoverage() (could get by with 2, but then would need a perfect split).
                            // Since getLength() includes the head, we see if current length EXCEEDS the maxTreeDepthInLiterals.
                            // Since 'maxTreeDepthInLiterals' includes bridgers, count them as well.
                            if (atMaxDepth) { Utils.println("%   Creating a TRUE-branch and FALSE-branch leaves because level = "  + interiorNode.getLevel() + " >= " + maxTreeDepthInInteriorNodes); }
                            if (atMaxDepth || goodEnoughFitTrueBranch ||
                                newClause.getLength()   >  maxTreeDepthInLiterals || // We use '>' here since we don't count the head literal in depth.
                                wgtedCountTrueBranchPos <  2.1 * innerLoopTask.getMinPosCoverage() ||
                                wgtedCountTrueBranchPos <  outerLoopState.getOverallMinPosWeight()) {
                                

                                if (!atMaxDepth && LearnOneClause.debugLevel > -10) {
                                    if      (newClause.getLength()   >  maxTreeDepthInLiterals)                  { Utils.println("%   Creating a TRUE-branch leaf because length = " + newClause.getLength()   + " > " + maxTreeDepthInLiterals); }
                                    else if (wgtedCountTrueBranchPos <  2.1 * innerLoopTask.getMinPosCoverage()) { Utils.println("%   Creating a TRUE-branch leaf because wgtedCountTrueBranchPos = "  + Utils.truncate(wgtedCountTrueBranchPos, 1) + " < 2.1 * minPosCov = " + Utils.truncate(2.1 * innerLoopTask.getMinPosCoverage(), 1)); }
                                    else if (wgtedCountTrueBranchPos <  outerLoopState.getOverallMinPosWeight()) { Utils.println("%   Creating a TRUE-branch leaf because wgtedCountTrueBranchPos = "  + Utils.truncate(wgtedCountTrueBranchPos, 1) + " < minPosWgt = "       + Utils.truncate(outerLoopState.getOverallMinPosWeight(), 1)); }
                                    else if (goodEnoughFitTrueBranch) 											 { Utils.println("%   Creating a TRUE-branch leaf because good enough fit since score < " +  outerLoopState.maxAcceptableNodeScoreToStop); }
                                }
                                Term leaf = null; 
                                if (learnMultiValPredicates) {
                                	leaf = createLeafNodeFromCurrentExamples(meanVecTrue);
                                } else {
                                	leaf = createLeafNodeFromCurrentExamples(meanTrue);
                                }
                                trueBranch = new TreeStructuredTheoryLeaf(wgtedCountTrueBranchPos, wgtedCountTrueBranchNeg, bestNode.getVarianceTrueBranch(), leaf, Example.makeLabel(trueBranchPosExamples));
                            } else {
                                // Have another learning task.
                                TreeStructuredTheoryInteriorNode newTreeNode = new TreeStructuredTheoryInteriorNode(wgtedCountTrueBranchPos, wgtedCountTrueBranchNeg, null, null, null);
                                TreeStructuredLearningTask       newTask     = new TreeStructuredLearningTask(      trueBranchPosExamples,   trueBranchNegExamples, newTreeNode);
                                trueBranch = newTreeNode;
                                newTreeNode.setParent(interiorNode); // Need a back pointer in case we later make this interior node a leaf.
                                newTreeNode.setBoolPath(interiorNode.returnBoolPath()); newTreeNode.addToPath(true);// Set the path taken to this node
                                if (learnMultiValPredicates) {
                                	newTreeNode.setRegressionVectorIfLeaf(meanVecTrue);
                                } else {
                                	newTreeNode.setRegressionValueIfLeaf(meanTrue);
                                }
                                
                                // Since elsewhere we negate the score, do so here as well.
                                Utils.println("%   Creating a TRUE-branch interior node with wgtedCountTrueBranchPos = " + Utils.truncate(wgtedCountTrueBranchPos, 1));
                                outerLoopState.addToQueueOfTreeStructuredLearningTasks(newTask, newTreeNode, bestNode, -bestNode.getVarianceTrueBranch(sortTreeStructedNodesByMeanScore));
                            }
                            double meanFalse = 0;
                            double[] meanVecFalse = null;
                            
                            
                            if (learnMLNTheory) {
                            	meanFalse = bestNode.mlnRegressionForFalse();
                            } else {
                            	if (!learnOCCTree) {
                            		meanFalse = bestNode.meanIfFalse();
                            	} else {
                            		meanFalse = 1;
                            		for (Boolean b : interiorNode.returnBoolPath()) {
										meanFalse = 10*meanFalse + (b?1:0);
									}
                            		meanFalse = 10*meanFalse + 0;
                            		//meanFalse = 1;
                            	}
                            }
                            
                            if (learnMultiValPredicates) {
                            	meanVecFalse = bestNode.meanVectorIfFalse();
                            }
                            // No need to check max clause length (maxTreeDepthInLiterals) since that should have been checked at parent's call (since no literals added for FALSE branch).
                            if (atMaxDepth || goodEnoughFitFalseBranch ||
                            //	newClause.getLength()   >  maxTreeDepthInLiterals  ||
                                wgtedCountFalseBranchPos <  2.1 * innerLoopTask.getMinPosCoverage() ||
                                wgtedCountFalseBranchPos <  outerLoopState.getOverallMinPosWeight()) {
          
                                Term leaf = null; 
                                if (learnMultiValPredicates) {
                                	leaf = createLeafNodeFromCurrentExamples(meanVecFalse);
                                } else {
                                	leaf = createLeafNodeFromCurrentExamples(meanFalse);
                                }
                                

                                if (!atMaxDepth && LearnOneClause.debugLevel > -10) {
                                    if      (interiorNode.getLevel() >= maxTreeDepthInInteriorNodes) { Utils.println("%   Creating a FALSE-branch leaf because level = "  + interiorNode.getLevel() + " > " + maxTreeDepthInInteriorNodes); }
                                    else if (wgtedCountFalseBranchPos <  2.1 * innerLoopTask.getMinPosCoverage()) { Utils.println("%   Creating a FALSE-branch leaf because wgtedCountFalseBranchPos = "  + Utils.truncate(wgtedCountFalseBranchPos, 1) + " < 2.1 * minPosCov = " + Utils.truncate(2.1 * innerLoopTask.getMinPosCoverage(), 1)); }
                                    else if (wgtedCountFalseBranchPos <  outerLoopState.getOverallMinPosWeight()) { Utils.println("%   Creating a FALSE-branch leaf because wgtedCountFalseBranchPos = "  + Utils.truncate(wgtedCountFalseBranchPos, 1) + " < minPosWgt = "       + Utils.truncate(outerLoopState.getOverallMinPosWeight(), 1)); }
                                    else if (goodEnoughFitFalseBranch) 									   		  { Utils.println("%   Creating a FALSE-branch leaf because good enough fit since score < " +  outerLoopState.maxAcceptableNodeScoreToStop); }
                                }

                                falseBranch = new TreeStructuredTheoryLeaf(wgtedCountFalseBranchPos, wgtedCountFalseBranchNeg, bestNode.getVarianceFalseBranch(), leaf, Example.makeLabel(falseBranchPosExamples));
                            } else {
                                // Have another learning task.
                                TreeStructuredTheoryInteriorNode newTreeNode = new TreeStructuredTheoryInteriorNode(wgtedCountFalseBranchPos, wgtedCountFalseBranchNeg, null, null, null);
                                TreeStructuredLearningTask       newTask     = new TreeStructuredLearningTask(      falseBranchPosExamples,   falseBranchNegExamples, newTreeNode);
                                // On the FALSE branch, we need to use the PARENT's node (since the latest node failed).  There should always be a parent, but play it safe here.
                                // NOTE: we need to get the parent in the TREE and not in the LearnOneClause search.  I.e., bestNode might have more than 1 literal!  So can't do bestNode.getParentNode().
                                // Also, need to get the TIME A TRUE BRANCH WAS TAKEN.
                                TreeStructuredTheoryInteriorNode parentOfCurrentNode = interiorNode.getLastParentOnTrueBranch(interiorNode);
                                SingleClauseNode parentSearchNode = (parentOfCurrentNode == null ? null : parentOfCurrentNode.getSearchNodeThatLearnedTheClause());
                                falseBranch = newTreeNode;
                                newTreeNode.setParent(interiorNode); // Need a back pointer in case we later make this interior node a leaf.
                                newTreeNode.setBoolPath(interiorNode.returnBoolPath()); newTreeNode.addToPath(false);// Set the path taken to this node

                                if (learnMultiValPredicates) {
                                	newTreeNode.setRegressionVectorIfLeaf(meanVecFalse);
                                } else {
                                	newTreeNode.setRegressionValueIfLeaf(meanFalse);
                                }
                                // Since elsewhere we negate the score, do so here as well.
                                Utils.println("%   Creating a FALSE-branch interior node with wgtedCountFalseBranchPos = " + Utils.truncate(wgtedCountFalseBranchPos, 1));
                          //      Utils.println("Creating " + interiorNode.getFullNodeTest() + " with trueBranchParent: " + 
                          //      		(parentOfCurrentNode == null ? "null" :parentOfCurrentNode.getFullNodeTest()));
                                outerLoopState.addToQueueOfTreeStructuredLearningTasks(newTask, newTreeNode, parentSearchNode, -bestNode.getVarianceFalseBranch(sortTreeStructedNodesByMeanScore)); // We want to sort by TOTAL error, not AVERAGE.
                            }
                            //Utils.waitHere();
                            interiorNode.setTreeForTrue( trueBranch);
                            interiorNode.setTreeForFalse(falseBranch);
                        }
                        else {
                            getStdILPtheory().addMainClause(newClause, innerLoopTask.getInlineManager()); // The inline manager probably has already been sent, but send it again anyway.
                            if (learnMLNTheory && !learningTreeStructuredTheory) {
                            	double reg = bestNode.mlnRegressionForTrue();
                            	Utils.println("Setting " + reg + " for " + newClause);
                            	int len = getStdILPtheory().getClauses().size();
                            	getStdILPtheory().getClauses().get(len-1).setWeightOnSentence(reg);
                            	// Update gradients
                            	for (Example eg : coveredPosExamplesThisCycle) {
									((RegressionRDNExample)eg).setOutputValue(((RegressionRDNExample)eg)
											.getOutputValue() - reg); 
								}
                            }
                        }

                        long end = System.currentTimeMillis();
                        if (LearnOneClause.debugLevel > -1 && learningTreeStructuredTheory) {
                            Utils.println("\n% Time for loop #" + getNumberOfCycles() + ": " + Utils.convertMillisecondsToTimeSpan(end - start, 3) + ".");
                            Utils.println(  "% Internal node max length = " + getMaxNumberOfLiteralsAtAnInteriorNode());
                            Utils.println(  "% Max tree depth in lits   = " + getMaxTreeDepthInLiterals());
                            Utils.println(  "% Max tree depth in nodes  = " + getMaxTreeDepth());
                            Utils.println(  "% Max number of clauses    = " + maxNumberOfClauses);
                        }

                        if (LearnOneClause.debugLevel > -1) {
                            setFractionOfPosCovered((double) getNumberOfPosExamplesCovered() / (double) getNumberOfPosExamples());
                            setFractionOfNegCovered((double) getNumberOfNegExamplesCovered() / (double) getNumberOfNegExamples());
                            Utils.println("\n% On cycle #" + getNumberOfCycles()+ ", the best clause found is:");
                            Utils.println("%      " + bestNode);
                            Utils.println("% This clause covers " + coveredPosExamplesCount + " " + (isFlipFlopPosAndNegExamples() ? "flipped " : "") + "positive examples, of which " + newlyCoveredPosExamples + " are newly covered.");
                            Utils.println("% It also covers "	  + coveredNegExamplesCount + " " + (isFlipFlopPosAndNegExamples() ? "flipped " : "") + "negative examples, of which " + newlyCoveredNegExamples + " are newly covered.");
                            if (learningTreeStructuredTheory == false) {
                                Utils.println("% The current set of " + Utils.getSizeSafely(getStdILPtheory().getClauses()) + " best clauses covers "
                                              + Utils.truncate(100 * getFractionOfPosCovered(), 1) + "% of the positive examples and "
                                              + Utils.truncate(100 * getFractionOfNegCovered(), 1) + "% of the negatives." + "}");
                            }
                        }
                    } else {
                        if (LearnOneClause.debugLevel > -10) {
                            Utils.println(MessageType.ILP_INNERLOOP, "\n% No acceptable clause was learned on this cycle of the ILP inner loop (LearnOneClause).");
                            Utils.println(MessageType.ILP_INNERLOOP,   "% The closest-to-acceptable node found (score = " + Utils.truncate(theGleaner.bestScoreRegardless, 4) + "):\n%  " + theGleaner.bestNodeRegardless);
                       //     Utils.waitHere();
                        }

                        if (learningTreeStructuredTheory) { // Need to make the current node a leaf.
                            TreeStructuredLearningTask currentTask = outerLoopState.getCurrentTreeLearningTask();
                            createTreeStructuredLearningTaskLeaf(currentTask);
                        }
                    }
                }


                if (writeGleanerFilesToDisk && getGleanerFileName() != null) {
                    ((Gleaner) innerLoopTask.searchMonitor).dumpCurrentGleaner(getGleanerFileName(), innerLoopTask);
                }

                // Increment clock time used.
                long clockTimeUsed = getClockTimeUsedInMillisec();
                clockTimeUsed += stopwatch.getTotalTimeInMilliseconds();
                setClockTimeUsedInMillisec(clockTimeUsed);


                if (isCheckpointEnabled()) {
                    writeCheckpoint();
                }

                if (learningTreeStructuredTheory) {
                    stoppedBecauseTreeStructuredQueueEmpty = outerLoopState.queueOfTreeStructuredLearningTasksIsEmpty();
                }

            } // End of WHILE

            if (LearnOneClause.debugLevel > -1) {
                Utils.println(MessageType.ILP_INNERLOOP, "\n% ******************************************\n");
                if (!innerLoopTask.regressionTask && getFractionOfPosCovered() >= minFractionOfPosCoveredToStop) {
                    Utils.println(MessageType.ILP_INNERLOOP, "% Have stopped ILP's outer loop because have exceeded the minimal fraction ("
                                    + minFractionOfPosCoveredToStop	+ ") of positive examples to cover.");
                } else if (!canStillMeetPrecisionRecallAccuracyF1specs(true)) {
                    // The call  to canStillMeetPrecisionRecallAccuracyF1specs(true) will report why.
                } else if (stoppedBecauseTreeStructuredQueueEmpty) {
                    Utils.println(MessageType.ILP_INNERLOOP, "%  Have stopped ILP's outer loop because the tree-structured queue is empty.");
                } else if (getNumberOfCycles() >= maxNumberOfCycles) {
                    Utils.println(MessageType.ILP_INNERLOOP, "% Have stopped ILP's outer loop because have reached the maximum number of iterations (" + maxNumberOfCycles + ").");
                } else if (getNumberOfLearnedClauses() >= maxNumberOfClauses) {
                    Utils.println(MessageType.ILP_INNERLOOP, "% Have stopped ILP's outer loop because have reached the maximum number of learned clauses (" + maxNumberOfClauses + ").");
                } else if (stoppedBecauseNoMoreSeedsToTry) {
                    Utils.println(MessageType.ILP_INNERLOOP, "% Have stopped ILP's outer loop because have run out of seed positive examples to try.");
                } else if (getTotal_nodesConsidered() >= max_total_nodesExpanded) {
                    Utils.println(MessageType.ILP_INNERLOOP, "% Have stopped ILP's outer loop because have reached the maximum number of nodes to consider.");
                } else if (getTotal_nodesCreated() >= max_total_nodesCreated) {
                    Utils.println(MessageType.ILP_INNERLOOP, "% Have stopped ILP's outer loop because have reached the maximum number of nodes to created.");
                } else if (getClockTimeUsedInMillisec() >=  getMaximumClockTimeInMillisec()) {
                    Utils.println(MessageType.ILP_INNERLOOP, "%  Have stopped ILP's outer loop because have reached the maximum clock time.");
                } else if (stoppedBecauseNoMoreSeedsToTry) {
                    Utils.println(MessageType.ILP_INNERLOOP, "%  Have stopped ILP's outer loop because there are no more seeds to try.");
                }
                Utils.println(MessageType.ILP_INNERLOOP, "\n% ******************************************");
            }

            if (learningTreeStructuredTheory ) {
                // May have stopped for reasons other than the queue is empty.  In that case, need to convert all pending nodes to leaves.
                while (!outerLoopState.queueOfTreeStructuredLearningTasksIsEmpty()) {
                    createTreeStructuredLearningTaskLeaf(outerLoopState.popQueueOfTreeStructuredLearningTasks());
                }
            }



            // To be safe, dump one last time.
            if (getGleanerFileName() != null && writeGleanerFilesToDisk) {
                ((Gleaner) innerLoopTask.searchMonitor).dumpCurrentGleaner(getGleanerFileName(),innerLoopTask);
            }
            if (holdBodyModes != null) { innerLoopTask.setBodyModes(holdBodyModes); holdBodyModes = null; }
            Theory finalTheory = produceFinalTheory();

            unsetAdvice();

            innerLoopTask.fireOuterLoopFinished(this);

            return finalTheory;

        }
        else if (action == ILPSearchAction.SKIP_ITERATION) {
            Utils.println("ILPSearchListener skipped outer-loop execution.");
            return null;
        }
        else {
            Utils.println("ILPSearchListener terminated outer-loop execution.");
            throw new SearchInterrupted("ILPSearchListener terminated outer-loop execution.");
        }
	}


	private void createTreeStructuredLearningTaskLeaf(TreeStructuredLearningTask currentTask) {
		//TreeStructuredTheoryLeaf leaf = null;
		Term val = null;
		
		// Use getRegressionValueIfLeaf irrespective of model
		//if (learnMLNTheory) {
			if (currentTask.getNode() instanceof TreeStructuredTheoryInteriorNode) {
				if (isLearnMultiValPredicates()) {
					val = createLeafNodeFromCurrentExamples(((TreeStructuredTheoryInteriorNode)currentTask.getNode()).getRegressionVectorIfLeaf());
				} else {
					val = createLeafNodeFromCurrentExamples(((TreeStructuredTheoryInteriorNode)currentTask.getNode()).getRegressionValueIfLeaf());
				}
			} else {
				Utils.error("task is not interior node!!");
			}			
		//} else {
//			val =  createLeafNodeFromCurrentExamples(currentTask.getPosExamples());
		//}
		
		TreeStructuredTheoryLeaf leaf = new TreeStructuredTheoryLeaf(currentTask.getNode().getWeightedCountOfPositiveExamples(),
																	 currentTask.getNode().getWeightedCountOfNegativeExamples(),
																	 computeVarianceOverTheseExamples( currentTask.getPosExamples()),
																	 val,
																	 Example.makeLabel(currentTask.getPosExamples()));
		// The parent had been expecting an interior node, so need to do some surgery.
		TreeStructuredTheoryNode node   = currentTask.getNode();
		TreeStructuredTheoryNode parent = node.getParent();
		if (parent == null) {
			outerLoopState.getTreeBasedTheory().setRoot(leaf);
		} else if (parent instanceof TreeStructuredTheoryInteriorNode) {
			Utils.println("Created a leaf under " + ((TreeStructuredTheoryInteriorNode) parent).getNodeTest());
			((TreeStructuredTheoryInteriorNode) parent).changeChild(node, leaf);
			leaf.setParent((TreeStructuredTheoryInteriorNode)parent);
		} else {
			Utils.error("Expecting an INTERIOR NODE HERE: " + parent);
		}
	}

   private Term createLeafNodeFromCurrentExamples(double value) {
	   return innerLoopTask.stringHandler.getNumericConstant(value);
   }
   private Term createLeafNodeFromCurrentExamples(double[] value) {
	   List<Term> terms = new ArrayList<Term>();
	   for (double val : value) {
		terms.add(innerLoopTask.stringHandler.getNumericConstant(val));
	   }
	   return innerLoopTask.stringHandler.getConsCellFromList(terms);
   }
   
   private Term createLeafNodeFromCurrentExamples(Collection<Example> currentExamples) {
		if (innerLoopTask.regressionTask) {
			
			if (!innerLoopTask.constantsAtLeaves) {
				Utils.error("createLeafNodeFromCurrentExamples: This method assumes we have constants at leaves in regression trees.");
			}
			
			if (Utils.getSizeSafely(currentExamples) < 1) {
				Utils.error("Should not reach here with ZERO examples!");
				return innerLoopTask.stringHandler.getNumericConstant(0.0);
			}
			
			// Compute the mean value over all the (weighted) examples.
			double numerator   = 0.0;
			double denominator = 0.0;
			if (currentExamples != null) for (Example ex : currentExamples) {
				double wgt = ex.getWeightOnExample();
				numerator   += wgt * ((RegressionExample) ex).getOutputValue();
				denominator += wgt;
			}
			
			return innerLoopTask.stringHandler.getNumericConstant(numerator / denominator);
		}
		// Else return the majority class.
		if (innerLoopTask.getTotalPosWeight() >= innerLoopTask.getTotalNegWeight()) {
			return innerLoopTask.stringHandler.trueIndicator;
		}
		return innerLoopTask.stringHandler.falseIndicator;
	}
   private Term createMLNLeafNodeFromCurrentExamples(Collection<Example> currentExamples, SingleClauseNode node) {
		if (innerLoopTask.regressionTask) {
			
			if (!innerLoopTask.constantsAtLeaves) {
				Utils.error("createLeafNodeFromCurrentExamples: This method assumes we have constants at leaves in regression trees.");
			}
			
			if (Utils.getSizeSafely(currentExamples) < 1) {
				Utils.error("Should not reach here with ZERO examples!");
				return innerLoopTask.stringHandler.getNumericConstant(0.0);
			}
			BranchStats stats= new BranchStats();
			Utils.println("Using groundings from " + node.getClause() + "to count gndings");
			for (Example eg : currentExamples) {
				RegressionRDNExample rex = (RegressionRDNExample)eg;
				long num= node.getNumberOfGroundingsForRegressionEx(rex);
				stats.addNumOutput(num, rex.getOutputValue(), rex.getWeightOnExample(), rex.getProbOfExample().getProbOfBeingTrue());
			}
			
			
			return innerLoopTask.stringHandler.getNumericConstant(stats.getLambda(innerLoopTask.useProbabilityWeights));
		} else {
			Utils.error("Can't learn MLNs with non-regresssion trees");
		}
		return null;
	}
   private double computeVarianceOverTheseExamples(Collection<Example> currentExamples) {
		if (innerLoopTask.regressionTask) {
			
			if (!innerLoopTask.constantsAtLeaves) {
				Utils.error("createLeafNodeFromCurrentExamples: This method assumes we have constants at leaves in regression trees.");
			}
			
			if (Utils.getSizeSafely(currentExamples) < 1) {
				Utils.error("Should not reach here with ZERO examples!");
				return -1;
			}
			
			if (learnMultiValPredicates) {
				VectorStatistics vecStats = new VectorStatistics();
				if (currentExamples != null) for (Example ex : currentExamples) {
					vecStats.addVector(VectorStatistics.scalarProduct(((RegressionExample) ex).getOutputVector(), 
																		ex.getWeightOnExample()));
				}
				return vecStats.getVariance();
			}
			// Compute the mean value over all the (weighted) examples.
			double totalOfOutputValues  = 0.0;
			double totalSquaredOfOutput = 0.0;
			double weightedCount        = 0.0;
			if (currentExamples != null) for (Example ex : currentExamples) {
				double output = ex.getWeightOnExample() * ((RegressionExample) ex).getOutputValue();
				totalOfOutputValues  += output; 
				totalSquaredOfOutput += output * output;
				weightedCount        += ex.getWeightOnExample();
			}
			
			double result = (weightedCount <= 0.0 ? 0.0
					          : (    totalSquaredOfOutput / weightedCount)
						          - ((totalOfOutputValues  / weightedCount * totalOfOutputValues / weightedCount)));
			if (result < 0.0) { return 0.0; } // Be robust to numeric errors.
			return result;
			
		}
		// Else return -1 to save this is not relevant (though could compute variance for the binomial distribution).
		return -1;
   }

   /** Resets the state of the search from the beginning.
    *
    * This should reset the state of both the outer and inner loop
    * so that a new search can be started.
    */
   private long hold_Literal_instancesCreated         = 0;
   private long hold_Clause_instancesCreated          = 0;
   private long hold_Variable_instancesCreated        = 0;
   private long hold_StringConstant_instancesCreated  = 0;
   private long hold_NumericConstant_instancesCreated = 0;
   public void resetAll() {
      //  Utils.println("resetAll(before): " + Utils.reportSystemInfo());
        innerLoopTask.resetAll(false);  // Clean up the inner loop in case we are starting a new fold...
      //  Utils.println("resetAll(after resetAll for inner loop): " + Utils.reportSystemInfo());
        outerLoopState.clearAll();
      //  Utils.println("resetAll(after resetAll for outer loop state): " + Utils.reportSystemInfo());
      //  ((DefaultHornClausebase)innerLoopTask.getProver().getClausebase()).resetIndexes();
      //  Utils.println("resetAll(after resetIndex for outer loop state): " + Utils.reportSystemInfo());
      //  ((DefaultHornClausebase)innerLoopTask.getProver().getClausebase()).reportStats();
        
      //  Utils.println(((DefaultHornClausebase)innerLoopTask.getProver().getClausebase()).toString());
        innerLoopTask.stringHandler.resetVarCounters();
      // innerLoopTask.stringHandler.reportStats();
        
        /*
        Utils.println("% Before creating numericConstants: " + Utils.reportSystemInfo());
        int n = 100000;
        for (int i = 0; i < n; i++) {
        	innerLoopTask.getStringHandler().getNumericConstant(2.0 * i + i / 10.0); // Want unique values.
        	if ((i + 1) % 1000 == 0) { Utils.println("% After creating " + Utils.comma(i + 1) + " numericConstants: " + Utils.reportSystemInfo()); } 
        }
        Utils.println("% After creating " + Utils.comma(n) + " numericConstants: " + Utils.reportSystemInfo()); Utils.waitHere();
        if (getGleaner() != null) { getGleaner().resetAllMarkers(); } else { Utils.println("\n% No gleaner is in use."); }
        if (getGleaner() != null) { getGleaner().reportStats(); }     
        */                
        /*
        Utils.println("% # literals  created = " + Utils.comma(Literal.instancesCreated)  + " [" + Utils.comma(Literal.instancesCreated - hold_Literal_instancesCreated) + " are new since last report]");
        Utils.println("% # clauses   created = " + Utils.comma(Clause.instancesCreated)   + " [" + Utils.comma(Clause.instancesCreated - hold_Clause_instancesCreated)   + " new]");
        Utils.println("% # variables created = " + Utils.comma(Variable.instancesCreated) + " [" + Utils.comma(Clause.instancesCreated - hold_Variable_instancesCreated) + " new]");
        Utils.println("% # string  constants created = " + Utils.comma(StringConstant.instancesCreated)  + " [" + Utils.comma(StringConstant.instancesCreated  - hold_StringConstant_instancesCreated) + " new]");
        Utils.println("% # numeric constants created = " + Utils.comma(NumericConstant.instancesCreated) + " [" + Utils.comma(NumericConstant.instancesCreated - hold_NumericConstant_instancesCreated) + " new]");
        if (true) {
        	hold_Literal_instancesCreated  = Literal.instancesCreated;
        	hold_Clause_instancesCreated   = Clause.instancesCreated;
        	hold_Variable_instancesCreated = Variable.instancesCreated;
        	hold_StringConstant_instancesCreated  = StringConstant.instancesCreated;
        	hold_NumericConstant_instancesCreated = NumericConstant.instancesCreated;
        }
        */
        //Utils.println("%   " + Utils.reportSystemInfo()); Utils.waitHere(); 
        
        setStdILPtheory(new Theory(innerLoopTask.stringHandler, null, innerLoopTask.getInlineManager()));
        setCoveredPosExamples(new HashSet<Example>());
        setCoveredNegExamples(new HashSet<Example>());
        setNumberOfCycles(0);
        setNumberOfLearnedClauses(0);
        setNumberOfPosExamplesCovered(0);  // These are normal (ie, UNweighted) counts.  Wgt'ing of examples happens when they are covered (so the next round they can count 1.0 [fully], 0.0 [not at all], or somewhere in between).
        setNumberOfNegExamplesCovered(0);
        setFractionOfPosCovered(0.0);
        setTotal_nodesConsidered(0);
        setTotal_nodesCreated(0);
        setTotal_nodesNotAddedToOPENsinceMaxScoreTooLow(0);
        setTotal_nodesRemovedFromOPENsinceMaxScoreNowTooLow(0);
        setTotal_countOfPruningDueToVariantChildren(0);
        clearSeedPosExamplesUsed();
        clearSeedNegExamplesUsed();
        setClockTimeUsedInMillisec(0);
        //setNumberOfPosExamples(Utils.getSizeSafely(innerLoopTask.getPosExamples()));
        //setNumberOfNegExamples(Utils.getSizeSafely(innerLoopTask.getNegExamples()));

        if (learningTreeStructuredTheory) {
        	TreeStructuredTheoryInteriorNode newTreeNode = new TreeStructuredTheoryInteriorNode(innerLoopTask.getTotalPosWeight(), innerLoopTask.getTotalNegWeight(), null, null, null);
        	TreeStructuredLearningTask         firstTask = new TreeStructuredLearningTask(      innerLoopTask.getPosExamples(),    innerLoopTask.getNegExamples(), newTreeNode);
        	TreeStructuredTheory         treeBasedTheory = new TreeStructuredTheory(innerLoopTask.stringHandler, getTargetLiteral(), newTreeNode);
        	newTreeNode.setLevel(0);
        	outerLoopState.setTreeBasedTheory(treeBasedTheory);
        	outerLoopState.setOverallMinPosWeight(innerLoopTask.getMinPosCoverage()); // We want to keep this constant for all the recursive tree-building calls.
        	outerLoopState.addToQueueOfTreeStructuredLearningTasks(firstTask, newTreeNode, null, Double.MAX_VALUE);
        	// Set the acceptable score based on variance at root
        	double totalVariance = firstTask.getVariance();
        	Utils.println("Variance:" + totalVariance);
        	setMaxAcceptableNodeScoreToStop(Math.min(getMaxAcceptableNodeScoreToStop(), totalVariance*0.25));
        	Utils.println("Set score:" + getMaxAcceptableNodeScoreToStop());
            
        //	Utils.waitHere("getMinPosCoverage = " + innerLoopTask.getMinPosCoverage());
        }
        //Utils.waitHere("resetAll(after): " + Utils.reportSystemInfo());
    }
    
    private Literal getTargetLiteral() {
    	List<Literal> targets = innerLoopTask.targets;
    	
    	if (Utils.getSizeSafely(targets) == 1) { return targets.get(0); }
    	Utils.error("Have too many/few (" + Utils.getSizeSafely(targets) + ") targets (should have exactly one): " + targets); 
    	return null;
    }

    public void initialize(boolean creatingCompoundFeaturesOnly) throws SearchInterrupted { // Pull this out from the constructor so that the caller can set some globals in innerLoopTask after that instance is created.
    	
		// All the stuff that used to be here was moved to resetAll()...
    	
        innerLoopTask.initialize(creatingCompoundFeaturesOnly);
        // Calling it here as one might be setting the parameters to initial values.
    	overwriteParametersFromBK();
	}
    
    public void overwriteParametersFromBK() {
		////////////////////////////////////////////////////////
		// Set parameters using setParams:
		////////////////////////////////////////////////////////
		String lookup=null;
		if ((lookup =  innerLoopTask.getStringHandler().getParameterSetting("maxNodesToConsider")) != null) {
			innerLoopTask.setMaxNodesToConsider(Integer.parseInt(lookup));
		}
		if ((lookup = innerLoopTask.getStringHandler().getParameterSetting("maxNodesToCreate")) != null) {
			innerLoopTask.setMaxNodesToCreate(Integer.parseInt(lookup));
		}
		if ((lookup = innerLoopTask.getStringHandler().getParameterSetting("maxTreeDepth")) != null) {
			setMaxTreeDepth(Integer.parseInt(lookup));
		}
		if ((lookup = innerLoopTask.getStringHandler().getParameterSetting("clauseLength")) != null) {
			setMaxTreeDepthInLiterals(Integer.parseInt(lookup));
		}
		if ((lookup = innerLoopTask.getStringHandler().getParameterSetting("nodeSize")) != null) {
			setMaxNumberOfLiteralsAtAnInteriorNode(Integer.parseInt(lookup));
			innerLoopTask.maxBodyLength = getMaxNumberOfLiteralsAtAnInteriorNode();
		}
		if ((lookup = innerLoopTask.getStringHandler().getParameterSetting("numOfClauses")) != null) {
			maxNumberOfClauses = Integer.parseInt(lookup);
		}
		if ((lookup = innerLoopTask.getStringHandler().getParameterSetting("numOfCycles")) != null) {
			maxNumberOfCycles = Integer.parseInt(lookup);
		}
		if ((lookup = innerLoopTask.getStringHandler().getParameterSetting("numOfFreeBridgers")) != null) {
			// TODO set it once available			
		}
		if ((lookup = innerLoopTask.getStringHandler().getParameterSetting("maxScoreToStop")) != null) {
			setMaxAcceptableNodeScoreToStop(Double.parseDouble(lookup));
		}
		
		if ((lookup = innerLoopTask.getStringHandler().getParameterSetting("minPosCoverage")) != null) {
			innerLoopTask.setMinPosCoverage(Double.parseDouble(lookup));
		}

	}		

	/**
     * 
     * @param all_pos_wt : Weight set on all positive regression examples.
     * @param all_neg_wt : Weight set on all negative regression examples
     * @param ratioOfNegToPositiveEx : How many negative examples for each positive example. Set it to a negative number if you dont
     * want to subsample. 
     */
    
    // TODO - put all this RDN stuff in a subclass of ILPouterLoop.
    public  void setLearnMLNTheory(boolean val) {
    	learnMLNTheory = val;
    	innerLoopTask.setMlnRegressionTask(val);
    }
    
    public  void setLearnOCCTree(boolean val) {
    	innerLoopTask.oneClassTask = val;
    	learnOCCTree = val;
    }
    
    private boolean useSamplingWithReplacementOnPos = (RunBoostedRDN.numbModelsToMake > 1 ? true : false);  // TODO integrate this better if we decide to keep it.
    private boolean useSamplingWithReplacementOnNeg = false;

    public void setFlagsForRegressionTask(boolean notLearnTrees) {
    	innerLoopTask.regressionTask           = true;
		innerLoopTask.stopIfPerfectClauseFound = false;
		
		innerLoopTask.stopWhenUnacceptableCoverage = false;
		learningTreeStructuredTheory           = !notLearnTrees;
		innerLoopTask.setIsaTreeStructuredTask(!notLearnTrees); // TODO - couple this with setting the above (via a setter)
    }
    
    public void morphToRDNRegressionOuterLoop(double all_pos_wt, double all_neg_wt, double ratioOfNegToPositiveEx, 
    		double samplePositiveProb, boolean notLearnTrees, boolean reweighExs, boolean areRegressionEgs) {
    	setFlagsForRegressionTask(notLearnTrees);
		
		List<Example>  origPosExamples = getPosExamples();
		List<Example> positiveExamples = new ArrayList<Example>(4);
		int        numbOrigPosExamples = Utils.getSizeSafely(origPosExamples);
		int		   numbNewPosExamples  = (int) samplePositiveProb * numbOrigPosExamples;
		
		// Less than zero means we dont want to sample.
		if (numbNewPosExamples <= 0) {
			numbNewPosExamples = numbOrigPosExamples;
		}
		double	   reweighPositiveExamples = numbOrigPosExamples / numbNewPosExamples;
		//Utils.println("\n%  samplePositiveProb = " + samplePositiveProb);
		
		int countOfPosKept = 0;
		if (useSamplingWithReplacementOnPos) { // Sample WITH REPLACEMENT.   IF THIS IS SET, IGNORE (for now) samplePositiveProb.
			if (numbOrigPosExamples > 0) for (int i = 0; i < numbNewPosExamples; i++) {
				Example eg = origPosExamples.get(Utils.random0toNminus1(numbOrigPosExamples));
				double outputVal = all_pos_wt;
				if (areRegressionEgs) {
					if (eg instanceof RegressionExample) {
						outputVal = ((RegressionExample)eg).getOutputValue();
						
					} else {
						Utils.waitHere("Expected regression examples for learning regression trees");
					}
				}
				RegressionRDNExample regEx = new RegressionRDNExample(eg.getStringHandler(), eg.extractLiteral(),
																	  outputVal, eg.provenance, eg.extraLabel, true);
				if (areRegressionEgs) {
					regEx.originalRegressionOrProbValue = regEx.getOutputValue();
					//Utils.println("Setting reg value to : " + regEx.originalRegressionOrProbValue);
				}
				if (reweighExs) {
					regEx.setWeightOnExample(eg.getWeightOnExample() * reweighPositiveExamples);
					
				}
				positiveExamples.add(regEx);
				countOfPosKept++;
			}
		} else { // TODO - should this also be sampling with replacement of the expected number to collect?  Correctly no duplicates, but number collected can vary.
			if (numbOrigPosExamples > 0) for (Example eg : origPosExamples) { // Should we ignore this positive example?
				if (samplePositiveProb >= 0 && samplePositiveProb < 1 && Utils.random() > samplePositiveProb) {	continue; }
				double outputVal = all_pos_wt;
				if (areRegressionEgs) {
					if (eg instanceof RegressionExample) {
						outputVal = ((RegressionExample)eg).getOutputValue();
					} else {
						Utils.waitHere("Expected regression examples for learning regression trees");
					}
				}
				RegressionRDNExample regEx = new RegressionRDNExample(eg.getStringHandler(), eg.extractLiteral(),
																	  outputVal, eg.provenance, eg.extraLabel, true);
				if (areRegressionEgs) {
					regEx.originalRegressionOrProbValue = regEx.getOutputValue();
					//Utils.println("Setting reg value to : " + regEx.originalRegressionOrProbValue);
				}
				if (reweighExs) {
				regEx.setWeightOnExample(eg.getWeightOnExample() * reweighPositiveExamples);
				
				}
				positiveExamples.add(regEx);
				countOfPosKept++;
			}
		}
		//Utils.println("\n%  countOfPosKept = " + countOfPosKept);
		
		// TODO - Handle skew in both directions.
		// Now move the negative examples to positives (since for regression all examples are positives).
		List<Example> origNegExamples = getNegExamples();
		int       numbOrigNegExamples = Utils.getSizeSafely(origNegExamples);
	//	double   probOfSelectingNegEx = (ratioOfNegToPositiveEx * (double) numbOrigPosExamples) / (double) numbOrigNegExamples;
		double   probOfSelectingNegEx = (ratioOfNegToPositiveEx * (double) countOfPosKept)      / (double) numbOrigNegExamples; // Use the NEW number of positive examples, NOT the original!
		
		// If #positives = 0, we do need few negative example but not all. 
		if (countOfPosKept == 0) {
			probOfSelectingNegEx = ratioOfNegToPositiveEx / (double) numbOrigNegExamples;
		}
		int           countOfNegsKept = 0;	
		double	   reweighNegativeExamples = 1 / probOfSelectingNegEx;
		if (probOfSelectingNegEx >= 1 || probOfSelectingNegEx <= 0) {
			reweighNegativeExamples = 1;
		}

		if (useSamplingWithReplacementOnNeg && numbOrigNegExamples > 0 && probOfSelectingNegEx >= 0 && probOfSelectingNegEx < 1) {
			int numbOrigNegExamplestoUse = Math.max(1, Math.min(numbOrigNegExamples, (int) Math.round(probOfSelectingNegEx * numbOrigNegExamples)));
			
		//	Utils.println("aaaa  numbOrigNegExamplestoUse = " + numbOrigNegExamplestoUse);			
			for (int i = 0; i < numbOrigNegExamplestoUse; i++) {
				int exToGet = Utils.random0toNminus1(numbOrigNegExamples); // Utils.println("     get neg #" + Utils.comma(exToGet));
				Example eg = origNegExamples.get(exToGet);
				double outputVal = all_neg_wt;
				if (areRegressionEgs) {
					if (eg instanceof RegressionExample) {
						outputVal = ((RegressionExample)eg).getOutputValue();
					}
				}
				RegressionRDNExample regEx = new RegressionRDNExample(eg.getStringHandler(), eg.extractLiteral(),
																	  outputVal, eg.provenance, eg.extraLabel, false);
				if (areRegressionEgs) {
					regEx.originalRegressionOrProbValue = regEx.getOutputValue();
				}
				if (reweighExs) {
				regEx.setWeightOnExample(eg.getWeightOnExample() * reweighNegativeExamples);
				
				}
				positiveExamples.add(regEx);
				countOfNegsKept++;
			}
		} else {
			/*  TUSHAR - I (JWS) replaced this (above) with random sampling with replacement.  Will be faster if we have a lot of negatives (though that probably doesn't matter much),
			 *           but maybe more importantly we'll always get the same number of negatives.
			 */
		//	Utils.println("bbbb   probOfSelectingNegEx = " + probOfSelectingNegEx);
			if (numbOrigNegExamples > 0) for (Example eg : origNegExamples) {
				if (probOfSelectingNegEx >= 0 && probOfSelectingNegEx < 1 && Utils.random() > probOfSelectingNegEx)	{ continue; }
				double outputVal = all_neg_wt;
				if (areRegressionEgs) {
					if (eg instanceof RegressionExample) {
						outputVal = ((RegressionExample)eg).getOutputValue();
					}
				}
				RegressionRDNExample regEx = new RegressionRDNExample(eg.getStringHandler(), eg.extractLiteral(),
																	  outputVal, eg.provenance, eg.extraLabel, false);
				if (areRegressionEgs) {
					regEx.originalRegressionOrProbValue = regEx.getOutputValue();
				}
				if (reweighExs) {
					regEx.setWeightOnExample(eg.getWeightOnExample() * reweighNegativeExamples);
					
				}
				positiveExamples.add(regEx);
				countOfNegsKept++;
			}
		}
		
		Utils.println("% Kept " + (useSamplingWithReplacementOnPos ? "(via sampling with replacement) " : "") + Utils.comma(countOfPosKept)  + " of the " + Utils.comma(numbOrigPosExamples) + " positive examples.");
		Utils.println("% Kept " + (useSamplingWithReplacementOnNeg ? "(via sampling with replacement) " : "") + Utils.comma(countOfNegsKept) + " of the " + Utils.comma(numbOrigNegExamples) + " negative examples.");
	//	Utils.waitHere("in prepareExamplesForTarget, useSamplingWithReplacementOnPos=" + useSamplingWithReplacementOnPos + ", useSamplingWithReplacementOnNeg=" + useSamplingWithReplacementOnNeg + ", ratioOfNegToPositiveEx=" + ratioOfNegToPositiveEx + ", samplePositiveProb=" + samplePositiveProb);
		setPosExamples(positiveExamples);
		setNegExamples(new ArrayList<Example>(0));
	//	Utils.waitHere();
    }

	

	/**
	 * @return the learnMultiValPredicates
	 */
	public boolean isLearnMultiValPredicates() {
		return learnMultiValPredicates;
	}
	/**
	 * @param learnMultiValPredicates the learnMultiValPredicates to set
	 */
	public void setLearnMultiValPredicates(boolean learnMultiValPredicates) {
		this.learnMultiValPredicates = learnMultiValPredicates;
		innerLoopTask.setLearnMultiVal(learnMultiValPredicates);
	}
	public Theory produceFinalTheory() {
		// TODO allow theories to come from some covering algorithm, possibly based on all the Gleaners.		
		Theory result = null;
		if (learningTreeStructuredTheory) {
			// Note: this code assumes all the heads have the same arguments, other than the last variables that stores the numeric answer. 
			// The renameAllVariables() is only used to make the tree-structured theory a bit more human readable.
			result = outerLoopState.getTreeBasedTheory().renameAllVariables().convertToStandardTheory(innerLoopTask.getInlineManager()).renameAllClausesWithUniqueBodyVariables(); // Cleanup the variable names and then convert to Horn clauses.
			
			/* For debugging ...
			TreeStructuredTheory r1 = outerLoopState.getTreeBasedTheory(); Utils.println("R1: " + r1);
			TreeStructuredTheory r2 = r1.renameAllVariables();             Utils.println("R2: " + r2);
			TreeStructuredTheory r3 = r2.convertToStandardTheory(innerLoopTask.getInlineManager()); Utils.println("R3: " + r3);
			TreeStructuredTheory r4 = r3.renameAllClausesWithUniqueBodyVariables();                 Utils.println("R4: " + r4);
			*/
			
		} else {
			result = getStdILPtheory(); // Is in-lining properly handled here?  Presumably this should happen when clauses are learned?
			if (learnMLNTheory) {
				Utils.println("adding regression values");
				for (Clause cl : result.getClauses()) {
					Term leafValue =  innerLoopTask.stringHandler.getNumericConstant(cl.getWeightOnSentence());
					Utils.println("Added " + cl.getWeightOnSentence() + " to " + cl);
					Literal      headCopy = cl.getDefiniteClauseHead();
					//List<Term>   args     = headCopy.getArguments();
					List<String> argNames = headCopy.getArgumentNames();
					if (argNames != null) {
						headCopy.addArgument(leafValue, "OutputVarTreeLeaf");
					} else {
						headCopy.addArgument(leafValue);
					}
					//args.add(leafValue);
					//if (argNames != null) { headCopy.addargNames.add("OutputVarTreeLeaf"); } // Presumably this is a unique name ...
					//Utils.println(cl.toString());
				}
				
			}
		}
		
		if (result == null) { return result; }
		
		if (!prefixForExtractedRules.equals("") || !postfixForExtractedRules.equals("")) { 
			Literal target = getTargetLiteral();
			if (!target.predicateName.isaTemporaryName(target.getArity() + (innerLoopTask.regressionTask ? 1 : 0))) { // Possibly add 1 since we add the output value for regression tasks.
				 target.predicateName.addTemporary(    target.getArity() + (innerLoopTask.regressionTask ? 1 : 0)); 
			}
			result.addPreAndPostfixToTemporaryNames(prefixForExtractedRules, postfixForExtractedRules); 
		}
		// Set inline mgr before simplifying
		result.setInlineHandler(this.innerLoopTask.getInlineManager());
		if (learningTreeStructuredTheory) { // Need to wait until any pre/post-fix stuff has been applied.
			return ((TreeStructuredTheory) result).createFlattenedClauses().simplify();
		}
		return result.simplify();
	}

	public String reportSearchStats() {
		return reportSearchStats(true); // Default is to not print out much info.
	}

	public String reportSearchStats(boolean briefVersion) {
		// if (briefVersion) ...
		String result = "% Created a total of "    + Utils.comma(getTotal_nodesCreated())
						+ " clauses and expanded " + Utils.comma(getTotal_nodesConsidered())
						+ " of them.\n"
						+ "% The collection of best clauses per cycle covers "
						+ Utils.comma(getNumberOfPosExamplesCovered()) + " (out of " + Utils.comma(isFlipFlopPosAndNegExamples() ? getNumberOfNegExamples() : getNumberOfPosExamples()) + ") pos and "
						+ Utils.comma(getNumberOfNegExamplesCovered()) + " (out of " + Utils.comma(isFlipFlopPosAndNegExamples() ? getNumberOfPosExamples() : getNumberOfNegExamples()) + ") neg examples.";
		
		if (getTotal_nodesNotAddedToOPENsinceMaxScoreTooLow()     > 0) { result += "\n% A total of " + Utils.comma(getTotal_nodesNotAddedToOPENsinceMaxScoreTooLow())     + " search nodes were not added to OPEN because their maximum score could not exceed the best score found so far."; }
        if (getTotal_nodesRemovedFromOPENsinceMaxScoreNowTooLow() > 0) { result += "\n% A total of " + Utils.comma(getTotal_nodesRemovedFromOPENsinceMaxScoreNowTooLow()) + " search nodes were removed from OPEN because their maximum score could not exceed the best score found so far."; }
        if (getTotal_countOfPruningDueToVariantChildren()         > 0) { result += "\n% A total of " + Utils.comma(getTotal_countOfPruningDueToVariantChildren())         + " search nodes were pruned because they were variant children."; }
        if (innerLoopTask.pruner != null) {
        	if (innerLoopTask.pruner.nodesPrunedDueToIntervalAnalysis     > 0) { result += "\n% A total of " + Utils.comma(innerLoopTask.pruner.nodesPrunedDueToIntervalAnalysis)     + " nodes pruned due to interval analysis."; }
        	if (innerLoopTask.pruner.nodesPrunedDueToSingleClauseAnalysis > 0) { result += "\n% A total of " + Utils.comma(innerLoopTask.pruner.nodesPrunedDueToSingleClauseAnalysis) + " nodes pruned due to within-clause analysis.";}
        }
        
        return result;
	}

   /** Bridge method to ILPMain.main(String[]) method.
    *
    * Please update your code to use ILPMain.main() instead of ILPouterLoop.main().
    *
	* @param args
	* @throws SearchInterrupted
    * @throws IOException 
    * @deprecated
	*/
	@Deprecated
	public static void main(String[] args) throws SearchInterrupted, IOException {
       ILPMain.main(args);
   }

    /**
     * @return the outerLoopState
     */
    public ILPouterLoopState getOuterLoopState() {
        return outerLoopState;
    }

    /**
     * @param outerLoopState the outerLoopState to set
     */
    protected void setOuterLoopState(ILPouterLoopState outerLoopState) {
        this.outerLoopState = outerLoopState;
    }

    /** Attempts to write a checkpoint file to disk.
     *
     * This may throw an error if the checkpoint cannot be written.  I could
     * catch the errors here, but I am afraid that an error later will
     * break the checkpointing silently.
     *
     * If you want to silence these error (or just print an error message and
     * continue), just comment out the Utils.error.
     *
     */
    protected void writeCheckpoint()  {

        String filename = getCheckpointFileName();

        outerLoopState.setNumberOfNegExamples( innerLoopTask.getNumberOfNegExamples());
        outerLoopState.setNumberOfPosExamples( innerLoopTask.getNumberOfPosExamples());

        ObjectOutputStream oos = null;
        try {
            oos = new ObjectOutputStream(new GZIPOutputStream(new CondorFileOutputStream(filename)));
            oos.writeObject(outerLoopState); // Store outer loop state...
            //oos.writeObject(innerLoopTask.getLearnOneClauseState()); // Store inner loop state...
            oos.writeObject(getGleaner()); // Store the gleaner...
            oos.close();
        } catch (Exception ex) {
            String msg = "Unable to write checkpoint file: " + filename + ".  Error message: " + ex.getClass().getCanonicalName() + ": " + ex.getMessage();
            //Utils.println(msg);
            Utils.error(msg);
        } finally {
            try {
                if ( oos != null ) oos.close();
            } catch (IOException ex) {
            }
        }
    }

    /** Attempts to restore a checkpoint file from disk.
     *
     * Unlike writeCheckpoint, this method will never throw an exception.  It
     * is assumed that the checkpoint file may not exist or may exist, but is
     * from a previous search.
     *
     * If the checkpoint does exists and appears to be from this search, this method
     * will automatically update the ILPouterLoop information (along with the inner
     * loop information) with the checkpoint search state.
     *
     * Note, this method requires the ILPouterLoop to be setup and ready to start
     * a search, since it uses this information to both reconstitute the checkpoint
     * and verify that the checkpoint is valid.
     *
     * @return True if the checkpoint was found and the search was resumed.  False
     *        if either the checkpoint is missing or incompatible.
     */
    protected boolean readCheckpoint() {
        String filename = getCheckpointFileName();

        ILPObjectInputStream ilpois = null;
        boolean result = false;
        try {
            HandleFOPCstrings stringHandler = innerLoopTask.getStringHandler();

            ilpois = new ILPObjectInputStream(new GZIPInputStream(new CondorFileInputStream(filename)), stringHandler, innerLoopTask);

            ILPouterLoopState chkptOuterLoopState = (ILPouterLoopState) ilpois.readObject();
            Gleaner theGleaner = (Gleaner) ilpois.readObject();

            try {
                chkptOuterLoopState.checkStateCongruency(outerLoopState);
                //chkptInnerLoopState.checkStateCongruency(innerLoopTask.getLearnOneClauseState());
                // We found a valid checkpoint, so let's replace the state information of
                // the current search with the checkpoint information...

                setOuterLoopState(chkptOuterLoopState);

                if ( theGleaner != null ) {
                    setGleaner(theGleaner);
                }

                result = true;
            }
            catch(IncongruentSavedStateException ex) {
                Utils.println(ex.getMessage());
            }

            ilpois.close();
            ilpois = null;

        } catch (FileNotFoundException ex) {

        } catch (IOException ex) {
                Utils.println("Exception occurred reading checkpoint file: " + ex.getClass() + ": " + ex.getMessage());
        } catch (ClassNotFoundException classNotFoundException) {
        } finally {
            if ( ilpois != null ) try {
                ilpois.close();
                ilpois = null;
            } catch (IOException ex) {
            }
        }
        
        return result;
    }

    /** Removes the checkpoint file for the current fold.
     * 
     */
    protected void deleteCheckpoint()  {
        String filename = getCheckpointFileName();
        File f = new CondorFile(filename);

        if ( f.exists() ) {
            f.delete();
        }
    }

    protected void clearSeedPosExamplesUsed() {
        outerLoopState.clearSeedPosExamplesUsed();
    }

    protected void clearSeedNegExamplesUsed() {
        outerLoopState.clearSeedNegExamplesUsed();
    }

    public final void setGleaner(Gleaner gleaner) {
    	Gleaner oldGleaner = (Gleaner) innerLoopTask.getGleaner(); // cth updated to pass structured output flag
        innerLoopTask.setGleaner(gleaner);
        
    	if ( gleaner == null ) { return; }
    	gleaner.setFileNameProvider(this);
        gleaner.setILPouterLooper(this);	
      	if (oldGleaner != null) { gleaner.setUseStructuredOutput(oldGleaner.getUseStructuredOutput()); }
        // cth updated to make structured output flag (for visualizer) persistent, based on notes from Jude
        if (oldGleaner != null) { gleaner.setUseStructuredOutput(oldGleaner.getUseStructuredOutput()); }
        this.gleaner = gleaner;
      	gleanerFlipFlopped = new Gleaner();
      	gleanerFlipFlopped.setFileNameProvider(this);
      	gleanerFlipFlopped.setILPouterLooper(this); 
      	gleanerFlipFlopped.setUseStructuredOutput(gleaner.getUseStructuredOutput());
    }

    public Gleaner getGleaner() {
        if ( innerLoopTask.searchMonitor instanceof Gleaner ) {
            return (Gleaner) innerLoopTask.searchMonitor;
        }
		return null;
    }

    /**
     * @return the checkpointEnabled
     */
    public boolean isCheckpointEnabled() {
        return checkpointEnabled;
    }

    /**
     * @param checkpointEnabled the checkpointEnabled to set
     */
    public void setCheckpointEnabled(boolean checkpointEnabled) {
        this.checkpointEnabled = checkpointEnabled;
    }

    public void proveExamples(Clause clause, Collection<Example> inputExamples, Collection<Example> trueExamples, Collection<Example> falseExamples) {
        innerLoopTask.proveExamples(clause, inputExamples, trueExamples, falseExamples);
    }

    public boolean proveExample(Clause clause, Example ex) {
        return innerLoopTask.proveExample(clause, ex);
    }

    public CoverageScore getWeightedCoverageOnTrainingExamples(Clause clause) {
        return getWeightedCoverage(clause, getPosExamples(), getNegExamples());
    }

    public CoverageScore getWeightedCoverage(Theory theory, Collection<Example> positiveExamples, Collection<Example> negativeExamples, CoverageScore coverageScore) {
        return innerLoopTask.getWeightedCoverage(theory, positiveExamples, negativeExamples, coverageScore);
    }

    public CoverageScore getWeightedCoverage(Theory theory, Collection<Example> positiveExamples, Collection<Example> negativeExamples) {
        return innerLoopTask.getWeightedCoverage(theory, positiveExamples, negativeExamples);
    }

    public CoverageScore getWeightedCoverage(Clause clause, Collection<Example> positiveExamples, Collection<Example> negativeExamples, CoverageScore coverageScore) {
        return innerLoopTask.getWeightedCoverage(clause, positiveExamples, negativeExamples, coverageScore);
    }

    public CoverageScore getWeightedCoverage(Clause clause, Collection<Example> positiveExamples, Collection<Example> negativeExamples) {
        return innerLoopTask.getWeightedCoverage(clause, positiveExamples, negativeExamples);
    }

    private void setupAdvice() {
        if ( innerLoopTask.isRelevanceEnabled() && getActiveAdvice() == null) {
            createdActiveAdvice = innerLoopTask.getAdviceProcessor().processAdvice(innerLoopTask.getCurrentRelevanceStrength(), getPosExamples(), getNegExamples());
            setActiveAdvice(createdActiveAdvice);
        }
    }

    private void unsetAdvice() {
        if ( createdActiveAdvice != null ) {
            innerLoopTask.getAdviceProcessor().retractRelevanceAdvice();
            setActiveAdvice(null);
            createdActiveAdvice = null;
        }
    }

    public ActiveAdvice getActiveAdvice() {
        return innerLoopTask.getActiveAdvice();
    }

    public void setActiveAdvice(ActiveAdvice activeAdvice) {
        innerLoopTask.setActiveAdvice(activeAdvice);
    }

    // <editor-fold defaultstate="collapsed" desc="Getters and Setters">
    protected void setTotal_nodesRemovedFromOPENsinceMaxScoreNowTooLow(int total_nodesRemovedFromOPENsinceMaxScoreNowTooLow) {
        outerLoopState.setTotal_nodesRemovedFromOPENsinceMaxScoreNowTooLow(total_nodesRemovedFromOPENsinceMaxScoreNowTooLow);
    }

    protected void setTotal_nodesNotAddedToOPENsinceMaxScoreTooLow(int total_nodesNotAddedToOPENsinceMaxScoreTooLow) {
        outerLoopState.setTotal_nodesNotAddedToOPENsinceMaxScoreTooLow(total_nodesNotAddedToOPENsinceMaxScoreTooLow);
    }

    protected void setTotal_nodesCreated(int total_nodesCreated) {
        outerLoopState.setTotal_nodesCreated(total_nodesCreated);
    }

    protected void setTotal_nodesConsidered(int total_nodesConsidered) {
        outerLoopState.setTotal_nodesConsidered(total_nodesConsidered);
    }

    protected void setTotal_countOfPruningDueToVariantChildren(int total_countOfPruningDueToVariantChildren) {
        outerLoopState.setTotal_countOfPruningDueToVariantChildren(total_countOfPruningDueToVariantChildren);
    }

    protected void setStdILPtheory(Theory stdILPtheory) {
        outerLoopState.setStdILPtheory(stdILPtheory);
    }

    protected void setPosSeedIndicesToUse(int[] posSeedIndicesToUse) {
        outerLoopState.setPosSeedIndicesToUse(posSeedIndicesToUse);
    }

    protected void setNumberOfPosExamplesCovered(int numberOfPosExamplesCovered) {
        outerLoopState.setNumberOfPosExamplesCovered(numberOfPosExamplesCovered);
    }

    protected void setNumberOfNegExamplesCovered(int numberOfNegExamplesCovered) {
        outerLoopState.setNumberOfNegExamplesCovered(numberOfNegExamplesCovered);
    }

    protected void setNumberOfLearnedClauses(int numberOfLearnedClauses) {
        outerLoopState.setNumberOfLearnedClauses(numberOfLearnedClauses);
    }

    protected void setNumberOfCycles(int numberOfCycles) {
        outerLoopState.setNumberOfCycles(numberOfCycles);
    }

    protected void setLengthPosSeedArray(int lengthPosSeedArray) {
        outerLoopState.setLengthPosSeedArray(lengthPosSeedArray);
    }

    protected void setIndexIntoPosSeedArray(int indexIntoPosSeedArray) {
        outerLoopState.setIndexIntoPosSeedArray(indexIntoPosSeedArray);
    }

    protected void setFractionOfPosCovered(double fractionOfPosCovered) {
        outerLoopState.setFractionOfPosCovered(fractionOfPosCovered);
    }

    protected void setFractionOfNegCovered(double fractionOfNegCovered) {
        outerLoopState.setFractionOfNegCovered(fractionOfNegCovered);
    }

    protected void setCoveredPosExamples(Collection<Example> coveredPosExamples) {
        outerLoopState.setCoveredPosExamples(coveredPosExamples);
    }

    protected void setCoveredNegExamples(Collection<Example> coveredNegExamples) {
        outerLoopState.setCoveredNegExamples(coveredNegExamples);
    }

    public int getTotal_nodesRemovedFromOPENsinceMaxScoreNowTooLow() {
        return outerLoopState.getTotal_nodesRemovedFromOPENsinceMaxScoreNowTooLow();
    }

    public int getTotal_nodesNotAddedToOPENsinceMaxScoreTooLow() {
        return outerLoopState.getTotal_nodesNotAddedToOPENsinceMaxScoreTooLow();
    }

    public int getTotal_nodesCreated() {
        return outerLoopState.getTotal_nodesCreated();
    }

    public int getTotal_nodesConsidered() {
        return outerLoopState.getTotal_nodesExpanded();
    }

    public int getTotal_countOfPruningDueToVariantChildren() {
        return outerLoopState.getTotal_countOfPruningDueToVariantChildren();
    }

    public Theory getLearnedTheory() {
        if (learningTreeStructuredTheory) {
            return outerLoopState.getTreeBasedTheory();
        }
        return outerLoopState.getStdILPtheory();
    }

    public Theory getStdILPtheory() {
        return outerLoopState.getStdILPtheory();
    }

    public TreeStructuredTheory getTreeBasedTheory() {
        return outerLoopState.getTreeBasedTheory();
    }

    public int[] getPosSeedIndicesToUse() {
        return outerLoopState.getPosSeedIndicesToUse();
    }

    public int getNumberOfPosExamplesCovered() {
        return outerLoopState.getNumberOfPosExamplesCovered();
    }

    public int getNumberOfPosExamples() {
        return innerLoopTask.getNumberOfPosExamples();
    }

    public int getNumberOfNegExamplesCovered() {
        return outerLoopState.getNumberOfNegExamplesCovered();
    }

    public int getNumberOfNegExamples() {
        return innerLoopTask.getNumberOfNegExamples();
    }

    public int getNumberOfLearnedClauses() {
        return outerLoopState.getNumberOfLearnedClauses();
    }

    public int getNumberOfCycles() {
        return outerLoopState.getNumberOfCycles();
    }

    public int getLengthPosSeedArray() {
        return outerLoopState.getLengthPosSeedArray();
    }

    public int getIndexIntoPosSeedArray() {
        return outerLoopState.getIndexIntoPosSeedArray();
    }

    public double getFractionOfPosCovered() {
        return outerLoopState.getFractionOfPosCovered();
    }

    public double getFractionOfNegCovered() {
        return outerLoopState.getFractionOfNegCovered();
    }

    public Collection<Example> getCoveredPosExamples() {
        return outerLoopState.getCoveredPosExamples();
    }

    public Collection<Example> getCoveredNegExamples() {
        return outerLoopState.getCoveredNegExamples();
    }

    public double getOverallMinPosWeight() {
        return outerLoopState.getOverallMinPosWeight();
    }

    public void setOverallMinPosWeight(double wgt) {
        outerLoopState.setOverallMinPosWeight(wgt);
    }
    
    private boolean canStillMeetPrecisionRecallAccuracyF1specs(boolean printReason) {
    	if (minimalAcceptablePrecision > 0 && bestPossibleWeightedPrecision() < minimalAcceptablePrecision) {
    		if (printReason) {  reportOuterLooperStatus("\n% STATUS OF THE OUTER LOOPER:");
    							Utils.warning("%  Have stopped ILP's outer loop because the best possible (weighted) precision is " 
    											+ Utils.truncate(bestPossibleWeightedPrecision(), 2) + ", and that does not meet the specification of " + Utils.truncate(minimalAcceptablePrecision, 3) + ".", 1); }
    		return false;
    	}
    	if (minimalAcceptableRecall    > 0 && bestPossibleWeightedRecall()    < minimalAcceptableRecall) {
    		if (printReason) {  reportOuterLooperStatus("\n% STATUS OF THE OUTER LOOPER:");
								Utils.warning("%  Have stopped ILP's outer loop because the best possible (weighted) recall is " 
    											+ Utils.truncate(bestPossibleWeightedRecall(), 2)   + ", and that does not meet the specification of "  + Utils.truncate(minimalAcceptableRecall,    3) + ".", 1); }
    		return false;
    	}
    	if (minimalAcceptableAccuracy  > 0 && bestPossibleWeightedAccuracy()  < minimalAcceptableAccuracy) {
    		if (printReason) {  reportOuterLooperStatus("\n% STATUS OF THE OUTER LOOPER:");
								Utils.warning("%  Have stopped ILP's outer loop because the best possible (weighted) accuracy is " 
    											+ Utils.truncate(bestPossibleWeightedAccuracy(), 2) + ", and that does not meet the specification of "  + Utils.truncate(minimalAcceptableAccuracy,  3) + ".", 1); }
    		return false;
    	}
    	if (minimalAcceptableRecall    > 0 && bestPossibleWeightedF1()        < minimalAcceptableF1) {
    		if (printReason) {  reportOuterLooperStatus("\n% STATUS OF THE OUTER LOOPER:");
								Utils.warning("%  Have stopped ILP's outer loop because the best possible (weighted) F1 is " 
    											+ Utils.truncate(bestPossibleWeightedF1(), 2) + ", and that does not meet the specification of "        + Utils.truncate(minimalAcceptableF1,        3) + ".", 1); }
    		return false;
    	}
    	return true;
    }
    
    private void reportOuterLooperStatus(String firstMsg) {
    	if (firstMsg != null) { Utils.println(firstMsg); }
		Utils.println("%  getNumberOfLearnedClauses() = " + getNumberOfLearnedClauses() + " vs " + Utils.comma(maxNumberOfClauses));
		Utils.println("%  getNumberOfCycles()         = " + getNumberOfCycles()         + " vs " + Utils.comma(maxNumberOfCycles));
		Utils.println("%  getFractionOfPosCovered()   = " + getFractionOfPosCovered()   + " vs " + Utils.comma(minFractionOfPosCoveredToStop));
		Utils.println("%  getTotal_nodesConsidered()  = " + getTotal_nodesConsidered()  + " vs " + Utils.comma(max_total_nodesExpanded));
		Utils.println("%  getTotal_nodesCreated()     = " + getTotal_nodesCreated()     + " vs " + Utils.comma(max_total_nodesCreated));
		Utils.println("%  getClockTimeUsedInMillisec()          = " + getClockTimeUsedInMillisec()          + " vs " + Utils.comma(getMaximumClockTimeInMillisec()) );
    }

    // Assume the next learned clause will cover all the currently uncovered positive and none of the currently uncovered negative examples.
	private double bestPossibleWeightedPrecision() {
		double totalPosWgt = innerLoopTask.getTotalPosWeight();
	//	double totalNegWgt = innerLoopTask.getTotalNegWeight();
		double totalCoveredNegWgt = 0.0;
		
		for (Example ex : getCoveredNegExamples()) { totalCoveredNegWgt += ex.getWeightOnExample(); } // We only do this after every clause, so don't worry about the recomputation.
		return totalPosWgt / (totalCoveredNegWgt + totalPosWgt);
	}
	private double bestPossibleWeightedRecall() {
		return 1.0; // Ignoring m-estimates, can always cover all positives (but still left this in for completeness).
	}
	private double bestPossibleWeightedAccuracy() {
		double totalPosWgt = innerLoopTask.getTotalPosWeight();
		double totalNegWgt = innerLoopTask.getTotalNegWeight();
		double totalCoveredNegWgt = 0.0;
		
		for (Example ex : getCoveredNegExamples()) { totalCoveredNegWgt += ex.getWeightOnExample(); } // We only do this after every clause, so don't worry about the recomputation.
		return (totalPosWgt + (totalNegWgt - totalCoveredNegWgt)) / (totalPosWgt + totalNegWgt) ;
	}
    private double bestPossibleWeightedF1() {
		return Utils.getF1(bestPossibleWeightedPrecision(), bestPossibleWeightedRecall());
	}

	/**
     * @return the baseDirectory
     */
    public String getWorkingDirectory() {
        return workingDirectory;
    }

    /**
     * @param workingDirectory the workingDirectory to set
     */
    public final void setWorkingDirectory(String workingDirectory) {
        this.workingDirectory = workingDirectory;
    }

    /**
     * @return the checkpointFileName
     */
    public String getCheckpointFileName() {

        if ( checkpointFileName == null ) {
            String flipFlop = isFlipFlopPosAndNegExamples() ? "_flipFlopped" : "";
            String rrr = isRRR() ? "RRR" : "Std";
            return getWorkingDirectory() + "/" + getPrefix() + rrr + flipFlop + getFoldInfoString() + ".chkpt.gz";
        }

        return checkpointFileName;
    }

    /**
     * @param checkpointFileName the checkpointFileName to set
     */
    public void setCheckpointFileName(String checkpointFileName) {
        this.checkpointFileName = checkpointFileName;
    }
    public void setCheckpointFileNameFlipFlopped(String checkpointFileName) {
        this.checkpointFileNameFlipFlopped = checkpointFileName;
    }

    public final void setRRR(boolean useRRR) {
        outerLoopState.setRRR(useRRR);
    }

    public final void setPrefix(String prefix) {
        outerLoopState.setPrefix(prefix);
    }

    public void setFlipFlopPosAndNegExamples(boolean flipFlopPosAndNegExamples) {
    //	Utils.println("% ILPouterLoop: flipFlopPosAndNegExamples = " + flipFlopPosAndNegExamples);
        outerLoopState.setFlipFlopPosAndNegExamples(flipFlopPosAndNegExamples);
        if (flipFlopPosAndNegExamples) {
        	if (gleanerFlipFlopped != null) { setGleaner(gleanerFlipFlopped); }
        } else {
        	if (gleaner            != null) { setGleaner(gleaner); }
        }
    }

    public boolean isFlipFlopPosAndNegExamples() {
    	//Utils.println("% ILPouterLoop: isFlipFlopPosAndNegExamples = " + outerLoopState.isFlipFlopPosAndNegExamples());
        return outerLoopState == null ? false : outerLoopState.isFlipFlopPosAndNegExamples();
    }

    public void setAnnotationForCurrentRun(String annotationForRun) {
    	//Utils.println("% ILPouterLoop: setAnnotationForCurrentRun = " + annotationForRun);
    	this.annotationForRun = annotationForRun;
    }
    public String getAnnotationForCurrentRun() {
    	//Utils.println("% ILPouterLoop: getAnnotationForCurrentRun = " + annotationForRun);
    	return annotationForRun;
    }

    public boolean isRRR() {
        return outerLoopState.isRRR();
    }

    public String getPrefix() {
        return outerLoopState.getPrefix();
    }

    public String directoryForGleanerFile = null; // Allow overriding of where Gleaner files go.
    /**
     * @return the gleanerFileName
     */
    public String getGleanerFileName() {
    	// Utils.waitHere("getGleanerFileName: flip? " +  isFlipFlopPosAndNegExamples() + "\ngleanerFileName=" + gleanerFileName + "\ngleanerFileNameFlipFlopped=" + gleanerFileNameFlipFlopped);

    	if (isFlipFlopPosAndNegExamples()) {
    		if ( gleanerFileNameFlipFlopped == null ) {
    			String rrr = isRRR() ? "RRR" : ""; // "Std";

    			gleanerFileNameFlipFlopped = (directoryForGleanerFile != null ? directoryForGleanerFile : getWorkingDirectory()) + "/" + getPrefix() + rrr + "_flipFlopped" + getFoldInfoString() + "_gleaner";
    		}
    		Utils.ensureDirExists(gleanerFileNameFlipFlopped);
    		return gleanerFileNameFlipFlopped;
        }

    	if ( gleanerFileName == null ) {
			String rrr = isRRR() ? "RRR" : ""; // "Std";

			gleanerFileName = (directoryForGleanerFile != null ? directoryForGleanerFile : getWorkingDirectory()) + "/" + getPrefix() + rrr + getFoldInfoString() + "_gleaner";
		}
		Utils.ensureDirExists(gleanerFileName);
        return gleanerFileName;
    }

    public String getResultFileNameForFold(int fold) {
        String foldText = fold == -1 ? "" : "_fold" + fold;
        return getWorkingDirectory() + "/" + getExtendedPrefix() + foldText + ".results.gz";
    }

    /**
     * @param gleanerFileName the gleanerFileName to set
     */
    public void setGleanerFileName(String gleanerFileName) {
    	Utils.ensureDirExists(gleanerFileName);
        this.gleanerFileName = gleanerFileName;
    }
    /**
     * @param gleanerFileNameFlipFlopped the gleanerFileNameFlipFlopped to set
     */
    public void setGleanerFileNameFlipFlopped(String gleanerFileNameFlipFlopped) {
    	Utils.ensureDirExists(gleanerFileNameFlipFlopped);
        this.gleanerFileNameFlipFlopped = gleanerFileNameFlipFlopped;
    }

    public String getExtendedPrefix() {
            String flipFlop = isFlipFlopPosAndNegExamples() ? "_ff" : "";
            String rrr = isRRR() ? "_rrr" : "";

            return getPrefix() + rrr + flipFlop;
    }

    /** Sets the PosExamples to use for the search.
     *
     * This is just a convenience method.  The list is actually stored in the LearnOneClause object.
     *
     * @param posExamples the posExamples to set
     */
    public void setPosExamples(List<Example> posExamples) {
        innerLoopTask.setPosExamples(posExamples);
    }

    /** Sets the NegExamples to use for the search.
     *
     * This is just a convenience method.  The list is actually stored in the LearnOneClause object.
     *
     * @param negExamples the negExamples to set
     */
    public void setNegExamples(List<Example> negExamples) {
        innerLoopTask.setNegExamples(negExamples);
    }

    /** Returns the PosExamples to use for the search.
     *
     * This is just a convenience method.  The list is actually stored in the LearnOneClause object.
     *
     * @return
     */
    public List<Example> getPosExamples() {
        return innerLoopTask.getPosExamples();
    }

    /** Returns the NegExamples to use for the search.
     *
     * This is just a convenience method.  The list is actually stored in the LearnOneClause object.
     *
     * @return
     */
    public List<Example> getNegExamples() {
        return innerLoopTask.getNegExamples();
    }

    /**
     * @return the evaltSetPosExamples
     */
    public List<Example> getEvalSetPosExamples() {
        return evalSetPosExamples;
    }

    /**
     * @param evalSetPosExamples the evaSetPosExamples to set
     */
    public void setEvalSetPosExamples(List<Example> evaSetPosExamples) {
        this.evalSetPosExamples = evaSetPosExamples;
    }

    /**
     * @return the evalSetNegExamples
     */
    public List<Example> getEvalSetNegExamples() {
        return evalSetNegExamples;
    }

    /**
     * @param evalSetNegExamples the evalSetNegExamples to set
     */
    public void setEvalSetNegExamples(List<Example> evalSetNegExamples) {
        this.evalSetNegExamples = evalSetNegExamples;
    }

    public Set<Example> getNegExamplesUsedAsSeeds() {
        return outerLoopState.getNegExamplesUsedAsSeeds();
    }

    protected void setSeedPosExamplesUsed(Set<Example> seedPosExamplesUsed) {
        outerLoopState.setSeedPosExamplesUsed(seedPosExamplesUsed);
    }

    protected void setSeedNegExamplesUsed(Set<Example> seedNegExamplesUsed) {
        outerLoopState.setSeedNegExamplesUsed(seedNegExamplesUsed);
    }

    protected Set<Example> getSeedPosExamplesUsed() {
        return outerLoopState.getSeedPosExamplesUsed();
    }

    protected Set<Example> getSeedNegExamplesUsed() {
        return outerLoopState.getSeedNegExamplesUsed();
    }


    public void setMaximumClockTimeInMillisec(long maximumClockTime) {
    	if (maximumClockTime < 0) { Utils.waitHere("setMaximumClockTime = " + maximumClockTime); }
        outerLoopState.setMaximumClockTimeInMillisec(maximumClockTime);
    }

    protected void setClockTimeUsedInMillisec(long clockTimeUsed) {
        outerLoopState.setClockTimeUsedInMillisec(clockTimeUsed);
    }

    public long getMaximumClockTimeInMillisec() {
        return outerLoopState.getMaximumClockTimeInMillisec();
    }

    public long getClockTimeUsedInMillisec() {
        return outerLoopState.getClockTimeUsedInMillisec();
    }

    /** Returns the amount of time in milliseconds left for the search.
     *
     * @return
     */
    public long getTimeAvailableInMillisec() {
       return getMaximumClockTimeInMillisec() == Long.MAX_VALUE ? Long.MAX_VALUE : Math.max(0, getMaximumClockTimeInMillisec() - getClockTimeUsedInMillisec());
    }

    public HornClauseContext getContext() {
        return innerLoopTask.getContext();
    }

    public void setMaxAcceptableNodeScoreToStop(double score) {
    	outerLoopState.maxAcceptableNodeScoreToStop = score;
    }

    public double getMaxAcceptableNodeScoreToStop() {
    	return outerLoopState.maxAcceptableNodeScoreToStop;
    }

	public int getMaxNumberOfLiteralsAtAnInteriorNode() {
		return maxNumberOfLiteralsAtAnInteriorNode;
	}

	public void setMaxNumberOfLiteralsAtAnInteriorNode(int maxNumberOfLiteralsAtAnInteriorNode) {
		this.maxNumberOfLiteralsAtAnInteriorNode = Math.max(1, maxNumberOfLiteralsAtAnInteriorNode);
	}

	public int getMaxTreeDepthInLiterals() {
		return maxTreeDepthInLiterals;
	}

	public void setMaxTreeDepthInLiterals(int maxTreeDepthInLiterals) {
		this.maxTreeDepthInLiterals = Math.max(1, maxTreeDepthInLiterals);
	}

	public String getPrefixForExtractedRules() {
		return prefixForExtractedRules;
	}

	public void setPrefixForExtractedRules(String prefixForExtractedRules) {
		this.prefixForExtractedRules = prefixForExtractedRules;
	}

	public String getPostfixForExtractedRules() {
		return postfixForExtractedRules;
	}

	public void setPostfixForExtractedRules(String postfixForExtractedRules) {
		this.postfixForExtractedRules = postfixForExtractedRules;
	}

    /**
	 * @return the "maxTreeDepthInInteriorNodes
	 */
	public int getMaxTreeDepth() {
		return maxTreeDepthInInteriorNodes;
	}

	/**
	 * @param maxTreeDepth the maxTreeDepth to set
	 */
	public void setMaxTreeDepth(int maxTreeDepth) {
		this.maxTreeDepthInInteriorNodes = Math.max(1, maxTreeDepth);
	}


    // </editor-fold>

}
