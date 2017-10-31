/**
 *
 */
package edu.wisc.cs.will.ILP;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.Reader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;
import javax.swing.event.EventListenerList;

import edu.wisc.cs.will.Boosting.EM.HiddenLiteralState;
import edu.wisc.cs.will.Boosting.OneClass.PairWiseExampleScore;
import edu.wisc.cs.will.DataSetUtils.ArgSpec;
import edu.wisc.cs.will.DataSetUtils.CreateSyntheticExamples;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.DataSetUtils.RegressionExample;
import edu.wisc.cs.will.DataSetUtils.TypeManagement;
import edu.wisc.cs.will.DataSetUtils.WorldState;
import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Constant;
import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.LiteralToThreshold;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.PredicateSpec;
import edu.wisc.cs.will.FOPC.ProcedurallyDefinedPredicateHandler;
import edu.wisc.cs.will.FOPC.RelevanceStrength;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.SentenceAsTerm;
import edu.wisc.cs.will.FOPC.StringConstant;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Theory;
import edu.wisc.cs.will.FOPC.Type;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.FOPC.UniversalSentence;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.ILP.Regression.RegressionInfoHolder;
import edu.wisc.cs.will.ILP.Regression.RegressionInfoHolderForMLN;
import edu.wisc.cs.will.ILP.Regression.RegressionInfoHolderForRDN;
import edu.wisc.cs.will.ILP.Regression.RegressionVectorInfoHolderForRDN;
import edu.wisc.cs.will.ResThmProver.DefaultHornClauseContext;
import edu.wisc.cs.will.ResThmProver.DefaultHornClausebase;
import edu.wisc.cs.will.ResThmProver.DefaultProof;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.ResThmProver.HornClauseProver;
import edu.wisc.cs.will.ResThmProver.HornClausebase;
import edu.wisc.cs.will.ResThmProver.LazyHornClausebase;
import edu.wisc.cs.will.ResThmProver.Proof;
import edu.wisc.cs.will.ResThmProver.ProofDone;
import edu.wisc.cs.will.ResThmProver.InitHornProofSpace;
import edu.wisc.cs.will.Utils.NamedReader;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CompressedFileReader;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.Utils.condor.CondorFileOutputStream;
import edu.wisc.cs.will.Utils.condor.CondorFileReader;
import edu.wisc.cs.will.Utils.condor.CondorFileWriter;
import edu.wisc.cs.will.stdAIsearch.BestFirstSearch;
import edu.wisc.cs.will.stdAIsearch.EndTest;
import edu.wisc.cs.will.stdAIsearch.Initializer;
import edu.wisc.cs.will.stdAIsearch.OpenList;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchMonitor;
import edu.wisc.cs.will.stdAIsearch.SearchResult;
import edu.wisc.cs.will.stdAIsearch.SearchStrategy;
import edu.wisc.cs.will.stdAIsearch.StateBasedSearchTask;
import java.io.PrintStream;
 
/**
 * @author shavlik
 *
 * This is the ILP inner loop.  See broad-based comments in ILPouterLoop.java
 *
 *
 * TODO list: (not meant to be understood by users - this is simply a place to collect local notes)
 *
 *
 *
 *  check for other uses of cached files (other than neg examples?)
 *    document all the cached files in one place!
 *
 *
 * 	post-pruning code: drop one literal (if legal to do so?) and repeat as long as progress made
 * 		- maybe say unacceptable if ANY pos are lost?  Are using F1 as the heuristic to hill climb?
 *
 * 		figure out how to avoid too many outer parents when printString'ing
 *
 * List<Example> coveredPosExamplesThisCycle = innerLoopTask.collectPosExamplesCovered(bestNode); NEED TO DO THIS MORE EFFICIENTLY!
 *
      Handle these (for both pos and neg)
:- jws_set(positive_examples_filtered_out,        25).
:- jws_set(inverse_sampling_rate_of_neg_examples, 4.0000).

		if something is no good in RRR for one set of seeds,
		it will also be no good for restarts in that seed
			- keep a hashmap for these  KEEP SAME ROOT

			save gleaner after every N outer loops?


 *        no hits to these (not even 2x)
 *          between_args_frequencies.b:mode: phrase_contains_several_between_10x_word(+phrase, #arg, #pos,        +fold). %  +fold was #fold
            between_args_frequencies.b:precompute1: phrase_contains_several_between_10x_word(Phrase, Arg, POS,        Fold) :-
 *
 *        need to figure out to deal with CLAUSES during parsing (for now, 'canPrune(Literal lit)' does not allow pruning with such cases).
 *
 *        infer modes through deduction and not just from basic facts?  or too cpu-complicated?
 *
 *        in 'precompute:' allow a file name to be provided?  leave for later, since complicated bookkeeping
 *
 *
 *        allow other specs about predicates:
 *
 *        	symmetric: p/2  <-- use this in creating neg examples
 *          symmetric: p(s,s,s,_,_) <-- any permutation of the s's equivalent
 *          etc
//:- symmetric(different_phrases/2).  <-- automatically create prune rules
// :- symmetric(different_words/2).
 *
 *        allow inference of types to be turned off - with some sort of parser command
 *
 *        handle a fact like (where X is a variable):   s(1, X).
 *
 *        make use of 'target' in modes - can put on hold
 * *
 *        accept Aleph's spec for modes?  and for determinations?  - can put on hold
 *   *
 *  	  have an argument that means: clear all cached files (gleaner, precomputed, etc)
 *
 *  	  have a "checkpoint" facility
 *  	  need gleaner to also do this (write and read)
 *
 *
 *  	  here's a Prolog benchmark: http://www.sics.se/sicstus/bench.pl
 *
 *       add Vitor's trick to see if current clause same as previous (maybe hold N such clauses?)
 *          - index by parent node (don't want to "reuse" two nodes with different parents)
 *          - doesn't happen w/o the bottom clause, though confirm current code removes duplicates
 *
 *      think through the Exists stuff and MLNs
 *
 *		allow facts to include lessThan(small, medium) <- assume transitivity [this allows "tiles" to be used on symbolic constants]
 *
 *		if facts have variables in then, is the naming done properly?  probably not ...
 * *
 */

public class LearnOneClause extends StateBasedSearchTask {
	protected final static int    debugLevel = 0; // Used to control output from this project (0 = no output, 1=some, 2=much, 3=all).
	
	public    boolean             needToCheckTheAdviceProcessor     = true;    // Added (7/18/10) by JWS so that we can have advice persist across all the calls of outer looper to this (ie, the inner looper).
	
	private   boolean             ignoreNegatedLiterals             = false;   // Added (11/11/10) by JWS.  When learning TREE-structured theories and only considering ONE literal at a node, no need to consider P and not_P since the branches involve both cases.
	
	public    boolean             whenComputingThresholdsWorldAndStateArgsMustBeWorldAndStateOfAcurrentExample = true; // This will prevent test sets bleeding unto train set (if these stringHandler.locationOfWorldArg or stringHandler.locationOfStateArg are -1, then matching is not required).

	public    boolean             createCacheFiles                  = false;   // Create files that cache computations, to save time, for debugging, etc.
	public    boolean             useCachedFiles                    = false;   // Files cached (if requested):
	                                                                           //    prune.txt (or whatever Utils.defaultFileExtensionWithPeriod is)
																			   //    types.txt
	                                                                           //    gleaner.txt (users can name this whatever they wish)
																			   //    the generated negative examples (same file name as used for negatives)
	
	public    boolean             loadAllLibraries                  = true;
	public    boolean             loadAllBasicModes                 = true; // TODO - these should be lower than the features used for the task; currently handled via cost.
	
	public    boolean             overwritePruneFileIfExists        = false;
	public    boolean             overwritePrecomputeFileIfExists   = false;

	protected Object              caller     = null;                           // The instance that called this LearnOneClause instance.
	protected String              callerName = "unnamed caller";               // Used to annotate printing during runs.
//	protected String              gleanerFileName = null;                      // Allow dumping of gleaner in the middle of learning one clause.
	private int                   dumpGleanerEveryNexpansions = -1;

	private   FileParser          parser;

	private   boolean             isaTreeStructuredTask = false; // For a tree-structured task, we don't want to generalize the heads (e.g., p(X,X) might be a good rule - will need to learn this via sameAs() calls ...).
	protected SingleClauseNode    currentStartingNode   = null;  // For some calculations we want to stop at this node.

	public    boolean			  regressionTask    = false; // Is this a REGRESSION task?
	public	  boolean			  mlnRegressionTask	= false; 
    public    boolean             learnMultiValPredicates             = false;
    public	  boolean			  oneClassTask		= false;
    public 	  PairWiseExampleScore occScorer			= null;
	public 	  boolean 			  sampleForScoring  = false;
	public 	  int				  maxExamplesToSampleForScoring = 300;
	public 	  boolean			  useProbabilityWeights = false;
	public    boolean             constantsAtLeaves = true;  // Are leaves CONSTANTS or linear models?  TODO - implement linear models, using (say) regularized least squares.
	public    int                 normToUse         = 2;     // Other norms implemented: NONE
	
	public    int                 maxCrossProductSize               =1000;     // When generating candidate groundings of a literal in the child-generator, randomly seleect if more than this many.
	public    int                 maxBodyLength                     =   9;     // Max length for the bodies of clauses.
	public    int                 maxFreeBridgersInBody             = maxBodyLength; // Bridgers can run amok so limit them (only has an impact when countBridgersInLength=true).  This is implemented as follows: the first  maxBridgersInBody don't count in the length, but any excess does.
	public    int                 maxNumberOfNewVars                =  10;     // Limit on the number of "output" variables used in a rule body.
	public    int        		  maxDepthOfNewVars                 =   7;     // The depth of variables in the head is 0.  The depth of a new variable is 1 + max depth of the input variables in the new predicate.
	public    int                 maxPredOccurrences                =   5;     // Maximum number of times a given predicate can appear in a clause (REGARDLESS of whether or not the input variables differ).  Ccn be overwritten on a per-predicate basis.
	public    int                 maxPredOccursPerInputVars         =   5;     // Maximum number of times a given predicate can occur PER SETTING of the input variables (can be overwritten on a per-predicate basis).
	public    int                 maxConstantBindingsPerLiteral     = 100;     // When trying to fill #vars in a new literal, don't create more than this many candidates (if more than randomly discard - note, if more than 1000 collected, the collecting process terminates, so if more than 1000 possibilities, selection will NOT be random).  If this is not a positive number, it is ignored.  Note: this can also be accomplished via maxPredOccursPerInputVars, though that does not solely deal with #vars and that is a DEPTH limit whereas this is a BREADTH limit.  TODO allow this to be done on a per-literal basis?
	private   double              minPosCoverage                    =   2.0;   // [If in (0,1), treat as a FRACTION of totalPosWeight].  Acceptable clauses must cover at least this many positive examples.  NOTE: this number is compared to SUMS of weighted examples, not simply counts (which is why this is a 'double').
	private   double              maxNegCoverage                    =  -1.0;   // [If in (0,1), treat as a FRACTION of totalNegWeight].  Acceptable clauses must cover no  more this many negative examples.  NOTE: this number is compared to SUMS of weighted examples, not simply counts (which is why this is a 'double').  IGNORE IF A NEGATIVE NUMBER.
	public    double              minPrecision                      =   0.501; // Acceptable clauses must have at least this precision.
	public    double              maxRecall                         =   1.01;  // When learning trees, don't want to accept nodes with TOO much recall, since want some examples on the 'false' branch.
	public    double              stopExpansionWhenAtThisNegCoverage =  0.0;   // Once a clause reaches this negative coverage, don't bother expanding it further.
	public    boolean             stopIfPerfectClauseFound          =   true;  // Might want to continue searching if a good SET of rules (eg, for Gleaner) is sought.
	public    boolean             errorToHaveModesWithoutInputVars  =   true;  // Error if a mode of the form 'predicateName(-human,#age)' is provided since such literals are uncoupled from a clause and hence lead to search inefficiency (so only expert users should override this boolean).
	public    double              clausesMustCoverFractPosSeeds     =   0.499; // ALL candidate clauses must cover at least this fraction of the pos seeds.  If performing RRR, these sets are used when creating the starting points.
	public    double              clausesMustNotCoverFractNegSeeds  =   0.501; // And all must NOT cover at least this fraction of the negative seeds (if any).
	public    double              fractionOfTimesUphillMoveCreated  =   0.010; // Occasionally, generalize a node by DROPPING one existing literal.
	public    boolean             allowPosSeedsToBeReselected       =  false;  // Can a positive seed be used more than once (in the ILP outer loop)?
	public    boolean             allowNegSeedsToBeReselected       =  false;  // Ditto for negatives?
	public    boolean             stopWhenUnacceptableCoverage      =   true;  // If set to  true, don't continue to prove examples when impossible to meet the minPosCoverage and minPrecision specifications.
	public    boolean	          collectTypedConstants             =   true;  // Checks for errors in the data.
	public    int                 minChildrenBeforeRandomDropping   =  10;     // Before randomly discarding children, there must be this many.
	public    double              probOfDroppingChild               =  -1.0;   // If not negative, probability of dropping a child.
	public    int                 maxSizeOfClosed                   =  100000;     // Limit the closed list to 100K items.  Note that items aren't placed here until EXPANDED, but items wont be placed in OPEN if already in CLOSED.
	public    int                 minNumberOfNegExamples            =  10;     // If less than this many negative examples, create some implicit negative examples.
	public    double              fractionOfImplicitNegExamplesToKeep = 0.10;  // NEW: if > 1.1, then count this NUMBER of examples, otherwise when generating implicit negatives, keep this fraction (but first make sure the min neg's number above is satisfied).
	public    boolean             requireThatAllRequiredHeadArgsAppearInBody         = false;  // If true, then a clause will not be considered accepted unless all required variables in the head appear in the body.
	public    boolean             allTargetVariablesMustBeInHead                     = false;
	public    boolean             dontAddNewVarsUnlessDiffBindingsPossibleOnPosSeeds = true;  // If have p(x) :- q(x,y) but if over all positive seeds can never get x and y to bind to different constants, then use p(x) :- q(x,x).  Similar (equivalent?) to "variable splitting" = false in Aleph.
	public    long                maxResolutionsPerClauseEval    = 10000000;     // When evaluating a clause, do not perform more than this many resolutions.  If this is exceeded, a clause is said to cover 0 pos and 0 neg, regardless of how many have been proven and it won't be expanded.
	public    boolean             usingWorldStates                        = false; // Does this task involve time-stamped facts?
	public    List<WorldState>    worldStatesContainingNoPositiveExamples = null;  // All ways of matching the target predicate in these states are known (or at least assumed) to be NEGATIVE examples.
	public    boolean             findWorldStatesContainingNoPosExamples  = false;
	public    boolean             createdSomeNegExamples                  = false; // Record if some negative examples were created (caller might want to write them to a file).
	public    int                 skewMaxNegToPos                         = -1; // If negative, don't alter the neg-pos ratio.  TODO - handle cases where we want to limit the POS wrt NEG. 
	////////////////////////////////////////////////////////////
	//  Variables for controlling random-rapid-restart searches (i.e., repeatedly randomly create an initial clause, then do some local search around each).
	//    The initial clause randomly created will meet the specification on the positive and negative seeds.
	////////////////////////////////////////////////////////////
	public    boolean             performRRRsearch      = false;
	public    int                 beamWidthRRR          =     1; // When doing RRR, use this beam width (if set too low, might not find a starting point for local search of the requested length).
	public    int                 minBodyLengthRRR      =     1; // Uniformly choose body lengths from minBodyLengthRRR to maxBodyLengthRRR (inclusive).
	public    int                 maxBodyLengthRRR      =    10;
	public    int                 restartsRRR           =   100; // Do this many RRR restarts per "ILP inner loop" call.
	public    int                 maxNodesToConsiderRRR =   100; // These are per each RRR iteration.
	public    int                 maxNodesToCreateRRR   =  1000;

	////////////////////////////////////////////////////////////
	protected boolean             stillInRRRphase1      =  true; // In the first phase of RRR, build a random clause that covers the required fraction of POS seeds.
	protected int                 savedBeamWidth;                // Save the old beam width so it can be restored when in phase 2 of RRR.
	protected int                 thisBodyLengthRRR;             // The chosen body length for this RRR iteration.
	public    int                 maxExamplesToUse      = -1;    // If > 0, then sample examples if more than this many.  When done, restore.
	public    boolean             onlyDiscardNegsWhenSampling = false;
	private List<Example>         posExamples;
    private List<Example>         negExamples;
	protected double              totalPosWeight = -1.0;   // Sum of the weights on the positive examples.
	protected double              totalNegWeight;          // Ditto for negative examples.
	protected double              totalWeightOnPosSeeds  = -1;
	protected double              totalWeightOnNegSeeds  = -1;
	protected List<PredicateNameAndArity> targetModes;     // The modes for the target.
	protected Set<PredicateNameAndArity>  bodyModes;       // Should we keep as a list so user can impact order they are considered (though that might not matter much ...)?  But if we do then we need to check for duplicates.

	protected List<Example>       seedPosExamples;
	protected List<Example>       seedNegExamples;

	protected PredicateName       procDefinedEnoughDiffMatches   = null;  // This is a built-in predicate that tests if a new literal being added to a clause being grown can be matched in a unique way on some POS seeds.
	protected PredicateName       procDefinedForConstants        = null;  // This is used to see which constants in the positive seeds can fill some arguments in a new literal.
	protected PredicateName       procDefinedNeedForNewVariables = null;  // See if these new variables ever bind in the positive seeds to some thing new in the clause (otherwise they aren't needed).  Only used if dontAddNewVarsUnlessDiffBindingsPossibleOnPosSeeds=true.
	protected List<List<Term>>    collectedConstantBindings;    // This is used as a temporary variable by a method below.
	protected BindingList         bindings = new BindingList(); // Only recreate theta if needed, in order to save on creating new lists.

	public    boolean              allowMultipleTargets       = true;

	private   List<PredicateNameAndArity>  examplePredicates          = null; // These store the positive example predicates that are eventually turned into targets.
	//private   List<Integer>        examplePredicateArities    = null; // Not really needed now that we have signatures, but we'll keep for at least awhile.
	private   List<List<Term>>     examplePredicateSignatures = null; // Something like [constant, function(constant), constant].

    public    List<Literal>        targets                    = null; // These are the actual targets determined from the examplePredicates.
	protected List<List<ArgSpec>>  targetArgSpecs             = null; // The info about the target argument being used and the variables matched with their types.
	protected List<List<Term>>     variablesInTargets         = null; // These are really 'arguments' since it is possible a mode specifies a constant be used.

    protected HornClauseContext    context;

	protected HandleFOPCstrings    stringHandler;
	protected Unifier              unifier; // Make instances out of some things that could be 'statics' so the code is safer.
	private   HornClauseProver     prover; // This is initialized by getProver() so please don't use this variable directly.
	protected PruneILPsearchTree   pruner = null;  // Used to prune search trees that are unlikely to pan out (called by ChildrenClausesGenerator and its extensions).
	protected Precompute           precomputer;
	private   ThresholdManager     thresholdHandler;
	private   InlineManager        inlineHandler; // Handle the in-lining of literal bodies (should only be applied to literals that are only defined by ONE clause).
	protected TypeManagement       typeManager;

	//private   HornClauseProverChildrenGenerator ruleAndFactsHolder;
	private   Reader               posExamplesReader; // We now also delay this in case we want to specify this is a regression task.
	private   Reader               negExamplesReader; // Needed in case implicit negatives need to be created (we delay doing this to allow the caller to set parameters related to this neg-generation process).
	@SuppressWarnings("unused")
	private   boolean              creatingConjunctiveFeaturesOnly = false; // Will be set to true when using this code to create features.
	// Clarification on how m-estimates are currently used in this code:
	//  All clauses are assumed to also match mEstimateNeg negative examples
	//  The set of positive examples is assumed to have mEstimatePos examples added to it, but these examples are NOT covered the clause.
	//  So if a clause covers 3 of 7 positive and 2 of 10 negative examples, and these two m-estimates are 1, then
	//    precision = 3 of 3+2+1 and recall = 3 of 7+1
	private   double               mEstimatePos = 0.1; // When computing coverage of a rule use these "m estimates."  NOTE these are also used when examples are weighted, so if total weight is small, might want to change these.
	private   double               mEstimateNeg = 0.1; // Note: these are used in recall as well as precision.

	protected List<Literal> requiredBodyPredicatesForAcceptableClauses = null; // See documentation for the method addRequiredBodyPredicateForAcceptableClauses.
	protected int           minRequiredBodyPredicates = 0;
	protected int           maxRequiredBodyPredicates = Integer.MAX_VALUE;

    protected long          totalProofTimeInNanoseconds = 0;
    protected int           totalProofsProved = 0;

    RelevanceStrength       currentRelevanceStrength = RelevanceStrength.getWeakestRelevanceStrength();
    private Set<PredicateNameAndArity> factPredicateNames = new HashSet<PredicateNameAndArity>();

    private Boolean relevanceEnabled = true;  // When null or false, relevance is disabled.

    private boolean optimizeClauses  = true;

    private List<ModeConstraint> modeConstraints = null;

    private final AdviceProcessor adviceProcessor;
    private ActiveAdvice activeAdvice = null;

    private EventListenerList searchListenerList = new EventListenerList();

    private List<Sentence> facts = null; // This temporarily stores the facts between construction and initialization.  After initialization it will be null.

    /** Override to disable thresholding.
     *
     * If set to false, thresholding will be skipped.  This is particularly useful
     * when we are only using the LearnOneClause to evaluate a learned theory.
     */
    private boolean thresholdingEnabled = true;

    private boolean syntheticExamplesEnabled = false; // JWS: I turned this OFF on 8/18/11.  Not sure how it get turned on ...

    // Precompute filename : precompute_file_prefix + PRECOMPUTED_FILENAME  + number +  precompute_file_postfix
    // The following values can be set using
    // setParam: precomputePostfix = ".txt".
    // setParam: precomputePrefix = "../../".
    // setParam: numberOfPrecomputes = 100.
    
    @SuppressWarnings("FieldNameHidesFieldInSuperclass")
    private boolean initialized = false;

	/** Constructs a new LearnOneClause search.
     *
     * @param workingDir
     * @param prefix
     * @param posExamplesFileName
     * @param negExamplesFileName
     * @param backgroundClausesFileName
     * @param factsFileName
     * @param strategy
     * @param scorer
	 * @throws IOException 
	 *
	 */
	public LearnOneClause(String workingDir, // Location where 'imports' can be found, results can be written, etc.
						  String prefix,     // Common prefix of files used.
						  String posExamplesFileName,       String negExamplesFileName,
						  String backgroundClausesFileName, String factsFileName,
			              SearchStrategy strategy,          ScoreSingleClause scorer) throws IOException {
		this(workingDir, prefix, posExamplesFileName, negExamplesFileName, backgroundClausesFileName, factsFileName, strategy, scorer, null);
	}


    public LearnOneClause(String directory, String task) throws IOException {
		this(directory, task,
			 new NamedReader(new CompressedFileReader(directory + "/" + task + "_pos.txt"), directory + "/" + task + "_pos.txt"),
			 new NamedReader(new CompressedFileReader(directory + "/" + task + "_neg.txt"), directory + "/" + task + "_neg.txt"),
			 new NamedReader(new CompressedFileReader(directory + "/" + task + "_bk.txt"), directory + "/" + task + "_bk.txt"),
			 new NamedReader(new CompressedFileReader(directory + "/" + task + "_facts.txt"), directory + "/" + task + "_facts.txt"),
  			 new BestFirstSearch(),             // Search strategy.
  			 new ScoreSingleClauseByAccuracy(), // Scorer.
  			 null,                              // Could also pass in a pruner.
  			 new Gleaner(),
  			 new HandleFOPCstrings());
	}

    public LearnOneClause(String directory, String task, HornClauseContext context) throws IOException {
		this(directory, task,
			 new NamedReader(new CompressedFileReader(directory + "/" + task + "_pos.txt"), directory + "/" + task + "_pos.txt"),
			 new NamedReader(new CompressedFileReader(directory + "/" + task + "_neg.txt"), directory + "/" + task + "_neg.txt"),
			 new NamedReader(new CompressedFileReader(directory + "/" + task + "_bk.txt"), directory + "/" + task + "_bk.txt"),
			 new NamedReader(new CompressedFileReader(directory + "/" + task + "_facts.txt"), directory + "/" + task + "_facts.txt"),
  			 new BestFirstSearch(),             // Search strategy.
  			 new ScoreSingleClauseByAccuracy(), // Scorer.
  			 null,                              // Could also pass in a pruner.
  			 new Gleaner(),
  			 context, false);
	}

    /** Constructs a new LearnOneClause search.
     *
     * @param workingDir
     * @param prefix
     * @param posExamplesFileName
     * @param negExamplesFileName
     * @param backgroundClausesFileName
     * @param factsFileName
     * @param strategy
     * @param scorer
     * @param monitor
     * @throws IOException 
     */
	public LearnOneClause(String workingDir,                String prefix,
			  			  String posExamplesFileName,       String negExamplesFileName,
			  			  String backgroundClausesFileName, String factsFileName,
			              SearchStrategy strategy,          ScoreSingleClause scorer,
                          SearchMonitor monitor) throws IOException {
		this(workingDir, prefix,
			 new NamedReader(new CondorFileReader(posExamplesFileName), posExamplesFileName),
			 new NamedReader(new CondorFileReader(negExamplesFileName), negExamplesFileName),
			 new NamedReader(new CondorFileReader(backgroundClausesFileName), backgroundClausesFileName),
			 new NamedReader(new CondorFileReader(factsFileName), factsFileName),
			 strategy, scorer, null, monitor, new DefaultHornClauseContext(), false);
	}

	// A minimal version (e.g., if one wants this class' structures but doesn't want to do ILP).
	public LearnOneClause(String workingDir, String prefix, String backgroundClausesFileName, String factsFileName) throws IOException {
		this(workingDir, prefix, null, null,
			 (backgroundClausesFileName == null ? null : new NamedReader(new CondorFileReader(backgroundClausesFileName), backgroundClausesFileName)),
			 (factsFileName             == null ? null : new NamedReader(new CondorFileReader(factsFileName), factsFileName)),
			 new BestFirstSearch(), new ScoreSingleClauseByAccuracy(), null, new Gleaner(), new DefaultHornClauseContext(), false);
		minNumberOfNegExamples = 0;
	}

	// A minimal version + string handler to allow changing flags such as keepQuoteMarks.
	public LearnOneClause(String workingDir, String prefix,String backgroundClausesFileName, String factsFileName, HandleFOPCstrings stringHandler) throws IOException {
		this(workingDir, prefix, null, null,
			 (backgroundClausesFileName != null ? new NamedReader(new CondorFileReader(backgroundClausesFileName), backgroundClausesFileName) : null),
			 (factsFileName             != null ? new NamedReader(new CondorFileReader(factsFileName), factsFileName)             : null),
			 new BestFirstSearch(), new ScoreSingleClauseByAccuracy(), null, new Gleaner(), stringHandler);
		minNumberOfNegExamples = 0;
	}

	// A minimal version + string handler to allow changing flags such as keepQuoteMarks.
	public LearnOneClause(String workingDir, String prefix,String backgroundClausesFileName, String factsFileName, HornClauseContext context) throws IOException {
		this(workingDir, prefix, null, null,
			 (backgroundClausesFileName != null ? new NamedReader(new CondorFileReader(backgroundClausesFileName),backgroundClausesFileName) : null),
			 (factsFileName             != null ? new NamedReader(new CondorFileReader(factsFileName), factsFileName)             : null),
			 new BestFirstSearch(), new ScoreSingleClauseByAccuracy(), null, new Gleaner(), context, false);
		minNumberOfNegExamples = 0;
	}
    /** Constructs a new LearnOneClause search.
     *
     * @param workingDir
     * @param prefix,
     * @param posExamplesReader
     * @param negExamplesReader
     * @param backgroundClausesReader
     * @param factsFile
     * @param strategy
     * @param scorer
     * @param monitor
     */
	public LearnOneClause(String workingDir,              String prefix,
			  			  Reader posExamplesReader,       Reader negExamplesReader,
						  Reader backgroundClausesReader, Reader factsFile,
	          			  SearchStrategy strategy,        ScoreSingleClause scorer,
                          SearchMonitor monitor) {
		this(workingDir, prefix, posExamplesReader, negExamplesReader, backgroundClausesReader, factsFile, strategy, scorer, null, monitor, new DefaultHornClauseContext(), false);
	}

    /** Constructs a new LearnOneClause search.
     *
     * @param workingDir
     * @param prefix
     * @param posExamplesReader
     * @param negExamplesReader
     * @param backgroundClausesReader
     * @param factsFile
     * @param strategy
     * @param scorer
     * @param monitor
     * @param stringHandler
     */
	public LearnOneClause(String workingDir,              String prefix,
			  			  Reader posExamplesReader,       Reader negExamplesReader,
						  Reader backgroundClausesReader, Reader factsFile,
	          			  SearchStrategy strategy,        ScoreSingleClause scorer,
                          SearchMonitor monitor,          HandleFOPCstrings stringHandler) {
		this(workingDir, prefix, posExamplesReader, negExamplesReader, backgroundClausesReader, factsFile, strategy, scorer, null, monitor, stringHandler);
	}

    /** Constructs a new LearnOneClause search.
     *
     * @param workingDir
     * @param prefix
     * @param posExamplesReader
     * @param negExamplesReader
     * @param backgroundClausesReader
     * @param factsReader
     * @param strategy
     * @param scorer
     * @param pruner
     * @param monitor
     * @param stringHandler
     */
	public LearnOneClause(String             workingDir,              String prefix,
			  			  Reader             posExamplesReader,       Reader            negExamplesReader,
						  Reader             backgroundClausesReader, Reader            factsReader,
				  		  SearchStrategy     strategy,                ScoreSingleClause scorer,
                          PruneILPsearchTree pruner,                  SearchMonitor     monitor,
                          HandleFOPCstrings  stringHandler) {
        this(workingDir, prefix, posExamplesReader, negExamplesReader, backgroundClausesReader, factsReader, strategy, scorer, pruner, monitor, new DefaultHornClauseContext(stringHandler), false);
    }
    /** Constructs a new LearnOneClause search.
     *
     * @param workingDir
     * @param prefix
     * @param posExamplesReader
     * @param negExamplesReader
     * @param backgroundClausesReader
     * @param factsReader
     * @param strategy
     * @param scorer
     * @param monitor
     * @param context
     * @param deferLoadingExamples
     */
    public LearnOneClause(String            workingDir,              String prefix,
                          Reader            posExamplesReader,       Reader negExamplesReader,
                          Reader            backgroundClausesReader, Reader factsReader,
                          SearchStrategy    strategy,                ScoreSingleClause scorer,
                          SearchMonitor     monitor,                 HornClauseContext context,
                          boolean           deferLoadingExamples) {
        this(workingDir, prefix, posExamplesReader, negExamplesReader, backgroundClausesReader, factsReader, strategy, scorer, null, monitor, context, deferLoadingExamples);
    }
    public LearnOneClause(String            workingDir,              String prefix,
            			  Reader            posExamplesReader,       Reader negExamplesReader,
            			  Reader            backgroundClausesReader, Reader factsReader,
            			  SearchStrategy    strategy,                ScoreSingleClause scorer,
            			  SearchMonitor     monitor,                 HornClauseContext context) {
    	this(workingDir, prefix, posExamplesReader, negExamplesReader, backgroundClausesReader, factsReader, strategy, scorer, null, monitor, context, false);
    }

        // TODO: Special interface for ILP 2010 experiment runs
	public LearnOneClause(String testsetDir, String lesson, HandleFOPCstrings stringHandler, boolean usingILPData) throws IOException {
		this(testsetDir, lesson,
				new BufferedReader(new CondorFileReader(testsetDir + "/" + lesson + (usingILPData ? "_pos.txt"   : "_posAll.txt"))),
				new BufferedReader(new CondorFileReader(testsetDir + "/" + lesson + (usingILPData ? "_neg.txt"   : "_negAll.txt"))),
				new BufferedReader(new CondorFileReader(testsetDir + "/" + lesson + (usingILPData ? "_bk.txt"    : "_bkOne.txt"))),
				new BufferedReader(new CondorFileReader(testsetDir + "/" + lesson + (usingILPData ? "_facts.txt" : "factsAll.txt"))),
				new BestFirstSearch(),             // Search strategy.
				new ScoreSingleClauseByAccuracy(), // Scorer.
				null,                              // Could also pass in a pruner.
				new Gleaner(),
				stringHandler);
	}

    public LearnOneClause(String             workingDir,              String            prefix,
                          Reader             posExamplesReader,       Reader            negExamplesReader,
                          Reader             backgroundClausesReader, Reader            factsReader,
                          SearchStrategy     strategy,                ScoreSingleClause scorer,
                          PruneILPsearchTree pruner,                  SearchMonitor     monitor,
                          HornClauseContext  context,                 boolean           deferLoadingExamples) {

        taskName = "LearnOneClause";
        this.stringHandler = (context == null ? null : context.getStringHandler());
        if ( stringHandler == null ) stringHandler = new HandleFOPCstrings();
        if ( strategy == null ) strategy = new BestFirstSearch();
        if ( scorer   == null ) scorer   = new ScoreSingleClauseByAccuracy();
        if ( monitor  == null ) monitor  = new Gleaner();

		this.unifier       = Unifier.UNIFIER;
        this.stringHandler = context.getStringHandler();
		this.parser        = context.getFileParser();
		this.setDirectoryName(workingDir);
		this.setPrefix(prefix);
        this.context       = context;

		this.precomputer   = new Precompute();
		this.typeManager   = new TypeManagement(stringHandler);
        
		verbosity = 1;

        setInlineManager(new InlineManager(   stringHandler, getProver().getClausebase()));
        setThresholder(  new ThresholdManager(this, stringHandler, unifier, inlineHandler));
        adviceProcessor = new AdviceProcessor(context, this);

		// Load BK first since it is the place where 'usePrologVariables' etc is typically set.
		if (backgroundClausesReader != null) { context.assertSentences(readBackgroundTheory(backgroundClausesReader, null, true)); }

		Initializer              init        = new InitializeILPsearchSpace();
		EndTest                  endTest     = null;
		ChildrenClausesGenerator nodeGen     = new ChildrenClausesGenerator();
		VisitedClauses           c           = new VisitedClauses(maxSizeOfClosed);
		initalizeStateBasedSearchTask(init, endTest, monitor, strategy, scorer, nodeGen, c);
		nodeGen.initialize();
		setGleaner(monitor);
		
		// Currently we automatically loading all 'basic' modes unless overridden - this might use a lot of cycles, so use with care.
		String mStr = stringHandler.getParameterSetting("loadAllBasicModes");
		if (loadAllBasicModes && (mStr == null || !mStr.equalsIgnoreCase("false"))) {
			
			List<Sentence> modeSentences = null;
			try {
				modeSentences = parser.loadAllBasicModes();
			} catch (Exception e) {
				Utils.reportStackTrace(e);
				Utils.error("Problem loading basic mode files.");
			}

            context.assertSentences(modeSentences);
		}
		
		// Currently we automatically loading all libraries unless overridden - only a few and if no modes added, these won't impact run time anyway.
		String vStr = stringHandler.getParameterSetting("loadAllLibraries");
		if (loadAllLibraries && (vStr == null || !vStr.equalsIgnoreCase("false"))) {
			List<Sentence> librarySentences = null;
			try {
				librarySentences = parser.loadAllLibraries();
			} catch (Exception e) {
				Utils.reportStackTrace(e);
				Utils.error("Problem loading library files.");
			}

            context.assertSentences(librarySentences);
		}
/*		
		// If any clauses are in this string, then the returned value needs to be processed.
		String specialCasesString = "relevant: sameAs/2,    @mixAndMatchAdviceLiterals.\n" +
									"relevant: different/2, @mixAndMatchAdviceLiterals.\n" +
									"";
		List<Sentence> results = parser.readFOPCstream(specialCasesString);
		if (Utils.getSizeSafely(results) > 0) { Utils.error("Need to handle: " + results); }
*/	
		if (debugLevel > 2) {
			boolean hold = stringHandler.printVariableCounters;
		//	stringHandler.printVariableCounters = true; // Turn this on if you want to see the 'true names' of the variables.  I.e., two x's might be different.
			Utils.println("\n%  The Background Rules:\n");
            for (Clause clause : context.getClausebase().getBackgroundKnowledge()) {
                Utils.println("%  " + clause.toPrettyString("%     ", Integer.MAX_VALUE));
            }
			stringHandler.printVariableCounters = hold;
		}

        if (debugLevel > -1) { Utils.println("\n%  Read the facts."); }

        if (factsReader != null) { 
        	facts = readFacts(factsReader, workingDir);
        	context.assertSentences(facts);
        	 if (debugLevel > -1) { Utils.println("%  Have read " + Utils.comma(facts) + " facts."); }
        }

		// NO LONGER BEING DONE.  checkBKforFacts(); // See if some facts were in the BK file.  If so, move them without complaint.
		if (Utils.getSizeSafely(stringHandler.getKnownModes()) < 1) { Utils.severeWarning("Need to have at least one mode: " + stringHandler.getKnownModes()); }

		this.posExamplesReader = posExamplesReader; // Hold on to in case we want to say this is a regression task.
		this.negExamplesReader = negExamplesReader; // Hold on to this to allow the caller a chance to set parameters (e.g., sampling rate).

        // Wait until initialize() is called, in case some things need to be set.  
		if (!deferLoadingExamples && posExamplesReader != null) { 
			readExamples(posExamplesReader, negExamplesReader, skewMaxNegToPos);
			if (posExamplesReader       != null) closeWithoutException(posExamplesReader);
			if (negExamplesReader       != null) closeWithoutException(negExamplesReader);
		}
        if (factsReader             != null) closeWithoutException(factsReader);
        if (backgroundClausesReader != null) closeWithoutException(backgroundClausesReader);


		//	stringHandler.dumpIsaHier(); Utils.waitHere();

		//  stringHandler.nearestCommonParent("float",             "singleAgent",  false); // Testing this code ... (6/09)
		//  stringHandler.nearestCommonParent("vehicle",           "device",       false);
		//  stringHandler.nearestCommonParent("perceivableObject", "intersection", false); Utils.waitHere();
        
        if (debugLevel > -1) { Utils.println("\n%  LearnOneClause initialized."); }
	}

    public final void readExamples(Reader positiveReader, Reader negativeReader, int skewMaxNegToPosToUse) {
    //	Utils.println("readExamples: |posExamples| = " + Utils.getSizeSafely(posExamples) + "  getDirectoryName() = " + getDirectoryName() + "  positiveReader = " + positiveReader);
        if (posExamples == null) {
            setPosExamples(positiveReader == null ? null : readExamples(positiveReader, getDirectoryName(), true));
        }
        if (negExamples == null && !regressionTask) {
            setNegExamples(negativeReader == null ? null : readExamples(negativeReader, getDirectoryName(), true)); // Negative examples can be EXPLICIT (or absent).
        }
        if (posExamples == null && positiveReader != null) {
            Utils.error("You should provide some positive examples.  None were found in reader '" + positiveReader + "'.");
        }
        
        if (skewMaxNegToPosToUse > 0) {
        	int numberPos = Utils.getSizeSafely(posExamples);
        	int numberNeg = Utils.getSizeSafely(negExamples);
        	
        	double ratio = numberNeg / (1.0 * numberPos);
        	if (ratio > skewMaxNegToPosToUse) {
        		Utils.println("\n% Need to sample the negatives so the skew goes from " + Utils.truncate(ratio, 1) + ":1 to " + Utils.truncate(skewMaxNegToPosToUse, 1) + ":1.");
        		
        		int desiredNumberOfNeg = (int)(numberPos * skewMaxNegToPosToUse);
        		List<Example>   newNeg = new ArrayList<Example>(desiredNumberOfNeg);
        		double      probToKeep = (3.0 + desiredNumberOfNeg * 1.05) / numberNeg; // Grab a few extra so we can be likely to have enough (since deleting will maintain example order but adding doesn't).
        		int         numberKept = 0;
        		for (Example ex : negExamples) if (Utils.random() < probToKeep) {
        			newNeg.add(ex);
        			numberKept++;
        		}
        		Utils.println("% Have to randomly delete " + Utils.comma(numberNeg - desiredNumberOfNeg) + " of " + Utils.comma(numberNeg) + " negative examples.");
        		// See if we have the correct number.  If we need to ADD more there, the example ordering will not be preserved, but that should be OK.
        		int tries = 10 * (desiredNumberOfNeg - numberKept);
        		while (numberKept < desiredNumberOfNeg && tries > 0) { // If we need a few more, do so, but put a limit on it.
        			tries--;
        			Example newEx = negExamples.get(Utils.random0toNminus1(numberNeg));
        			if (!newNeg.contains(newEx)) { // See if this is a new one.
        				newNeg.add(newEx);
            			numberKept++;
        			}        				
        		}
        		while (numberKept > desiredNumberOfNeg) { // If we have too many, discard some randomly.
        			newNeg.remove(Utils.random0toNminus1(numberKept)); // This is inefficient since an ArrayList ...
        			numberKept--;
        		}
        		setNegExamples(newNeg);
        	}
        }
        
   // 	Utils.println("readExamplesAFTER: |posExamples| = " + Utils.getSizeSafely(posExamples));
    }
    // cth: Added so that previous gleaner can be grabbed from the LearnOneClause object
    // needed to make Gleaner setting persistent
    protected final SearchMonitor getGleaner() {
    	return this.searchMonitor;
    }

	protected final void setGleaner(SearchMonitor monitor) {

       this.searchMonitor = monitor;

		if (monitor != null) {
			monitor.setSearchTask(this); // Connect the search monitor (if one) to this search task.

         // TAW: Jude, just as a comment on a better design (you mention it in the line below)...
         // For this type of situation, make the target do the work of extracting the stringHandler
         // from the LearnOneClause.  In other words, in the Gleaner code, override setSearchTask with
         // something like this:
         //    public void setSearchTask(StateBasedSearchTask task) {
         //        if ( task instanceof LearnOneClause == false ) throw new IllegalArgumentException("Gleaner only works on LearnOneClause search tasks.");
         //
         //        super.setSearchTask(task);
         //
         //        setStringHandler( ((LearnOneClause)task)stringHandler);
         //    }
         // That way the Class that has the extra requirement can handle it appropriately and this
         // class can treat all SearchMonitors exactly the same.
			if (monitor instanceof Gleaner) {
				((Gleaner) monitor).setStringHandler(stringHandler); // Need to special-case this code.  TODO cleanup if some better design comes to mind.
			}
		}
	}


	private void checkForSetParameters() {
		String vStr = null;

		vStr = stringHandler.getParameterSetting("discardIfBestPossibleScoreOfNodeLessThanBestSeenSoFar");
		if (vStr != null) {                       discardIfBestPossibleScoreOfNodeLessThanBestSeenSoFar = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("createCacheFiles");
		if (vStr != null) {                       createCacheFiles                                      = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("requireThatAllRequiredHeadArgsAppearInBody");
		if (vStr != null) {                       requireThatAllRequiredHeadArgsAppearInBody            = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("allTargetVariablesMustBeInHead");
		if (vStr != null) {                       allTargetVariablesMustBeInHead                        = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("stopIfPerfectClauseFound");
		if (vStr != null) {                       stopIfPerfectClauseFound                              = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("useCachedFiles");
		if (vStr != null) {                       useCachedFiles                                        = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("usingWorldStates");
		if (vStr != null) {                       usingWorldStates                                      = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("errorToHaveModesWithoutInputVars");
		if (vStr != null) {                       errorToHaveModesWithoutInputVars                      = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("allowPosSeedsToBeReselected");
		if (vStr != null) {                       allowPosSeedsToBeReselected                           = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("allowNegSeedsToBeReselected");
		if (vStr != null) {                       allowNegSeedsToBeReselected                           = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("stopWhenUnacceptableCoverage");
		if (vStr != null) {                       stopWhenUnacceptableCoverage                          = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("collectTypedConstants");
		if (vStr != null) {                       collectTypedConstants                                 = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("dontAddNewVarsUnlessDiffBindingsPossibleOnPosSeeds");
		if (vStr != null) {                       dontAddNewVarsUnlessDiffBindingsPossibleOnPosSeeds    = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("findWorldStatesContainingNoPosExamples");
		if (vStr != null) {                       findWorldStatesContainingNoPosExamples                = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("performRRRsearch");
		if (vStr != null) {                       performRRRsearch                                      = Boolean.parseBoolean(vStr); }
		vStr = stringHandler.getParameterSetting("allowMultipleTargets");
		if (vStr != null) {                       allowMultipleTargets                                  = Boolean.parseBoolean(vStr); }

		vStr = stringHandler.getParameterSetting("minPosCoverage");
		if (vStr != null) {
			double value_minPosCoverage = Double.parseDouble(vStr);  if (value_minPosCoverage < 1) { Utils.waitHere("minPosCoverage expressed as a FRACTION no longer supported.  Use minPosCovFraction instead."); }
			setMinPosCoverage(              value_minPosCoverage); 
		}
		vStr = stringHandler.getParameterSetting("minPosCovFraction");
		if (vStr != null) {
			double value_minPosCovFraction = Double.parseDouble(vStr);  if (value_minPosCovFraction > 1) { Utils.waitHere("minPosCovFraction should not be given numbers greater than 1."); }
			setMinPosCoverageAsFraction    (value_minPosCovFraction);
		}
		vStr = stringHandler.getParameterSetting("minPrecision");
		if (vStr != null) {                    setMinPrecision(  Double.parseDouble(vStr));  }
		vStr = stringHandler.getParameterSetting("mEstimatePos");
		if (vStr != null) {                    setMEstimatePos(  Double.parseDouble(vStr));  }
		vStr = stringHandler.getParameterSetting("mEstimateNeg");
		if (vStr != null) {                    setMEstimateNeg(  Double.parseDouble(vStr));  }
		vStr = stringHandler.getParameterSetting("maxNegCoverage");
		if (vStr != null) {                    setMaxNegCoverage( Double.parseDouble(vStr)); }
		vStr = stringHandler.getParameterSetting("fractionOfImplicitNegExamplesToKeep");
		if (vStr != null) {                       fractionOfImplicitNegExamplesToKeep = Double.parseDouble(vStr); }
		vStr = stringHandler.getParameterSetting("stopExpansionWhenAtThisNegCoverage");
		if (vStr != null) {                       stopExpansionWhenAtThisNegCoverage  = Double.parseDouble(vStr); }
		vStr = stringHandler.getParameterSetting("clausesMustCoverFractPosSeeds");
		if (vStr != null) {                       clausesMustCoverFractPosSeeds       = Double.parseDouble(vStr); }
		vStr = stringHandler.getParameterSetting("clausesMustNotCoverFractNegSeeds");
		if (vStr != null) {                       clausesMustNotCoverFractNegSeeds    = Double.parseDouble(vStr); }
		vStr = stringHandler.getParameterSetting("fractionOfTimesUphillMoveCreated");
		if (vStr != null) {                       fractionOfTimesUphillMoveCreated    = Double.parseDouble(vStr); }
		vStr = stringHandler.getParameterSetting("probOfDroppingChild");
		if (vStr != null) {                       probOfDroppingChild                 = Double.parseDouble(vStr); }

		vStr = stringHandler.getParameterSetting("minNumberOfNegExamples");
		if (vStr != null) {                       minNumberOfNegExamples          = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("maxBodyLength");
		if (vStr != null) {                       maxBodyLength                   = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("maxNumberOfNewVars");
		if (vStr != null) {                       maxNumberOfNewVars              = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("maxDepthOfNewVars");
		if (vStr != null) {                       maxDepthOfNewVars               = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("maxPredOccurrences");
		if (vStr != null) {                       maxPredOccurrences              = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("maxNodesToCreate");
		if (vStr != null) {                                     setMaxNodesToCreate(Integer.parseInt(vStr)); }
		vStr = stringHandler.getParameterSetting("maxResolutionsPerClauseEval");
		if (vStr != null) {                       maxResolutionsPerClauseEval     = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("maxSizeOfClosed");
		if (vStr != null) {                       maxSizeOfClosed                 = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("minChildrenBeforeRandomDropping");
		if (vStr != null) {                       minChildrenBeforeRandomDropping = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("maxConstantBindingsPerLiteral");
		if (vStr != null) {                       maxConstantBindingsPerLiteral   = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("maxPredOccursPerInputVars");
		if (vStr != null) {                       maxPredOccursPerInputVars       = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("beamWidthRRR");
		if (vStr != null) {                       beamWidthRRR                    = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("minBodyLengthRRR");
		if (vStr != null) {                       minBodyLengthRRR                = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("maxBodyLengthRRR");
		if (vStr != null) {                       maxBodyLengthRRR                = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("restartsRRR");
		if (vStr != null) {                       restartsRRR                     = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("maxNodesToConsiderRRR");
		if (vStr != null) {                       maxNodesToConsiderRRR           = Integer.parseInt(vStr); }
		vStr = stringHandler.getParameterSetting("maxNodesToCreateRRR");
		if (vStr != null) {                       maxNodesToCreateRRR             = Integer.parseInt(vStr); }
		
	}


	private List<Sentence> cachedClauseswithGroundings = new ArrayList<Sentence>();
	private List<Long> cachedGroundingsOfClauses	 = new ArrayList<Long>();
	private boolean cacheClauseGroundings			 = false;
	public int num_hits = 0;
	public int num_misses = 0;
	
	public void resetCachedClauseGroundings() {
		cachedClauseswithGroundings = new ArrayList<Sentence>();
		cachedGroundingsOfClauses	 = new ArrayList<Long>();
	}
	/*
	public long lookupCachedGroundings(Sentence cl) {
		if (!cacheClauseGroundings) return -1;
		Utils.waitHere("Caching this breaks caching of binding lists. also this is very slow since it searches for 'variants'");
		int index=0;
		for (Sentence clause : cachedClauseswithGroundings) {
			if (cl.variants(clause, null) != null) {
				//Utils.println("cache hit");
				num_hits++;
				return cachedGroundingsOfClauses.get(index);
			}
			index++;
		}
		num_misses++;
		return -1;
	}
	// Make sure to do the lookup before adding to cache as this code doesn't do a check
	public void addToCachedGroundings(Sentence cl, long num) {
		if (!cacheClauseGroundings) return;
		cachedClauseswithGroundings.add(cl);
		cachedGroundingsOfClauses.add(num);
	}
	

	public List<BindingList> getAllPossibleGroundingsOf(Literal lit) {
		PredicateName pName = lit.predicateName;
		int index=-1;
		List<Collection<Term>> rangeForArguments = new ArrayList<Collection<Term>>();
		List<Term> variableArguments = new ArrayList<Term>();
		List<BindingList> bindings = new ArrayList<BindingList>();
		for (Term arg : lit.getArguments()) {
			index++;
			if (!arg.isGrounded()) {
				if (!(arg instanceof Variable)) {
					Utils.error("expected variable here: " + arg + " in " + lit);
							
				}
				variableArguments.add(arg);
				rangeForArguments.add(new HashSet<Term>());
				int varIndex = rangeForArguments.size() - 1;
				// Look for all possible types that this arg can have
				for (PredicateSpec spec : pName.getTypeOnlyList()) {
					// Only if arity matches
					if (spec.getArity() == lit.getArity()) {
						Set<Term> consts = getStringHandler().isaHandler.getAllInstances(spec.getTypeSpec(index).isaType);
						rangeForArguments.get(varIndex).addAll(consts);
					}
				} 
				if (rangeForArguments.get(varIndex).size() == 0 ) {
					Utils.error("No constants for argument: " + arg + " in " + lit);
				}
			}
		}
		if (variableArguments.isEmpty()) {
			bindings.add(new BindingList());
			return bindings;
		}
		
		List<List<Term>> crossProd = Utils.computeCrossProduct(rangeForArguments);
		
		for (List<Term> oneGrounding : crossProd) {
			BindingList bl = new BindingList();
			for (int i = 0; i < oneGrounding.size(); i++) {
				bl.addBinding((Variable)variableArguments.get(i), oneGrounding.get(i));
			}
			bindings.add(bl);
		}
		return bindings;
	}
	
	public boolean useOnlyProverForGroundings = true;
	public boolean literalInFactBase(Literal lit) {
		return getContext().getClausebase().getPossibleMatchingBackgroundKnowledge(lit, null) == null;
	}
	
	public boolean isaFact(Literal lit) {
		HornClausebase base = getContext().getClausebase();
		if (literalInFactBase(lit)) {
			// Rather than counting, just check if size > 0
			Iterator<Literal> facts = base.getPossibleMatchingFacts(lit, null).iterator();
			return (facts != null && facts.hasNext());
			// return Utils.getSizeSafely(base.getPossibleMatchingFacts(lit,null).iterator()) > 0;
		}
	
		if (groundings_prover == null) {
			groundings_prover = new HornClauseProver(getContext(), true);
		}
		List<Literal> lits = new ArrayList<Literal>();
		lits.add(lit);
		((InitHornProofSpace) groundings_prover.initializer).loadNegatedConjunctiveQuery(lits,
				groundings_prover.open);

		BindingList bl = getNextProof(groundings_prover);
		return bl != null;
	}
	
	
	public long numberOfGroundings(Sentence cl, Set<BindingList> blSet) {
		if (cl.containsVariables()) {
			// only cache clauses that have variables
			try {
				return numberOfGroundingsForClauseWithVar(cl, blSet);
			} catch (SearchInterrupted e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			return 0;
		}
	
		// No variables so just a fact lookup
		Clause cls = (Clause)cl;
		if (cls.posLiterals != null) {
			for (Literal pLit : cls.posLiterals) {
				if (!isaFact(pLit)) {
					//Utils.println(" not fact" + pLit);
					return 0;
				}
			}
		}
		if (cls.negLiterals != null) {
			for (Literal nLit : cls.negLiterals) {
				if (isaFact(nLit)) {
					//Utils.println(" is fact" + nLit);
					return 0;
				}
			}
		}
		if (blSet != null) {
			blSet.add(new BindingList());
		}
		return 1;
	}
	
	HornClauseProver groundings_prover = null;
	public long numberOfGroundingsForClauseWithVar(Sentence cl, Set<BindingList> blSet) throws SearchInterrupted {
		long num = lookupCachedGroundings(cl);
		if (num >= 0) {
			return num;
		}
		if (groundings_prover == null) {
			groundings_prover = new HornClauseProver(getContext(), true);
		}
		
		// Proof proof = new DefaultProof(getContext(), cl);
		// ((DefaultProof)proof).getProver().setRedoable(true);
		if (!( cl instanceof Clause)) {
			Utils.waitHere( cl + " should be clause");
		}
		Clause clause = (Clause)cl;
		//if (clause.getNegativeLiterals().size() > 0) {
		//	Utils.waitHere( cl + "should have no neg literals");
		//}
		
		//if (clause.negLiterals.size() > 1) {
			((InitHornProofSpace) groundings_prover.initializer).loadNegatedConjunctiveQuery(clause.getPositiveLiterals(),
					groundings_prover.open);
		//}
        
		BindingList bl = getNextProof(groundings_prover);
		long counter = 0;
		// BindingList bl = proof.prove();
		HashSet<BindingList> seen_bls = new HashSet<BindingList>();
		while(bl != null) {
			
			// Make sure that none of the negative literals are satisfied for exists
			// Enable once you have code to pass "Exists"
			boolean allNegAreFalse = true;
			if (false) {
				DefaultHornClausebase base = (DefaultHornClausebase)getContext().getClausebase();
				for (Literal lit : clause.getNegativeLiterals()) {
					Literal newLit = lit.applyTheta(bl);

					if (Utils.getSizeSafely(base.getPossibleMatchingFacts(newLit,null)) > 0) {
						allNegAreFalse = false;
						break;
					}
				}
			}
			
			
			
			if (allNegAreFalse) {
				
				Collection<BindingList> negBLs = new ArrayList<BindingList>();
				negBLs.add(bl);
				
				for (Literal lit : clause.getNegativeLiterals()) {
					negBLs = expandNegativeLiteralBindingList(lit, negBLs); 
				}
				counter+= negBLs.size();
				//	 Utils.println("Found binding: " + bl + " for "  + cl);
				if (blSet != null) {
					blSet.addAll(negBLs);
				}
				if(!seen_bls.addAll(negBLs) && !negBLs.isEmpty()) {
					Utils.println("Already seen binding: " + negBLs);
				}
				/* if (counter % 20 == 0) {
				 for (BindingList bl1 : seen_bls) {					
					// Utils.println("Found binding: " + bl1 + " for "  + cl);
				 }
				 Utils.waitHere("");

			}*//*
			}
		// 	bl = proof.prove();
			 
			 bl = getNextProof(groundings_prover);
		}
		/*
		if (seen_bls.size() != counter) {
			Utils.waitHere("Different number of bindings: " + seen_bls.size() + " and counter " + counter);
		}*//*
		if (Utils.getSizeSafely(cl.collectAllVariables()) > 1 || counter > 20) {
			addToCachedGroundings(cl, counter);
		}
	//	if (counter > 20) { Utils.waitHere();}
		return counter;
	}

	
	private Collection<BindingList> expandNegativeLiteralBindingList(
			Literal lit, Collection<BindingList> negBLs) {
		Collection<BindingList> outBLs = new HashSet<BindingList>();
		for (BindingList bl : negBLs) {
			Literal newLit = lit.applyTheta(bl);
			Collection<BindingList> thisLitBL = getAllPossibleGroundingsOf(newLit);
			for (BindingList newBL : thisLitBL) {
				Literal groundedLit = newLit.applyTheta(newBL);
				// If not in fact base, consider this BL
				if (getContext().getClausebase().getPossibleMatchingFacts(groundedLit, null) == null) {
					BindingList addBL = new BindingList(newBL.collectBindingsInList());
					addBL.addBindings(bl);
					outBLs.add(addBL);
				//	Utils.println("Expanded BLs to include " + groundedLit + " from " + lit + " via " + newLit + " with " + addBL);
				}
			}
		}
		return outBLs;
		
	}
	*/

	private BindingList getNextProof(HornClauseProver prover2) {
		SearchResult result = null;
		try {
			result = prover2.performSearch();
		} catch (SearchInterrupted e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
        if (result.goalFound()) {
        	return new BindingList(((ProofDone) prover2.terminator).collectQueryBindings());
        }
        return null;
	}


	public void setMEstimateNeg(double mEstimateNeg) {
		if (mEstimateNeg < 0.0) Utils.error("The 'm' for neg examples covered needs to be a non-negative number.  You provided: " + mEstimateNeg);
		this.mEstimateNeg = mEstimateNeg;
		//Utils.waitHere("setting mEstimateNeg = " + mEstimateNeg);
	}
	public double getMEstimateNeg() {
		return mEstimateNeg;
	}
	public void setMEstimatePos(double mEstimatePos) {
		if (mEstimatePos < 0.0) Utils.error("The 'm' for pos examples covered needs to be a non-negative number.  You provided: " + mEstimatePos);
		this.mEstimatePos = mEstimatePos;
	}
	public double getMEstimatePos() {
		return mEstimatePos;
	}

	void flipFlopPosAndNegExamples() {
       throw new UnsupportedOperationException("This hasn't been tested since the checkpointing and cross validation code changed." +
               "Please verify that it still works after removing this throw.  Note, some of this data now exists at the outerLoop" +
               " level, so it might make sense to move this method there.");

//		List<Example>       hold_posExamples           = getPosExamples();           setPosExamples(getNegExamples());           setNegExamples(hold_posExamples);
//		double              hold_totalPosWeight        = totalPosWeight;        totalPosWeight        = totalNegWeight;        totalNegWeight        = hold_totalPosWeight;
//		Map<Example,Double> hold_wgtOnPosExamples      = wgtOnPosExamples;      wgtOnPosExamples      = wgtOnNegExamples;      wgtOnNegExamples      = hold_wgtOnPosExamples;
//		double              hold_totalWeightOnPosSeeds = totalWeightOnPosSeeds; totalWeightOnPosSeeds = totalWeightOnNegSeeds; totalWeightOnNegSeeds = hold_totalWeightOnPosSeeds;
//		List<Example>       hold_seedPosExamples       = seedPosExamples;       seedPosExamples       = seedNegExamples;       seedNegExamples       = hold_seedPosExamples;
//		Set<Example>        hold_seedPosExamplesUsed   = getSeedPosExamplesUsed();   setSeedPosExamplesUsed(getSeedNegExamplesUsed());   setSeedNegExamplesUsed(hold_seedPosExamplesUsed);
	}

	// Some accessor functions.
	public List<Example> getPosExamples() {
		return posExamples;
	}
	public List<Example> getNegExamples() {
	       return negExamples;
	}


	public Iterable<Literal> getFacts(){
	       return context.getClausebase().getFacts();
	}

    public Iterable<Clause> getBackgroundKnowledge() {
        return context.getClausebase().getBackgroundKnowledge();
    }

	public HandleFOPCstrings getStringHandler() {
		return stringHandler;
	}
	public final HornClauseProver getProver() {
        if ( prover == null ) {
            prover = new HornClauseProver( context );
        }
		return prover;
	}
	public Unifier getUnifier() {
		return unifier;
	}
	public void setAllPosExamplesAsSeeds() {
		seedPosExamples = getPosExamples();
	}

	public List<SingleClauseNode> collectCompoundFeatures(int maxLength) throws SearchInterrupted {
		setSeedWgtedCounts();
		OpenList openList = new OpenList(this);
		initializer.initializeOpen(openList);
		SingleClauseNode firstNode = (SingleClauseNode) openList.popOpenList();
		return ((ChildrenClausesGenerator) childrenGenerator).collectAllConjuncts(firstNode, maxLength);
	}

	public void initialize() throws SearchInterrupted {
		initialize(false);
	}
	public void initialize(boolean creatingConjunctiveFeaturesOnly) throws SearchInterrupted { // Make this a separate call so that caller can set some public variables if it wants to do so.
		if ( initialized == false ) {
			long istart = System.currentTimeMillis();
            initialized = true;

            if (regressionTask) {
                stopIfPerfectClauseFound = false;
                // This causes the posExamplesThatFailedHere to be incomplete, if not set to false.
                stopWhenUnacceptableCoverage = false;
            }
            readExamples(posExamplesReader, negExamplesReader, skewMaxNegToPos);
            if (posExamplesReader       != null) closeWithoutException(posExamplesReader);
			if (negExamplesReader       != null) closeWithoutException(negExamplesReader);
            checkForSetParameters();
            this.creatingConjunctiveFeaturesOnly = creatingConjunctiveFeaturesOnly;
            savedBeamWidth = beamWidth;  // To be safe, grab this even if not doing RRR search.

            targetModes = new ArrayList<PredicateNameAndArity>(1);
            bodyModes   = new LinkedHashSet<PredicateNameAndArity>(Utils.getSizeSafely(stringHandler.getKnownModes()) - 1);
            for (PredicateNameAndArity pName : stringHandler.getKnownModes()) {
                if (examplePredicates != null && examplePredicates.contains(pName)) { targetModes.add(pName); }
                else if (!bodyModes.contains(pName) && acceptableMode(pName))       { bodyModes.add(  pName); } // Note: we are not allowing recursion here since P is either a head or a body predicate.
            }

        ProcedurallyDefinedPredicateHandler procHandler   = new ILPprocedurallyDefinedPredicateHandler(this);
		procDefinedEnoughDiffMatches   = stringHandler.getPredicateName("differentlyBoundOutputVars");
		procDefinedForConstants        = stringHandler.getPredicateName("collectContantsBoundToTheseVars");
		procDefinedNeedForNewVariables = stringHandler.getPredicateName("newTermBoundByThisVariable");
//		procedurallyDefinedPredicates.add(procDefinedEnoughDiffMatches);
//		procedurallyDefinedPredicates.add(procDefinedForConstants);
//		procedurallyDefinedPredicates.add(procDefinedNeedForNewVariables);
        context.getClausebase().setUserProcedurallyDefinedPredicateHandler(procHandler);

		//ruleAndFactsHolder = (HornClauseProverChildrenGenerator) getProver().childrenGenerator;

		if (Utils.getSizeSafely(posExamples) + Utils.getSizeSafely(negExamples) > 0) { // Sometimes we just want to use the precompute facility.
			chooseTargetMode();
		}

		// TODO - remove or comment this out at some point.
		for (int i = 0; i < getParser().getNumberOfPrecomputeFiles(); i++) {
			List<Sentence> precomputeThese = getParser().getSentencesToPrecompute(i);
			if (Utils.getSizeSafely(precomputeThese) > 0) {
				Utils.println("\n% Precompute #" + i + "'s requests: '" + replaceWildCardsForPrecomputes(getParser().getFileNameForSentencesToPrecompute(i)) + "'");
				for (Sentence s : precomputeThese) { Utils.println("%   " + s.toString(Integer.MAX_VALUE)); }
			}
		} // Utils.waitHere("after precomputing; overwritePrecomputeFileIfExists=" + overwritePrecomputeFileIfExists);


		/* for each precompute file to output, precompute all the corresponding rules... */
		for (int i = 0; i < getParser().getNumberOfPrecomputeFiles(); i++) {
			List<Sentence> precomputeThese = getParser().getSentencesToPrecompute(i); // Note that this is the set of ALL precompute's encountered during any file reading.
			if (Utils.getSizeSafely(precomputeThese) > 0) {
				// Utils.println("Have " + Utils.getSizeSafely(precomputeThese) + " sentences to precompute (i=" + i + ").");
				try {
					String precomputeFileNameToUse = replaceWildCardsForPrecomputes(getParser().getFileNameForSentencesToPrecompute(i));
					//add working dir to all files
					//precomputeFileNameToUse = parser.getDirectoryName() + precomputeFileNameToUse;
					Utils.ensureDirExists(precomputeFileNameToUse);
					// The method below will check if the precompute file already exists, and if so, will simply return.
					Utils.println("% Processing precompute file: " + precomputeFileNameToUse);
					File f = new File(precomputeFileNameToUse);
                	Utils.println("Writing to file: " + f.getAbsolutePath());
					/* Actually do the precomputes, writing precompute facts out to file*/
					precomputer.processPrecomputeSpecifications(overwritePrecomputeFileIfExists, getContext().getClausebase(), precomputeThese, precomputeFileNameToUse);
					Utils.println("% Loading: " + precomputeFileNameToUse);
					addToFacts(precomputeFileNameToUse, true); // Load the precomputed file.
				}
				catch (SearchInterrupted e) {
					Utils.reportStackTrace(e);
					Utils.error("Something went wrong during precomputing clauses.  Error message: " + e.getMessage());
				}
			}
		} // Utils.waitHere("after precomputing");
		

		String pruneFileNameToUse = Utils.createFileNameString(getDirectoryName(), "prune.txt");
		// The method below will check if the prune file already exists, and if so, will simply return true.
		Boolean pruneFileAlreadyExists = lookForPruneOpportunities(useCachedFiles && !overwritePruneFileIfExists, getParser(), pruneFileNameToUse);
		if (pruneFileAlreadyExists && useCachedFiles) { addToFacts(pruneFileNameToUse, true); } // Load the prune file, if it exists.
		// Utils.waitHere("after pruners created");
		Utils.println("\n% Started collecting constants");
		long start = System.currentTimeMillis();
		// The following will see if the old types file exists.
		if (collectTypedConstants) {
			String  typesFileNameToUse     = Utils.createFileNameString(getDirectoryName(), "types.txt");
		//	Utils.waitHere("TEMP FOR DEBUGGING: " + typesFileNameToUse);
			Boolean typesFileAlreadyExists = typeManager.collectTypedConstants(createCacheFiles, useCachedFiles, typesFileNameToUse, targets, targetArgSpecs, bodyModes, getPosExamples(), getNegExamples(), facts); // Look at all the examples and facts, and collect the typed constants in them wherever possible.
			if (typesFileAlreadyExists) {
				addToFacts(typesFileNameToUse, true); // Load the types file, if it exists.
			}
		}
		long end = System.currentTimeMillis();
		Utils.println("% Time to collect constants: " + Utils.convertMillisecondsToTimeSpan(end - start));
		
		start = System.currentTimeMillis();
        if ( syntheticExamplesEnabled ) {
            if (usingWorldStates && Utils.getSizeSafely(worldStatesContainingNoPositiveExamples) < 1 && findWorldStatesContainingNoPosExamples) {
                //Utils.println("facts:");	for (Sentence fact : backgroundFacts) { Utils.println("  " + fact); }
                worldStatesContainingNoPositiveExamples = CreateSyntheticExamples.createWorldStatesWithNoPosExamples(stringHandler,getParser(), getProver(), getPosExamples());
            }
            int oldNumbNegs = Utils.getSizeSafely(getNegExamples());
            // TODO if the constructed negative examples are created and SAVED, in the next run they will AGAIN be created (but duplicates will be filtered, so only a waste of CPU cycles).
            if (usingWorldStates && !regressionTask && Utils.getSizeSafely(getNegExamples()) < minNumberOfNegExamples && Utils.getSizeSafely(worldStatesContainingNoPositiveExamples) > 0) { // If non-null, create all the negatives examples that are implicit in these world states.
                int    oldNegCount       = Utils.getSizeSafely(getNegExamples());
                double negsStillNeeded   = Math.max(1.2, minNumberOfNegExamples - oldNegCount);  // Need this to be greater than 1.1 in order to be viewed as an integer.
                double fractOrTotalToUse = (fractionOfImplicitNegExamplesToKeep < 1.1 ? fractionOfImplicitNegExamplesToKeep : Math.max(negsStillNeeded, fractionOfImplicitNegExamplesToKeep));

                // Always save the synthetic negatives, at least for now.
                   setNegExamples(CreateSyntheticExamples.createImplicitNegExamples(worldStatesContainingNoPositiveExamples, true, "from a world-state containing no known positive examples", true || createCacheFiles, stringHandler, getProver(), targets, targetArgSpecs, examplePredicateSignatures, getPosExamples(), getNegExamples(), negExamplesReader, fractOrTotalToUse, factPredicateNames)); // TODO use a variable to set the maximum.
                if (debugLevel > 0) { Utils.println("% Now have |negExamples| = " + Utils.comma(getNegExamples()) + ", of which " + Utils.comma(Utils.getSizeSafely(getNegExamples()) - oldNegCount) + " were created from world states containing no positive examples."); }
            }
            // See if we still need to create any random examples.
            if (!creatingConjunctiveFeaturesOnly && !regressionTask && Utils.getSizeSafely(getNegExamples()) < minNumberOfNegExamples) {
                // Utils.println(" minNumberOfNegExamples=" + minNumberOfNegExamples + " and |negExamples|=" + Utils.getSizeSafely(negExamples));
                int    oldNegCount       = Utils.getSizeSafely(getNegExamples());
                double negsStillNeeded   = Math.max(1.2, minNumberOfNegExamples - oldNegCount);  // Need this to be greater than 1.1 in order to be viewed as an integer.
                double fractOrTotalToUse = (fractionOfImplicitNegExamplesToKeep < 1.1 ? fractionOfImplicitNegExamplesToKeep : Math.max(negsStillNeeded, fractionOfImplicitNegExamplesToKeep));

                // Always save the synthetic negatives, at least for now.
                   List<Example> negativeExamples = CreateSyntheticExamples.createImplicitNegExamples(null, usingWorldStates, "a randomly generated negative example", true || createCacheFiles, stringHandler, getProver(), targets, targetArgSpecs, examplePredicateSignatures, getPosExamples(), getNegExamples(), negExamplesReader, fractOrTotalToUse, factPredicateNames);  // Need to have set targetModes and create all the the above instances before calling this.
                   setNegExamples(negativeExamples);

                   if (debugLevel > 0) { Utils.println("% Now have |negExamples| = " + Utils.getSizeSafely(getNegExamples()) + ", of which " + Utils.comma(Utils.getSizeSafely(getNegExamples()) - oldNegCount) + " were created randomly."); }
            }
            //setExampleWeights(); // Set this here to be safe.
            if (!regressionTask && oldNumbNegs != Utils.getSizeSafely(getNegExamples())) { createdSomeNegExamples = true; }
        }
        end=System.currentTimeMillis();
        Utils.println("% Time to collect examples: " + Utils.convertMillisecondsToTimeSpan(end-start));
		//Utils.println("Neg=" + Utils.comma(getNegExamples()));
		if (stringHandler.needPruner) {
			this.pruner = (pruner == null ? new PruneILPsearchTree(this) : pruner);
		}
		else if (pruner != null) {
			Utils.warning("A pruner was supplied but not needed.");
			this.pruner = null;
		}
		if (!creatingConjunctiveFeaturesOnly && minNumberOfNegExamples > 0 && getNegExamples() == null) { Utils.severeWarning("Have ZERO negative examples!  Variable 'minNumberOfNegExamples' is currently set to " + minNumberOfNegExamples + "."); }
		if (debugLevel > -1) {
			Utils.println("\n% Read " + Utils.comma(getPosExamples()) + " pos examples and " + Utils.comma(getNegExamples()) + " neg examples.");//  Also read (or created) " + Utils.comma(getBackgroundKnowledge()) + " ILP background rules and " + Utils.comma(getFacts()) + " facts.");
			if (debugLevel > 1) {
				Utils.println("% The Target Modes:");
				if (targetModes != null) for (PredicateNameAndArity tName : targetModes) { tName.getPredicateName().reportPossibleInstantiations(); }
				Utils.println("% The Body Modes:");
				if (bodyModes != null)   for (PredicateNameAndArity bName : bodyModes)   { bName.getPredicateName().reportPossibleInstantiations(); }
			}
		}

        processThresholds();

        facts = null; // Release the temporarily stored facts so we aren't wasting memory.
        long iend = System.currentTimeMillis();
        Utils.println("% Time to init learnOneClause: " + Utils.convertMillisecondsToTimeSpan(iend-istart));
        }		

		// If nodes are sampled due to a decision-forest-like algorithm, then this might be incorrect.
		reportModesToFile(Utils.createFileNameString(getDirectoryName(), getPrefix() + "_modesInUse" + Utils.defaultFileExtensionWithPeriod));
	//	Utils.waitHere(getDirectoryName());
	}

    public boolean lookForPruneOpportunities(Boolean useCachedFiles, FileParser parser, String fileName) { // Be sure to do this AFTER any precomputing is done.
        // See if any 'prune' rules can be generated from this rule set.
        // For example, if 'p :- q, r' is the ONLY way to derive 'p,' then if 'p' in a clause body, no need to consider adding 'q' nor 'r.'

        //  Could simply redo this each time, since the calculation is simple, but this design allows the user to EDIT this file.
        File file = new CondorFile(fileName);
        String parseThisString = "";
        if (useCachedFiles && file.exists()) {
            Utils.warning("\n% The automatic creation of 'prune:' commands has previously occurred.  If this is incorrect, delete:\n%   '" + file.getPath() + "'", 3);
            Utils.waitHere("\n% The automatic creation of 'prune:' commands has previously occurred.  If this is incorrect, delete:\n%   '" + file.getPath() + "'");
            return true;
        }
        try {
            CondorFileOutputStream outStream = null; // Don't create unless needed.
            PrintStream printStream = null;
//			if (hashedHornTheory != null) for (List<Clause> listOfClauses : hashedHornTheory.values()) for (Clause clause : listOfClauses) {
            for (DefiniteClause definiteClause : getContext().getClausebase().getAssertions()) {
                if (definiteClause instanceof Clause) {
                    Clause clause = (Clause) definiteClause;

                    Literal clauseHead = clause.posLiterals.get(0);
                    PredicateName clauseHeadName = clauseHead.predicateName;

                    if (clauseHeadName.getTypeOnlyList(clauseHead.numberArgs()) == null) {
                        continue;
                    } // Need to have some mode.  NOTE: this means modes need to be read before this method is called.
                    Collection<Variable> boundVariables = clauseHead.collectFreeVariables(null);
                    boolean canPrune = (clause.negLiterals != null); // Should always be true, but need to test this anyway.

                    if (canPrune) { // If ANY fact has the matches the clause head, cannot prune since cannot be sure this clause was used to deduce the head.
                        canPrune = (matchingFactExists(getContext().getClausebase(), clauseHead) == null);
                    }

                    // See if there are any other ways clauseHead can be derived.  If so, set canPrune=false.
                    if (canPrune) {
                        canPrune = (matchingClauseHeadExists(getContext().getClausebase(), clauseHead, clause) == null);
                    }

                    // Can only prune predicates that are DETERMINED by the arguments in the clauseHead.  ALSO SEE Precompute.java
                    // Note: this code is 'safe' but it misses some opportunities.  E.g., if one has 'p(x) :- q(x,y)' AND THERE IS ONLY ONE POSSIBLE y FOR EACH x, then pruning is valid.  (Called "determinate literals" in ILP - TODO handle such cases.)
                    if (canPrune) {
                        for (Literal prunableLiteral : clause.negLiterals) {
                            if (prunableLiteral.predicateName.getTypeOnlyList(prunableLiteral.numberArgs()) != null && canPrune(prunableLiteral) && prunableLiteral.collectFreeVariables(boundVariables) == null) { // Could include 'if (!canPrune) then continue;' but this code should be fast enough.
                                if (useCachedFiles && outStream == null) {
                                    outStream = new CondorFileOutputStream(fileName);
                                    printStream = new PrintStream(outStream, false); // (Don't) Request auto-flush (can slow down code).
                                    printStream.println("////  This file contains inferred pruning that can be done during ILP (i.e., 'structure') search.");
                                    printStream.println("////  It can be hand edited by the knowledgeable user, but the file name should not be changed.");
                                    printStream.println("////  Note that the file 'precomputed.txt' - if it exists - might also contain some 'prune:' commands.");
                                    printStream.println("////  'Prune:' commands can also appear in BK and facts files, though including them in facts files isn't recommended.");
                                }
                                String newStringLine = "prune: " + prunableLiteral + ", " + clauseHead + ", warnIf(2)."; // Use '2' here, since if more than one rule, the inference is incorrect.
                                parseThisString += newStringLine + "\n";
                                if (debugLevel > 2) {
                                    Utils.println("\n% Inferring: '" + newStringLine + "'\n%   From: " + clause.toString(Integer.MAX_VALUE) + "."); // TODO clean up so no need for this MAX_VALUE here.
                                }
                                if (useCachedFiles) {
                                    printStream.println("\n" + newStringLine + " % From: " + clause.toString(Integer.MAX_VALUE) + "."); // TODO clean up so no need for this MAX_VALUE here.
                                    //prunableLiteral.predicateName.recordPrune(prunableLiteral, clauseHead, 2); // Complain if ever a second rule with 'clauseHead' as its head is encounted.
                                }
                            }
                        }
                    }
                }
            }
        } catch (FileNotFoundException e) {
            Utils.reportStackTrace(e);
            Utils.error("Unable to successfully open this file for writing: '" + fileName + "'.  Error message: " + e.getMessage());
        }
        parser.readFOPCstream(parseThisString);
        return false;
    }

    /** Returns whether a literal can be pruned.
     *
     * Filter some things we don't want to add to the list of prunable items.
     * Wouldn't hurt to include these, but might confuse/distract the user.
     */
    private boolean canPrune(Literal lit) {
        if (lit.predicateName == getStringHandler().standardPredicateNames.cutMarker) {
            return false;
        }
        if (lit.numberArgs() > 0) {
            for (Term term : lit.getArguments()) {
                if (term instanceof SentenceAsTerm) {
                    return false;
                }
            } // Cannot handle clauses in the parser.
        }
        return true;
    }


    /** Does an item in the fact base match (i.e., unify with) this query?
     *
     * @param query
     * @return The matching fact, if one exists. Otherwise null.
     */
    public Literal matchingFactExists(HornClausebase clausebase, Literal query) {
        if (query == null) {
            Utils.error("Cannot have query=null here.");
        }

        BindingList aBinding = new BindingList(); // Note: the unifier can change this.  But save on creating a new one for each fact.
        Iterable<Literal> factsToUse = clausebase.getPossibleMatchingFacts(query, null);

        if (factsToUse != null) {
            for (Literal fact : factsToUse) {
                aBinding.theta.clear(); // Revert to the empty binding list.
                if (Unifier.UNIFIER.unify(fact, query, aBinding) != null) {
                    return fact;
                }
            }
        }
        return null;
    }

    /**
     * Does this query unify with any known clause, other than the one to ignore?  (OK to set ignoreThisClause=null.)
     *
     * @param query
     * @param ignoreThisClause
     * @return The matching clause head if one exists, otherwise null.
     */
    public Clause matchingClauseHeadExists(HornClausebase clausebase, Literal query, Clause ignoreThisClause) {
        Iterable<Clause> candidates = clausebase.getPossibleMatchingBackgroundKnowledge(query, null);
        if (candidates == null) {
            return null;
        }
        return matchingClauseHeadExists(clausebase, query, ignoreThisClause, candidates);
    }

    /**
     * Does this query unify with the head of any of these clauses, other than the one to ignore?  (OK to set ignoreThisClause=null.)
     *
     * @param query
     * @param ignoreThisClause
     * @param listOfClauses
     * @return The matching clause head if one exists, otherwise null.
     */
    public Clause matchingClauseHeadExists(HornClausebase clausebase, Literal query, Clause ignoreThisClause, Iterable<Clause> listOfClauses) {
        if (query == null) {
            Utils.error("Cannot have query=null here.");
        }
        if (listOfClauses == null) {
            return null;
        }

        BindingList aBinding = new BindingList(); // Note: the unifier can change this.
        for (Clause clause : listOfClauses) {
            if (!clause.isDefiniteClause()) {
                Utils.error("Call clauses passed to the method must be Horn.  You provided: '" + clause + "'.");
            }
            if (clause != ignoreThisClause) {
                if (clause == null) {
                    Utils.error("Cannot have clause=null here.");
                } // Should be checked elsewhere, but play it safe.
                aBinding.theta.clear();
                if (Unifier.UNIFIER.unify(clause.posLiterals.get(0), query, aBinding) != null) {
                    return clause;
                }
            }
        }
        return null;
    }
	
	private String replaceWildCardsForPrecomputes(String precomputeFileNameString) {
		if (precomputeFileNameString.charAt(0) == '@') { precomputeFileNameString = stringHandler.getParameterSetting(precomputeFileNameString.substring(1)); }
		
	//	Utils.println("precomputeFileNameString: " + precomputeFileNameString);
		String result = precomputeFileNameString.replace("PRECOMPUTE_VAR1", Utils.removeAnyOuterQuotes(stringHandler.precompute_assignmentToTempVar1));
	//	Utils.println("precomputeFileNameString: " + result + " " + stringHandler.precompute_assignmentToTempVar1);
		result        =                   result.replace("PRECOMPUTE_VAR2", Utils.removeAnyOuterQuotes(stringHandler.precompute_assignmentToTempVar2));
	//	Utils.println("precomputeFileNameString: " + result + " " + stringHandler.precompute_assignmentToTempVar2);
		result        =                   result.replace("PRECOMPUTE_VAR3", Utils.removeAnyOuterQuotes(stringHandler.precompute_assignmentToTempVar3));
	//	Utils.waitHere("precomputeFileNameString: " + result + " " + stringHandler.precompute_assignmentToTempVar3);
		result         =                  result.replace("FACTS",           Utils.removeAnyOuterQuotes(stringHandler.FACTS));
		result         =                  result.replace("PRECOMP",         Utils.removeAnyOuterQuotes(stringHandler.PRECOMP)); // Note: this matches "PRECOMPUTE_VAR3"
		result         =                  result.replace("SWD",             Utils.removeAnyOuterQuotes(stringHandler.SWD));
		result         =                  result.replace("TASK",            Utils.removeAnyOuterQuotes(stringHandler.TASK));
		return Utils.replaceWildCards(result);
	}

    private void processThresholds() throws SearchInterrupted {

        if ( getThresholder() != null && thresholdingEnabled == true ) {

            Collection<LiteralToThreshold> thresholdThese = getParser().getLiteralsToThreshold(); // Note that this is the set of ALL thresholds's encountered during any file reading.

            // We have to make sure that we don't try to threshold the actual target predicate
            if ( targets != null && thresholdThese != null) {
                for (Iterator<LiteralToThreshold> it = thresholdThese.iterator(); it.hasNext();) {
                    LiteralToThreshold literalToThreshold = it.next();
                    PredicateNameAndArity pnaa = literalToThreshold.getPredicateNameAndArity();
                    for (Literal literal : targets) {
                        if ( pnaa.equals(literal.getPredicateNameAndArity()) ) {
                            it.remove();
                            break;
                        }
                    }
                }
            }

            if (Utils.getSizeSafely(thresholdThese) > 0) {
            	// NOTE: currently this is all done in memory and the writing to a file is only a debugging aid.
            	// So no big deal if the file is corrupted due to two runs writing at the same time (though we should still fix this).
                String thresholdFileNameToUse = (Utils.doNotCreateDribbleFiles ? null : Utils.createFileNameString(getDirectoryName(), getPrefix() + "_thresholdsNEW" + Utils.defaultFileExtensionWithPeriod)); // TODO allow user to name 'thresholded' files (i.e., by a directive command).
                getThresholder().processThresholdRequests(thresholdFileNameToUse, thresholdThese); 
            }
        }
    }

	public void resetModes(List<PredicateNameAndArity> modes) { // This doesn't impact the TARGET modes.
		bodyModes = new LinkedHashSet<PredicateNameAndArity>(Utils.getSizeSafely(modes));
		stringHandler.setKnownModes(modes);
		for (PredicateNameAndArity pName : modes) if (!examplePredicates.contains(pName)) {
			if (!bodyModes.contains(pName)) { bodyModes.add(pName); } // Note: we are not allowing recursion here since P is either a head or a body predicate.
		}
	}
	
	public boolean acceptableMode(PredicateNameAndArity pName) {
		if (!ignoreNegatedLiterals) { return true; }
		
		boolean result =  !pName.getPredicateName().name.startsWith("not_");
		if (!result) { Utils.println("% Ignoring '" + pName + "' because ignoreNegatedLiterals=true."); }
		return result;
	}

    public void addBodyMode(PredicateNameAndArity pName) {
        bodyModes.add(pName);
        stringHandler.addKnownMode(pName);
    }

    public void removeBodyMode(PredicateNameAndArity pName) {
        bodyModes.remove(pName);
        stringHandler.removeKnownMode(pName);
    }
    
    public void reportModesToFile(String fileName) {
        if ( false ) {
            try {
                StringBuilder stringBuilder = new StringBuilder();
                stringBuilder.append("% The Target Modes:\n");
                if (targetModes != null) for (PredicateNameAndArity tName : targetModes) { stringBuilder.append(tName.getPredicateName().reportPossibleInstantiationsAsString()).append("\n"); }
                stringBuilder.append("% The Body Modes:\n");
                if (bodyModes != null)   for (PredicateNameAndArity bName : bodyModes)   { stringBuilder.append(bName.getPredicateName().reportPossibleInstantiationsAsString()).append("\n"); }
                File file = Utils.ensureDirExists(fileName);
                //Utils.obtainLock(file);
                new CondorFileWriter(file, false).append(stringBuilder.toString()).close();
                //Utils.releaseLock(file);
            //	Utils.waitHere(stringBuilder.toString());
            } catch (IOException e) {
                Utils.waitHere("% Could not save the information about modes to file:\n%  " + fileName + "\n%  " + e);
            }
        }
    }

    private int countOfSearchesPerformedWithCurrentModes = 0;  // Trevor - if you wish to see getSearchParametersString, feel free to add some reportFirstNsearches variable.  Jude
    @Override
    public SearchResult performSearch() throws SearchInterrupted {

        SearchResult result = null;

        ILPSearchAction action = fireInnerLoopStarting(this);
 
        if ( action == ILPSearchAction.PERFORM_LOOP ) {

            ActiveAdvice createdActiveAdvice = null;
            if (isRelevanceEnabled() == false) {
                if ( getActiveAdvice() != null ) adviceProcessor.retractRelevanceAdvice();
            }
            else {
                if ( getActiveAdvice() != null ) {
                    createdActiveAdvice = adviceProcessor.processAdvice(currentRelevanceStrength, posExamples, negExamples);
                } 
            }

            // Limit number of reports.
            if (++countOfSearchesPerformedWithCurrentModes < 2 || debugLevel > 2) { Utils.print(getSearchParametersString()); }

            if (maxExamplesToUse > 0) {
                List<Example> holdPosExamples = getPosExamples();
                List<Example> holdNegExamples = getNegExamples();
                int     totalExamples = (onlyDiscardNegsWhenSampling ? 0 : Utils.getSizeSafely(holdPosExamples)) + Utils.getSizeSafely(holdNegExamples);
                boolean needToReduce  = totalExamples > 1.1 * maxExamplesToUse; // Don't worry if close.
                if (needToReduce) {
                    List<Example>  newPosExamples = (!onlyDiscardNegsWhenSampling && holdPosExamples == null ? null : new ArrayList<Example>(4));
                    List<Example>  newNegExamples = (                                holdNegExamples == null ? null : new ArrayList<Example>(4));
                    double fractionToKeep =  maxExamplesToUse / (double)totalExamples;
                    if (!onlyDiscardNegsWhenSampling && holdPosExamples != null) for (Example pos : holdPosExamples) if (Utils.random() <= fractionToKeep)  { newPosExamples.add(pos); }
                    if (                                holdNegExamples != null) for (Example neg : holdNegExamples) if (Utils.random() <= fractionToKeep)  { newNegExamples.add(neg); }
                    if (!onlyDiscardNegsWhenSampling) { setPosExamples(newPosExamples); }
                    setNegExamples(newNegExamples);
                }
                
            	Utils.println("% performSearch: maxExamplesToUse=" + maxExamplesToUse + "  #totalExamples=" + totalExamples);
                SearchResult sr;
                try {
                    sr = super.performSearch();
                } catch (SearchInterrupted e) {
                    if (needToReduce) {
                        if (!onlyDiscardNegsWhenSampling) { setPosExamples(holdPosExamples); }
                        setNegExamples(holdNegExamples);
                    }
                    throw e;
                }
                if (needToReduce) {
                    if (!onlyDiscardNegsWhenSampling) { setPosExamples(holdPosExamples); }
                    setNegExamples(holdNegExamples);
                }
                result = sr;
            } else {
                result = super.performSearch();
            }

            if ( createdActiveAdvice != null ) {
                adviceProcessor.retractRelevanceAdvice();
            }

            fireInnerLoopFinished(this);
        }
        else if (action == ILPSearchAction.SKIP_ITERATION) {
            Utils.println("ILPSearchListener skipped inner-loop.");
        }
        else {
            Utils.println("ILPSearchListener terminated further inner-loop execution.");
            throw new SearchInterrupted("ILPSearchListener terminated further inner-loop execution.");
        }

        return result;
    }

    public SearchResult performSearch(SingleClauseNode bestNodeFromPreviousSearch) throws SearchInterrupted {
    	if (debugLevel > 2) { Utils.println("\n% performSearch() called."); }
        if ( initialized == false ) { initialize(); }
        ((InitializeILPsearchSpace) initializer).setBestNodeFromPreviousSearch(bestNodeFromPreviousSearch);
        return performSearch();
    }

    public String getSearchParametersString() {
        StringBuilder stringBuilder = new StringBuilder();
        stringBuilder.append("\n% LearnOneClause Parameters:\n");
        
        Set<String> theTargets = getModeStrings(targetModes);
        stringBuilder.append("%   Targets (").append(Utils.comma(theTargets)).append("):\n%    ");
        stringBuilder.append(Utils.toString(theTargets, ",\n%    "));
        stringBuilder.append("\n");

        Set<String> modes = getModeStrings(bodyModes);
        stringBuilder.append("%  Modes (").append(Utils.comma(modes)).append("):\n%    ");
        stringBuilder.append(Utils.toString(modes, ",\n%    "));

        stringBuilder.append("\n");
        return stringBuilder.toString();
    }

    public Set<String> getModeStrings(Collection<PredicateNameAndArity> modes) {

        Set<String> set = new LinkedHashSet<String>();

        for (PredicateNameAndArity predicateName : modes) {

            List<PredicateSpec> types = predicateName.getPredicateName().getTypeList();
            for (PredicateSpec predicateSpec : types) {
                StringBuilder stringBuilder = new StringBuilder();
                stringBuilder.append(predicateName.getPredicateName().name).append("(");

                List<TypeSpec> typeSpecs = predicateSpec.getTypeSpecList();
                boolean first = true;
                for (TypeSpec typeSpec : typeSpecs) {
                    if ( first == false ) {
                        stringBuilder.append(", ");
                    }

                    stringBuilder.append(typeSpec);
                    first = false;
                }
                stringBuilder.append(")");
                set.add(stringBuilder.toString());
            }
        }

        return set;
    }


    public Set<String> getAlchemyModeStrings(Collection<PredicateNameAndArity> pnameArities) {

        Set<String> set = new LinkedHashSet<String>();

        for (PredicateNameAndArity predicateName : pnameArities) {

            List<PredicateSpec> types = predicateName.getPredicateSpecs();
            for (PredicateSpec predicateSpec : types) {
                StringBuilder stringBuilder = new StringBuilder();
                stringBuilder.append(predicateName.getPredicateName().name).append("(");

                List<TypeSpec> typeSpecs = predicateSpec.getTypeSpecList();
                boolean first = true;
                for (TypeSpec typeSpec : typeSpecs) {
                    if ( first == false ) {
                        stringBuilder.append(", ");
                    }

                    stringBuilder.append(typeSpec.isaType.toString().toLowerCase());
                    first = false;
                }
                stringBuilder.append(")");
                set.add(stringBuilder.toString());
                break;
            }
        }

        return set;
    }




	/** Adds a required body for a clause to be acceptable.
     *
     * The user can specify body predicates that MUST be a a clause for it to be acceptable.
	 * If more than one, the variables 'minRequiredBodyPredicates' and 'maxRequiredBodyPredicates'
	 * determine how many need to present (with these variables, one can specify AND, OR, at least N of M, exactly N of M, etc.).
	 * The default settings produce an OR (i.e., min=1 and max=infinity).  AND might be a better default, but using it would require changing min each time, and the user might have already set min or max to a desired value.  TODO devise a better interface, e.g., allow the user to specify the "semantics" to use and the code sets min and max.
     *
     * @param pNameString Required predicate name.
     * @param arity Arity of predicate.
     */
	public void addRequiredBodyPredicateForAcceptableClauses(String pNameString, int arity) {
		PredicateName pName           = stringHandler.getPredicateName(pNameString);
		Literal       literalAsHolder = stringHandler.getLiteral(pName);
		if (arity > 0) { literalAsHolder.setArguments(new ArrayList<Term>(arity)); }
		for (int i = 0; i < arity; i++) { // Although a bit inefficient, use existing data structures to record predicate name and arity.
			List<Term> arguments2 = literalAsHolder.getArguments(); // Do things this way in case the arguments are named.
			arguments2.add(stringHandler.getStringConstant("dummyArgument"));
			literalAsHolder.setArguments(arguments2);
		}
		if (requiredBodyPredicatesForAcceptableClauses == null) {
			requiredBodyPredicatesForAcceptableClauses = new ArrayList<Literal>(1);
		}
		requiredBodyPredicatesForAcceptableClauses.add(literalAsHolder);
	}

	// Record the weights on the examples and compute the total weight of the positive and negative training sets.

    // I redistributed the setExampleWeights functionality (perhaps better called
    // updateExampleWeights) off to the setPosExamples & setNegExamples methods.
    //
    // I also encapsulated the logic for min coverage settings into the
    // getters for min coverage.
    // -Trevor

//	protected void setExampleWeights() {
//		setExampleWeights(getPosExamples(), getNegExamples());
//	}
//	protected void setExampleWeights(List<Example> posExamplesToUse, List<Example> negExamplesToUse) {
//		if (posExamplesToUse == null) { posExamplesToUse = getPosExamples(); }
//		if (negExamplesToUse == null) { negExamplesToUse = getNegExamples(); }
//		if (!creatingConjunctiveFeaturesOnly && Utils.getSizeSafely(posExamplesToUse) < 1)                                 { Utils.severeWarning("Should have at least one positive training example."); return; }
//		if (!creatingConjunctiveFeaturesOnly && (minNumberOfNegExamples > 0 && Utils.getSizeSafely(negExamplesToUse) < 1)) { Utils.severeWarning("Should have at least one negative training examples"); return; }
//		totalPosWeight = sumPosExampleWgts(posExamplesToUse);
//		totalNegWeight = sumNegExampleWgts(negExamplesToUse);
//
//		if (getMinPosCoverage() > 0 && getMinPosCoverage() < 1 && totalPosWeight > 0) {
//			setMinPosCoverage(getMinPosCoverage() * totalPosWeight); // In this situation, interpret minPosCoverage as a FRACTION.
//		}
//		if (getMaxNegCoverage() > 0 && getMaxNegCoverage() < 1 && totalNegWeight > 0) {
//			setMaxNegCoverage(getMaxNegCoverage() * totalNegWeight); // In this situation, interpret maxPosCoverage as a FRACTION.
//		}
//	}

    /** Checks the minPosCoverage and minPrecision to make sure the values are in legal and attainable ranges.
     *
     * @return True if the values of minPosCoverage and minPrecision are legal and attainable.  False otherwise.
     * @throws IllegalArgumentException Throws an Illegal argument exception if a value is out of range and cannot be reset appropriately.
     */
	public boolean checkIfAcceptableClausePossible() throws IllegalArgumentException {
        boolean rv = true;

        if ( checkMinPosCoverage() == false ) {
            rv = false;
        }

		checkMinPrecision();

        return rv;
	}

    /** Sets the min weight of covered positive example for a clause to be valid.
     *
     * If 0 &gte minPosCoverage &gt 1, it is considered the fraction of positive
     * examples required.  If minPosCoverage &gte 1, it is used directly.
     *
     * Note, the actual value returned by getMinPosCoverage() is always the
     * computed value after the above conversion has been done.  Thus, getMinPosCoverage()
     * may return a different value than the one set via this method.
     *
     * @param minPosCoverage The minimum weighted positive values to cover, 0 &gte minPosCoverage &gte totalPosWeight.
     */
	public void setMinPosCoverage(double minPosCoverage) {
        // I left the "out of range" warnings here, but I moved
        // the logic for determining the actual value into getMinPosCoverage.
        // I did this so that if totalPosWeight is set or updated after
        // setMinPosCoverage is call, we still get same values (although we
        // might miss the warnings in that case). -Trevor

		// Actually, I moved the error checking up to checkMinPosCoverage().
        // It should have the same functionality as before...
        checkMinPosCoverage();

		this.minPosCoverage = minPosCoverage;
	//	Utils.waitHere("setMinPosCoverage: " + minPosCoverage);
	}
	
	public void setMinPosCoverageAsFraction(double minPosCoverageAsFractionOfPosExamples) {
		if (posExamples == null) { Utils.error("Calling setMinPosCoverageAsFraction when posExamples == null."); } // Setting posExamples will set totalPosWeight.
		setMinPosCoverage(minPosCoverageAsFractionOfPosExamples * totalPosWeight);
	}

    /** Returns the minPosCoverage value.
     *
     * If minPosCoverage is between 0 and 1, it will be considered a fraction
     * of the total positives and the computed value will be returned.
     *
     * @return
     */
	public double getMinPosCoverage() {
		double result = help_getMinPosCoverage();
	//	Utils.waitHere(" getMinPosCoverage: result = " + result + "  minPosCoverage = " + minPosCoverage + "  totalPosWeight = " + totalPosWeight);
		return Math.max(result, Double.MIN_VALUE); // Make sure we never allow zero.
	}
	private double help_getMinPosCoverage() {
//		if ( totalPosWeight > 0 && minPosCoverage > totalPosWeight && minPosCoverage >= 1.0 ) {
//            return Math.max(1.001, 0.975 * totalPosWeight); // Don't want to produce a FRACTION here, since fractions have special semantics.
//        }
//        else if ( minPosCoverage < 0 ) {
//            return 1.9;
//        }
//        else if ( minPosCoverage >= 0 && minPosCoverage < 1 ) {
//            return Math.max(1.000, 0.975 * minPosCoverage * totalPosWeight); // Don't want to produce a FRACTION here, since fractions have special semantics.
//        }
//        else {
//            return minPosCoverage;
//        }
        if ( minPosCoverage > totalPosWeight ) {
            return maxPossiblePrecision() * totalPosWeight;
        }
        else if ( minPosCoverage < 0) {
            return 0;
        }
        else return minPosCoverage;
	}

    /** Checks if the value of minPosCoverage is valid for this run.
     *
     * @return True if the value was valid, false otherwise.  If false, getMinPosCoverage() will probably
     * fix the value to a reasonable value anyway.
     */
    public boolean checkMinPosCoverage() {
        // Check the min pos coverage values...
    	if (totalPosWeight > 0 && debugLevel > 0) { Utils.println("%     totalPosWeight = " + totalPosWeight + "  minPosCoverage = " + minPosCoverage); }
		if (totalPosWeight > 0 && minPosCoverage > totalPosWeight) {  // Anything odd happen here if totalPosWeight < 1?
			Utils.warning("% Should not set minPosCoverage (" + Utils.truncate(minPosCoverage) + ") to more than the total weight on the positive examples (" + Utils.truncate(totalPosWeight) + ").  Will use the maximum possible value.");
            return false;
        }
        else if (minPosCoverage < 0) {
			Utils.warning("% Should not set minPosCoverage (" + Utils.truncate(minPosCoverage) + ") to a negative value.");
            return false;
        }
        else {
            return true;
        }
    }

    /** Sets the max weight of covered negative example for a clause to be valid.
     *
     * If 0 &gte maxNegCoverage &gt 1, it is considered the fraction of negative
     * examples required.  If maxNegCoverage &gte 1, it is used directly.
     *
     * Note, the actual value returned by getMaxNegCoverage() is always the
     * computed value after the above conversion has been done.  Thus, getMaxNegCoverage()
     * may return a different value than the one set via this method.
     *
     * @param maxNegCoverage The maximum weighted negative values to cover, 0 &gte minPosCoverage &gte totalPosWeight.
     */
	public void setMaxNegCoverage(double maxNegCoverage) {
        // I moved the logic for determining the actual value into getMaxNegCoverage.
        // I did this so that if totalNegWeight is set or updated after
        // setMinPosCoverage is call, we still get sane values (although we
        // might miss the warnings in that case). -Trevor
		this.maxNegCoverage = maxNegCoverage;

	}

    /** Returns the maximum negative coverage value.
     *
     * If maxNegCoverage is between 0 and 1, it will be considered a fraction
     * of the total negative and the computed value will be returned.
     *
     * @return
     */
	public double getMaxNegCoverage() {
        if (maxNegCoverage > 0 && maxNegCoverage < 1 && totalNegWeight > 0) {
			return maxNegCoverage * totalNegWeight; // In this situation, interpret maxNegCoverage as a FRACTION.
		}
		return maxNegCoverage;
	}

	public void setMinPrecision(double minPrecision) {
		checkMinPrecision();
		this.minPrecision = minPrecision;
	}

	public double getMinPrecision() {
		return minPrecision;
	}


	public void setMaxRecall(double maxRecall) {
		checkMaxRecall();
		this.maxRecall = maxRecall;
	}

	public double getMaxRecall() {
		return maxRecall;
	}

    /** Checks the value of the minPrecision.
     *
     * @throws IllegalArgumentException Throws an IllegalArgumentException if the parameter is out of range.
     */
    public void checkMinPrecision() throws IllegalArgumentException {
    	if (debugLevel > 0) { Utils.println("%     maxPossiblePrecision = " +  maxPossiblePrecision() + "  minPrecision = " + minPosCoverage); }
        if (minPrecision < 0) {
        	minPrecision = 0.0;
		//	throw new IllegalArgumentException("Should not set minPrecision (" + Utils.truncate(minPrecision) + ") to a negative value.");
        	Utils.warning("Should not set minPrecision (" + Utils.truncate(minPrecision) + ") to a negative value.  Will use 0.");
		}

		if (minPrecision > 1) {
			minPrecision = maxPossiblePrecision();
		//	throw new IllegalArgumentException("Should not set minPrecision (" + Utils.truncate(minPrecision) + ") to a value above 1.");
			Utils.warning("Should not set minPrecision (" + Utils.truncate(minPrecision) + ") to a value above 1.  Will use the maxPossiblePrecision().");
		}

		if (totalPosWeight > 0 && minPrecision > maxPossiblePrecision()) {
			minPrecision= maxPossiblePrecision();
		//	throw new IllegalArgumentException("Should not set minPrecision (" + Utils.truncate(minPrecision) + ") to a value above the max possible precision (" + maxPossiblePrecision() + ").");
			Utils.warning("Should not set minPrecision (" + Utils.truncate(minPrecision) + ") to a value above the max possible precision (" + maxPossiblePrecision() + ").  Will use this max value instead.");
		}
    }

    public void checkMaxRecall()  throws IllegalArgumentException {
        if (maxRecall <= 0.0) {
        	maxRecall = 0.000001;
		//	throw new IllegalArgumentException("Should not set maxRecall (" + Utils.truncate(maxRecall) + ") to a non-positive value.");
        	Utils.warning("Should not set maxRecall (" + Utils.truncate(maxRecall) + ") to a non-positive value.  Using " + maxRecall);
		}
    }

	public double maxPossiblePrecision() {
		return totalPosWeight / (totalPosWeight +  getMEstimateNeg());
	}

	public SearchResult performRRRsearch(SingleClauseNode bestNodeFromPreviousSearch) throws SearchInterrupted { //TODO: add some early-stopping criteria

		int hold_maxNodesToExpand = getMaxNodesToConsider(); // Save these so they can be restored.
		int hold_maxNodesToCreate = getMaxNodesToCreate();
		int hold_nodesExpanded    = 0;
		int hold_nodesCreated     = 0;

		performRRRsearch   = true;
		setMaxNodesToConsider(maxNodesToConsiderRRR); // Switch to the RRR-specific settings.
		setMaxNodesToCreate(maxNodesToCreateRRR);
		for (int i = 1; i <= restartsRRR; i++) {
			if (hold_nodesExpanded >= hold_maxNodesToExpand) {
				searchMonitor.searchEndedByMaxNodesConsidered(hold_nodesExpanded);
				break;
			}
			if (hold_nodesCreated    >= hold_maxNodesToCreate) {
				searchMonitor.searchReachedMaxNodesCreated(   hold_nodesCreated);
				break;
			}
			stillInRRRphase1  = true;
			thisBodyLengthRRR = minBodyLengthRRR + Utils.random1toN(maxBodyLengthRRR - minBodyLengthRRR);
			if (debugLevel > 1) { Utils.println("\n***********\nPerform RRR iteration #" + i + " with the initial body length = " + thisBodyLengthRRR + " (in the ILP inner loop, created a total of " + Utils.comma(hold_nodesCreated) + " clauses so far and explored " + Utils.comma(hold_nodesExpanded) + ")\n***********"); }
			performSearch(bestNodeFromPreviousSearch);  // No need to do a open.clear() since performSearch() does that.
			hold_nodesExpanded += nodesConsidered;
			hold_nodesCreated  += nodesCreated;
		}
		nodesConsidered    = hold_nodesExpanded; // Set the search totals to count ALL the RRR iterations.
		nodesCreated       = hold_nodesCreated;
		setMaxNodesToConsider(hold_maxNodesToExpand); // Revert to the old settings for these.
		setMaxNodesToCreate(hold_maxNodesToCreate);
		return null; // TODO return something useful
	}

	public List<Example> collectPosExamplesCovered(SingleClauseNode node) throws SearchInterrupted {
		return collectExamplesCovered(getPosExamples(),node);
	}
	public List<Example> collectNegExamplesCovered(SingleClauseNode node) throws SearchInterrupted {
		return collectExamplesCovered(getNegExamples(),node);
	}

	public int collectPosExamplesCovered(Clause clause, boolean reportErrors) throws SearchInterrupted {
		return countExamplesCovered(getPosExamples(),clause, reportErrors, true);
	}
	public int collectNegExamplesCovered(Clause clause, boolean reportErrors) throws SearchInterrupted {
		return countExamplesCovered(getNegExamples(),clause, reportErrors, false);
	}

    /** Evaluates each example in inputExamples against the clause, putting it into trueExamples or falseExamples, as appropriate.
     *
     * Both trueExamples and falseExamples can be null.  If either one is null, that type of example will
     * just not be recorded.  If both are null, nothing will actually be done.
     *
     * It is safe for inputExamples to be the same collection as either coveredExamples or uncoveredExamples.
     * If it is, inputExamples will be modified appropriately.  Otherwise, inputExamples will not be modified.
     *
     * @param clause Clause to evaluate.
     * @param inputExamples Examples to evaluate against.
     * @param trueExamples Collection to add provable examples to.
     * @param falseExamples Collection to add unprovable Examples to.
     */
    public void proveExamples(Clause clause, Collection<Example> inputExamples, Collection<Example> trueExamples, Collection<Example> falseExamples) {
        if (inputExamples == null || (trueExamples == null && falseExamples == null)) {
            return;
        }

        if (!clause.isDefiniteClause()) {
            throw new IllegalArgumentException("This code only handles definite clauses (only one positive literal): " + clause);
        }

        boolean setsOverlap = (inputExamples == trueExamples || inputExamples == falseExamples);

        for (Iterator<Example> it = inputExamples.iterator(); it.hasNext();) {
            Example example = it.next();

            boolean isTrue = proveExample(clause, example);

            if ( setsOverlap ) {
                // If the inputExamples list is the same as either of the true examples
                // or the false examples, we need to play some games to make sure
                // the lists are updated correctly.
                if ( inputExamples == trueExamples && isTrue == false ) {
                    // The input and true examples are the same but the example is
                    // false.  Remove it from the inputExamples and put it
                    // in the false examples.
                    it.remove();

                    if ( falseExamples != null ) {
                        falseExamples.add(example);
                    }
                }
                else if ( inputExamples == falseExamples && isTrue == true ) {
                    // The input and false examples  are the same but the example is
                    // true.  Remove it from the inputExamples and put it
                    // in the true examples.
                    it.remove();

                    if ( trueExamples != null ) {
                        trueExamples.add(example);
                    }
                }

                // If things fall through to here, the examples will just be left in
                // the input set, which also matches the set it should be in, so
                // nothing needs to be done here.
            }
            else {
                if ( isTrue ) {
                    // examples is true and the sets are disjoint
                    if ( trueExamples != null ) {
                        trueExamples.add(example);
                    }
                }
                else {
                    // examples is false and the sets are disjoint
                    if ( falseExamples != null ) {
                        falseExamples.add(example);
                    }
                }
            }
        }
    }


    /** Attempts to prove a single example given clause <code>clause</code> and returns
    * the bindings if finds a proof.
    * If an error occurs, this method silently catches the error and returns
    * false.
    *
    * @param clause Clause to evaluate.
    * @param ex Example to prove.
    * @return binding list for head, if the example is true, null otherwise.
    */
   public BindingList proveExampleAndReturnBindingList(Clause clause, Example ex) {

       try {
           Literal head = clause.posLiterals.get(0);
           List<Literal> clauseBody = clause.negLiterals;
           BindingList bindingList = unifier.unify(head, ex);

           if (bindingList == null) {
           		Utils.println("% proveExampleAndReturnBindingList: " + head + ":" + ex + ":" + clause);
           		Utils.error("%%%%%%%%%%%%%%%%% COULDNT FIND BINDING %%%%%%%%%%%%");
           		return null;
           }
           else if (clauseBody == null) {
           		Utils.error("%%%%%%%%%%%%%%%%% EMPTY BODY %%%%%%%%%%%%");
               return null;
           }
           else {
               List<Literal> query = bindingList.applyTheta(clauseBody);
               //Utils.println(" query=" + query + "\n ex=" + ex + "\n head=" + head + "\n body=" + clauseBody + "\n bindings=" + bindingList);

               BindingList result = proveAndReturnBindings(query);
               return result;
           }
       } catch (SearchInterrupted si) {
       }
       return null;
   }
    /** Attempts to prove a single example given clause <code>clause</code>.
     *
     * If an error occurs, this method silently catches the error and returns
     * false.
     *
     * @param clause Clause to evaluate.
     * @param ex Example to prove.
     * @return True if the example is true, false otherwise.
     */
    public boolean proveExample(Clause clause, Example ex) {

        try {
            Literal head = clause.posLiterals.get(0);
            List<Literal> clauseBody = clause.negLiterals;
            BindingList bindingList = unifier.unify(head, ex);

            if (bindingList == null) {
            	Utils.println("%%%%%% NO BINDINGS %%%%%% for clause head (" + head.numberArgs() + " [head] vs. " + ex.numberArgs() + " [example] args)\n  '" + head + "'\n and example\n  '" + ex + "'.");
                return false;
            }
            else if (clauseBody == null) {
                return true;
            }
            else {

                if ( prover.getTraceLevel() == 0 && prover.getSpyEntries().includeElement(head.predicateName, head.numberArgs())) {
                    Utils.println("Spy point encountered on " + head.predicateName + "/" + head.numberArgs() + ".  Enabling tracing.");
                    prover.setTraceLevel(1);
                }

                List<Literal> query = bindingList.applyTheta(clauseBody);
                
                //Utils.println(" query=" + query + "\n ex=" + ex + "\n head=" + head + "\n body=" + clauseBody + "\n bindings=" + bindings);
                //Utils.println(" prover=" + prover);
                if (prove(query)) {
                    return true;
                }
				return false;
            }
        } catch (SearchInterrupted si) {
        }

        return false;
    }

    /** Returns the coverage score for sets of examples.
     *
     * @param clause Clause to prove.
     * @param positiveExamples Set of positive examples.
     * @param negativeExamples Set of negative examples.
     * @return Sum of the weights of all covered examples in examples.
     */
    public CoverageScore getWeightedCoverage(Clause clause, Collection<Example> positiveExamples, Collection<Example> negativeExamples) {
        return getWeightedCoverage(clause, positiveExamples, negativeExamples, null);
    }

    /** Returns the coverage score for sets of examples.
     *
     * @param clause Clause to prove.
     * @param positiveExamples Set of positive examples.
     * @param negativeExamples Set of negative examples.
     * @param coverageScore CoverageScore object to store results in.  If null, one will be created.  If non-null, the counts will be incremented, no replaced.
     * @return Sum of the weights of all covered examples in examples.
     */
    public CoverageScore getWeightedCoverage(Clause clause, Collection<Example> positiveExamples, Collection<Example> negativeExamples, CoverageScore coverageScore) {
    	if (regressionTask) { Utils.error("Do not call 'getWeightedCoverage' when regressionTask = true."); }
        if ( coverageScore == null ) {
            coverageScore = new CoverageScore();
            coverageScore.setFalseNegativeMEstimate(getMEstimatePos());
            coverageScore.setFalsePositiveMEstimate(getMEstimateNeg());
            // Utils.waitHere("#1 mEstimatePos=" + getMEstimatePos() + " mEstimateNeg=" + getMEstimateNeg());
        }

        HashSet<Example> truePositives  = new HashSet<Example>();
        HashSet<Example> falsePositives = new HashSet<Example>();
        HashSet<Example> trueNegatives  = new HashSet<Example>();
        HashSet<Example> falseNegatives = new HashSet<Example>();

        if ( positiveExamples != null ) {
            proveExamples(clause, positiveExamples, truePositives, falseNegatives);
        }

        if ( negativeExamples != null ) {
            proveExamples(clause, negativeExamples, falsePositives, trueNegatives);
        }

        double tp = Example.getWeightOfExamples(truePositives);
        double fp = Example.getWeightOfExamples(falsePositives);
        double tn = Example.getWeightOfExamples(trueNegatives);
        double fn = Example.getWeightOfExamples(falseNegatives);

        coverageScore.setTruePositives(  coverageScore.getTruePositives()  + tp);
        coverageScore.setFalsePositives( coverageScore.getFalsePositives() + fp);
        coverageScore.setTrueNegatives(  coverageScore.getTrueNegatives()  + tn);
        coverageScore.setFalseNegatives( coverageScore.getFalseNegatives() + fn);

        return coverageScore;
    }

    /** Returns the coverage score for sets of examples.
     *
     * Calculates the weighted coverage of a Theory on a set of examples.
     * An example is considered covered by the Theory if any of the
     * clauses in the Theory cover the example.
     *
     * @param theory Theory to prove.
     * @param positiveExamples Set of positive examples.
     * @param negativeExamples Set of negative examples.
     * @return Sum of the weights of all covered examples in examples.
     */
    public CoverageScore getWeightedCoverage(Theory theory, Collection<Example> positiveExamples, Collection<Example> negativeExamples) {
        return getWeightedCoverage(theory, positiveExamples, negativeExamples, null);
    }
    
    /** Returns the coverage score for the CURRENT set of examples stored in this instance.
     *
     * Calculates the weighted coverage of a Theory on a set of examples.
     * An example is considered covered by the Theory if any of the
     * clauses in the Theory cover the example.
     *
     * @param theory Theory to prove.
     * @param positiveExamples Set of positive examples.
     * @param negativeExamples Set of negative examples.
     * @return Sum of the weights of all covered examples in examples.
     */
    public CoverageScore getWeightedCoverage(Theory theory) {
        return getWeightedCoverage(theory, posExamples, negExamples, null);
    }

    /** Returns the coverage score for sets of examples.
     *
     * Calculates the weighted coverage of a Theory on a set of examples.
     * An example is considered covered by the Theory if any of the
     * clauses in the Theory cover the example.
     *
     * @param theory Theory to prove.
     * @param positiveExamples Set of positive examples.
     * @param negativeExamples Set of negative examples.
     * @param coverageScore CoverageScore object to store results in.  If null, one will be created.  If non-null, the counts will be incremented, no replaced.
     * @return Sum of the weights of all covered examples in examples.
     */
    public CoverageScore getWeightedCoverage(Theory theory, Collection<Example> positiveExamples, Collection<Example> negativeExamples, CoverageScore coverageScore) {
    	if (regressionTask) { Utils.error("Do not call 'getWeightedCoverage' when regressionTask = true."); }
        if ( coverageScore == null ) {
            coverageScore = new CoverageScore();
            coverageScore.setFalseNegativeMEstimate(getMEstimatePos());
            coverageScore.setFalsePositiveMEstimate(getMEstimateNeg());
            // Utils.waitHere("#2 mEstimatePos=" + getMEstimatePos() + " mEstimateNeg=" + getMEstimateNeg());
        }

        HashSet<Example> truePositives  = new LinkedHashSet<Example>(); //   Covered positives.
        HashSet<Example> falsePositives = new LinkedHashSet<Example>(); //   Covered negatives.
        HashSet<Example> trueNegatives  = new LinkedHashSet<Example>(); // Uncovered negatives.
        HashSet<Example> falseNegatives = new LinkedHashSet<Example>(); // Uncovered positives.

        if ( positiveExamples != null ) {
            falseNegatives.addAll(positiveExamples);
        }

        if ( negativeExamples != null ) {
            trueNegatives.addAll(negativeExamples);
        }

        if ( theory.getClauses() != null ) {
            Utils.println(    "  initially:  |falseNegatives| = " + Utils.comma(falseNegatives) + " and |trueNegatives| = " +  Utils.comma(trueNegatives) + ".");
            for (Clause clause : theory.getClauses()){
            	Utils.println("     getWeightedCoverage: apply this clause " + clause);
                proveExamples(clause, falseNegatives, truePositives, falseNegatives);
                proveExamples(clause, trueNegatives, falsePositives, trueNegatives);
                Utils.println("  currently:  |falseNegatives| = " + Utils.comma(falseNegatives) + " and |trueNegatives| = " +  Utils.comma(trueNegatives) + ".");
            }
        }

        double tp = Example.getWeightOfExamples(truePositives);
        double fp = Example.getWeightOfExamples(falsePositives);
        double tn = Example.getWeightOfExamples(trueNegatives);
        double fn = Example.getWeightOfExamples(falseNegatives);

        coverageScore.setTruePositives(  coverageScore.getTruePositives()  + tp);
        coverageScore.setFalsePositives( coverageScore.getFalsePositives() + fp);
        coverageScore.setTrueNegatives(  coverageScore.getTrueNegatives()  + tn);
        coverageScore.setFalseNegatives( coverageScore.getFalseNegatives() + fn);

        return coverageScore;
    }

	public void setDumpGleanerEveryNexpansions(int dumpGleanerEveryNexpansions) {
		this.dumpGleanerEveryNexpansions = dumpGleanerEveryNexpansions;
	}

	public int getDumpGleanerEveryNexpansions() {
		return dumpGleanerEveryNexpansions;
	}

	/**
         * If fewer than minWgtedCoverage or more than maxWgtedCoverage, can
         * stop and return null since this node is unacceptable.
         *
         * @param examples
         * @param node
         * @return A list of examples covered by this node.
         * @throws SearchInterrupted
         */
	private List<Example> collectExamplesCovered(List<Example> examples, SingleClauseNode node) throws SearchInterrupted {
		if (examples == null) { return null; }
		List<Example> results    = null;
		List<Literal> clauseBody = node.getClauseBody();
		Literal       target     = node.getTarget();
		for (Example ex : examples) {
			if (node.proveExample(this, target, clauseBody, ex, bindings)) { // AT LEAST LOOK AT THE EX'S ALREADY CANCELED.
				if (results == null) { results = new ArrayList<Example>(32); }
				results.add(ex);
			}
		}
		return results;
	}
	private int countExamplesCovered(List<Example> examples, Clause clause, boolean reportErrors, boolean category) throws SearchInterrupted {
		if (examples == null) { return 0; }
		int count = 0;
		if (!clause.isDefiniteClause()) { Utils.error("This code only handles definite clauses (only one positive literal): " + clause); }
		Literal head = clause.posLiterals.get(0);
		List<Literal> clauseBody = clause.negLiterals;
		for (Example ex : examples) {
			BindingList bindingList = unifier.unify(head, ex);
			if (bindingList == null) {
				if (head.predicateName != ex.predicateName || head.numberArgs() != ex.numberArgs()) {
					Utils.error("Cannot match " + head + " and " + ex);  // Flag a POSSIBLE problem (e.g., examples could vary in arity).
				}
				continue;
			}
			if (clauseBody == null) { count++; }
			else {
				List<Literal> query = bindingList.applyTheta(clauseBody);
				//Utils.println(" query=" + query + "\n ex=" + ex + "\n head=" + head + "\n body=" + clauseBody + "\n bindings=" + bindings);
				//Utils.println(" prover=" + prover);
				if (prove(query)) {
					if    (reportErrors && !category) { Utils.println("%   Error on NEG example: '" + ex + "'."); }
					count++;
				} else if (reportErrors &&  category) { Utils.println("%   Error on POS example: '" + ex + "'."); }
			}
		}
		return count;
	}

    public boolean isPositiveExample(Literal ex) {
        if (regressionTask) {
            Utils.error("Do not call 'isPositiveExample' when regressionTask = true.");
        }
        for (Example pos : getPosExamples()) {
            if (pos.equals(ex)) {
                return true;
            } // TODO - if this is too slow, also hash examples.
        }
        return false;
    }

    public boolean isNegativeExample(Literal ex) {
        if (regressionTask) {
            Utils.error("Do not call 'isNegativeExample' when regressionTask = true.");
        }
        for (Example neg : getNegExamples()) {
            if (neg.equals(ex)) {
                return true;
            }
        }
        return false;
    }

	// Allow direct specification of the seeds.
	public void selectTheseSeeds(List<Example> posSeeds, List<Example> negSeeds) {
		selectTheseSeeds(posSeeds, negSeeds, true);
	}
	public void selectTheseSeeds(List<Example> posSeeds, List<Example> negSeeds, boolean confirmAllSeedExamplesExist) {

		if (confirmAllSeedExamplesExist) {
			for (Example ex : posSeeds) if (!isPositiveExample(ex)) { Utils.error("Positive seed '" + ex + "' is not a known positive example."); }
			for (Example ex : negSeeds) if (!isNegativeExample(ex)) { Utils.error("Negative seed '" + ex + "' is not a known negative example."); }
		}

		seedPosExamples = posSeeds;
		seedNegExamples = negSeeds;
		setSeedWgtedCounts();
	}

	// Allow the user to choose which seeds (eg, might want to use Condor and let the Condor run # deterministically indicate which seed(s) to select.
	public void selectTheseSeedsByIndex(int[] posSeedIndices, int[] negSeedIndices, Set<Example> seedPosExamplesUsed, Set<Example> seedNegExamplesUsed) {
		selectTheseSeedsByIndex(posSeedIndices, negSeedIndices, true, seedPosExamplesUsed, seedNegExamplesUsed);
	}
	public void selectTheseSeedsByIndex(int[] posSeedIndices, int[] negSeedIndices, boolean complainIfPreviouslyUsed, Set<Example> seedPosExamplesUsed, Set<Example> seedNegExamplesUsed) {
		int numberOfPosEx = Utils.getSizeSafely(getPosExamples());
		int numberOfNegEx = Utils.getSizeSafely(getNegExamples());

      if ( seedPosExamplesUsed == null || seedNegExamplesUsed == null ) {
           throw new NullPointerException("seedPosExamplesUsed and seedNegExamplesUsed must be non-null.");
       }

		if (allowPosSeedsToBeReselected ) {
			seedPosExamplesUsed.clear();
		}
		if (allowNegSeedsToBeReselected ) {
			seedNegExamplesUsed.clear();
		}
		if (posSeedIndices != null && posSeedIndices.length > 0) {
			seedPosExamples = new ArrayList<Example>(posSeedIndices.length);
			for (int index : posSeedIndices) {
				if (index < 0 || index >= numberOfPosEx) { Utils.error("Pos seed index " + index + " must be in [0," + (numberOfPosEx - 1) + "]"); }
				Example chosenExample = getPosExamples().get(index);

            // TAW: There seems to be a little logic problem here.
            // It seems like allowPosSeedsToBeReselected and complainIfPreviouslyUsed do the same thing.
				if (complainIfPreviouslyUsed && seedPosExamplesUsed.contains(chosenExample)) {
					Utils.error("Pos seed #" + index + " has already been used.");
				}
				    seedPosExamplesUsed.add(chosenExample);
				seedPosExamples.add(    chosenExample);
			}
		}
		if (negSeedIndices != null && negSeedIndices.length > 0) {
			seedNegExamples = new ArrayList<Example>(negSeedIndices.length);
			for (int index : negSeedIndices) {
				if (index < 0 || index >= numberOfNegEx) { Utils.error("Neg seed index " + index + " must be in [0," + (numberOfNegEx - 1) + "]"); }
				Example chosenExample = getNegExamples().get(index);

				if (complainIfPreviouslyUsed && seedNegExamplesUsed.contains(chosenExample)) {
					Utils.error("Neg seed #" + index + " has already been used.");
				}
				    seedNegExamplesUsed.add(chosenExample);
				seedNegExamples.add(    chosenExample);
			}
		}
		setSeedWgtedCounts();
	}


	private void setSeedWgtedCounts() {
		totalWeightOnPosSeeds = Example.getWeightOfExamples(seedPosExamples);
		totalWeightOnNegSeeds = Example.getWeightOfExamples(seedNegExamples);
	}

	public boolean selectSeedsRandomly(int numberPos, int numberNeg, Set<Example> seedPosExamplesUsed, Set<Example> seedNegExamplesUsed) {

       if ( seedPosExamplesUsed == null ) {
           seedPosExamplesUsed = new HashSet<Example>();
       }

       if ( seedNegExamplesUsed == null ) {
           seedNegExamplesUsed = new HashSet<Example>();
       }

		int desiredNumberOfPosSeeds = Math.max(0, numberPos);
		int desiredNumberOfNegSeeds = Math.max(0, numberNeg);

		if (desiredNumberOfPosSeeds < 1) { seedPosExamples = null; }
		else {
			seedPosExamples = new ArrayList<Example>(desiredNumberOfPosSeeds);
			if (allowPosSeedsToBeReselected ) {
				    seedPosExamplesUsed.clear();
			}
			for (int i = 0; i < desiredNumberOfPosSeeds; i++) {
				boolean found = false;
				int     count = 0;
				while (!found && count++ < 100) { // Try 100 times to find.  Alternate: remove seeds used from candidate list?
					int     index = Utils.random0toNminus1(Utils.getSizeSafely(getPosExamples()));
					Example chosenExample = getPosExamples().get(index);

					if (allowPosSeedsToBeReselected || !seedPosExamplesUsed.contains(chosenExample)) { // If not already used, this is a good seed.
						      seedPosExamplesUsed.add(chosenExample);
						seedPosExamples.add(chosenExample);
						found = true;
					}
				}
				// If can't find all the pos seeds wanted, live with the number found.
				if (!found) { setSeedWgtedCounts(); return false; /* Utils.error("Could not find pos seed #" + i + " after 100 tries."); */ }
			}
		}
		if (desiredNumberOfNegSeeds < 1) { seedNegExamples = null; }
		else {
			seedNegExamples = new ArrayList<Example>(desiredNumberOfNegSeeds);
			if (allowNegSeedsToBeReselected ) {
				    seedNegExamplesUsed.clear();
			}
			for (int i = 0; i < desiredNumberOfNegSeeds; i++) {
				boolean found = false;
				int     count = 0;
				while (!found && count++ < 100) { // Try 100 times to find.  Alternate: remove seeds used from candidate list?
					int     index = Utils.random0toNminus1(Utils.getSizeSafely(getNegExamples()));
					Example chosenExample = getNegExamples().get(index);

					if (allowNegSeedsToBeReselected || !seedNegExamplesUsed.contains(chosenExample)) { // If not already used, this is a good seed.
						      seedNegExamplesUsed.add(chosenExample);
						seedNegExamples.add(    chosenExample);
						found = true;
					}
				}
				// If can't find all the neg seeds wanted, live with the number found.
				if (!found) { setSeedWgtedCounts(); return false; /* Utils.error("Could not find neg seed #" + i + " after 100 tries."); */ }
			}
		}
		setSeedWgtedCounts();
		return true;
	}

	// Note: this is NOT used to prove examples.  See SingleClauseNode.proveExample() for that.
	protected boolean prove(Literal negatedFact) throws SearchInterrupted {
		return getProver().proveSimpleQuery(negatedFact);
	}

//    private static final boolean RECORD_ALL_PROOFS = false;
//    private BufferedWriter log;
//    private long proofCount = 0;

	protected BindingList proveAndReturnBindings(List<Literal> negatedConjunctiveQuery) throws SearchInterrupted {
		if (negatedConjunctiveQuery == null) {
			Utils.error("Called for null query");
			return new BindingList();
		} // The empty list is really a body that equals the built-in predicate 'true()'.

        long startTime = System.nanoTime();

		BindingList result = getProver().proveConjunctiveQueryAndReturnBindings(negatedConjunctiveQuery);

        totalProofTimeInNanoseconds += System.nanoTime() - startTime;
        totalProofsProved++;
        return result;
	}

	protected boolean prove(List<Literal> negatedConjunctiveQuery) throws SearchInterrupted {
		if (negatedConjunctiveQuery == null) { return true; } // The empty list is really a body that equals the built-in predicate 'true()'.

        long startTime = System.nanoTime();

		boolean result = getProver().proveConjunctiveQuery(negatedConjunctiveQuery);

        totalProofTimeInNanoseconds += System.nanoTime() - startTime;
        totalProofsProved++;

//        if ( RECORD_ALL_PROOFS ) {
//            try {
//                if ( log == null ) log = new BufferedWriter( new CondorFileWriter("/tmp/log2", false) ); // Create a new file.
//                log.append(Long.toString(proofCount++));
//                log.append(": ");
//                log.append(negatedConjunctiveQuery.toString());
//                log.append(" = " );
//                log.append(result?"True":"False");
//                log.newLine();
//            }
//            catch(IOException e) {
//
//            }
//        }

        return result;
	}

	// Make sure all the examples have the same predicate and the same arity (unless allowMultipleTargets = true).
	private int warningCountAboutExamples = 0;

	// TVK - Made public to allow moving facts to examples (needed for joint inference)[06/10/10]
	public boolean confirmExample(Literal lit) {
		int litSize = lit.numberArgs();
        PredicateNameAndArity pnaa = lit.getPredicateNameAndArity();
		
	//	Utils.waitHere("Confirm example: " + lit);

		if (litSize > 0 && Utils.getSizeSafely(lit.collectAllVariables()) > 0) {  // TODO - could just like to see if any variables and same some cpu cycles and memory.
			Utils.severeWarning("Do you really want to have VARIABLEs in examples?  If so, WILL code needs updating (e.g, in terms of counting coverage, etc.)\n " + lit);
		}

		if (examplePredicates == null) {
			examplePredicates          = new ArrayList<PredicateNameAndArity>(1);
			//examplePredicateArities    = new ArrayList<Integer>(1);
			examplePredicateSignatures = new ArrayList<List<Term>>(1);
		}

		if (allowMultipleTargets || examplePredicates.isEmpty()) {
			if (!matchesExistingTargetSpec(lit)) {
				// Utils.println("% Adding a predicate name for an example: " + lit.predicateName);
				examplePredicates.add(pnaa);
				//examplePredicateArities.add(litSize);
				examplePredicateSignatures.add(stringHandler.getSignature(lit.getArguments()));
			}
		}
		else if (!examplePredicates.contains(pnaa) && warningCountAboutExamples++ < 10) {
			Utils.severeWarning("AllowMultipleTargets = false and example '" + lit + "' does not have the predicate name of the other examples: " + examplePredicates +".");
		}
//		else if (!examplePredicateArities.contains(litSize)     && warningCountAboutExamples++ < 10) {
//			Utils.severeWarning("AllowMultipleTargets = false and example " + lit + " does not have the arity of the other examples: " + examplePredicates + "/" + examplePredicateArities);
//		}
		return true;
	}

	private boolean matchesExistingTargetSpec(Literal lit) {
		if (examplePredicates == null) { Utils.error("matchesExistingTargetSpec: examplePredicates = null"); }
		for (int i = 0; i < examplePredicates.size(); i++) {
			if (examplePredicates.get(i).equals(lit.getPredicateNameAndArity()) && 
				matchingSignatures(examplePredicateSignatures.get(i), stringHandler.getSignature(lit.getArguments()))) { return true; }
		}
		if (debugLevel > 1) { Utils.println("matchesExistingTargetSpec false for: " + lit + "  sig = " + stringHandler.getSignature(lit.getArguments()) + "  " + Utils.limitLengthOfPrintedList(examplePredicates)); }
		//Utils.waitHere();
		return false;
	}

	private boolean matchingSignatures(List<Term> terms1, List<Term> terms2) {
		if (terms1 == terms2)                 { return true;  }
		if (terms1 == null || terms2 == null) { return false; }
		if (terms1.size() != terms2.size())   { return false; }
		for (int i = 0; i < terms1.size(); i++) {
			if (terms1.get(i) != terms2.get(i)) { // If not a direct match, then must be matching functions.
				if (terms1.get(i) instanceof Function && terms2.get(i) instanceof Function) {
					if (!matchingSignatures(((Function) terms1.get(i)).getArguments(),
											((Function) terms2.get(i)).getArguments())) {
						return false;
					}
				} else { return false; }
			}
		}
		return true;
	}

	private PredicateName annotationPredName        = null;
	private PredicateName regressionExamplePredName = null;
	@SuppressWarnings("unused")
	   public List<Example> readExamples(Reader examplesReader, String readerDirectoryName) {
		return readExamples(examplesReader, readerDirectoryName, false);
	}
	private List<Example> readExamples(Reader examplesReader, String readerDirectoryName,  boolean okIfNoExamples) {
		if (examplesReader == null) {
			Utils.error("Have no examples reader!");
			return null;
		}
		List<Sentence> sentences = null;
		try {
			sentences = getParser().readFOPCreader(examplesReader, readerDirectoryName);
		}
		catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Problem encountered reading examples: " + examplesReader);
		}

		if (okIfNoExamples && sentences == null) { return null; }
		if (sentences == null) { Utils.error("There are no examples in: " + examplesReader); }
		List<Example> result = new ArrayList<Example>(Utils.getSizeSafely(sentences));

		if (annotationPredName        == null) { annotationPredName        = stringHandler.getPredicateName("annotatedExample"); }
		if (regressionExamplePredName == null) { regressionExamplePredName = stringHandler.getPredicateName("regressionExample"); }
		for (Sentence s : sentences) {  // Utils.println(" " + s);
			if        (s instanceof Literal) {
				Literal lit = (Literal) s;
				Example ex = processReadExample(lit);
				if (ex != null) { result.add(ex); }
			} else if (s instanceof UniversalSentence) { // Can drop the ForAll since the clausal-form converter converts all variables to universals.
				Sentence body = ((UniversalSentence) s).body;

				// Having an Example class leads to some extra copying of literals, but seems worth having clean classes (e.g., to catch errors),
				if (body instanceof Literal) {
					Literal lit = (Literal) body;
					Example ex = processReadExample(lit);
					if (ex != null) { result.add(ex); }
				} else { Utils.error("Illegal form of an example: '" + s + "' - should be a single (unnegated) fact."); }
			} else     { Utils.error("Illegal form of an example: '" + s + "' - should be a single (unnegated) fact."); }
		}
		Utils.println("% Have read " + Utils.comma(result) + " examples from '" + readerDirectoryName + "' [" + getDirectoryName() + "/" + getPrefix() + "*].");
		return result;
	}

	// Note: for regression examples, here is how things are determined:
	//    predicate(args)   <-- uses the weight on this literal as the output (see FileParser.java) and resets weight to the default value.
	//    regressionExample(pred(args), outputValue)   <-- uses the 2nd argument
	//    annotatedPredicate(regressionExample(pred(args), outputValue), annotation)   <-- uses outputValue
	private Example processReadExample(Literal lit) {
		
		//		Utils.println("processReadExample: " + annotationPredName + "  " + lit);
		
		if (lit.predicateName.name.equals(annotationPredName.name)) { // See if this is annotation of an example.
			if (lit.numberArgs() != 2) { Utils.error("Expecting exactly two arguments here: " + lit); }
			Term arg0 = lit.getArgument(0);
			if (arg0 instanceof Function) {
				Function f = (Function) arg0;
				Literal internalLit = (f).convertToLiteral(stringHandler);
				return createExample(internalLit, "Read from file.", null, lit.getArgument(1));
			}
			Utils.error("Should get a literal posing as a function here, but got: " + arg0);
		} else { return createExample(lit, "Read from file.", null, null); } // Grab the outer weight.
		return null;
	}

	private Example createExample(Literal lit, String provenance, String extraLabel, Term annotationTerm) {
		//Utils.waitHere("createExample: regressionTask = " + regressionTask + "  litPname = " + lit.predicateName + "  regressionExamplePredName = " + regressionExamplePredName);
		if (regressionTask) {
			double outputValue = lit.getWeightOnSentence();
			if (lit.predicateName.name.equals(regressionExamplePredName.name)) {
				if (lit.numberArgs() != 2 && lit.numberArgs() != 3) { Utils.error("Expecting either two or three arguments here: " + lit); }
				Term    arg0        = lit.getArgument(0);
				Literal internalLit = null;
				StringConstant   sc = null;
				if (arg0 instanceof Function) {
					Function f = (Function) arg0;
					internalLit = f.convertToLiteral(stringHandler);
				} else { Utils.error("Should get a literal posing as a function here, but got: " + arg0); }
				Term arg1 = lit.getArgument(1);
				if (arg1 instanceof NumericConstant) {
					NumericConstant nc = (NumericConstant) arg1;
					outputValue = nc.value.doubleValue();
				} else { Utils.error("Should get a number here, but got: " + arg1); }
				if (lit.numberArgs() > 2) {
					Term arg2 = lit.getArgument(2);
					if (arg2 instanceof StringConstant) {
						sc = (StringConstant) arg2;
					} else { Utils.error("Should get a string here, but got: " + arg2); }
				}
				// Utils.println("createExample:   " + internalLit + " with wt = " + outputValue);
				if (!confirmExample(internalLit)) { return null; }
				return new RegressionExample(stringHandler, internalLit, outputValue, provenance, combineLabels(extraLabel, sc == null ? null : sc.getName()), annotationTerm);
			}
			lit.setWeightOnSentence(1.0);
			if (!confirmExample(lit)) { return null; }
			return new RegressionExample(stringHandler, lit, outputValue, provenance, extraLabel, annotationTerm);
		}
		if (!confirmExample(lit)) { return null; }
		return new Example(stringHandler, lit, provenance, extraLabel, annotationTerm);
	}

	private String combineLabels(String str1, String str2) {
		if (str1 == null) { return str2; }
		if (str2 == null) { return str1; }
		return str1 + str2;
	}
	
	private Theory readBackgroundTheory(Reader bkReader, String readerDirectoryName, boolean okIfNoBK) {
		if (bkReader == null && okIfNoBK) { return null; }
		List<Sentence> sentences = null;
		try {
		    Utils.println("% Reading background theory from dir: " + readerDirectoryName);
			sentences = getParser().readFOPCreader(bkReader, readerDirectoryName);
		}
		catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Problem encountered reading background knowledge: " + bkReader);
		}
		if (sentences == null) { return null; } // It is possible there are no inference rules, though some modes should have been read.
		return new Theory(stringHandler, sentences);
	}

	private List<Sentence> readFacts(Reader factsReader, String readerDirectoryName) {
		return readFacts(factsReader, readerDirectoryName, false);
	}
	private List<Sentence> readFacts(Reader factsReader, String readerDirectoryName, boolean okIfNoFacts) {
		if (factsReader == null && okIfNoFacts) { return null; }
		List<Sentence> sentences = null;
		try {
			sentences = getParser().readFOPCreader(factsReader, readerDirectoryName);  // TODO - should find the directory for the reader.

            for (Sentence sentence : sentences) {
                // These should all be facts, but there is really no way to enforce it.
                // However, if they are literals we will consider them as facts.
                // We add the fact predicate/arity to a set so we know that they
                // came in as facts and can be used as so later.
                if (sentence instanceof Literal) {
                    Literal literal = (Literal) sentence;
                    PredicateNameAndArity pnaa = literal.getPredicateNameAndArity();
                    factPredicateNames.add(pnaa);
                }
            }

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
			boolean isCompressed = false;
			if (!Utils.fileExists(factsFileName)) {
				if (Utils.fileExists(factsFileName + ".gz")) {
					factsFileName += ".gz";
					isCompressed = true;
				} else {
					Utils.error("Cannot find this file (nor its GZIPPED version):\n  " + factsFileName);
				}
			}
			File factsFile = Utils.ensureDirExists(factsFileName);
			addToFacts(isCompressed ? new CondorFileReader(factsFileName) : new CondorFileReader(factsFile), factsFile.getParent(), okIfNoFacts); // Need the String in CondorFileReader since that will check if compressed. 
		}
		catch (FileNotFoundException e) {
			Utils.reportStackTrace(e);
			Utils.error("Cannot find this file: " + factsFileName);
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Cannot find this file: " + factsFileName);
		}
	}
	private void addToFacts(Reader factsReader, String readerDirectory, boolean okIfNoFacts) {
		List<Sentence> moreFacts = readFacts(factsReader, readerDirectory, okIfNoFacts);
		if (moreFacts == null) { return; }
		Utils.println("% Read an additional " + Utils.comma(moreFacts) + " facts from " + factsReader + ".");
		addFacts(moreFacts);
	}

	protected void addFact(Sentence newFact) {
		List<Sentence> newFacts = new ArrayList<Sentence>(1); // A bit of a waste to wrap one fact in a list, but arguably better than writing many new methods.
		newFacts.add(newFact);
		addFacts(newFacts);
	}
	protected void addFacts(List<Sentence> newFacts) {
        for (Sentence sentence : newFacts) {
            // These should all be facts, but there is really no way to enforce it.
            // However, if they are literals we will consider them as facts.
            // We add the fact predicate/arity to a set so we know that they
            // came in as facts and can be used as so later.
            if (sentence instanceof Literal) {
                Literal literal = (Literal) sentence;
                PredicateNameAndArity pnaa = literal.getPredicateNameAndArity();
                factPredicateNames.add(pnaa);
            }
        }

		context.assertSentences(newFacts);
	}

    public boolean isFactPredicate(PredicateNameAndArity pnaa) {
        return factPredicateNames.contains(pnaa);
    }

	protected void addRule(Clause rule) {
		context.assertDefiniteClause(rule);
	}
	protected void addClause(Clause clause) {
		context.assertDefiniteClause(clause);
	}

	// See if any facts are in the BK file.  Not a big deal, but might as well clean up and no need to require the user to get this exactly right.
	private void checkBKforFacts() {
        // TAW: I took this out since we don't have a nice clean way to do this with the
        // TAW: newer Clausebase logic.  Additionally, this was only modifying the local
        // TAW: copy of the clauses and not the actual clauses that we proved against.

//		// Need this iterator since we might want to do a clauses.remove() below.
//		for (ListIterator<Clause> clauses = backgroundRules.getClauses().listIterator(); clauses.hasNext(); ) {
//			Clause c = clauses.next();
//			int negSize = Utils.getSizeSafely(c.negLiterals);
//			int posSize = Utils.getSizeSafely(c.posLiterals);
//			if (posSize == 1 && negSize == 0) { // See if a clause containing only ONE literal WITH NO VARIABLES.  If so, can move to the facts.
//				boolean noVars = true;
//				if (c.posLiterals.get(0).numberArgs() > 0) for (Term arg : c.posLiterals.get(0).getArguments()) {
//					if (arg instanceof Variable) { noVars = false; break; }
//				}
//				if (noVars) {
//					addFact(c.posLiterals.get(0));
//					clauses.remove(); // Removes the current item.
//				}
//			}
//			if (posSize == 0 && negSize == 1) { // Ditto for a single negative literal.  NOTE: this shouldn't happen for ILP, but allowing for future use.
//				boolean noVars = true;
//				if (c.negLiterals.get(0).numberArgs() > 0) for (Term arg : c.negLiterals.get(0).getArguments()) {
//					if (arg instanceof Variable) { noVars = false; break; }
//				}
//				if (noVars) {
//					addFact(c.negLiterals.get(0));
//					clauses.remove(); // Removes the current item.
//				}
//			}
//		}
	}
	private void chooseTargetMode() {
		chooseTargetMode(stringHandler.dontComplainIfMoreThanOneTargetModes);
		
	}
	
	// TVK - Made public to allow moving facts to examples (needed for joint inference)[06/10/10]
	public void chooseTargetMode(boolean dontComplainForMoreThanOneModes) {

		if (Utils.getSizeSafely(examplePredicates) < 1) {
			Utils.severeWarning("Need to have a target predicate here.");
			return;
		}
		for (int i = 0; i < examplePredicates.size(); i++) {
			PredicateNameAndArity targetPred = examplePredicates.get(i);
			int numberOfTargetModes = Utils.getSizeSafely(targetPred.getPredicateName().getTypeList());

		    if (numberOfTargetModes <= 0) { Utils.severeWarning("No target modes were provided for '" + targetPred + "'."); continue; }
		    // if (numberOfTargetModes >  1) { Utils.warning("% There are " + numberOfTargetModes + " target modes.  Will use the first one of these."); }
		    List<PredicateSpec> predSpecs = targetPred.getPredicateName().getTypeList();
		    
		    if (Utils.getSizeSafely(predSpecs) != 1) {
		    	if (!(Utils.getSizeSafely(predSpecs) > 1 && dontComplainForMoreThanOneModes)) {
		    		Utils.error("Should only have ONE predicate spec, but have:\n " + predSpecs);
		    	}
		    } // TODO - what if more than 1????
		    
	
		    if (targets == null) {
		    	targets            = new ArrayList<Literal>(      1);
		    	targetArgSpecs     = new ArrayList<List<ArgSpec>>(1);
		    	variablesInTargets = new ArrayList<List<Term>>(   1);
		    }

		    boolean targetExists = addToTargetModes(targetPred);
		}
	}

	private boolean addToTargetModes(PredicateNameAndArity targetPred) {

	    PredicateSpec targetArgTypes = targetPred.getPredicateName().getTypeList().get(0);

	    // The signature records the structure of the literal, including functions with arbitrary embedding.
	    // The typeSpec simply records in a list the types of the 'leaves' in the parser of the literal.
		// This is a little kludgy, but that is because it grew out of a much simpler design.
	    List<Term>     targetArguments     = new ArrayList<Term>(   Utils.getSizeSafely(targetArgTypes.getSignature()));
	    List<ArgSpec>  theseTargetArgSpecs = new ArrayList<ArgSpec>(Utils.getSizeSafely(targetArgTypes.getTypeSpecList()));
	    List<Term>     theseVars           = new ArrayList<Term>(   Utils.getSizeSafely(targetArgTypes.getTypeSpecList()));
	    traverseSignatureAndAddVariables(targetArgTypes.getSignature(), 0, targetArgTypes.getTypeSpecList(), targetArguments, theseVars, theseTargetArgSpecs);

	    Literal newTarget = stringHandler.getLiteral(targetPred.getPredicateName(), targetArguments);
		checkExamplesToSeeIfTargetArgSpecsShouldBeConstrained(newTarget, theseTargetArgSpecs);

        boolean targetExists = getTargetAlreadyExists(newTarget, theseTargetArgSpecs);
        if (!targetExists) {
            targets.add(newTarget);
            targetArgSpecs.add(theseTargetArgSpecs);
            variablesInTargets.add(theseVars);

            if (debugLevel > -1) {
            	Utils.println("\n% NEW target:                 " + newTarget);
            	//Utils.println(  "%  targetPredicateArities:    " + examplePredicateArities.get(i));
            	//Utils.println(  "%  targetPredicateSignatures: " + examplePredicateSignatures.get(i));
            	Utils.println(  "%  targetPred:                " + targetPred);
            	Utils.println(  "%  targetArgTypes:            " + targetArgTypes);
            	Utils.println(  "%  targets:                   " + targets);
            	Utils.println(  "%  targetPredicates:          " + examplePredicates);
            	Utils.println(  "%  targetArgSpecs:            " + targetArgSpecs);
            	Utils.println(  "%  variablesInTargets:        " + variablesInTargets);
            	//	Utils.waitHere();
            }

        }
        else  {
        	Utils.println("\n% Target variant already exists.  Skipping target:                 " + newTarget + ".");
       // 	Utils.println(  "%  examplePredicateSignatures: " + examplePredicateSignatures.get(i));
        	Utils.println(  "%  targetArgTypes:            " + targetArgTypes);
        	Utils.println(  "%  targetArgSpecs:            " + targetArgSpecs);
        }
        return targetExists;
	}
	
    private ArgSpec lookupInArgSpecList(List<ArgSpec> specs, Term term) {
        for (ArgSpec argSpec : specs) {
            if ( argSpec.arg == term ) {
                return argSpec;
            }
        }
        return null;
    }

    private boolean getTargetAlreadyExists(Literal newTarget, List<ArgSpec> theseTargetArgSpecs) {

        boolean found = false;

        for (int j = 0; j < Utils.getSizeSafely(targets); j++) {

            Literal existingTarget = targets.get(j);
            List<ArgSpec> existingArgSpecs = targetArgSpecs.get(j);
            List<Term> existingVariables = variablesInTargets.get(j);

            BindingList bl = new BindingList();

            if (existingTarget.variants(newTarget, bl) != null) {

                for (Term term : existingVariables) {

                    if (term instanceof Variable) {
                        Variable existingVar = (Variable) term;

                        Term matchedTerm = bl.getMapping(existingVar);

                        if (matchedTerm instanceof Variable) {
                            Variable newVariable = (Variable) matchedTerm;

                            ArgSpec existingArgSpec = lookupInArgSpecList(existingArgSpecs, existingVar);
                            ArgSpec newArgSpec = lookupInArgSpecList(theseTargetArgSpecs, newVariable);

                            if (existingArgSpec != null && newArgSpec != null && existingArgSpec.typeSpec.equals(newArgSpec.typeSpec)) {
                                found = true;
                                break;
                            }
                        }
                    }
                }
            }
        }

        return found;
    }


	// There is no need for a target argument to be more general than ALL the examples' corresponding arguments.
	private void checkExamplesToSeeIfTargetArgSpecsShouldBeConstrained(Literal target, List<ArgSpec> theseTargetArgSpecs) {
		if (Utils.getSizeSafely(theseTargetArgSpecs) < 1 || target == null) { return; }
		List<Example> posEx = getPosExamples();
		List<Example> negEx = getNegExamples();

		if (debugLevel > 1) { Utils.println("\n% Checking to see any target argument types are too general, given the training examples."); }
		if (posEx == null && negEx == null) { Utils.waitHere("Have no examples yet!"); }

		int targetPredicateArity = target.numberArgs();
		for (int i = 0; i < target.numberArgs(); i++) {
			ArgSpec  aSpec = theseTargetArgSpecs.get(i);
			TypeSpec tSpec = aSpec.typeSpec;
			Type     type  = tSpec.isaType;
			Type typeToUse = null;
			boolean skipWithThisArgument = false;

			if (debugLevel > 1) { Utils.println("%   Target argument #" + (i + 1) + " is of type '" + type + "'."); }

			int counter = 0;
			if (posEx != null) for (Example ex : posEx) {
				counter++;
				if (skipWithThisArgument || ex.numberArgs() != targetPredicateArity || ex.predicateName != target.predicateName) { continue; }

				Term argI = ex.getArgument(i);
				List<Type> types = stringHandler.isaHandler.getAllKnownTypesForThisTerm(argI);

				if (debugLevel > 2 & counter < 25) { Utils.println("%   Argument #" + +(i + 1) + " in positive example " + counter + " is of types: " + types + "."); }
				if (types == null)     { skipWithThisArgument = true; typeToUse = null; break; }
				if (types.size() != 1) { skipWithThisArgument = true; typeToUse = null; break; } // Not sure what to do with multiple types.
				if (typeToUse == null) { typeToUse = types.get(0); }
				else {
					Type newType = types.get(0);
					if       (stringHandler.isaHandler.isa(typeToUse, newType)) { typeToUse = newType; } // Keep the more general type.
					else if (!stringHandler.isaHandler.isa(newType, typeToUse)) {
						skipWithThisArgument = true; typeToUse = null; break; // Could not compare types.
					}
				}
			}
			counter = 0;
			if (negEx != null) for (Example ex : negEx) {
				counter++;
				if (skipWithThisArgument || ex.numberArgs() != targetPredicateArity || ex.predicateName != target.predicateName) { continue; }
			//	Utils.println("% neg example: " + ex +" : " + i + " : " + target);
				Term argI = ex.getArgument(i);
				List<Type> types = stringHandler.isaHandler.getAllKnownTypesForThisTerm(argI);

				if (debugLevel > 2 & counter < 25) { Utils.println("%   Argument #" + +(i + 1) + " in negative example " + counter + " is of types: " + types + "."); }
				if (types == null)     { skipWithThisArgument = true; typeToUse = null; break; }
				if (types.size() != 1) { skipWithThisArgument = true; typeToUse = null; break; } // Not sure what to do with multiple types.
				if (typeToUse == null) { typeToUse = types.get(0); }
				else {
					Type newType = types.get(0);
					if       (stringHandler.isaHandler.isa(typeToUse, newType)) { typeToUse = newType; } // Keep the more general type.
					else if (!stringHandler.isaHandler.isa(newType, typeToUse)) {
						skipWithThisArgument = true; typeToUse = null; break; // Could not compare types.
					}
				}
			}
			if (debugLevel > 2) { Utils.println("%  Analyzing the examples says that typeToUse = '" + typeToUse + "' (compared to '" + type + "')."); }
			if (!skipWithThisArgument && typeToUse != type && stringHandler.isaHandler.isa(typeToUse, type)) {
				// If reached here, all the arguments in the examples are know to be more constrained than the target predicate,
				// so let's constrain the target.  TODO - should we add 'guard literals' to the learned concept?
				Utils.waitHere("Changing the type of argument #" + i + " from '" + type + "' to the more retrictive '" + typeToUse + "' because all the training examples are of this latter type.");
				tSpec.isaType = typeToUse; // NOTE: this is a destructive change, so hopefully the caller is not impacted by this ...
			}
		}
	}

	private void traverseSignatureAndAddVariables(List<Term> signature, int counter, List<TypeSpec> typeSpecs, List<Term> targetArguments, List<Term> theseVars, List<ArgSpec> theseTargetArgSpecs) {
		if (signature == null) { return; }
		for (Term arg : signature) {
			if (arg instanceof Constant) {
				int positionToFill = Utils.getSizeSafely(theseTargetArgSpecs);
				if (positionToFill != counter) { Utils.error("positionToFill = " + positionToFill + " != counter = " + counter); }
				TypeSpec typeSpec = typeSpecs.get(positionToFill);
				Term newTerm = null;
				if (typeSpec.mustBeThisValue()) {
					newTerm = stringHandler.getStringConstant(typeSpec.isaType.toString());
				} else {
					newTerm = stringHandler.getNewNamedGeneratedVariable();
				}
				if (debugLevel > 1) { Utils.println("% traverseSignatureAndAddVariables: assign " + newTerm + " to " + typeSpec); }
				theseTargetArgSpecs.add(new ArgSpec(newTerm, typeSpec));
				targetArguments.add(newTerm);
				theseVars.add(newTerm);
				counter++;
    		} else if (Function.isaConsCell(arg)) {
    			counter++; // We need to skip lists, since they can be of variable length.
			} else if (arg instanceof Function) {
				Function f = (Function) arg;
				List<Term> newArguments = new ArrayList<Term>(f.numberArgs());
				traverseSignatureAndAddVariables(f.getArguments(), counter, typeSpecs, newArguments, theseVars, theseTargetArgSpecs);
				targetArguments.add(stringHandler.getFunction(f.functionName, newArguments, f.getTypeSpec()));
				counter += f.countLeaves();
			} else { Utils.error("Unexpected argument in a signature: " + arg); }
		}
	}

	// This method helps select constants to fill arguments of type # during ILP search.
	protected void collectConstantBindings(List<Term> args) {
		if (collectedConstantBindings == null) { collectedConstantBindings = new ArrayList<List<Term>>(8); }
		if (Utils.getSizeSafely(collectedConstantBindings) >= 1000) { return; } // In case there are a huge number of constants, limit to 1000.  Ideally would collect a random set, but that doesn't seem worth the effort.
		int len1 = Utils.getSizeSafely(args);
		for (List<Term> entry : collectedConstantBindings) {
			if (len1 != Utils.getSizeSafely(entry)) { continue; } // Should be the same size, but check anyway.
			boolean foundDifference = false;
			for (ListIterator<Term> terms1 = args.listIterator(), terms2 = entry.listIterator(); terms1.hasNext(); ) {
				Term term1 = terms1.next();
				Term term2 = terms2.next();

				if (!term1.equals(term2)) { foundDifference = true; break; }
			}
			if (!foundDifference) { return; } // Have found a matching list, so this is a duplicate and can be ignored.

		}
		if (debugLevel > 3) { Utils.println(">>> found new collectConstantBindings: " + args); }
		collectedConstantBindings.add(args); // Should check for duplicates!  TODO
	}

	public final void setDirectoryName(String dir) {
		getParser().setDirectoryName(dir);
	}
	public final String getDirectoryName() {
		return getParser().getDirectoryName();
	}

	public final void setPrefix(String prefix) {
		getParser().setPrefix(prefix);
	}
	public final String getPrefix() {
		return getParser().getPrefix();
	}

//	public List<Literal> collectAllFactsOfThisName(PredicateName actionPname) {
//		return ruleAndFactsHolder.collectAllFactsOfThisName(actionPname);
//	}


	/**
	 * @param args
	 * @throws SearchInterrupted
	 * @throws IOException 
	 */
	public static void main(String[] args) throws SearchInterrupted, IOException {  // Sample usage (and testing of) of the ILP inner loop
		args = Utils.chopCommentFromArgs(args);
		Utils.createDribbleFile();
		SearchStrategy    strategy = new BestFirstSearch(); // new DepthFirstSearch(); //BreadthFirstSearch();
		ScoreSingleClause scorer   = new ScoreSingleClauseByAccuracy();

		if (args.length < 4) { Utils.error("This 'main' assumes that there are four input arguments: workingDirectory (with '/' at end), posExFile, negExFile, rulesFile, FactsFile.  You provided: " + args); }
		LearnOneClause task = null;
		try {
			task = new LearnOneClause(args[0], null, args[0]+args[1], args[0]+args[2], args[0]+args[3], args[0]+args[4], strategy, scorer, new Gleaner());
		}
		catch (FileNotFoundException e) {
			Utils.reportStackTrace(e);
			Utils.error("Something went wrong initializing LearnOneClause.");
		}

		task.setMaxNodesToConsider(1000);
		task.setMaxNodesToCreate(1000);
		task.maxSearchDepth     =  100;
		task.verbosity          =    0;

		task.selectSeedsRandomly(1, 0, new HashSet<Example>(), new HashSet<Example>());
		task.performSearch();

		Gleaner gleaner = (Gleaner) task.searchMonitor;
		gleaner.dumpCurrentGleaner("gleaner.txt", task);

		Utils.println("\nDone learning.  " + task.reportSearchStats() + "\nBest node found [scored = " + gleaner.bestScore + "]:");   // Print this regardless of debug level since this is in a 'main.'
		Utils.println("\n  " + gleaner.bestNode);
	}


    /**
     * @param posExamples the posExamples to set
     */
    public void setPosExamples(List<Example> posExamples) {
        this.posExamples = posExamples;
        
        if (this.posExamples == null) { this.posExamples = new ArrayList<Example>(0); } // Use an empty list (rather than null) so we know this has been called.

        // We should probably count the weights and stuff here...
        totalPosWeight = Example.getWeightOfExamples(posExamples);
    }

    /**
     * @param negExamples the negExamples to set
     */
    public void setNegExamples(List<Example> negExamples) {
        this.negExamples = negExamples;

        // We should probably count the weights and stuff here...
        totalNegWeight = Example.getWeightOfExamples(negExamples);
    }

    public int getNumberOfPosExamples() {
        return posExamples == null ? 0 : posExamples.size();
    }

    public int getNumberOfNegExamples() {
        return negExamples == null ? 0 : negExamples.size();
    }

	// TODO - should index modes by arity as well ...
	public boolean checkForBodyMode(PredicateName pName, int arity) {
		//Utils.println("checkForBodyMode: " + pName + "/" + arity);
		if (bodyModes == null || !bodyModes.contains(new PredicateNameAndArity(pName, arity))) { return false; }
		return true;
	}

    /** Provides an extremely course measure of the number of proofs completed by second.
     *
     * This measure is just a guideline, since the length of the proofs may different
     * substantially.  However, over the same set of inputs, this number should be
     * fairly stable.
     * @return
     */
    public double getAverageProofsCompletePerSecond() {
        return (double)totalProofsProved / totalProofTimeInNanoseconds * 1e9;
    }

    public long getTotalProofTimeInNanoseconds() {
        return totalProofTimeInNanoseconds;
    }

    public int getTotalProofsProved() {
        return totalProofsProved;
    }

	public final void setThresholder(ThresholdManager thresholder) {
		this.thresholdHandler = thresholder;
	}

	public ThresholdManager getThresholder() {
		return thresholdHandler;
	}

	public final void setInlineManager(InlineManager inliner) {
		this.inlineHandler = inliner;
	}

	public InlineManager getInlineManager() {
		return inlineHandler;
	}

    /**
     * @return the optimizeClauses
     */
    public boolean isOptimizeClauses() {
        return optimizeClauses;
    }

    /**
     * @param optimizeClauses the optimizeClauses to set
     */
    public void setOptimizeClauses(boolean optimizeClauses) {
        this.optimizeClauses = optimizeClauses;
    }

	public int[] evaluateOnTestset(String theoryFile, int reportFirstNerrors) throws SearchInterrupted {
		List<Sentence> sentences = getParser().readFOPCfile(theoryFile);

		context.assertSentences(sentences);
		initialize(); // Need to wait until the (presumably learned, but could be handcrafted) theory is loaded.
		int numberOfPosExamples = Utils.getSizeSafely(posExamples);
		int numberOfNegExamples = Utils.getSizeSafely(negExamples);
		int posExamplesCorrect  = 0;
		int negExamplesCorrect  = 0;
		int countOfPosErrors = 0;
		int countOfNegErrors = 0;
		if (numberOfPosExamples > 0) for (Example ex : posExamples) {
			if ( getProver().proveSimpleQuery(ex)) { posExamplesCorrect++; }
			else if (reportFirstNerrors > countOfPosErrors)                    { countOfPosErrors++; Utils.println("%  evaluateOnTestset FALSE NEGATIVE #" + countOfPosErrors + ": " + ex); }
		}

		if (numberOfNegExamples > 0) for (Example ex : negExamples) {
			if (!prover.proveSimpleQuery(ex)) { negExamplesCorrect++; }
			else if (reportFirstNerrors > countOfPosErrors + countOfNegErrors) { countOfNegErrors++; Utils.println("%  evaluateOnTestset FALSE POSITIVE #" + countOfNegErrors + " " + ex); }
		}

		Utils.println("\n% Testset Correctness for");
		Utils.println(  "%    " + theoryFile + "\n");
		if (numberOfPosExamples > 0) {
			Utils.println(  "%   " + Utils.comma(posExamplesCorrect) + " of " + Utils.comma(numberOfPosExamples) + " positive examples correctly classified, "
					               + Utils.truncate((100.0 * posExamplesCorrect) / numberOfPosExamples , 2) + "%.");
		} else {
			Utils.println(  "%   There were no positive examples to test.");
		}
		if (numberOfNegExamples > 0) {
			Utils.println(  "%   " + Utils.comma(negExamplesCorrect) + " of " + Utils.comma(numberOfNegExamples) + " negative examples correctly classified, "
					               + Utils.truncate((100.0 * negExamplesCorrect) / numberOfNegExamples , 2) + "%.");
		} else {
			Utils.println(  "%   There were no negative examples to test.");
		}

		context.getClausebase().retract(sentences);
		// GK: added return to collect statistics rather than just print out
		return new int[]{posExamplesCorrect, numberOfPosExamples, negExamplesCorrect, numberOfNegExamples};
	}

    public List<List<Literal>> getOptimizedClauseBodies(Literal target, List<Literal> clauseBody) {
        if ( isOptimizeClauses() ) {
            return stringHandler.getClauseOptimizer().bodyToBodies(target, clauseBody);
        }
        else {
            return Collections.singletonList(clauseBody);
        }
    }


    public HornClauseContext getContext() {
        return context;
    }

//	public HornClauseProverChildrenGenerator getRuleAndFactsHolder() {
//		return ruleAndFactsHolder;
//	}
//
//	public void setRuleAndFactsHolder(HornClauseProverChildrenGenerator ruleAndFactsHolder) {
//		this.ruleAndFactsHolder = ruleAndFactsHolder;
//	}

	public Precompute getPrecomputer() {
		return precomputer;
	}

	public double getTotalPosWeight() {
		return totalPosWeight;
	}

	public void setTotalPosWeight(double totalPosWeight) {
		this.totalPosWeight = totalPosWeight;
	}

	public double getTotalNegWeight() {
		return totalNegWeight;
	}

	public void setTotalNegWeight(double totalNegWeight) {
		this.totalNegWeight = totalNegWeight;
	}

	public boolean isaTreeStructuredTask() {
		return isaTreeStructuredTask;
	}

	public void  setIsaTreeStructuredTask(boolean value) {
		isaTreeStructuredTask = value;
	}
    
    public void setIgnoreNegatedLiterals(boolean value) {
    	ignoreNegatedLiterals = value;
    }
    
    public boolean getIgnoreNegatedLiterals() {
    	return ignoreNegatedLiterals;
    }

    public boolean isRelevanceEnabled() {
        return relevanceEnabled == null ? false : relevanceEnabled;
    }

    public void setRelevanceEnabled(boolean relevanceEnabled) {
        this.relevanceEnabled = relevanceEnabled;
    }

    /** Adds a relevant clause to the relevant clause list.
     *
     * Initially the RelevantClauseInformation will have default
     * attributes.  The user of the relevant clause must
     *
     * @param example
     * @param relevantClause
     * @param strength
     */
    public void addRelevantClause(Example example, Clause relevantClause, RelevanceStrength strength, boolean positive) {
        adviceProcessor.addGroundedAdvice(example, positive, relevantClause, strength);
     }

    public List<RelevantClauseInformation> getRelevantClausesForExample(Example example) {
        return adviceProcessor.getRelevantClausesForExample(example);
    }

    public boolean hasRelevantClauses(Example example) {
        return adviceProcessor.hasRelevantClauses(example);
    }

    public boolean hasRelevantInformation(Example example) {
        return adviceProcessor.hasRelevantInformation(example);
    }

    public boolean hasRelevantFeatures(Example example) {
        return adviceProcessor.hasRelevantFeatures(example);
    }

    public List<RelevantFeatureInformation> getRelevantFeatureForExample(Example example) {
        return adviceProcessor.getRelevantFeatureForExample(example);
    }

    public AdviceProcessor getAdviceProcessor() {
        return adviceProcessor;
    }

    /** Reads a relevance file and enables relevance if relevanceEnabled is unset.
     *
     * relevanceEnabled is tri-valued, either true, false, or unset.  If relevanceEnabled is
     * true or false, this method does not change the relevanceEnabled value.  However,
     * if it is unset, it will be set to true.
     * <P>
     * Note: This method must be called prior to initialization of the
     * LearnOneClause.
     *
     * @param relevanceFile
     * @throws FileNotFoundException
     * @throws IllegalStateException An IllegalStateException will be thrown if LearnOneClause is already initialized.
     */
    public void setRelevanceFile(String relevanceFileName) throws FileNotFoundException, IllegalStateException {
        if ( relevanceFileName != null ) {

        	File relevanceFile = Utils.ensureDirExists(relevanceFileName);
            BufferedReader relevanceReader = new BufferedReader( new CondorFileReader(relevanceFile));

            setRelevanceFile(relevanceReader, relevanceFile.getParent());
        }
    }

    /** Reads a relevance file and enables relevance if relevanceEnabled is unset.
     *
     * relevanceEnabled is tri-valued, either true, false, or unset.  If relevanceEnabled is
     * true or false, this method does not change the relevanceEnabled value.  However,
     * if it is unset, it will be set to true.
     * <P>
     * Note: This method must be called prior to initialization of the
     * LearnOneClause.
     *
     * @param relevanceFile
     * @throws FileNotFoundException
     * @throws IllegalStateException An IllegalStateException will be thrown if LearnOneClause is already initialized.
     */
    public void setRelevanceFile(File relevanceFile) throws FileNotFoundException, IllegalStateException {
        if ( relevanceFile != null ) {

            BufferedReader relevanceReader = new BufferedReader( new CondorFileReader(relevanceFile));

			String relevanceDirectoryName = relevanceFile.getParent();
            setRelevanceFile(relevanceReader, relevanceDirectoryName);
        }
    }

    /** Reads a relevance file and enables relevance if relevanceEnabled is unset.
     *
     * relevanceEnabled is tri-valued, either true, false, or unset.  If relevanceEnabled is
     * true or false, this method does not change the relevanceEnabled value.  However,
     * if it is unset, it will be set to true.
     * <P>
     * Note: This method must be called prior to initialization of the
     * LearnOneClause instance.
     *
     * @param relevanceReader
     * @throws IllegalStateException An IllegalStateException will be thrown if LearnOneClause is already initialized.
     */
    public void setRelevanceFile(Reader relevanceReader, String readerDirectoryName) throws IllegalStateException {
        if (initialized) {
            throw new IllegalStateException("Relevance files can not be added after LearnOneClause is initialized.");
        }
        else if (relevanceReader != null) {
            context.assertSentences(readBackgroundTheory(relevanceReader, readerDirectoryName, true));
            Utils.println("% Have read the relevance files.\n");
            if (relevanceEnabled == null) {
                relevanceEnabled = true;
            }
        }
    }

    public void addModeConstraint(ModeConstraint modeConstraint) {
        if ( modeConstraints == null ) {
            modeConstraints = new ArrayList<ModeConstraint>();
        }

        modeConstraints.add(modeConstraint);
    }

    public boolean removeModeConstraint(ModeConstraint modeConstraint) {
        if ( modeConstraints != null ) {
            return modeConstraints.remove(modeConstraint);
        }
		return false;
    }

    public void clearModeConstraints() {
        if ( modeConstraints != null ) {
            modeConstraints.clear();
        }
    }

    public List<ModeConstraint> getModeConstraints() {
        if (modeConstraints == null) {
			return Collections.emptyList();
        }
		return modeConstraints;
    }



    protected List<Literal>        backup_targets                   = null; // These are the actual targets determined from the examplePredicates.
	protected List<List<ArgSpec>>  backup_targetArgSpecs            = null; // The info about the target argument being used and the variables matched with their types.
	protected List<List<Term>>     backup_variablesInTargets        = null; // These are really 'arguments' since it is possible a mode specifies a constant be used.

	public void setTargetAs(String target) {
		setTargetAs(target, false, null);
	}

	public void setTargetAs(String target, boolean dontAddOtherTargetModes, String addPrefix) {
		// Check if we have already backed up the literals.
		if (backup_targets == null) {
			backup_targets            = targets;
			backup_targetArgSpecs     = targetArgSpecs;
			backup_variablesInTargets = variablesInTargets;
		}
		//Utils.println("%Backup Targets:"  + backup_targets + "\n%New target:" + target);
		int selectedTarget = -1;
		for (int i = 0; i < Utils.getSizeSafely(backup_targets); i++) {
			PredicateNameAndArity predName = backup_targets.get(i).getPredicateNameAndArity();
			if (predName.getPredicateName().name.equals(target)) {
				bodyModes.remove(predName);
				if (addPrefix != null) {
					if (!targetModes.contains(predName)) { targetModes.add(predName); }
				}
				selectedTarget = i;
			} else {
				if (dontAddOtherTargetModes) {
					if (bodyModes.contains(predName)) { bodyModes.remove(predName); }
				} else {
					if (!bodyModes.contains(predName)) { bodyModes.add(backup_targets.get(i).getPredicateNameAndArity()); }
				}
			}
		}
		targets            = new ArrayList<Literal>();
		targetArgSpecs     = new ArrayList<List<ArgSpec>>();
		variablesInTargets = new ArrayList<List<Term>>();
		
		if (addPrefix != null) {
			//TODO
			String multiPred = addPrefix + target;
			for (PredicateNameAndArity pnaa : bodyModes) {
				if (pnaa.getPredicateName().name.equals(multiPred)) {
					addToTargetModes(pnaa);
					break;
				}
			}
		} else {
			if (selectedTarget == -1) {
				Utils.error("Didn't find target '" + target + "' in: " + backup_targets);
			}

			targets.add(           backup_targets.get(           selectedTarget));
			targetArgSpecs.add(    backup_targetArgSpecs.get(    selectedTarget));
			variablesInTargets.add(backup_variablesInTargets.get(selectedTarget));
		}
		// Also edit modes


	}

	// ------------------------------------
	// TVK - Made getters to allow moving facts to examples(needed for joint inference)[06/10/10]
	
	/**
	 * @return the targetModes
	 */
	public List<PredicateNameAndArity> getTargetModes() {
		return targetModes;
	}
	/**
	 * set the targetModes
	 */
	public void setTargetModes(List<PredicateNameAndArity> targetModes) {
		this.targetModes = targetModes;
	}

	public Set<PredicateNameAndArity> getBodyModes() {
		return bodyModes;
	}

	public void setBodyModes(Set<PredicateNameAndArity> bodyModes) {
		this.bodyModes = bodyModes;
		countOfSearchesPerformedWithCurrentModes = 0; 
	}

	/**
	 * @return the targetArgSpecs
	 */
	public List<List<ArgSpec>> getTargetArgSpecs() {
		return targetArgSpecs;
	}

	/**
	 * @return the examplePredicateSignatures
	 */
	public List<List<Term>> getExamplePredicateSignatures() {
		return examplePredicateSignatures;
	}

	// ---------------------
	public void resetAll(boolean includingExamples) {
		resetAllForReal();
		if (includingExamples) {
			if (examplePredicates          != null) { examplePredicates.clear(); }
			//if (examplePredicateArities    != null) { examplePredicateArities.clear(); }
			if (examplePredicateSignatures != null) { examplePredicateSignatures.clear(); }
			if (targets                    != null) { targets.clear(); }
			if (targetArgSpecs             != null) { targetArgSpecs.clear(); }
			if (variablesInTargets         != null) { variablesInTargets.clear(); }
			if (backup_targets             != null) { backup_targets.clear(); }
			if (backup_targetArgSpecs      != null) { backup_targetArgSpecs.clear(); }
			if (backup_variablesInTargets  != null) { backup_variablesInTargets.clear(); }
			if (requiredBodyPredicatesForAcceptableClauses != null) { requiredBodyPredicatesForAcceptableClauses.clear(); }
			if (targetModes != null) { targetModes.clear(); }
			if (bodyModes   != null) { bodyModes.clear();   }
			if (posExamples != null) { posExamples.clear(); }
			if (negExamples != null) { negExamples.clear(); }
			if (worldStatesContainingNoPositiveExamples != null) { worldStatesContainingNoPositiveExamples.clear(); }
		}
		if (seedPosExamples != null) { seedPosExamples.clear(); }
		if (seedNegExamples != null) { seedNegExamples.clear(); }
		if (collectedConstantBindings != null) { collectedConstantBindings.clear(); }
	}

    /**
     * @return the parser
     */
    public FileParser getParser() {
        return parser;
    }

	public List<Literal> getTargets() {
		return targets;
}

	public void setTargets(List<Literal> targets) {
		this.targets = targets;
	}

    public RelevanceStrength getCurrentRelevanceStrength() {
        return currentRelevanceStrength;
    }

    public void setCurrentRelevanceStrength(RelevanceStrength currentRelevanceStrength) {
        if ( currentRelevanceStrength == null ) {
            currentRelevanceStrength = RelevanceStrength.getDefaultRelevanceStrength();
        }
        this.currentRelevanceStrength = currentRelevanceStrength;
    }

    private void handleRelevance() {

        // Extract relevance from the clause base...
        //
        // Relevant clauses are added to the factbase in the form of:
        //
        // relevantClause(example, clause, strength),
        //       where example is the example literal wrapped in a LiteralAsTerm,
        //             clause is a Clause wrapped in a SentenceAsTerm,
        //             strength is a StringConstant containing the name of the relevance strength.
//        Variable exampleVar = stringHandler.getNewUnamedVariable();
//        Variable clauseVar = stringHandler.getNewUnamedVariable();
//        Variable relevanceStrengthVar = stringHandler.getNewUnamedVariable();
//
//        Proof proof = new DefaultProof(context, stringHandler.getLiteral("relevant_clause", exampleVar, clauseVar, relevanceStrengthVar));
//        BindingList bl = null;
//
//            Literal example = ((LiteralAsTerm)bl.getMapping(exampleVar)).itemBeingWrapped;
//            Clause clause = (Clause) ((SentenceAsTerm)bl.getMapping(clauseVar)).sentence;
//            RelevanceStrength strength = RelevanceStrength.valueOf( ((StringConstant)bl.getMapping(relevanceStrengthVar)).name );
//
//            addRelevantClause(example, clause, strength, isPositiveExample(example) );
//        }
//
//        if ( relevantClauseList != null ) {
//            AdviceProcessor ap = new AdviceProcessor(stringHandler);
//            ap.addGroundedAdvice( relevantClauseList );
//
//            List<Clause> clauses = ap.processAdvice(context);
//        }

    }

    /**
     * @return the activeAdvice
     */
    public ActiveAdvice getActiveAdvice() {
        return activeAdvice;
    }

    /**
     * @param activeAdvice the activeAdvice to set
     */
    public void setActiveAdvice(ActiveAdvice activeAdvice) {
        this.activeAdvice = activeAdvice;
    }

    private void closeWithoutException(Reader posExamplesReader) {
        if (posExamplesReader != null) {
            try {
                posExamplesReader.close();
            } catch (IOException ex) {
            }
        }
    }

    // See if these args are in these positions in SOME training example.
    // TODO - allow argumentW and argumentS to be null, meaning we dont care if they match?  Arguments should not be 'null' - but that could happen, so maybe a better indicator of 'dont care' is needed?
	public boolean isWorldStateArgPairInAnExample(Term argumentW, Term argumentS) {
		return (isWorldStateArgPairInAnPosExample(argumentW, argumentS) ||
				isWorldStateArgPairInAnNegExample(argumentW, argumentS));
	}
	public boolean isWorldStateArgPairInAnPosExample(Term argumentW, Term argumentS) {
		if (posExamples != null) for (Example ex : posExamples) {
			int numbArgs = ex.numberArgs();
			int wArg = stringHandler.getArgumentPosition(stringHandler.locationOfWorldArg, numbArgs);
			int sArg = stringHandler.getArgumentPosition(stringHandler.locationOfStateArg, numbArgs);	
			if (ex.getArgument(wArg).equals(argumentW) && ex.getArgument(sArg).equals(argumentS)) { return true; }
		}
		return false;
	}
	public boolean isWorldStateArgPairInAnNegExample(Term argumentW, Term argumentS) {
		if (negExamples != null) for (Example ex : negExamples) {
			int numbArgs = ex.numberArgs();
			int wArg = stringHandler.getArgumentPosition(stringHandler.locationOfWorldArg, numbArgs);
			int sArg = stringHandler.getArgumentPosition(stringHandler.locationOfStateArg, numbArgs);	
			if (ex.getArgument(wArg) == argumentW && ex.getArgument(sArg) == argumentS) { return true; }
		}
		return false;
	}

    public void addILPSearchListener(ILPSearchListener listener) {
        searchListenerList.add(ILPSearchListener.class, listener);
    }

    public void removeILPSearchListener(ILPSearchListener listener) {
        searchListenerList.remove(ILPSearchListener.class, listener);
    }

    public ILPSearchAction fireOnionLayerStarting(TuneParametersForILP onion, ILPparameterSettings onionLayer) {
        ILPSearchAction action = ILPSearchAction.PERFORM_LOOP;

        Object[] listeners = searchListenerList.getListenerList();
        for (int i = 0; i < listeners.length; i+=2) {
            Class c = (Class)listeners[i];
            if ( ILPSearchListener.class.isAssignableFrom(c)) {
                ILPSearchListener listener = (ILPSearchListener)listeners[i+1];

                ILPSearchAction aAction = listener.onionLayerStarting(onion, onionLayer);
                action = ILPSearchAction.getHigherPrecedenceAction(action, aAction);
            }
        }
        return action;
    }

    public void fireOnionLayerFinished(TuneParametersForILP onion, ILPparameterSettings onionLayer) {
        Object[] listeners = searchListenerList.getListenerList();
        for (int i = 0; i < listeners.length; i+=2) {
            Class c = (Class)listeners[i];
            if ( ILPSearchListener.class.isAssignableFrom(c)) {
                ILPSearchListener listener = (ILPSearchListener)listeners[i+1];

                listener.onionLayerFinished(onion, onionLayer);
            }
        }
    }

    public ILPSearchAction fireCrossValidationFoldStarting(ILPCrossValidationLoop cvLoop, int fold) {
        ILPSearchAction action = ILPSearchAction.PERFORM_LOOP;

        Object[] listeners = searchListenerList.getListenerList();
        for (int i = 0; i < listeners.length; i+=2) {
            Class c = (Class)listeners[i];
            if ( ILPSearchListener.class.isAssignableFrom(c)) {
                ILPSearchListener listener = (ILPSearchListener)listeners[i+1];

                ILPSearchAction aAction = listener.crossValidationFoldStarting(cvLoop, fold);
                action = ILPSearchAction.getHigherPrecedenceAction(action, aAction);
            }
        }
        return action;
    }

    public void fireCrossValidationFoldFinished(ILPCrossValidationLoop cvLoop, int fold) {
        Object[] listeners = searchListenerList.getListenerList();
        for (int i = 0; i < listeners.length; i+=2) {
            Class c = (Class)listeners[i];
            if ( ILPSearchListener.class.isAssignableFrom(c)) {
                ILPSearchListener listener = (ILPSearchListener)listeners[i+1];

                listener.crossValidationFoldFinished(cvLoop, fold);
            }
        }
    }

    public ILPSearchAction fireOuterLoopStarting(ILPouterLoop outerLoop) {
        ILPSearchAction action = ILPSearchAction.PERFORM_LOOP;

        Object[] listeners = searchListenerList.getListenerList();
        for (int i = 0; i < listeners.length; i+=2) {
            Class c = (Class)listeners[i];
            if ( ILPSearchListener.class.isAssignableFrom(c)) {
                ILPSearchListener listener = (ILPSearchListener)listeners[i+1];

                ILPSearchAction aAction = listener.outerLoopStarting(outerLoop);
                action = ILPSearchAction.getHigherPrecedenceAction(action, aAction);
            }
        }
        return action;
    }

    public void fireOuterLoopFinished(ILPouterLoop outerLoop) {
        Object[] listeners = searchListenerList.getListenerList();
        for (int i = 0; i < listeners.length; i+=2) {
            Class c = (Class)listeners[i];
            if ( ILPSearchListener.class.isAssignableFrom(c)) {
                ILPSearchListener listener = (ILPSearchListener)listeners[i+1];

                listener.outerLoopFinished(outerLoop);
            }
        }
    }

    public ILPSearchAction fireInnerLoopStarting(LearnOneClause innerLoop) {
        ILPSearchAction action = ILPSearchAction.PERFORM_LOOP;

        Object[] listeners = searchListenerList.getListenerList();
        for (int i = 0; i < listeners.length; i+=2) {
            Class c = (Class)listeners[i];
            if ( ILPSearchListener.class.isAssignableFrom(c)) {
                ILPSearchListener listener = (ILPSearchListener)listeners[i+1];

                ILPSearchAction aAction = listener.innerLoopStarting(innerLoop);
                action = ILPSearchAction.getHigherPrecedenceAction(action, aAction);
            }
        }
        return action;
    }

    public void fireInnerLoopFinished(LearnOneClause innerLoop) {
        Object[] listeners = searchListenerList.getListenerList();
        for (int i = 0; i < listeners.length; i+=2) {
            Class c = (Class)listeners[i];
            if ( ILPSearchListener.class.isAssignableFrom(c)) {
                ILPSearchListener listener = (ILPSearchListener)listeners[i+1];

                listener.innerLoopFinished(innerLoop);
            }
        }
    }

    public boolean isThresholdingEnabled() {
        return thresholdingEnabled;
    }

    public void setThresholdingEnabled(boolean thresholdingEnabled) {
        this.thresholdingEnabled = thresholdingEnabled;
    }

    public boolean isSyntheticExamplesEnabled() {
        return syntheticExamplesEnabled;
    }

    public void setSyntheticExamplesEnabled(boolean syntheticExamplesEnabled) {
        this.syntheticExamplesEnabled = syntheticExamplesEnabled;
    }


	public void setMlnRegressionTask(boolean val) {
		mlnRegressionTask = val;
	}

	public void setLearnMultiVal(boolean val) {
		learnMultiValPredicates = val;
	}

	
	public RegressionInfoHolder getNewRegressionHolderForTask() {
		if (mlnRegressionTask) {
			// TODO(MLNTEST)
			return new RegressionInfoHolderForMLN();
			//return new RegressionInfoHolderForRDN();
		} else {
			if (learnMultiValPredicates) {
				return new RegressionVectorInfoHolderForRDN();
			} else {
				return new RegressionInfoHolderForRDN();
			}
		}
	}
	
	public void setMaxSkew(int skewMaxNegToPos) {
		this.skewMaxNegToPos = skewMaxNegToPos;		
	}
	
	public void updateFacts(HiddenLiteralState lastState,
			HiddenLiteralState newState, String target) {
		List<Literal> addExamples = new ArrayList<Literal>();
		List<Literal>  rmExamples = new ArrayList<Literal>();
		HiddenLiteralState.stateDifference(lastState, newState, addExamples, rmExamples, target);
		if(addExamples.size() > 0 || rmExamples.size() > 0) {
			// Utils.waitHere("Adding " + addExamples.size() + " examples and removing " + rmExamples.size());
		}
		for (Literal addEx : addExamples) {
			getContext().getClausebase().assertFact(addEx);
		}
		for (Literal rmEx : rmExamples) {
			getContext().getClausebase().retractAllClausesWithUnifyingBody(rmEx);
		}
	}

}
