/**
 * 
 */
package edu.wisc.cs.will.MLN_Task;

import java.io.FileNotFoundException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.LiteralComparator;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Type;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.Utils.CrossProductViaContinuation;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CondorFileOutputStream;

/**
 * "Semantic" differences in Lazy Inference (compared to normal inference):
 * 
 * 		lazy does not RANDOMIZE all the literals at the start (since there could be too many)
 * 
 * 		lazyMCSAT does not RANDOMIZE all non-selected literals (since there could be too many)
 * 			- but it does randomize all materialized gLits, which include the QUERY literals (since
 * 				this is needed in order to properly estimate their marginal probabilities)
 * 
 * Explicitly ground all 'small' clauses (if sum too large?) - call this set A
 * Collect all clauses that need to be treated lazily - call this set B
 * 
 * 
 * HANDLE LAZY BLOCKS ...
 * 
 * 
 *
 * UW Lazy Notes (finally got around to writing them)
 * -------------
 * 
 *  currently do not make QUERY literals lazy (we assume there arent too many of these)
 *  
 *  use 'marked' instead of 'active' since 'active' has another meaning in SAT
 *  
 *  Smart Randomization (using 1-neighbors)
 *  	initialize all those variables in the same clauses as marked variables
 *  
 *  Collecting a RANDOM GROUND LITERAL without enumerating them all
 *  	pick a literal proportional to the # of groundings it has
 *  	uniformly choose constants for the arguments in this literal
 *  
 *  for MCSAT, explicitly collect all CLAUSE GROUNDINGS NOT SATISFIED
 *  
 *  
 *  if a lazy clause has not been selected for K somethings, discard it
 *  
 *   have to note at parent this clause has been de-materialized!  <------------------
 *   addToGroundClauseIndex <------ dont use for LAZY's
 *   
		if (i < numberOfLazyGroundLiterals) {
			return allLazyGroundLiterals.get(i); 
 * 
 *
 *  
 * SIMPLIFY INFERENCE IF THE QUERY IS SIMPLER THAN THE REDUCED FROG NETWORK!
 * 
 * BUG: facts in BK file dont get properly handled for MLN stuff!
 * 
 * if doing WGT LEARNING need to keep individual
 * 
 * 
 * set a flag in ILP saying MLN being used, or (better) factor out common stuff
 * 
 * AGGREGATE COMMON CLAUSES
 * 	- use 'canonical form' here
 * 	- parents will be wrong (use special marker for "AggParent")
 *  - first merge SINGLETONS and see how much saved, dont forget sign * 
 * 
 *  
 * when getting a grounding GET ALL COPIES!
 * 
 * use queryPred when read from files ...
 * 
 * if MCSAT sets are small fractions of all, then use PUSH after all?
 * 
 * HOW BEST TO CHOOSE FOR DUP GROUNDINGS!
 * 
 * 
 * when in SampleSAT, can we avoid creating ALL explicitly?
 * (and if we DONT, then why not use the non-lazy SampleSAT?)
 * 
 * We are finding the prob a lit is true averaged over all worlds that (quasi) satisfy the given BK
 * 
 * LazySampleSAT same as regular!
 * 
 * isInCurrentActiveClauseList
 * 
 * should use isSatisfiedCached() in non-lazy, make sure flips update clauses, dont explicitly connect, let the ground clause stuff do that
 * 
 * do more printouts more non-lazy
 * 
 * merge the lazy/non-lazy inference classes
 * 
 * is there some way to expand ALL ground clauses from 'small' reduced clauses?
 * 		could expand and never gc
 * 		but better would be to have a LIST OF PERM gndClauses and another of Lazy!
 * 		(always do everything over both!)
 * 		add smallest to FIXED until reaching some threshold
 * 
 * 
 * if too many queries, then rep their counts as a SPARSE vector!
 * 
 * 
 * GroundClauses and GroundLiterals point to each other; when erasing, should clear these or no GC will happen!
 * 
 * What gets cleaned up between samples?
 * 
 * BE SURE TO CHECK FOR MORE GROUND CLAUSES WHEN A LITERAL IS "TENURED"
 * Record which clause groundings have been tenured.
 * Record when a clause has exhausted all of its groundings
 * 
 * periodically clear the cache of ground literals of then rebuild all those currently active
 * 
 * when can we GARBAGE COLLECT
 * 	- literals that have their default value
 *  - clauses that (a) are true and (b) have no saved literals
 *  NOTE: if we remove a literal, we need to remove it from the list of created ground literals
 * 
 * 
 * NEED FASTER seeIfBestCost - have two arrays for all the gLits?
 * 
 * WHEN POPPING THE STACK, DO WE WANT TO KEEP THE STATE OF *ALL* THE CLAUSES AND LITERALS?
 *   - seems we need to bring in the other clauses that contain literals turned ON!
 *   
 *   NEED TO STORE STATE FOR SAMPLESAT
 * 
 * DECIDE ON THE SA TEMP BASED ON SCORE
 * 
 * TO WRITE
 *    updateLazyDataStructures - needed?
 *    
 *    do more efficient way of flipping other literals in active clauses!
 * 
 * NEED TO FIX BLOCKS
 * 
 * NEED TO HAVE WGT-LEARNING USE LAZY INFERENCE!
 * 
 * 	fix non-lazy push/pop?
 * 
 * Notes: 'arity' in comments in this file really means 'number of unique variables [in a literal].'
 * 			Be sure to NOT copy literals nor clauses here, since used as key's into hash tables.
 *  
 * SEARCH FOR: JWSJWSJWS
 * 
 * See the following for an alternate approach:
 *   H. Poon, P. Domingos, and M. Sumner,
 *   A General Method for Reducing the Complexity of Relational Inference and its Application to MCMC
 *   AAAI-08 http://www.cs.washington.edu/homes/pedrod/papers/aaai08c.pdf
 *   
 *   TODO - add in http://en.wikipedia.org/wiki/Unit_propagation (into MS-SAT?)
 *   
 *   		possible to do exact inference on some clauses?  just return all their items if few!
 *      
 *      	once grounded out, need to account for the 'lost' groundings (TRUEs and FALSEs)
 *      		- eg, wgt learning needs this to be correct (are there only TRUEs?  if not, then probably ok)
 *      
 *   		NEED TO DEAL WITH BLOCKS - test better?
 *   		NEED TO HANDLE FUNCTIONS IN LITERALS (here or in MLN_Task)
 *   		when to store FALSEs instead of TRUEs?  never?
 *   TODO TODO
 *   
 *   
 *   need to create ALL query literals before doing inference ...
 *   
 *   if too big, then do not do all final groundings.  Instead auto use 'lazy'
 *   
 *   	should not do full cross product unless small!
 *   	- instead, count size, then walk through the KNOWN values (counting 'unknowns' according to CWA)   
 *   	   
 *     could cache    predicateName/constants for 1-arity predicates, or maybe for all predicates
 *     					but this is order dependent after the first one
 *   
 *   	Allow the network to grow to included additional clauses
 *   		- and/or figure out how N clauses interact ...
 *   	SHOULD CLEVERLY HANDLE  p(x,y) and ~p(y,z) ??
 *  


 * 
 * @author shavlik
 *
 */
public class GroundThisMarkovNetwork {
	public static final int      debugLevel   = 1;//Integer.MIN_VALUE;
	public static final boolean  doMajorDebug = false; // JWSJWSJWS Set to true if one wants to spend time checking for consistent data and recording how/when literals and clauses are updated.
	
	public static final boolean  createScatterPlots                 = true;
	public static final double   minNumberOfGroundingsToReportStats = -1; // 1e6;
	
	public  MLN_Task             task;
	protected Object             markerInUse = null;  // Can mark ground clauses with their 'owners,' for cases where only a subset of the groundings currently are of interest.
	
	public  boolean              doingLazyInference                      = false;
	private boolean              sortClausesByNumberOfPossibleGroundings = false; // If true, sort clauses after counting their size (# possible groundings).  Note: this will change the clause # for clauses, thereby reducing readability. 
	private boolean              postponeSavingGroundLiterals  = true;  // If true, will not archive ground literals until they need to be saved (a space-time tradeoff, when set to 'true' saves space at a cost of more new'ing). 
	private boolean              chooseReductionOrderRandomly  = false; // Will make choices randomly rather than by best score.
	private double               minimumReduction                = 0.50; // If cannot reduce by at least this fraction, do not bother (at least until a second round, when nothing better has been found).
	private double               minReductionToAcceptAtThisArity = 0.5; // If a reduction at a given arity reduces at least this much, don't look at higher arities.
	private double               maxSizeReduceRegardless = 100000;      // If this small, reduce regardless (but wait until a second round).  This to be a function of the number of such 'hard' literals and [TODO] the size of the space after the easy ones have been done.
	private int                  currentOverallIteration =  0;  // Used to count number of random restarts.
	private int                  currentCycle            =  0;
	public  int                  maxNumberOfRandomTries  = 10;  // Max number of times will try to find a solution that doesn't exceed the maxJoin* values below.
	public  double               multiplierOnSizeOfExplicitCrossProduct   = 0.20; // If the explicit size is no more fraction of the size of the 'knowns,' use the explicit cross product since more efficient.
	public  double               maxNumberOfKnownsToConsider              = 1e5;  // Processing known's can be slow, so skip if too many.
	public  double               maxCrossProductSizeToUseKnownsRegardless = 1e7;  // HOWEVER IF THE CROSS-PRODUCT SIZE EXCEEDS THIS SIZE, USE KNOWNS IF POSSIBLE.  (TODO - tweak these)
	public  double               maxNonLazyGroundingsPerClause            = 1e8;  // If a clause leads to more than this many groundings, thrown an error (which might be caught by code that does 'lazy' inference).
	public  double               maxLazyClauseGroundingsTotal             = 1e8;  // If more than this many, throw an error.  
	private double               maxJoinSizeComputation              = 1e8; // Don't join if result will exceed this number (in bindings considered).
	private double               maxJoinSizeStorage                  = 1e7; // Don't join if result will exceed this number (in size of a cross product created).
	private double               maxSkolemExpansionPerLiteral        = 1e6; // Throw an exception if one literal is expanded more times than this due to Skolems.
	private double               maxNumberClauseGroundings           = 1e8; // This is a PER CLAUSE value.  Should be less than Integer.MAX_VALUE since it is compared to a *.size() calculation.
	public  double               maxNumberOfGroundings               = 0.0; // Record the largest number of groundings for one clause.  TODO use accessor functions
	public  double               maxNumberOfGroundingsRemaining      = 0.0; // Record the largest number of groundings remaining for one clause.  TODO use accessor functions
//	public  double               maxTotalNumberOfRemainingGroundings = 1e9; // Throw an exception if this is exceeded, though note that this is (at least initially) a sum over ALL queries.
	public  double               warnIfNumberOfGroundingsExceedsThis = 1e7; // Before grounding a network, report clauses that have more than this many groundings remaining.
	private Collection<Clause>   allClauses;
	private Map<Clause,Integer>  clauseToIndex;
	private Map<Clause,Double>   countOfTRUEs; // Counts can be large, so use Double's.  (TODO - use long's instead?)
	private Map<Clause,Double>   countOfFALSEs;
	private Map<Clause,Double>   countOfSatisfiableGndClauses;
	private Map<Clause,Double>   largestSizeOfStoredGroundings;
	private Map<Clause,Double>   largestCrossProductCreated;
	protected Set<Clause>          stillTooLargeAfterReduction; // Collect those clauses that have too many groundings.
	protected Map<Clause,Double> countOfPossibleGroundings;
	private double               totalCountOfPossibleGroundings   = -1; // Sum over all clauses.  TODO BUGGY with pop/push? 
	public  double               totalNumberOfGroundingsRemaining = -1; // Sum over all clauses.  TODO BUGGY with pop/push?  
	
	private Set<Clause>          clausesFullyGrounded = new HashSet<Clause>(4); // Have fully grounded these clauses.
	
	private Map<PredicateName,Map<Term,List<List<Term>>>> allPosEvidenceIndexed; // Hash by predicate name and first argument for faster lookup. 
	private Map<PredicateName,Map<Term,List<List<Term>>>> allNegEvidenceIndexed; // Terms used here so no need to cast Literal arguments to Constants.
	private Map<PredicateName,Map<Term,List<List<Term>>>> allQueriesIndexed;
	private Map<PredicateName,Map<Term,List<List<Term>>>> allHiddensIndexed;
	private Map<PredicateName,Set<Integer>>               allPosEvidencePredNames; // Hashed so faster lookups than with PredicateNameArityPair's.
	private Map<PredicateName,Set<Integer>>               allNegEvidencePredNames;
	private Map<PredicateName,Set<Integer>>               allQueryPredNames;
	private Map<PredicateName,Set<Integer>>               allHiddenPredNames;
	
	// What to do if some constants of a given type don't appear at all?
	//	if CWA=true AND clause has at least one negative literal, then clause is true by CWA
	//  else if CWA=true and clause has no negative literals, then clause is false for all of these (and no need to count).
	//  if CWA=false then clause is false and no need to count.
	private Map<Clause,Integer> minPosArityEncountered; // Probably don't need these, but they might help in fancy heuristics (thought these would be of use when starting writing this code).
	private Map<Clause,Integer> minNegArityEncountered; // Note: am not including arity 0 and arity 1 here, since those are handled on the first pass.
	private Map<Clause,Integer> maxPosArityEncountered;
	private Map<Clause,Integer> maxNegArityEncountered;	
	private Map<Clause,Integer> numberOfLiteralsActive;
	private Map<Clause,Map<Literal,List<Integer>>> firstVariableAppearance; // If lit=p(1,x,x,y,x,2,y,z) then this should be {0, 1, -1, 3, -1, 0, -3, 8} where 0 means 'constant,' a positive number N means "first occurrence of a variable in position N (counting from 1), and -N means "subsequent appearance of variable that first appeared in position N." 
	
	private Map<Clause,Set<Literal>>                literalsToKeep;        // Should not be duplicates here.
	private Map<Clause,Set<Literal>>                literalsStillToReduce; // These are the literals that still need to be reduced.
	private Map<Clause,Set<Literal>>                literalsRejectedForReduction; // These are the literals that did not have a high-enough reduction (and hence would have increased the storage size too much).
	private Map<Clause,Set<Variable>>               accountedForVariables; // These variables in the clauses have been accounted for (in a final cleanup phase) and should not impact the size of the set of groundings.
	private Map<Clause,Map<Integer,List<Literal>>>  posLiteralsWithThisArity;
	private Map<Clause,Map<Integer,List<Literal>>>  negLiteralsWithThisArity;
	private Map<Clause,Map<Literal,List<Variable>>> freeVarsMap; // Need to be a list, since we want to maintain order.

	private Map<Clause,Set<Literal>> literalAlwaysInPosEvidence; // When a literal matches pName/arity information, store in these for convenient access.
	private Map<Clause,Set<Literal>> literalAlwaysInNegEvidence;
	private Map<Clause,Set<Literal>> literalAlwaysInQuery;
	private Map<Clause,Set<Literal>> literalAlwaysHidden;
	private Map<Clause,Set<Literal>> literalsContainingConstants;

	// This group is what is needed for inference (TODO see if any more - or could be less).
	private Map<Clause,Map<Variable,VariableIndexPair>>    aggregatorMap;
	private Map<Clause,Map<Variable,Set<Term>>>        varsToConstantsMap; // OK to use SET here since no duplicate constants.  (TODO - confirm this)
	private Map<Clause,Map<AggVar,List<List<Term>>>>   aggVarsToAggregatedConstantsMap; // Need to NOT remove duplicates since this might be a reduction from a longer list of variables, and we need to not lose counts (e,g., [a,b,c] and [a,b,d] might reduce to [[a,b], [a,b]]).  So cannot use SETs.  The variables here are AGGREGATED variables.
	private Map<Clause,Map<Literal,CacheLiteralGrounding>> litsToConstantsMap; // Cache all of the groundings of this literal.
	private Map<Clause,Set<Variable>>                      variablesInClause;  // Want a SET here since we do not want any duplicates.
	private Map<Clause,Set<Variable>>                      variablesRemainingInClause;  // After reduction, record which variables still remain.
	private Map<Clause,Double>                             multiplierPerSatisfiedClause; //Each satisfied state represents this many groundings (used when some variable(s) cannot satisfy the clause, but we still need to count all the combinations).
	
	private Map<Clause,Set<Variable>>                      singletonVarsInClauseProcessed; // Record that this variable in a 'singleton' literal has been reduced.  Thus if we have 'p(x) ^ q(x)' when we process p(x) we can look for previous calculations of its coverage, but we can NOT do so for q(x) since it needs to use the set remaining after p(x) was processed.
	private Map<PredicateName,List<CacheLiteralGrounding>> varsToConstantsMapForSingletonLiterals; // Other versions of this literal (in ANY clause) can share these results, assuming the variable is not yet in singletonVarsInClauseProcessed.  The first item in the list is the result for the NEGATED literal as the second is for the UNNEGATED one.

	// Information to save about the best solution found so far (if we do multiple restarts).
	private Map<Clause,Double>                           saved_countOfTRUEs;
	private Map<Clause,Double>                           saved_countOfFALSEs;
	private Map<Clause,Double>                           saved_countOfSatisfiableGndClauses;
	private Map<Clause,Double>                           saved_multiplierPerSatisfiedClause;
	private Map<Clause,Set<Literal>>                     saved_literalsToKeep;
	private Map<Clause,Set<Literal>>                     saved_literalsStillToReduce;
	private Map<Clause,Set<Literal>>                     saved_literalsRejectedForReduction;
	private Map<Clause,Map<Variable,VariableIndexPair>>  saved_aggregatorMap;
	private Map<Clause,Map<Variable,Set<Term>>>      saved_varsToConstantsMap;
	private Map<Clause,Map<AggVar,List<List<Term>>>> saved_aggVarsToAggregatedConstantsMap;
	private Map<Clause,Integer>                          cycle_when_solved; // Record when a clause was fully reduced.  Two pieces of information are stored.  A number like 12007 (12000 + 7) means that on the 12th overall 'trial' it was solved on the 7th iteration. 
	
	private BindingList bl  = new BindingList(); // Save some memory usage by reusing this.
	/* TVK : Not used here.
	private BindingList bl2 = new BindingList(); // Occasionally need another.
	*/
	private Literal     trueLit;
	private Literal     falseLit;
	private int         numberOfClausesToAnalyze;
	private Set<Clause> doneWithThisClause;
	private Term        variableInFactMarker;
	
	private LiteralSortComparator literalSorter = new LiteralSortComparator();
	private ClauseSortComparator  clauseSorter  = new ClauseSortComparator();
	private Set<PredicateName>    factsWithVariables; // TODO - should also use ARITY.
	private Set<PredicateName>    procedurallyDefinedPredicatesInUse;
	private Unifier               unifier;
	
	private Set<Term>                 dummySingletonSetOfConstants = new HashSet<Term>(4); // Needed as a place holder for aggregated variables.
	private Map<Clause,Long>              totalLiteralGroundingsConsidered;
	private Map<Clause,Map<Literal,Long>> totalLiteralGroundingsConsideredThisLiteral;
	private Collection<Clause>            errorThrownOnTheseClauses; // Record which clauses throw an error for needing too many cpu cycles or storage.
	private int[]                         emptyIntList = new int[0];

	// These are used AFTER reduction (unless doing LAZY inference).
	private ArrayList<GroundLiteral>      allGroundLiterals         = null; // Depending on the query being asked
	private ArrayList<GroundClause>       allGroundClauses          = null;
	private ArrayList<GroundLiteral>      allGroundLiteralsOrig     = null; // We specify ArrayList because we want speedy, random access.  Do NOT remove duplicates here, since the same reduced clause can arise from different original clauses.
	private ArrayList<GroundClause>       allGroundClausesOrig      = null;
	private int                           allGroundLiteralsOrigSize = -1; // Remember these, as a ways of checking of the Orig versions are improperly altered.
	private int                           allGroundClausesOrigSize  = -1;
	private Map<Clause,Set<GroundClause>> allGroundClausesPerClause = null;

	// Keep track of the clauses that exist after reduction.
	/* TVK : Not used here.
	private List<Clause>                            reducedClauses  = new ArrayList<Clause>(1); 
	private Map<Clause,Collection<Clause>>       reducedClausesMap  = new HashMap<Clause,Collection<Clause>>(4); 
	private Map<Clause,Clause>                clauseToReducedClause = new HashMap<Clause,Clause>(4);
	private Map<Clause,BindingList>   clauseToReducedClauseBindings = new HashMap<Clause,BindingList>(4);
	*/
	
	// Keep a CANONICAL collection of ground clauses.
	protected Map<Integer,List<GroundClause>> hashOfGroundClauses = new HashMap<Integer,List<GroundClause>>(4);
	// Keys: #negLits, #posLits, firstNegGndLit (or null), firstPosGndLit (or null), hashcode
	///TODO private Map<Integer,Map<Integer,Map<GroundLiteral,Map<GroundLiteral,Map<Integer,List<GroundClause>>>>>> hashOfGroundClauses2 = new HashMap<Integer,Map<Integer,Map<GroundLiteral,Map<GroundLiteral,Map<Integer,GroundClause>>>>>(4);

	private boolean clearListsOfConstantsAtEnd = false; // Set to true if OK to clear all data structures at the end (other than the counts).
	private boolean weightsLearnt = false;              // Initially set to false. Set to true, when the weights learnt for the MLN.
	/**
	 * @param network
	 */
	public GroundThisMarkovNetwork(MLN_Task task, Collection<Clause> allClauses) {	
		this.task       = task;
		// Each clause will be COPIED.  In one copy, reduction is on the TRUEs; on the other reduction is on the FALSEs.
		this.allClauses = new ArrayList<Clause>(allClauses); // Play it safe and get a fresh copy.  Plus, this way we can be sure it is an array list (assuming that matters somewhere ...).
		this.unifier    = task.unifier;  // Since can be called a lot, create a direct pointer.
		clauseToIndex   = new HashMap<Clause,Integer>(4);
		int counter = 0;
		for (Clause clause : allClauses) { clauseToIndex.put(clause, ++counter); } // NOTE: if we sort later, to work on clauses according to their #groundings, these counts will change!
		dummySingletonSetOfConstants.add(task.stringHandler.getStringConstant("PlaceHolderConstant"));
		trueLit                 = task.stringHandler.trueLiteral;
		falseLit                = task.stringHandler.falseLiteral;
		variableInFactMarker    = task.stringHandler.getStringConstant("VarInThisFact");
		allQueriesIndexed       = new HashMap<PredicateName,Map<Term,List<List<Term>>>>(4);
		allPosEvidenceIndexed   = new HashMap<PredicateName,Map<Term,List<List<Term>>>>(4);
		allNegEvidenceIndexed   = new HashMap<PredicateName,Map<Term,List<List<Term>>>>(4);
		allHiddensIndexed       = new HashMap<PredicateName,Map<Term,List<List<Term>>>>(4);
		allQueryPredNames       = new HashMap<PredicateName,Set<Integer>>(4);
		allPosEvidencePredNames = new HashMap<PredicateName,Set<Integer>>(4);
		allNegEvidencePredNames = new HashMap<PredicateName,Set<Integer>>(4);
		allHiddenPredNames      = new HashMap<PredicateName,Set<Integer>>(4);
		hashSetOfFacts(task.getQueryLiterals(),        allQueriesIndexed);
		hashSetOfFacts(task.getPosEvidenceLiterals(),  allPosEvidenceIndexed);
		hashSetOfFacts(task.getNegEvidenceLiterals(),  allNegEvidenceIndexed);
		hashSetOfFacts(task.getHiddenLiterals(),       allHiddensIndexed);
		hashPredNames( task.getQueryPredNames(),       allQueryPredNames);
		hashPredNames( task.getPosEvidencePredNames(), allPosEvidencePredNames);
		hashPredNames( task.getNegEvidencePredNames(), allNegEvidencePredNames);
		hashPredNames( task.getHiddenPredNames(),      allHiddenPredNames);
		errorThrownOnTheseClauses     = new ArrayList<Clause>(1); // Use a list so they stay in numeric order.
		
		numberOfClausesToAnalyze      = allClauses.size();
		doneWithThisClause            = new HashSet<Clause>(4);  // Do NOT reset this when restarting since once DONE, no need to continue (TODO confirm????)
		countOfTRUEs                  = new HashMap<Clause,Double>(4);
		countOfFALSEs                 = new HashMap<Clause,Double>(4);
		countOfSatisfiableGndClauses  = new HashMap<Clause,Double>(4);
		multiplierPerSatisfiedClause  = new HashMap<Clause,Double>(4);
		countOfPossibleGroundings     = new HashMap<Clause,Double>(4);
		largestSizeOfStoredGroundings = new HashMap<Clause,Double>(4);
		largestCrossProductCreated    = new HashMap<Clause,Double>(4);
		minPosArityEncountered        = new HashMap<Clause,Integer>(4);
		minNegArityEncountered        = new HashMap<Clause,Integer>(4);
		maxPosArityEncountered        = new HashMap<Clause,Integer>(4);
		maxNegArityEncountered        = new HashMap<Clause,Integer>(4);
		numberOfLiteralsActive        = new HashMap<Clause,Integer>(4);
		literalsToKeep                = new HashMap<Clause,Set<Literal>>(4);
		literalsStillToReduce         = new HashMap<Clause,Set<Literal>>(4);
		literalsRejectedForReduction  = new HashMap<Clause,Set<Literal>>(4);
		variablesInClause             = new HashMap<Clause,Set<Variable>>(4);
		variablesRemainingInClause    = new HashMap<Clause,Set<Variable>>(4);
		accountedForVariables         = new HashMap<Clause,Set<Variable>>(4);
		literalAlwaysInQuery          = new HashMap<Clause,Set<Literal>>(4);
		literalAlwaysHidden           = new HashMap<Clause,Set<Literal>>(4);
		literalAlwaysInPosEvidence    = new HashMap<Clause,Set<Literal>>(4);
		literalAlwaysInNegEvidence    = new HashMap<Clause,Set<Literal>>(4);
		literalsContainingConstants   = new HashMap<Clause,Set<Literal>>(4);
		posLiteralsWithThisArity      = new HashMap<Clause,Map<Integer,List<Literal>>>(4);
		negLiteralsWithThisArity      = new HashMap<Clause,Map<Integer,List<Literal>>>(4);
		varsToConstantsMap            = new HashMap<Clause,Map<Variable,Set<Term>>>(4);
		freeVarsMap                   = new HashMap<Clause,Map<Literal,List<Variable>>>(4);
		litsToConstantsMap            = new HashMap<Clause,Map<Literal,CacheLiteralGrounding>>(4);
		aggregatorMap                 = new HashMap<Clause,Map<Variable,VariableIndexPair>>(4);
		aggVarsToAggregatedConstantsMap             = new HashMap<Clause,Map<AggVar,List<List<Term>>>>(4);
		totalLiteralGroundingsConsidered            = new HashMap<Clause,Long>(4);
		totalLiteralGroundingsConsideredThisLiteral = new HashMap<Clause,Map<Literal,Long>>(4);
		firstVariableAppearance                     = new HashMap<Clause,Map<Literal,List<Integer>>>(4);

		singletonVarsInClauseProcessed         = new HashMap<Clause,Set<Variable>>(4);                // This needs to be reset each trial.
		varsToConstantsMapForSingletonLiterals = new HashMap<PredicateName,List<CacheLiteralGrounding>>(4); // Do NOT need to reset this for repeated trials.
		
		// Information to save about the best solution found so far (if we do multiple restarts).
		saved_countOfTRUEs                    = new HashMap<Clause,Double>(4);
		saved_countOfFALSEs                   = new HashMap<Clause,Double>(4);
		saved_countOfSatisfiableGndClauses    = new HashMap<Clause,Double>(4);
		saved_multiplierPerSatisfiedClause    = new HashMap<Clause,Double>(4);
		saved_literalsToKeep                  = new HashMap<Clause,Set<Literal>>(4);
		saved_literalsStillToReduce           = new HashMap<Clause,Set<Literal>>(4);
		saved_literalsRejectedForReduction    = new HashMap<Clause,Set<Literal>>(4);
		saved_aggregatorMap                   = new HashMap<Clause,Map<Variable,VariableIndexPair>>(4);
		saved_varsToConstantsMap              = new HashMap<Clause,Map<Variable,Set<Term>>>(4);
		saved_aggVarsToAggregatedConstantsMap = new HashMap<Clause,Map<AggVar,List<List<Term>>>>(4);
		cycle_when_solved                     = new HashMap<Clause,Integer>(4);
		
		resetAllInstanceVariables(false);
	}
	
	private void clearAllSAVEDs() {
		saved_countOfTRUEs.clear();
		saved_countOfFALSEs.clear();
		saved_countOfSatisfiableGndClauses.clear();
		saved_multiplierPerSatisfiedClause.clear();
		saved_literalsToKeep.clear();
		saved_literalsStillToReduce.clear();
		saved_literalsRejectedForReduction.clear();
		saved_aggregatorMap.clear();
		saved_aggregatorMap.clear();
		saved_varsToConstantsMap.clear();
		saved_aggVarsToAggregatedConstantsMap.clear();
		cycle_when_solved.clear();
	}

	private void resetAllInstanceVariables(boolean isaReset) { // If isaReset=true, then can CLEAR data instead of NEW'ing.
		for (Clause clause : allClauses) if (!isaReset || !doneWithThisClause.contains(clause)) { // Start over if not done and a reset.
			countOfTRUEs.put(                clause,  0.0);
		    countOfFALSEs.put(               clause,  0.0);
		    multiplierPerSatisfiedClause.put(clause,  1.0);
		    if (isaReset) {	
				accountedForVariables.get(          clause).clear();
				aggregatorMap.get(                  clause).clear();
				aggVarsToAggregatedConstantsMap.get(clause).clear();
				singletonVarsInClauseProcessed.get( clause).clear();
				variablesInClause.get(              clause).clear(); // NOTE: this does not change, but it needs to be empty in order for varsToConstantsMap to be properly built.
		    } else {
		    	countOfSatisfiableGndClauses.put( clause, -1.0); // This indicates that the first setting of this is not a 'change.'  (Minor detail in terms of status reporting via println's.)
			    cycle_when_solved.put(            clause, -1);   // Indicates 'not yet done.'  Be sure to only set this at the start.
		    	minPosArityEncountered.put(       clause, Integer.MAX_VALUE); // Don't redo these, since this information isn't recalculated.
			    minNegArityEncountered.put(       clause, Integer.MAX_VALUE);
			    maxPosArityEncountered.put(       clause, Integer.MIN_VALUE);
			    maxNegArityEncountered.put(       clause, Integer.MIN_VALUE);
				posLiteralsWithThisArity.put(     clause, new HashMap<Integer,List<Literal>>(4));
				negLiteralsWithThisArity.put(     clause, new HashMap<Integer,List<Literal>>(4));
			    largestSizeOfStoredGroundings.put(clause, 0.0); // Calculate this over ALL retries (maybe have another pair of variables that are PER TRIAL?).
			    largestCrossProductCreated.put(   clause, 0.0);
				totalLiteralGroundingsConsidered.put(           clause, (long)0);
				freeVarsMap.put(                                clause, new HashMap<Literal,List<Variable>>(4));
				firstVariableAppearance.put(                    clause, new HashMap<Literal,List<Integer>>(4));
				totalLiteralGroundingsConsideredThisLiteral.put(clause, new HashMap<Literal,Long>(4));
				litsToConstantsMap.put(                         clause, new HashMap<Literal,CacheLiteralGrounding>(4));
				singletonVarsInClauseProcessed.put(             clause, new HashSet<Variable>(4));

				// The remainder need to be reset for each new trial.
		    	accountedForVariables.put(        clause, new HashSet<Variable>(4));
				variablesInClause.put(            clause, new HashSet<Variable>(4)); // NOTE: this does not change, but it needs to be empty in order for varsToConstantsMap to be properly built.
				varsToConstantsMap.put(           clause, new HashMap<Variable,Set<Term>>(4));
				aggregatorMap.put(                clause, new HashMap<Variable,VariableIndexPair>(4));
				numberOfLiteralsActive.put(       clause, Utils.getSizeSafely(clause.posLiterals) + Utils.getSizeSafely(clause.negLiterals));
				aggVarsToAggregatedConstantsMap.put(      clause, new HashMap<AggVar,List<List<Term>>>(4));
				saved_varsToConstantsMap.put(             clause, new HashMap<Variable,Set<Term>>(4));
				saved_aggregatorMap.put(                  clause, new HashMap<Variable,VariableIndexPair>(4));
				saved_aggVarsToAggregatedConstantsMap.put(clause, new HashMap<AggVar,List<List<Term>>>(4));
		    }
			if (isaReset) {
				literalsToKeep.get(       clause).clear();
				literalsStillToReduce.get(clause).clear();
				literalsRejectedForReduction.get(clause).clear();
			} else {
				literalsToKeep.put(       clause, new HashSet<Literal>(4));
				literalsStillToReduce.put(clause, new HashSet<Literal>(4));
				literalsRejectedForReduction.put(clause, new HashSet<Literal>(4));
			}
			if (clause.posLiterals != null) for (Literal  pLit : clause.posLiterals) { 
				literalsToKeep.get(               clause).add(pLit); // Initially put everything in here, then remove if no longer needed.
				literalsStillToReduce.get(        clause).add(pLit);
				initializeVariablesInLiteralsInfo(clause, pLit);
			}
			if (clause.negLiterals != null) for (Literal  nLit : clause.negLiterals) { 
				literalsToKeep.get(               clause).add(nLit);
				literalsStillToReduce.get(        clause).add(nLit);
				initializeVariablesInLiteralsInfo(clause, nLit);
			}
			countCurrentCombinatorics(clause);
		}
	}
	
	private Map<Term,Integer> variablesSeenSoFar = new HashMap<Term,Integer>(4); // Reuse this memory space.	
	private void collectInitialLiteralInfo(Clause clause, Literal lit, boolean pos) {	
		
		// Store the free-variables list for each literal appearing in the clauses.
		if (freeVarsMap.get(clause).get(lit) == null) {
			List<Variable> result = (List<Variable>) lit.collectFreeVariables(task.setOfSkolemMarkers); // If cannot coerce, then create new memory.
			if (result != null) {
				freeVarsMap.get(clause).put(lit, result);
				// See definition of firstVariableAppearance for an explanation of its "semantics."
				List<Integer> varAppearanceMap = new ArrayList<Integer>(1);
				variablesSeenSoFar.clear();
				int counter = 1; // Note that for this encoding, counting starts at 1.
				for (Term term : lit.getArguments()) {
					if      (term instanceof Term)               { varAppearanceMap.add(0);  // Indicate constants via '0.'
																	   if (literalsContainingConstants.get(clause) == null) { literalsContainingConstants.put(clause, new HashSet<Literal>(4)); }
					                                                   literalsContainingConstants.get(clause).add(lit); }
					else if (task.setOfSkolemMarkers.contains(term)) { varAppearanceMap.add(0); } // These will become constants.
					else if (term instanceof Function) { throw new Error("Cannot handle functions here.  Should be removed before this is point."); }
					else if (variablesSeenSoFar.containsKey(term))   { varAppearanceMap.add(-variablesSeenSoFar.get(term)); } // Negate when reusing a constant.
					else {
						varAppearanceMap.add(counter);
						variablesSeenSoFar.put(term, counter);
					}
					counter++;
				}
				firstVariableAppearance.get(clause).put(lit, varAppearanceMap);
			}
		}

		// See if any procedurally defined predicates are in use.  These will only be in clauses, never in facts (by construction).
		PredicateName pName = lit.predicateName;
		if (task.prover.isProcedurallyDefined(pName,lit.numberArgs())) {
		 	 if (procedurallyDefinedPredicatesInUse == null) { procedurallyDefinedPredicatesInUse = new HashSet<PredicateName>(4); }
		 	 // TODO - use arity as well?
			 if (!procedurallyDefinedPredicatesInUse.contains(pName)) {
		 		Utils.println("\n% Procedurally defined predicate in use: '" + pName + "'");
		 		procedurallyDefinedPredicatesInUse.add(pName);
		 	 }
		}
		
		totalLiteralGroundingsConsideredThisLiteral.get(clause).put(lit, (long)0); // Count how many times this literal was grounded and checked against the facts.
		
		// Organize literals by the number of variables in them (a bit of a misnomer to call this 'arity' since constants and duplicated variables are not counted).
		int arity = Utils.getSizeSafely(freeVarsMap.get(clause).get(lit)); // Care about VARIABLES not #arguments.
		// Literals with arity = 0 are trivially handled - if true (when 'factoring in' if a pos or neg literal), clause is always satisfied; if false, literal can be discarded.
		// Literals with arity = 1 are also easily handled.  Simply only keep this settings for the included variable that do not make this literal true, BUT BE SURE TO COUNT ALL THOSE THAT MAKE IT TRUE.
		if (arity > 1 && arity < (pos ? minPosArityEncountered.get(clause) : minNegArityEncountered.get(clause))) { if (pos) minPosArityEncountered.put(clause, arity); else minNegArityEncountered.put(clause, arity); }
		if (arity > 1 && arity > (pos ? maxPosArityEncountered.get(clause) : maxNegArityEncountered.get(clause))) { if (pos) maxPosArityEncountered.put(clause, arity); else maxNegArityEncountered.put(clause, arity); }
		Map<Integer,List<Literal>> lookup1b = (pos ? posLiteralsWithThisArity.get(clause) : negLiteralsWithThisArity.get(clause));
		if (lookup1b == null) { 
			lookup1b = new HashMap<Integer,List<Literal>>(4); 
			if (pos) { posLiteralsWithThisArity.put(clause, lookup1b); } else { negLiteralsWithThisArity.put(clause, lookup1b); }
		}
		List<Literal> lookup2b = lookup1b.get(arity);
		if (lookup2b == null) {
			lookup2b = new ArrayList<Literal>(1);
			lookup1b.put(arity, lookup2b);
		}
		lookup2b.add(lit);
		
		initializeVariablesInLiteralsInfo(clause, lit);
	}
	
	private void initializeVariablesInLiteralsInfo(Clause clause, Literal lit) {
		// Look for new variables in this literal, and if any found collect all of the possible groundings.  TODO - what about functions???? COULD EXPAND TO HAVE MORE ARGS!
		List<TypeSpec> typeSpecs = task.collectLiteralArgumentTypes(lit);
		if (lit.numberArgs() != Utils.getSizeSafely(typeSpecs)) { Utils.error("Mismatch for " + wrapLiteral(clause, lit) + "  numbArgs=" + lit.numberArgs() + " typeSpecs=" + typeSpecs); }
		// Simultaneously walk through the arguments and the types.
		// Only collect if the argument is a variable that is not already bound.  Also if a variable appears multiple times, only collect it once.
		for (int i = 0; i < lit.numberArgs(); i++) {
			Type type = typeSpecs.get(i).isaType;
			Term term = lit.getArgument(i);			
			if (term instanceof Variable  && !isaSkolem(term)) {
				Variable var = (Variable) term;  // Skip if this variable has already been encountered.						
				if (variablesInClause.get(clause).add(var)) { // Returns true if NOT already there.
					Set<Term> cList = task.getReducedConstantsOfThisType(type); // Collect all the constants of this type.
					varsToConstantsMap.get(clause).put(var, cList);
					//Utils.println("  Storing " + cList.size() + " contants for variable '" + var + "'. " + literal + "  " + clause);
					// varsToConstantsMapNew.get(clause).put(var, new HashSet<Term>(4)); // Will add to this later, as we find constants we need to keep around.
				}
			}
		}
	}
	
	private boolean isaSkolem(Term term) {
		return task.setOfSkolemMarkers.contains(term);
	}
	
	private CacheLiteralGrounding countLiteralGroundings(Clause clause, Literal lit, boolean pos, Variable onlyThisSingletonVarInLiteral, boolean forceCollectionOfRemainingGroundings) throws MLNreductionProblemTooLargeException {
		if (onlyThisSingletonVarInLiteral != null && lit.numberArgs() == 1 && !singletonVarsInClauseProcessed.get(clause).contains(onlyThisSingletonVarInLiteral)) { // Save a small amount of time seeing if a single-variable literal has already been processed using the FULL set of constants.  But make sure this is the FIRST time this variable in this clause is being processed.
			// TODO - be careful if predicates can have more than mode ...	
			if (Utils.getSizeSafely(freeVarsMap.get(clause).get(lit)) != 1) { Utils.error("Should not reach here unless a literal has only one variable: " + wrapLiteral(clause, lit) + "."); }
			List<CacheLiteralGrounding> cachedSingleton = varsToConstantsMapForSingletonLiterals.get(lit.predicateName);
			if (cachedSingleton != null && cachedSingleton.get(pos ? 1 : 0) != null) {
				if (debugLevel > 1) { Utils.println("%      Using cached version for grounding " + wrapLiteral(clause, lit) + ".  T/F/U=" + cachedSingleton.get(pos ? 1 : 0).trueCount  + "/" + cachedSingleton.get(pos ? 1 : 0).falseCount + "/" + cachedSingleton.get(pos ? 1 : 0).unknownCount +  "  " + clause); }
				return cachedSingleton.get(pos ? 1 : 0);
			}
		}
		CacheLiteralGrounding cached = litsToConstantsMap.get(clause).get(lit); // See if this literal's groundings have been cached.
		if (cached != null) {
			if (debugLevel > 1) { Utils.println("%    Using CACHED grounding results for " + wrapLiteral(clause, lit) + "."); }
			return cached; 
		}		
		
		Collection<Variable> freeVariables = freeVarsMap.get(clause).get(lit);
		if (Utils.getSizeSafely(freeVariables) < 1) { Utils.error("Should not handle zero-arity literals here."); }
		CacheLiteralGrounding result = createFullCrossProductFromTheseVariables(clause, lit, pos, forceCollectionOfRemainingGroundings, freeVariables, emptyIntList);
		litsToConstantsMap.get(clause).put(lit, result);
		return result;
	}

	private double savingsDueToUseOfKnowns = 0.0;
	private long   excessChecks            = 0;
	private long   currentExcessChecks     = 0;
	Collection<Term> skolemsInLiteralUnderConsideration = null; // Using this instead of passing extra arguments.	
	// This method is a bit complex, because it only collects combinations that need to be kept.  Otherwise some large candidate list could be generated, only to be discarded later.  NOTE: still might GENERATE a lot, but at least most won't be saved.
	private CacheLiteralGrounding createFullCrossProductFromTheseVariables(Clause clause, Literal literalInUse, boolean pos, boolean forceCollectionOfRemainingGroundings, Collection<Variable> freeVariables, int[] positionsOfArgumentsInLiteralToUse) throws MLNreductionProblemTooLargeException {
		return help_createFullCrossProductFromTheseVariables(false, clause, literalInUse, pos, forceCollectionOfRemainingGroundings, freeVariables, positionsOfArgumentsInLiteralToUse);
	} 
	// Sometimes we need to collect all the groundings for a literal (e.g, after initial processing [see collectAndCacheRemainingGroundings], so provide a flag that supports this.
	// When simplyCollectAllGroundings=true, the counts need not be accurate.
	@SuppressWarnings("unchecked")
	private CacheLiteralGrounding help_createFullCrossProductFromTheseVariables(boolean simplyCollectAllGroundings, Clause clause, Literal literalInUse, boolean pos, boolean forceCollectionOfRemainingGroundings, Collection<Variable> freeVariables, int[] positionsOfArgumentsInLiteralToUse) throws MLNreductionProblemTooLargeException {
		//List<Variable> freeVariables = freeVarsMap.get(clause).get(literalInUse);
		if (Utils.getSizeSafely(freeVariables) < 1) { 
			if (containsVariables(literalInUse)) { Utils.error("There should be no free variables in this literal, but the literalInUse has variables: " + wrapLiteral(clause, literalInUse) + "."); }
			return createCacheLiteralGroundingFromVariableFreeClause(simplyCollectAllGroundings, clause, literalInUse, pos);
		}
		
		if (debugLevel > 1) { Utils.println("%      Need to create a cross product of all the groundings of these variables: " + freeVariables + " in " + wrapLiteral(clause, literalInUse) + "."); }
		Set<Variable>        unAggregatedVars    = null; // Only used for debugging, so can delete later.
		Set<Variable>          aggregatedVars    = null; // Only used for debugging, so can delete later.
		List<AggVar>         aggregatorsNeeded   = null;
		int                  numbFreeVariables   = Utils.getSizeSafely(freeVariables);
		Collection<Variable> freeVarsInLit       = (literalInUse == null ? null : freeVarsMap.get(clause).get(literalInUse));
		int                  numbFreeVarsInLit   = Utils.getSizeSafely(freeVarsInLit);
		List<Set<Term>>  allArgPossibilities = new ArrayList<Set<Term>>(numbFreeVariables);  // Order matters for the outer list, since it needs to match the order of the arguments, but the order constants appear doesn't matter.
		Map<Term,Integer> mapVariablesToPositionInAggregatorList = null; // If there are aggregators, we need to know their position in aggregatorsNeeded.
		if (debugLevel > 1) { Utils.print("%      Will be doing a 'brute force' cross product over these unaggregated variables ["); }
		// For each free variable, either collect it in unAggregatedVars or record which aggregator holds it.
		if (Utils.getSizeSafely(freeVariables) > 0) for (Variable var : freeVariables) {
			if (aggregatorMap.get(clause).get(var) == null) { // Only do the first cross product for the unaggregated variables.
				Set<Term> groundingsOfThisVariable = varsToConstantsMap.get(clause).get(var);
				if (debugLevel > 1) { Utils.print(" " + var); }
				allArgPossibilities.add(groundingsOfThisVariable);
				if (unAggregatedVars  == null) { unAggregatedVars  = new HashSet<Variable>(4); }
				unAggregatedVars.add(var);
			} else {
				if (aggregatedVars    == null) {   aggregatedVars  = new HashSet<Variable>(4); }
				if (aggregatedVars.contains(var)) { Utils.error("Already have '" + var + "' in aggregatedVars=" + aggregatedVars); } // Should never happen, but check anyway.
				aggregatedVars.add(var);
				if (aggregatorsNeeded == null) { aggregatorsNeeded = new ArrayList<AggVar>(1); }
				AggVar aggVar = aggregatorMap.get(clause).get(var).aggVar;
				if (!aggregatorsNeeded.contains(aggVar)) { // Collect the aggregators.
					aggregatorsNeeded.add(aggVar);
					if (mapVariablesToPositionInAggregatorList == null) { mapVariablesToPositionInAggregatorList = new HashMap<Term,Integer>(4); }
					if (mapVariablesToPositionInAggregatorList.containsKey(var)) { Utils.error("Already have '" + var + "' in " + mapVariablesToPositionInAggregatorList); }
					mapVariablesToPositionInAggregatorList.put(var, aggregatorsNeeded.size() - 1);
				} else { // Walk through the existing aggregators and record which one 'owns' this variable.
					for (int i = 0; i < aggregatorsNeeded.size(); i++) { 
						if (aggVar == aggregatorsNeeded.get(i)) { mapVariablesToPositionInAggregatorList.put(var, i); break; }
					}
				}
				allArgPossibilities.add(dummySingletonSetOfConstants); // Need to keep the arity the same.
			}
		}	
		if (debugLevel > 1) { Utils.println(" ]."); }
				
		CrossProductViaContinuation<Term> basicVarCrossProduct = new CrossProductViaContinuation(allArgPossibilities);
		double origSizeOfCrossProduct = Math.max(1.0, basicVarCrossProduct.sizeOfCrossProduct);
		double fullSizeOfCrossProduct = origSizeOfCrossProduct;  // Includes the sizes of the aggregators.
		int numbOfAggregators = Utils.getSizeSafely(aggregatorsNeeded);
		List<List<List<Term>>> allAggArgPossibilities = null;
		if (numbOfAggregators > 0) { // Now need to merge in any aggregated variables.
			if (debugLevel > 1) { Utils.println("%      Need to process these " + numbOfAggregators + " aggregators: " + aggregatorsNeeded + "."); }
			allAggArgPossibilities = new ArrayList<List<List<Term>>>(numbOfAggregators);
			for (AggVar aggVar : aggregatorsNeeded) {
				List<List<Term>> aggregatorListOfLists = aggVarsToAggregatedConstantsMap.get(clause).get(aggVar);
				if (debugLevel > 1) { Utils.println("% **** Aggregator '" + aggVar + "' has bindings = " + Utils.limitLengthOfPrintedList(aggregatorListOfLists, 5)); }
				allAggArgPossibilities.add(aggregatorListOfLists);
				fullSizeOfCrossProduct *= aggregatorListOfLists.size();
				if (debugLevel > 1) { Utils.println("%      Will be expanding the current cross product (size=" + Utils.truncate(origSizeOfCrossProduct, 0) + "), using the " +  Utils.comma(aggregatorListOfLists.size()) + " items of aggregator '"
														+ aggVar + "', for a total new size of aggregators of " + Utils.truncate(fullSizeOfCrossProduct,  0) + "."); }
			}
		}

		CrossProductViaContinuation<List<Term>> crossProductOfAggregatedVars = new CrossProductViaContinuation(allAggArgPossibilities);
		double sizeOfAggVarCrossProduct  = Math.max(1.0, crossProductOfAggregatedVars.sizeOfCrossProduct);	
		if (sizeOfAggVarCrossProduct > largestCrossProductCreated.get(clause)) { largestCrossProductCreated.put(clause, sizeOfAggVarCrossProduct); }
		if (debugLevel > 2) { Utils.println("%      |crossProduct| = " + Utils.truncate(origSizeOfCrossProduct, 0) + ",  |crossProductOfAggregatedVars| = " + Utils.truncate(sizeOfAggVarCrossProduct, 0) + ", and |total| = " + Utils.truncate(fullSizeOfCrossProduct, 0)); } 
		
		// Now collect those combinations that need to be retained.
		List<List<Term>> bindingsToKeep = new ArrayList<List<Term>>(1);	// Note: need to NOT return NULL unless we didn't collect all the groundings.  Cannot use List<Term> since getNextCrossProduct will return a LIST and need to add those to this list.
		int  debugCounter = 0; int maxDebugCounter = 3;//debugLevel; // Used to limit printing in debugging runs.
		long trueCount    = 0; // NOTE: these counts are for the literal in question IGNORING ITS SIGN (other code deals with that).
		long falseCount   = 0;
		long unknownCount = 0;
		long countOfLitGroundings = 0;	
		
		// Cannot use for literals where facts contains variables, since there we need to generate the combinations.
		Collection<GroundLiteral> queryKnowns       = null; // Defer setting these until we're sure they are needed.
		Collection<GroundLiteral> hiddenKnowns      = null;
		Collection<GroundLiteral> posEvidenceKnowns = null;
		Collection<GroundLiteral> negEvidenceKnowns = null;
		long numberOfKnowns = Long.MAX_VALUE;
		// Can walk through the knowns if we are not collecting all groundings (since then we should exactly be generating what we need)
		//      and we're not forced to collect all remaining groundings (or cwa=true and literal is negated - in this case, any implicit groundings satisfy the clause and hence need not be generated).
		// Also note that cannot uses this when this literal's predicate name involves any facts with variables.
		boolean considerKnowns = (!simplyCollectAllGroundings
								   && (factsWithVariables == null || !factsWithVariables.contains(literalInUse.predicateName))
							       && (!forceCollectionOfRemainingGroundings || (!pos && task.isClosedWorldAssumption(literalInUse)))); 
		if (considerKnowns) {
			queryKnowns       = (task.isClosedWorldAssumption(literalInUse) ? task.getQueryKnowns( literalInUse) : null); // If CWA=false, anything not in the positive or negative lists is assumed to be unknown anyway, so no need to check.
			hiddenKnowns      = (task.isClosedWorldAssumption(literalInUse) ? task.getHiddenKnowns(literalInUse) : null);
			posEvidenceKnowns =  task.getPosEvidenceKnowns(literalInUse);
			negEvidenceKnowns =  task.getNegEvidenceKnowns(literalInUse);
			numberOfKnowns = Utils.getSizeSafely(queryKnowns) + Utils.getSizeSafely(hiddenKnowns) + Utils.getSizeSafely(posEvidenceKnowns) + Utils.getSizeSafely(negEvidenceKnowns);
			if (debugLevel > 2) { Utils.println("% lit = " + wrapLiteral(clause, literalInUse) + "  |fullSizeOfCrossProduct| = " + Utils.truncate(fullSizeOfCrossProduct, 0) + "  |totalNumberOfKnowns| = " +  Utils.comma(numberOfKnowns) + "    |queryKnowns| = " +  Utils.comma(queryKnowns) + "   |hiddenKnowns| = " +  Utils.comma(hiddenKnowns) + "   |posKnowns| = " +  Utils.comma(posEvidenceKnowns) + "   |negKnowns| = " +  Utils.comma(negEvidenceKnowns)); }
		}
		if (considerKnowns && // See if substantially cheaper to walk through the knowns than the explicit cross product.
					(numberOfKnowns < maxNumberOfKnownsToConsider || fullSizeOfCrossProduct > maxCrossProductSizeToUseKnownsRegardless) &&
					 numberOfKnowns < multiplierOnSizeOfExplicitCrossProduct * fullSizeOfCrossProduct / 2) { // If not less than half the size, don't use this short cut.		
			if (numberOfKnowns > largestCrossProductCreated.get(clause)) { largestCrossProductCreated.put(clause, (double) numberOfKnowns); }
			/**
			 * Get grandTotal count, as done now.
			 * 
			 * Walk through each "knowns" list, compare to the legal variables for each argument, and count true/false/unknown (and calculate totalChecked=true+false+unknown) 
			 * Decide which to keep as before.
			 * 
			 * 		What is label for unchecked = grantTotal - totalChecked?  I.e., the unchecked bindings.  
			 * 	    If CWA=true, these are all FALSE else these are UNKNOWN.
			 * 
			 * Find all remaining constants for each argument, when walking through the knowns, SKIP if not a member of these.
			 * 
			 */
			currentExcessChecks = 0; // See how many UNNEEDED checks are done.
			
			List<Map<Term,Set<List<Term>>>> indexesForAggVarConstants = null;
			/*  ADD THIS BACK IN LATER.
			int numbAggVarCollections = crossProductOfAggregatedVars.getNumberOfCollections();
			if (crossProductOfAggregatedVars.sizeOfCrossProduct > 1000) { // If many unknowns, will consider indexing the AGGREGATED cross products for faster access.
				// allArgPossibilities uses SETs already, so no need to index.  Let Java's hashing do this for us.
				int counter = -1; // Since incremented early, start at -1 so 0 first value encountered.
				if (indexesForAggVarConstants == null) { indexesForAggVarConstants = new ArrayList<Map<Term,Set<List<Term>>>>(numbAggVarCollections); }
				for (List<List<Term>> argPossibility : allAggArgPossibilities) {
					int sizeThisAggVar = Utils.getSizeSafely(argPossibility);
					counter++; // Increment before the continue.
					if (sizeThisAggVar < 100) { indexesForAggVarConstants.add(null); continue; } // Simply walk through short lists, i.e., don't waste time and space creating an index.
					crossProductOfAggregatedVars.clearThisEntry(counter); // Return this space just in case doing so prevents overflow.
					Map<Term,Set<List<Term>>> indexDB = new HashMap<Term,Set<List<Term>>>(4);
					indexesForAggVarConstants.add(indexDB);
					for (List<Term> args : argPossibility) {
						Term arg0 = args.get(0);
						Set<List<Term>> lookup = indexDB.get(arg0);
						if (lookup == null) { lookup = new HashSet<List<Term>> (4); indexDB.put(arg0, lookup); }
						lookup.add(args); // We just want to see if IN the cross product and don't care how many times it appears.
					}
				}
			}
			*/
		
			if (debugLevel > -2) {
				Utils.println("% mapVariablesToPositionInAggregatorList = " + mapVariablesToPositionInAggregatorList +
							  "  free variables = "                         + freeVariables + 
							  "  |basicVarCrossProduct| = "                 + Utils.truncate(basicVarCrossProduct.sizeOfCrossProduct, 0) +
							  "  |crossProductOfAggregatedVars| = "         + Utils.truncate(crossProductOfAggregatedVars.sizeOfCrossProduct, 0) +
							  "  |aggVarIndexes| = "                        + Utils.getSizeSafely(indexesForAggVarConstants));
			}
			int progressCounter = 0; int frequency = 1000;
			if (queryKnowns       != null) for (GroundLiteral gLit : queryKnowns)       { 
				countOfLitGroundings++; // Seems fair to count all the knowns considered as part of the count of groundings considered.
				if (debugLevel > 1 && ++progressCounter % frequency == 0) { Utils.println("%   At " + Utils.comma(progressCounter) + " in the query knowns for " + wrapLiteral(clause, literalInUse) + "."); }
				if (gLitArgumentsStillExistInVariableCrossProducts(clause, literalInUse, positionsOfArgumentsInLiteralToUse, mapVariablesToPositionInAggregatorList, gLit, basicVarCrossProduct, aggregatorsNeeded, crossProductOfAggregatedVars, indexesForAggVarConstants)) { unknownCount++;           bindingsToKeep.add(extractConstants(clause, literalInUse, gLit)); }
			}
			progressCounter = 0;
			if (hiddenKnowns      != null) for (GroundLiteral gLit : hiddenKnowns)      { 
				countOfLitGroundings++;
				if (debugLevel > 1 && ++progressCounter % frequency == 0) { Utils.println("%   At " + Utils.comma(progressCounter) + " in the hidden knowns for " + wrapLiteral(clause, literalInUse) + "."); }
				if (gLitArgumentsStillExistInVariableCrossProducts(clause, literalInUse, positionsOfArgumentsInLiteralToUse, mapVariablesToPositionInAggregatorList, gLit, basicVarCrossProduct, aggregatorsNeeded, crossProductOfAggregatedVars, indexesForAggVarConstants)) { unknownCount++;           bindingsToKeep.add(extractConstants(clause, literalInUse, gLit)); }
			}
			progressCounter = 0;
			if (posEvidenceKnowns != null) for (GroundLiteral gLit : posEvidenceKnowns) { 
				countOfLitGroundings++;
				if (debugLevel > 1 && ++progressCounter % frequency == 0) { Utils.println("%   At " + Utils.comma(progressCounter) + " in the pos-evidence knowns for " + wrapLiteral(clause, literalInUse) + "."); }
				if (gLitArgumentsStillExistInVariableCrossProducts(clause, literalInUse, positionsOfArgumentsInLiteralToUse, mapVariablesToPositionInAggregatorList, gLit, basicVarCrossProduct, aggregatorsNeeded, crossProductOfAggregatedVars, indexesForAggVarConstants)) { trueCount++;  if (!pos) { bindingsToKeep.add(extractConstants(clause, literalInUse, gLit)); }}
			}
			progressCounter = 0;
			if (negEvidenceKnowns != null) for (GroundLiteral gLit : negEvidenceKnowns) { 
				countOfLitGroundings++;
				if (debugLevel > 1 && ++progressCounter % frequency == 0) { Utils.println("%   At " + Utils.comma(progressCounter) + " in the neg-evidence knowns for " + wrapLiteral(clause, literalInUse) + "."); }
				if (gLitArgumentsStillExistInVariableCrossProducts(clause, literalInUse, positionsOfArgumentsInLiteralToUse, mapVariablesToPositionInAggregatorList, gLit, basicVarCrossProduct, aggregatorsNeeded, crossProductOfAggregatedVars, indexesForAggVarConstants)) { falseCount++; if ( pos) { bindingsToKeep.add(extractConstants(clause, literalInUse, gLit)); }}
			}
			if (debugLevel > 2) { Utils.println("% FULL SIZE = " + Utils.truncate(fullSizeOfCrossProduct, 0) + "   unknownCount=" + Utils.comma(unknownCount) + " trueCount=" + Utils.comma(trueCount) + " falseCount=" + Utils.comma(falseCount)); }
			double implicitGroundings = fullSizeOfCrossProduct - (unknownCount + trueCount + falseCount);
			if (implicitGroundings > 0) {
				if (task.isClosedWorldAssumption(literalInUse)) {
					if (debugLevel > 0) { Utils.println("%       Since cwa=true, moving all " + Utils.truncate(implicitGroundings, 0) + " implicit groundings to the FALSE category."); }
					falseCount += implicitGroundings;
					// TODO - could collect if number of implicitGroundings is small, but then just wait until next call with forceCollectionOfRemainingGroundings=true;
					///HEREHERE 
					if (forceCollectionOfRemainingGroundings) { // The implicitGroundings are all unsatisfied AND NEED TO BE KEPT!
						//Utils.error("Need to figure how what to do with these for pos lits and CWA=true!  #implicitGroundings = " + Utils.truncate(implicitGroundings, 0));
					}
				} else {
					unknownCount += implicitGroundings;
					// TODO - could collect if number of implicitGroundings is small, but then just wait until next call with forceCollectionOfRemainingGroundings=true;
					if (forceCollectionOfRemainingGroundings) {
						//Utils.error("Need to figure how what to do with these for CWA=false!  #implicitGroundings = " + Utils.truncate(implicitGroundings, 0));
					}
				}
				savingsDueToUseOfKnowns += implicitGroundings; // Did not need to look at any of these.
				if (debugLevel > 0) { Utils.println("%  *** Was able to skip " + Utils.truncate(implicitGroundings, 0) + " groundings due to looking only at the " + Utils.comma(numberOfKnowns) + " known groundings for " + wrapLiteral(clause, literalInUse) + ".  Total savings so far: " + Utils.truncate(savingsDueToUseOfKnowns, 0) + ".'"); }
				implicitGroundings = 0;
			}
			if (currentExcessChecks > 0) {
				excessChecks += currentExcessChecks;
				if (debugLevel > 0) { Utils.println("%  *** Considered  " + Utils.comma(currentExcessChecks) +
													  " groundings that weren't in the cross products, due to looking only at all the known groundings for " + wrapLiteral(clause, literalInUse) + ".  Total excess checks so far: " + Utils.truncate(excessChecks, 0) + ".'"); }
			}
		} else {		
			if (fullSizeOfCrossProduct > maxJoinSizeComputation) {
				throw new MLNreductionProblemTooLargeException(debugLevel > 1 ? " ***** Estimated computation size of join of the non-aggregated variables (" + Utils.truncate(fullSizeOfCrossProduct, 0) + ") exceeds the maximum allowed (" + Utils.truncate(maxJoinSizeComputation, 0) + ").  So cancelling this join." : null);
			}
			if (fullSizeOfCrossProduct > largestCrossProductCreated.get(clause)) { largestCrossProductCreated.put(clause, fullSizeOfCrossProduct); }
			while (!basicVarCrossProduct.isEmpty()) {
				List<Term> bindings  = basicVarCrossProduct.getNextCrossProduct(); // Expand this binding using all the items in aggregatorListOfLists.
				boolean        firstTime = true; // If crossProductOfAggregatedVars is empty, we still need to do through the WHILE once.
				crossProductOfAggregatedVars.reset(); // Need to start this 'inner loop' afresh each time the outer loop is called.
				while (firstTime || !crossProductOfAggregatedVars.isEmpty()) { //  // Collect all the combinations for the aggregated variables.
					List<List<Term>> argVarLists = crossProductOfAggregatedVars.getNextCrossProduct();
					List<Term>       newBindings = new ArrayList<Term>(bindings); // Get a fresh COPY. Do not REUSE, since these will be collected plus getNextCrossProduct reuses the same memory cells.
					
					if (firstTime) { firstTime = false; }
					// Now walk through each aggregator and correctly fill in the positions in newBindings.
					if (argVarLists != null) for (int argNumber = 0; argNumber < numbFreeVariables; argNumber++) { // Walk through the variables in this literal and see which need to get their values from an aggregator.
						Variable basicVar                      = Utils.getIthItemInCollectionUnsafe(freeVariables, argNumber);
						Integer  aggVarPositionForThisBasicVar = mapVariablesToPositionInAggregatorList.get(basicVar);	// Indexes into argVarList.				
						
						if (aggVarPositionForThisBasicVar != null) { // See if this variable is owned by some aggregator.
							AggVar            aggVar               = aggregatorsNeeded.get(aggVarPositionForThisBasicVar);
							VariableIndexPair pair                 = aggregatorMap.get(clause).get(basicVar);
							List<Term>    argVarListForThisVar = argVarLists.get(aggVarPositionForThisBasicVar);
							if (debugLevel > 2 && debugCounter < maxDebugCounter)    { 
								Utils.println("%            Var '" + basicVar + "' is aggregated by aggregator var '" + aggVar + "'.  ArgVarListForThisVar = " + argVarListForThisVar + ".");
								Utils.println("%              Have this pair for arg #" + argNumber + ": index=" + pair.index + " for aggVar = " + pair.aggVar + ".");
							//	Utils.println("%              Set position " + argNumber + " in " + newBindings + " to " + argVarListForThisVar.get(pair.index) + ".");
							}
							if (argNumber < Utils.getSizeSafely(newBindings)) {
								if (pair.index < Utils.getSizeSafely(argVarListForThisVar)) {
									newBindings.set(argNumber, argVarListForThisVar.get(pair.index));
								} else { Utils.warning(" pair.index = " + pair.index + " argVarListForThisVar.size() = " + Utils.getSizeSafely(argVarListForThisVar)); }
							} else { Utils.warning(" argNumber = " + argNumber + " newBindings.size() = " + Utils.getSizeSafely(newBindings)); }
						} else if (debugLevel > 2 && debugCounter < maxDebugCounter) { Utils.println("%            Var '" + basicVar + "' is NOT aggregated."); }
					}
					if (debugLevel > 2) { debugCounter++; }	
					
					boolean keepTheseVariables = false;				
					if (simplyCollectAllGroundings) {
						keepTheseVariables = true;
					}
					else { // TODO - maybe make a version where just the arguments are passed in, saving the creation of a literal?  Don't want to use the unifier, since then can't index of arguments (where doing so is justified).
						bl.theta.clear();
						List<Variable>  freeVarsInLitAsList = (List<Variable>) freeVarsInLit;
						if (positionsOfArgumentsInLiteralToUse.length < 1) { // There is no mapping. Just pull out the variables in order.
							for (int i = 0; i < numbFreeVarsInLit; i++) {
								bl.addBinding(freeVarsInLitAsList.get(i), newBindings.get(i));
							}
						} else { //  // Pull out the variables for this literal from the possibly longer fullSetOfVariables, using the provided 'map.'
							for (int i = 0; i < numbFreeVarsInLit; i++) {
								//Utils.println("      i=" + i + ":  var=" + variablesToCombine.get(i) + " term=" + bindings.get(positionsOfArgumentsInLiteralToUse[i]) + " via position=" + positionsOfArgumentsInLiteralToUse[i]);
								bl.addBinding(freeVarsInLitAsList.get(i), newBindings.get(positionsOfArgumentsInLiteralToUse[i]));
							}
						}
						Literal litGroundedRaw = literalInUse.applyTheta(bl.theta);
						Literal litGrounded    = null;
						countOfLitGroundings++;					
						if (task.skolemsPerLiteral.get(literalInUse) != null) {
							litGrounded = litGroundedRaw; // Still want any other bindings.
							skolemsInLiteralUnderConsideration = task.skolemsPerLiteral.get(literalInUse); // Using a 'global' instead of passing another argument everywhere.
							if (debugLevel > 3) { Utils.println(literalInUse + " -> " + skolemsInLiteralUnderConsideration); } 
						} else {
							litGrounded = task.getCanonicalRepresentative(litGroundedRaw, true, postponeSavingGroundLiterals); // Want to have one copy of a specific literal.  TODO - saves some space, at a time cost (NOTE: after reduction we want the canonical versions in any case).
						}
						if (debugLevel > 3) { Utils.println("    bindings = " + bindings + "  BL = " + bl + "  lit = " + literalInUse + "  litGnd = " + litGrounded); }
						
						if (litGrounded == null) { // This grounding has not been seen.
							// IF POS AND NOT SEEN, if CWA=true, then UNSAT.  (All other pName/arity possibilities already checked.)
							// IF NEG AND NOT SEEN, if CWA=true, then   SAT.  (All other pName/arity possibilities already checked.)
							if (pos) {
								if (task.isClosedWorldAssumption(litGroundedRaw)) { falseCount++;    keepTheseVariables = true; }
								else                                              { unknownCount++;  keepTheseVariables = true; } // If CWA=false, then treat as a 'hidden' literal.
							} else {
								if (task.isClosedWorldAssumption(litGroundedRaw)) { falseCount++; } // No need to keep, since satisfied.
								else                                              { unknownCount++;  keepTheseVariables = true; } // If CWA=false, then treat as a 'hidden' literal.
							}
						} else if (pos) { // OTHERWISE WE NEED TO LOOK AT THE GROUNDED LITERAL.  If we have  p(...) and it is TRUE,  we do NOT need to keep it.
							if      (matchesPosEvidenceFast(litGrounded)) { trueCount++; }
							else if (matchesNegEvidenceFast(litGrounded)) { falseCount++;    keepTheseVariables = true; }
							else if (matchesQueryFast(      litGrounded)) { unknownCount++;  keepTheseVariables = true; } // Need to keep all literals that can be true or false (which is the case for queries).
							else if (matchesHiddenFast(     litGrounded)) { unknownCount++;  keepTheseVariables = true; } // Need to keep all literals that can be true or false (which is the case for hiddens).
							else if (isaFalseByCWAfast(     litGrounded)) { falseCount++;    keepTheseVariables = true; } // This will FAIL if the literal matches the list of hiddens.
							else                                          { unknownCount++;  keepTheseVariables = true; } // If CWA=false, then treat as a 'hidden' literal.
						} else {   // If we have ~p(...) and it is FALSE, we do NOT need to keep it.
							if      (matchesNegEvidenceFast(litGrounded)) { falseCount++; }
							else if (matchesPosEvidenceFast(litGrounded)) { trueCount++;     keepTheseVariables = true; }
							else if (matchesQueryFast(      litGrounded)) { unknownCount++;  keepTheseVariables = true; } // If a query and IN posEvidence or negEvidence, proper to let the evidence decide.
							else if (matchesHiddenFast(     litGrounded)) { unknownCount++;  keepTheseVariables = true; }
							else if (isaFalseByCWAfast(     litGrounded)) { falseCount++; }
							else                                          { unknownCount++;  keepTheseVariables = true; } // If CWA=false, then treat as a 'hidden' literal.
						}
						skolemsInLiteralUnderConsideration = null; // Need to erase this 'global' when done (TODO clean up this fragile code?).
					}
					if (keepTheseVariables) { 
						// No need to save in the canonical ground literal database, since we're only saving the BINDINGS.
						bindingsToKeep.add(newBindings);
						if (bindingsToKeep.size() > maxJoinSizeStorage) {
							throw new MLNreductionProblemTooLargeException(debugLevel > 1 ? " ***** Storage size of join (" + Utils.truncate(bindingsToKeep.size(), 0) + ") exceeds the maximum allowed (" + Utils.truncate(maxJoinSizeStorage, 0) + ").  So cancelling this join." : null);
						}
					}				
				}
			}
		}
	
		if (!simplyCollectAllGroundings) { updateCountOfTotalGroundings(clause, literalInUse, (pos ? trueCount : falseCount), countOfLitGroundings); }
		if (debugLevel > 3) { Utils.println(" true=" + Utils.comma(trueCount) + " false=" + Utils.comma(falseCount) + " unknown=" + unknownCount + " |keepers|=" + Utils.comma(bindingsToKeep)); }
		return new CacheLiteralGrounding(bindingsToKeep, trueCount, falseCount, unknownCount);
	}

	// Neither this clause nor this literal have any free variables.  Create a CacheLiteralGrounding for this special case.
	// TODO - get rid of duplicated code?
	private CacheLiteralGrounding createCacheLiteralGroundingFromVariableFreeClause(boolean simplyCollectAllGroundings, Clause clause, Literal literalInUse, boolean pos) {
		if (literalInUse == null) { Utils.error("Cannot handle literalInUse == null here."); }
		long trueCount    = 0;
		long falseCount   = 0;
		long unknownCount = 0;
		boolean keeper = false;
		if (simplyCollectAllGroundings) {
			keeper = true;
		} else {
			if (pos) { // If we have  p(...) and it is TRUE,  we do NOT need to keep it.
				if      (matchesPosEvidence(literalInUse)) { trueCount++; }
				else if (matchesNegEvidence(literalInUse)) { falseCount++;    keeper = true; }
				else if (matchesQuery(      literalInUse)) { unknownCount++;  keeper = true; } // Need to keep all literals that can be true or false (which is the case for queries).
				else if (matchesHidden(     literalInUse)) { unknownCount++;  keeper = true; } // Need to keep all literals that can be true or false (which is the case for hidden).
				else if (isaFalseByCWAfast( literalInUse)) { falseCount++;    keeper = true; }
				else                                       { unknownCount++;  keeper = true; } // If CWA=false, then treat as a 'hidden' literal.
			} else {   // If we have ~p(...) and it is FALSE, we do NOT need to keep it.
				if      (matchesNegEvidence(literalInUse)) { falseCount++; }
				else if (matchesPosEvidence(literalInUse)) { trueCount++;     keeper = true; }
				else if (matchesQuery(      literalInUse)) { unknownCount++;  keeper = true; } // If a query and IN posEvidence or negEvidence, proper to let the evidence decide.
				else if (matchesHidden(     literalInUse)) { unknownCount++;  keeper = true; }
				else if (isaFalseByCWAfast( literalInUse)) { falseCount++; }
				else                                       { unknownCount++;  keeper = true; } // If CWA=false, then treat as a 'hidden' literal.
			}			
		}
		List<List<Term>> groundingsStillNeeded = new ArrayList<List<Term>>(1); // This needs to be non-null if we WERE collecting groundings.
		if (keeper && literalInUse.numberArgs() > 0) {
			List<Term> listOfConstants = new ArrayList<Term>(1);
			for (Term term : literalInUse.getArguments()) { listOfConstants.add((Term) term); }
			groundingsStillNeeded.add(listOfConstants);
		}
		return new CacheLiteralGrounding(groundingsStillNeeded, trueCount, falseCount, unknownCount);
	}

	// See if this literal contains any variables.
	private boolean containsVariables(Literal literalInUse) {
		if (literalInUse.numberArgs() < 1) { return false; }
		for (Term term : literalInUse.getArguments()) {
			if (term instanceof Variable) { return true; }
			if (term instanceof Function) { Utils.error("Need to deal with functions: " + term); }
		}
		return false;
	}
	
	// Keep track of which literals are known to always be one of {query, hidden, positive, negative}.
	private void addLiteralToAlwaysInMap(Clause clause, Literal literal, Map<Clause,Set<Literal>> map, String mapName) {
		if (map.get(clause) == null) { map.put(clause, new HashSet<Literal>(4)); }
		if (debugLevel > 2) { Utils.println("% ****   ADD " + wrapLiteral(clause, literal) + " to always map '" + mapName + "' which currently contains " + Utils.comma(map.get(clause).size()) + " items."); }
		map.get(clause).add(literal);
	}
	private boolean isAlwaysQuery(Clause clause, Literal literal) {
		Collection<Literal> collection = literalAlwaysInQuery.get(clause);
		if (collection == null) { return false; }
		return collection.contains(literal);
	}
	private boolean isAlwaysHidden(Clause clause, Literal literal) {
		Collection<Literal> collection = literalAlwaysHidden.get(clause);
		if (collection == null) { return false; }
		return collection.contains(literal);
	}
	private boolean isAlwaysTrue(Clause clause, Literal literal) {
		Collection<Literal> collection = literalAlwaysInPosEvidence.get(clause);
		if (collection == null) { return false; }
		return collection.contains(literal);
	}
	private boolean isAlwaysFalse(Clause clause, Literal literal) {
		Collection<Literal> collection = literalAlwaysInNegEvidence.get(clause);
		if (collection == null) { return false; }
		return collection.contains(literal);
	}

	private void prepareToAnalyzeClauses() {		
		for (Clause clause : allClauses) { // Collect information about the literals in this clause.
			if (clause.posLiterals != null) for (Literal posLit : clause.posLiterals) { collectInitialLiteralInfo(clause, posLit, true);  }
			if (clause.negLiterals != null) for (Literal negLit : clause.negLiterals) { collectInitialLiteralInfo(clause, negLit, false); }
			
			if (debugLevel > 0) { Utils.println("\n%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n"); }
			int index = clauseToIndex.get(clause);
			if (debugLevel > 0 || index % 1000 == 0) { Utils.println("%   FROG is preprocessing clause #" + Utils.comma(clauseToIndex.get(clause)) + ": '" + clause.toString(Integer.MAX_VALUE) + "'."); }
			countOfPossibleGroundings.put(clause, countCurrentCombinatorics(clause));
						
			// There is a minor advantage in sorting single-variable literals (the first calculation of p(x) can be shared across literals).
			if (posLiteralsWithThisArity.get(clause).get(1) != null) { Collections.sort(posLiteralsWithThisArity.get(clause).get(1), literalSorter); }
			if (negLiteralsWithThisArity.get(clause).get(1) != null) { Collections.sort(negLiteralsWithThisArity.get(clause).get(1), literalSorter); }
			
			// Next look for literals that match the PredicateName/Arity information, since we can handle them at once.
			// Even if we find we're done with a clause, process all of these since that information is elsewhere assumed to have been collected.
			if (clause.posLiterals != null) for (Literal pLit : clause.posLiterals) {
				// If we have  p(...) and it is always TRUE,  then we're done with this clause!.
				// If it is always false, then we can delete it.
				// If it is hidden or a query, we can skip it (but need to keep it around).
				if        (matchesPosPnameArity(       pLit)) { 
					if (debugLevel > 0) { Utils.println("%   Positive literal '" + pLit + "' has a predicate name and arity stated to be always true."); }
					addLiteralToAlwaysInMap(      clause, pLit, literalAlwaysInPosEvidence, "literalAlwaysInPosEvidence");
					clauseAlwaysTrue(             clause, pLit);
				} else if (matchesNegPnameArity(       pLit)) { 
					if (debugLevel > 0) { Utils.println("%   Positive literal '" + pLit + "' has a predicate name and arity stated to be always false."); }
					addLiteralToAlwaysInMap(      clause, pLit, literalAlwaysInNegEvidence, "literalAlwaysInNegEvidence");
					noLongerNeedToKeepThisLiteral(clause, pLit);
				} else if (matchesQueryPnameArity(     pLit)) {   // If a query (or hidden literal) and IN posEvidence or negEvidence, proper to let the evidence decide.
					if (debugLevel > 0) { Utils.println("%   Positive literal '" + pLit + "' has a predicate name and arity stated to be always a query."); }
					addLiteralToAlwaysInMap(      clause, pLit, literalAlwaysInQuery, "literalAlwaysInQuery");
					recordLiteralHasBeenReduced(  clause, pLit);
				} else if (matchesHiddenPnameArity(    pLit)) { 
					if (debugLevel > 0) { Utils.println("%   Positive literal '" + pLit + "' has a predicate name and arity stated to be always a hidden literal."); }
					addLiteralToAlwaysInMap(      clause, pLit, literalAlwaysHidden, "literalAlwaysHidden");
					recordLiteralHasBeenReduced(  clause, pLit); 
				} else if (!task.isaKnownLiteral(pLit)) {
					if (task.warningCount < MLN_Task.maxWarnings) { Utils.println("% MLN WARNING #" + Utils.comma(++task.warningCount) + ": this positive literal has no known groundings: '" + pLit + 
																						"'.  Since CWA=" + task.isClosedWorldAssumption(pLit) + " it will " + (task.isClosedWorldAssumption(pLit) ? "always be false." : "will behave like a hidden literal.")); }
					if (task.isClosedWorldAssumption(pLit)) { noLongerNeedToKeepThisLiteral(clause, pLit); } // Always false by CWA.
					else     						        { recordLiteralHasBeenReduced(  clause, pLit); }					
				}
			}
			if (clause.negLiterals != null) for (Literal nLit : clause.negLiterals) {
				// See comments for the posLiterals.
				if        (matchesNegPnameArity(       nLit)) { 
					if (debugLevel > 0) { Utils.println("%   Negative literal '" + nLit + "' has a predicate name and arity stated to be always false."); }
					addLiteralToAlwaysInMap(      clause, nLit, literalAlwaysInNegEvidence, "literalAlwaysInNegEvidence");
					clauseAlwaysTrue(             clause, nLit);
				} else if (matchesPosPnameArity(       nLit)) { 
					if (debugLevel > 0) { Utils.println("%   Negative literal '" + nLit + "' has a predicate name and arity stated to be always true."); }
					addLiteralToAlwaysInMap(      clause, nLit, literalAlwaysInPosEvidence, "literalAlwaysInPosEvidence");
					noLongerNeedToKeepThisLiteral(clause, nLit);
				} else if (matchesQueryPnameArity(     nLit)) { 
					if (debugLevel > 0) { Utils.println("%   Negative literal '" + nLit + "' has a predicate name and arity stated to be always a query."); }
					addLiteralToAlwaysInMap(      clause, nLit, literalAlwaysInQuery, "literalAlwaysInQuery");
					recordLiteralHasBeenReduced(  clause, nLit);
				} else if (matchesHiddenPnameArity(    nLit)) { 
					if (debugLevel > 0) { Utils.println("%   Negative literal '" + nLit + "' has a predicate name and arity stated to be always a hidden literal."); }
					addLiteralToAlwaysInMap(      clause, nLit, literalAlwaysHidden, "literalAlwaysHidden");
					recordLiteralHasBeenReduced(  clause, nLit); 
				} else if (!task.isaKnownLiteral(nLit)) {
					if (task.warningCount < MLN_Task.maxWarnings) { Utils.println("% MLN WARNING #" + Utils.comma(++task.warningCount) + ": this negative literal has no known groundings: '" + nLit + "'.  Since CWA=" + task.isClosedWorldAssumption(nLit) + " it will " + (task.isClosedWorldAssumption(nLit) ? "always be true." : "will behave like a hidden literal.")); }
					if (task.isClosedWorldAssumption(nLit)) { clauseAlwaysTrue(clause, nLit); } // Always TRUE by CWA.
					else     						        { recordLiteralHasBeenReduced(  clause, nLit); }
					
				}
			}
			
			// Next look at the arity-zero and arity-one clauses (recall that arity is number of distinct variables),
			// since they can be handled without interacting variables.
			List<Literal> posLitsArity0 = posLiteralsWithThisArity.get(clause).get(0);
			List<Literal> negLitsArity0 = negLiteralsWithThisArity.get(clause).get(0);
			List<Literal> posLitsArity1 = posLiteralsWithThisArity.get(clause).get(1);
			List<Literal> negLitsArity1 = negLiteralsWithThisArity.get(clause).get(1);
						
			if (debugLevel > 0 && (posLitsArity0 != null || negLitsArity0 != null || posLitsArity1 != null || negLitsArity1 != null)) { 
				Utils.println("% Processing predicates with 0 or 1 variables in this clause.");
			}
			
			currentCycle = 0; // Use this for reporting "done at" if done on the arity 0 or 1 literals.
			// Better to do negatives first, since CWA helps them.
			if (!doneWithThisClause.contains(clause) && negLitsArity0 != null) for (Literal neg0 : negLitsArity0) {
				if (doneWithThisClause.contains(clause))               { continue; } // Put here in case DONE in middle of for loop.
				if (!literalsStillToReduce.get(clause).contains(neg0)) { continue; }
				if (thisNegLiteralIsSatisfied(neg0)) {
					if (debugLevel > 0) { Utils.println("% Negative literal " + wrapLiteral(clause, neg0) + " is satisfied."); }
					updateCountOfTotalGroundings( clause, neg0, 1, 1);
					clauseAlwaysTrue(clause, neg0);
				} else if (matchesPosEvidence(neg0)) {
					if (debugLevel > 0) { Utils.println("% Can DROP " + wrapLiteral(clause, neg0) + " because it is not satisfied."); }
					updateCountOfTotalGroundings( clause, neg0, 0, 1);
					noLongerNeedToKeepThisLiteral(clause, neg0);
				} else {
					if (debugLevel > 0) { Utils.println("% Negative literal " + wrapLiteral(clause, neg0) + " is satisfiable and so needs to be kept around."); }
					updateCountOfTotalGroundings( clause, neg0, 0, 1);
				}
				recordLiteralHasBeenReduced( clause, neg0);
			}
			if (!doneWithThisClause.contains(clause) && posLitsArity0 != null) for (Literal pos0 : posLitsArity0) {
				if (doneWithThisClause.contains(clause))               { continue; } 
				if (!literalsStillToReduce.get(clause).contains(pos0)) { continue; }
				if (matchesPosEvidence(pos0)) { 
					if (debugLevel > 0) { Utils.println("% Positive literal " + wrapLiteral(clause, pos0) + " is satisfied."); }
					updateCountOfTotalGroundings(clause, pos0, 1, 1);
					clauseAlwaysTrue(clause, pos0);
				} else if (thisNegLiteralIsSatisfied(pos0)) {
					if (debugLevel > 0) { Utils.println("% Can DROP " + wrapLiteral(clause, pos0) + " because it is not satisfied."); }
					updateCountOfTotalGroundings( clause, pos0, 0, 1);
					noLongerNeedToKeepThisLiteral(clause, pos0);
				} else {
					if (debugLevel > 0) { Utils.println("% Positive literal " + wrapLiteral(clause, pos0) + " is satisfiable and so needs to be kept around."); }
					updateCountOfTotalGroundings(clause, pos0, 0, 1);
				}
				recordLiteralHasBeenReduced( clause, pos0);
			}
			try {
				if (!doneWithThisClause.contains(clause) && negLitsArity1 != null) for (Literal neg1 : negLitsArity1) {
					if (doneWithThisClause.contains(clause))               { continue; }
					if (!literalsStillToReduce.get(clause).contains(neg1)) { continue; }
					handleSingleVariableLiteral(clause, neg1, false);
					recordLiteralHasBeenReduced(clause, neg1);
				}
				if (!doneWithThisClause.contains(clause) && posLitsArity1 != null) for (Literal pos1 : posLitsArity1) {
					if (doneWithThisClause.contains(clause))               { continue; }
					if (!literalsStillToReduce.get(clause).contains(pos1)) { continue; }
					handleSingleVariableLiteral(clause, pos1, true);
					recordLiteralHasBeenReduced(clause, pos1);
				}
			} catch (MLNreductionProblemTooLargeException e) {
				Utils.reportStackTrace(e);
				Utils.error("Should not throw an exception when dealing with arity-one literals.");
			}
			
			if (debugLevel > 0) {
				if (debugLevel > 2 && minPosArityEncountered.get(clause) <=  maxPosArityEncountered.get(clause)) { // Note this does NOT include 0 or 1 by design.
				  Utils.println("%   PosLit arity range = [" + minPosArityEncountered.get(clause) + "," + maxPosArityEncountered.get(clause) + "]");
				}
				if (debugLevel > 2 && minNegArityEncountered.get(clause) <=  maxNegArityEncountered.get(clause)) {
				  Utils.println("%   NegLit arity range = [" + minNegArityEncountered.get(clause) + "," + maxNegArityEncountered.get(clause) + "]");
				}
				Utils.println(  "%   LiteralsInClause:         " + literalsToKeep.get(clause));
				Utils.println(  "%   LiteralsStillToReduce:    " + literalsStillToReduce.get(clause));
				Utils.println(  "%   NumberPossibleGroundings: " + Utils.truncate(countOfSatisfiableGndClauses.get(clause), 0));
				Utils.println(  "%   PosLiteralsWithThisArity: " + posLiteralsWithThisArity.get(clause));
				Utils.println(  "%   NegLiteralsWithThisArity: " + negLiteralsWithThisArity.get(clause));
				Utils.println(  "%   VariablesInClause:        " + variablesInClause.get(clause));
				Utils.println(  "%   VarsToConstantsMap"); // Embedded lists can be very long, so handle printing explicitly.
				Set<Variable> items = varsToConstantsMap.get(clause).keySet();
				for (Variable var : items) {
					Utils.println("%      |" + var + "| =" + Utils.padLeft(Utils.getSizeSafely(varsToConstantsMap.get(clause).get(var)), 7) + ": " + Utils.limitLengthOfPrintedList(varsToConstantsMap.get(clause).get(var), 10));
				}				
			}
		}
	}

	public void analyzeClauses() {
		if (Utils.getSizeSafely(allClauses) < 1) { Utils.error("Should have some clauses to reduce!"); }
		if (debugLevel > -10) { Utils.println("\n% Preprocessing all " + Utils.comma(allClauses) + " clauses."); }
		prepareToAnalyzeClauses();
		int numberOfRandomTries = (chooseReductionOrderRandomly ? 1 : 0); // See if STARTING with random selection of literals to reduce.
		currentOverallIteration = 0;
		if (sortClausesByNumberOfPossibleGroundings) {
			if (task.warningCount < MLN_Task.maxWarnings) { Utils.println("% MLN WARNING #" + Utils.comma(++task.warningCount) + ": sorting clauses by the number of possible groundings each has, which means the 'clause #' of each clause will change.\n"); }
			// Sort the clauses by the number of possible groundings, and work on simplest ones first.  Assumes countOfPossibleGroundings gas been set.
			// Need to wrap the clauses to hold the countOfPossibleGroundings for use with the comparator.
			List<WrappedClause> wrappedForSorting = new ArrayList<WrappedClause>(allClauses.size());
			for (Clause c : allClauses) { wrappedForSorting.add(new WrappedClause(c, clauseToIndex.get(c), countOfPossibleGroundings.get(c), -1)); }
			Collections.sort(wrappedForSorting, clauseSorter);
			allClauses.clear();
			int counter = 0;
			for (WrappedClause w : wrappedForSorting) { allClauses.add(w.clause);  clauseToIndex.put(w.clause, ++counter); }
		}
		while (++numberOfRandomTries < maxNumberOfRandomTries) {
			currentOverallIteration++; // Counting starts at 1.
			if (debugLevel > -10) { Utils.println("\n% Analyzing the clauses still remaining."); }
			help_analyzeClauses();
			if (errorThrownOnTheseClauses.isEmpty()) {
				clearAllSAVEDs(); // Don't need the SAVED's, so reclaim their memory.
				reportFinalStatistics();
				return;
			} else { // If there is an error, copy ALL results that need to persist to the saved_* variables.  This will only happen the first time or if an improvement is made.
				if (debugLevel > 0) { 
					Utils.println("\n% Will restart for random trial #" + numberOfRandomTries + ".");
					for (Clause c : errorThrownOnTheseClauses) { Utils.println("  Had a problem reducing clause #" + Utils.comma(clauseToIndex.get(c)) + ": '" + c + "'."); }
				}
				Utils.waitHere("jwsjwsjws - trapping to see when this is happening");
				for (Clause clause : allClauses) { // Keep the best PER clause. Since doneWithThisClause() is NOT reset, won't restart on a clause once done.
					if (currentOverallIteration > 1 &&
						( errorThrownOnTheseClauses.contains(clause) &&  doneWithThisClause.contains(clause)) ||
						(!errorThrownOnTheseClauses.contains(clause) && !doneWithThisClause.contains(clause))) { 
						Utils.error("Have errorThrownOnTheseClauses = " + errorThrownOnTheseClauses.contains(clause) + " but " +
									    " doneWithThisClause = " +  doneWithThisClause.contains(clause) + " for clause '" + clause + "'.");
					}
					Double savedBest = saved_countOfSatisfiableGndClauses.get(clause); // We want this to be SMALL.
					double current   =       countOfSatisfiableGndClauses.get(clause);
					if (currentOverallIteration <= 1 || current < savedBest) { // If current result better than the previous best, save it.
						
						saved_countOfTRUEs.put( clause, countOfTRUEs.get( clause));
						saved_countOfFALSEs.put(clause, countOfFALSEs.get(clause)); // Don't really need all three, but the storage is minimal.
						saved_countOfSatisfiableGndClauses.put(clause, current); // This also serves as the best score.
						Utils.println("*** NEW BEST: cycle=" + currentOverallIteration + " *** current = " + Utils.truncate(current, 0) + (savedBest != null ? " [was " + Utils.truncate(savedBest, 0)+ "] for " : " for ") + clause);
						saved_multiplierPerSatisfiedClause.put(clause, multiplierPerSatisfiedClause.get(clause));						
						saved_literalsToKeep.put(              clause, literalsToKeep.get(clause));
						saved_literalsStillToReduce.put(       clause, literalsStillToReduce.get(clause));						
						saved_literalsRejectedForReduction.put(clause, literalsRejectedForReduction.get(clause));
						
						for (Variable var : variablesInClause.get(clause)) {
							VariableIndexPair currentOwnerOfVar = aggregatorMap.get(clause).get(var);
							if (currentOwnerOfVar == null) {
								saved_varsToConstantsMap.get(clause).put(var, varsToConstantsMap.get(clause).get(var));
							} else { // This else might be called multiple times with the same aggVar, but no need to worry about duplicate settings - not worth checking to see if already visited.
								AggVar aggVar = currentOwnerOfVar.aggVar;
								saved_aggVarsToAggregatedConstantsMap.get(clause).put(aggVar, aggVarsToAggregatedConstantsMap.get(clause).get(aggVar));
							}
							saved_aggregatorMap.get(clause).put(var, aggregatorMap.get(clause).get(var));
						}
					}
				}
				chooseReductionOrderRandomly = true;
				resetAllInstanceVariables(true);
			}	
		}
		// Since have caught errors the maximum tries, simply return the best.
		if (debugLevel > 0) { Utils.println("\n% Have failed to find a complete solution in " + maxNumberOfRandomTries + " random tries for all clauses, so simply returning the best solution found for each clause."); }
		varsToConstantsMap              = saved_varsToConstantsMap;
		aggVarsToAggregatedConstantsMap = saved_aggVarsToAggregatedConstantsMap;
		aggregatorMap                   = saved_aggregatorMap;
		countOfTRUEs                    = saved_countOfTRUEs;
		countOfFALSEs                   = saved_countOfFALSEs;
		countOfSatisfiableGndClauses    = saved_countOfSatisfiableGndClauses;
		multiplierPerSatisfiedClause    = saved_multiplierPerSatisfiedClause;
		literalsToKeep                  = saved_literalsToKeep;
		literalsStillToReduce           = saved_literalsStillToReduce;
		literalsRejectedForReduction    = saved_literalsRejectedForReduction;
		// Do NOT call clearAllSAVEDs!
		reportFinalStatistics();
	}

	private void help_analyzeClauses() {	
		numberOfClausesToAnalyze += errorThrownOnTheseClauses.size(); // All of these are now again in play.
		errorThrownOnTheseClauses.clear();  // Note: errors are caught PER clause, so that other clauses can continue if they don't throw an error.
		// (Aside: this could be written to process one clause at a time end-to-end, but it wasn't initially done that way, and there isn't (at least yet) a good reason to change.)
		// Handle any arity=0 and arity=1 literals.
		for (Clause clause : allClauses) if (doneWithThisClause.contains(clause)) { 
			if (debugLevel > 0)   { Utils.println(""); } 
			if (debugLevel > 0) { Utils.println("% SKIPPING (since DONE) the processing of clause #" + Utils.comma(clauseToIndex.get(clause)) + ": '" + clause + "'."); }
		} else try {
			
			if (debugLevel > 0) { Utils.println("\n%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n"); }
			int index = clauseToIndex.get(clause);
			if (debugLevel > 0 || index % 250 == 0) { Utils.println("%   FROG is processing clause #" + Utils.comma(clauseToIndex.get(clause)) + ": '" + clause + "'."); }

			int counterForOuterWhileLoop = 0; // Keep this extra variable, since it helps the readability of the code below.
			BestLiteralInfo bestLiteralInfo = new BestLiteralInfo();
			boolean inFinalPassToReduceLargeCases = false;  // When done with the 'easy' cases, do one last pass through the hard-to-reduce cases.
			Map<Clause,Integer> numberOfRejections = new HashMap<Clause,Integer>(4);
			int minArity = Math.min(minNegArityEncountered.get(clause), minPosArityEncountered.get(clause));
			int maxArity = Math.max(maxNegArityEncountered.get(clause), maxPosArityEncountered.get(clause));
			while (!doneWithThisClause.contains(clause)) {
				if (counterForOuterWhileLoop++ > 100) { Utils.error("Infinite loop in 'while (numberOfClausesToAnalyze > 0)'?"); } 
				currentCycle = counterForOuterWhileLoop;
				if (debugLevel > 0) { Utils.println(""); }
				if (debugLevel > 1) { Utils.println("% **********************************************************************************");  }
				if (debugLevel > 0) { Utils.println("% Trial #" + Utils.comma(currentOverallIteration) + ", Cycle #" + Utils.comma(counterForOuterWhileLoop) + " for clause #" + Utils.comma(clauseToIndex.get(clause)) + ": '" + clause.toString(Integer.MAX_VALUE) + "'."); }
				// Next walk through the collected information, using the smallest arity literals first.
				// As soon as we know something is always TRUE, we can stop.
				// No big deal walking-by-ones from minArity to maxArity, since we assume this range is small.  (If this becomes an issue, use a sorted, linked list of integers.)
				
				int counterForInnerWhileLoop = 0;
				int numberStillToReduce = Utils.getSizeSafely(literalsStillToReduce.get(clause));
				if (numberStillToReduce < 1) { Utils.error("Should not be here with numberStillToReduce=0!"); }
				boolean onlyOneChoiceLeft = (numberStillToReduce < 2); // If only one choice, force the collection of all groundings.
				bestLiteralInfo.reset();
				boolean madeUpdate = false;
				boolean doNegLitsFirst = task.isClosedWorldAssumption(null);
				int countOfPosLitsLeft = 0;
				int countOfNegLitsLeft = 0;
				if (clause.posLiterals != null) for (Literal pLit : clause.posLiterals) {
					if (literalsStillToReduce.get(clause).contains(pLit)) { countOfPosLitsLeft++; }
				}
				if (clause.negLiterals != null) for (Literal nLit : clause.negLiterals) {
					if (literalsStillToReduce.get(clause).contains(nLit)) { countOfNegLitsLeft++; }
				}
				MLNreductionProblemTooLargeException firstException = null;
				// Keep looking at increasing arities until an acceptable reduction found.
				int currentArity = minArity - 1; // Subtract this 1 since we want to increment currentArity at the START of the while, due to all the continue's.
				while (currentArity <= maxArity && !doneWithThisClause.contains(clause) && bestLiteralInfo.bestReduction < minReductionToAcceptAtThisArity) {
					currentArity++;
					if (counterForInnerWhileLoop++ > 100) { Utils.error("Infinite loop in 'while (currentArity <= maxArity)'?"  ); } 
					List<Literal> posLitsThisArity = (countOfPosLitsLeft < 1 ? null : posLiteralsWithThisArity.get(clause).get(currentArity));
					List<Literal> negLitsThisArity = (countOfNegLitsLeft < 1 ? null : negLiteralsWithThisArity.get(clause).get(currentArity));
					if (posLitsThisArity == null && negLitsThisArity == null)     { continue; }
					if (debugLevel > 1) { Utils.println("%   *****  CHECKING ARITY = " + currentArity + "  *****");	}	
					if (debugLevel > 1 && countOfNegLitsLeft > 0) { Utils.println("%    NegLitsThisArity = " + negLitsThisArity); }
					if (negLitsThisArity != null) for (Literal negLit : negLitsThisArity) {
						if (doneWithThisClause.contains(clause))                  { continue; }
						if (!literalsStillToReduce.get(clause).contains(negLit))  { continue; }
						try {
							madeUpdate = (considerThisLiteralForReduction(clause, negLit, false, currentArity, ((countOfNegLitsLeft < 2 && doNegLitsFirst) || onlyOneChoiceLeft), bestLiteralInfo, (inFinalPassToReduceLargeCases ? determineLargestAcceptableSizeForPoorReductionLiterals(numberOfRejections.get(clause)) : 0)) || madeUpdate); // The '||' means we won't lose a previous true.
						}
						catch (MLNreductionProblemTooLargeException e) {
							if (firstException == null) { firstException = e; }
						}
					}
					if (countOfNegLitsLeft > 0 && doNegLitsFirst) { continue; } // if CWA=true, focus on negative literals first, since they reduce more.
					if (doneWithThisClause.contains(clause))                      { continue; }
					if (debugLevel > 1 && countOfPosLitsLeft > 0) { Utils.println("%    PosLitsThisArity = " + posLitsThisArity); }
					if (posLitsThisArity != null) for (Literal posLit : posLitsThisArity) {
						if (doneWithThisClause.contains(clause))                  { continue; } // TODO - add a THROW to handle DONE?
						if (!literalsStillToReduce.get(clause).contains(posLit))  { continue; }
						try {
							madeUpdate = (considerThisLiteralForReduction(clause, posLit, true, currentArity, onlyOneChoiceLeft, bestLiteralInfo, (inFinalPassToReduceLargeCases  ? determineLargestAcceptableSizeForPoorReductionLiterals(numberOfRejections.get(clause)) : 0)) || madeUpdate); // Correct for the number of rejections on the first pass for this clause.
						}
						catch (MLNreductionProblemTooLargeException e) {
							if (firstException == null) { firstException = e; }
						}	
					}
				}
				if (doneWithThisClause.contains(clause))                         { continue; }
				if (debugLevel > 1) { Utils.println(      "\n%   Done processing, in cycle #" + Utils.comma(counterForOuterWhileLoop) + ", clause #" + Utils.comma(clauseToIndex.get(clause)) + ": '" + clause.toString(Integer.MAX_VALUE) + "'."); }
				if (bestLiteralInfo.bestReduction > 0.0) {
					if (!literalsStillToReduce.get(clause).contains(bestLiteralInfo.bestLiteral))  { Utils.error("Literal already reduced, so cannot be the best literal to reduce! " + bestLiteralInfo.bestLiteral); }
					if (debugLevel > 0) { Utils.println(    "%   Best literal to factor out is " + wrapLiteral(clause, bestLiteralInfo.bestLiteral) + ", which has a reduction of " + Utils.truncate(100 * bestLiteralInfo.bestReduction, 2) + "%."); }
					// Next account for the combinations 'skipped' when using the best reduction.
					updateNumberOfTRUEsForClause(clause, bestLiteralInfo.bestLiteral, bestLiteralInfo.bestSign, bestLiteralInfo.numberReduced);
					// Finally, create a new aggregated ("joint") variable that collects all the remaining possibilities for the variables in the bestLiteral.
					createAggregateVariable(clause, bestLiteralInfo.bestLiteral, bestLiteralInfo.bestSign, bestLiteralInfo.bestDenominator - bestLiteralInfo.numberReduced);										
					// Update the lists of variables.  TODO be sure that all changes are accounted for.
					// updateConstantCounts(clause);
					if (debugLevel > 0 && bestLiteralInfo.numberUnknown > 0) { Utils.println("%   Need to keep " + wrapLiteral(clause, bestLiteralInfo.bestLiteral) + " because it has " + Utils.comma(bestLiteralInfo.numberUnknown) + " groundings with unknown truth value."); }
					if (bestLiteralInfo.bestSign) { if (--countOfPosLitsLeft < 0) { Utils.error("countOfPosLitsLeft has become negative!"); } }
					else                          { if (--countOfNegLitsLeft < 0) { Utils.error("countOfNegLitsLeft has become negative!"); } }
					// Do these last in case this means we're done with the clause.
					if (bestLiteralInfo.numberUnknown == 0) { // Note: if a literal is never true or always true, it will not reach here and become the best literal (it will have been directly dealt with by considerThisLiteralForReduction). 
						if (debugLevel > 0) { Utils.println("%   Can remove " + wrapLiteral(clause, bestLiteralInfo.bestLiteral) + " from this clause since it has no groundings with unknown truth value."); }
						noLongerNeedToKeepThisLiteral(clause, bestLiteralInfo.bestLiteral);
					} else { recordLiteralHasBeenReduced(clause, bestLiteralInfo.bestLiteral); }
				} else if (firstException != null) {
					throw firstException;
				} else if (!madeUpdate && !doneWithThisClause.contains(clause)) {
					if (inFinalPassToReduceLargeCases || literalsRejectedForReduction.get(clause).isEmpty()) {
						if (debugLevel > 0) { Utils.println(    "%   DONE: Did not find any reduction for '" + clause + "'."); }
						recordDoneWithThisClause(clause);
					} else { // I (JWS) no longer recall why a second pass would be any different than taking the best reduction on the first pass ...
						if (debugLevel > 0) { Utils.println(    "%   Did not find any reduction, but try " + literalsRejectedForReduction.get(clause) + " for '" + clause + "'."); }
						//Utils.waitHere("clause = " + clause);
						inFinalPassToReduceLargeCases = true;  // Try again, reducing any that have been delayed.
						numberOfRejections.put(clause, literalsRejectedForReduction.size());
						literalsRejectedForReduction.get(clause).clear(); // Give all the literals one more chance (this time using maxSizeReduceRegardless).
					}
				}
			}
		} catch (MLNreductionProblemTooLargeException e) {
			if (debugLevel > 0) { Utils.println("% Throwing a problem-too-large exception: clause #" + Utils.comma(clauseToIndex.get(clause)) + ": " + e + " '" + clause + "'."); }
			errorThrownOnTheseClauses.add(clause);
			numberOfClausesToAnalyze--;
			continue;
		}
	}
	
	private double determineLargestAcceptableSizeForPoorReductionLiterals(Integer rejectionCount) {
		if (rejectionCount == null) { return 10; } // Should never matter here, but leave in to be safe.
		return Math.max(10, Math.pow(maxSizeReduceRegardless, 1 / Math.max(1, rejectionCount / 2))); // Account for there being multiple rejected literals, so there impact will multiply.
	}
	
	private String getSolvedAtString(Clause clause) {	
		Integer solvedAt = cycle_when_solved.get(clause);
		if (solvedAt == null || solvedAt < 0) { return "[never solved]"; }
		String solvedAtString = "[solved in";
		if (solvedAt >= 1000) { solvedAtString += " trial #" +  (solvedAt / 1000) + ","; }
		return solvedAtString += " cycle #" + (solvedAt % 1000) + "]";		
	}
	
	private void reportFinalStatistics() {
		if (false) return; // In case we want to turn this off.
		Set<Clause> consistencyChecked = new HashSet<Clause>(4);
		if (debugLevel > 0 || Utils.getSizeSafely(allClauses) < 25)
			for (Clause clause : allClauses) { if (countOfPossibleGroundings.get(clause) > minNumberOfGroundingsToReportStats) {	
			Utils.println("\n% Results " + getSolvedAtString(clause) + " for clause #" + Utils.comma(clauseToIndex.get(clause)) + ": '" + clause.toString(Integer.MAX_VALUE) + "'.");
			Utils.println(  "%     Number of possible groundings:   " + Utils.truncPad(countOfPossibleGroundings.get(clause),     0, 15) + ".");
			Utils.println(  "%     Count of TRUEs:                  " + Utils.truncPad(countOfTRUEs.get(clause),                  0, 15) + ".");
			Utils.println(  "%     Count of FALSEs:                 " + Utils.truncPad(countOfFALSEs.get(clause),                 0, 15) + ".");
			Utils.println(  "%     Count of SATISFIABLEs:           " + Utils.truncPad(countOfSatisfiableGndClauses.get(clause),  0, 15) + ".");
			if (countOfSatisfiableGndClauses.get(clause) > 0 && multiplierPerSatisfiedClause.get(clause) > 1) {
			  Utils.println("%     Multiplier per satisfying state: " + Utils.truncPad(multiplierPerSatisfiedClause.get(clause),  0, 15) + ".");
			 // Utils.waitHere("xyz");
			}
			Utils.println(  "%     Largest storage of groundings:   " + Utils.truncPad(largestSizeOfStoredGroundings.get(clause), 0, 15) + ".");
			Utils.println(  "%     Largest |cross product|:         " + Utils.truncPad(largestCrossProductCreated.get(clause),    0, 15) + ".");
			if (totalLiteralGroundingsConsidered.get(clause) > 0) {
				Utils.println("%     Total groundings evaluated:      " + Utils.padLeft(totalLiteralGroundingsConsidered.get(clause),  15) + ".");
				if (clause.posLiterals != null) for (Literal posLit : clause.posLiterals) {
					Utils.println("%      " + Utils.padLeft(totalLiteralGroundingsConsideredThisLiteral.get(clause).get(posLit), 15) + " for:  " + posLit);
				}
				if (clause.negLiterals != null) for (Literal negLit : clause.negLiterals) {
					Utils.println("%      " + Utils.padLeft(totalLiteralGroundingsConsideredThisLiteral.get(clause).get(negLit), 15) + " for: ~"  + negLit);
				}
			}
			if (countOfSatisfiableGndClauses.get(clause) > 0) {
				if (Utils.getSizeSafely(literalsToKeep.get(clause)) > 0) {
					Utils.println(  "%     Literals remaining:");
					for (Literal lit : literalsToKeep.get(clause)) { Utils.println(              "%        " + (clause.getSign(lit) ? " " : "~") + lit); } // Account for the leading '~'.	
				}
				if (Utils.getSizeSafely(literalsRejectedForReduction.get(clause)) > 0) {
					Utils.println(  "%     Literals rejected for reduction:");
					for (Literal lit : literalsRejectedForReduction.get(clause)) { Utils.println("%        " + (clause.getSign(lit) ? " " : "~") + lit); } // Account for the leading '~'.	
				}
				if (Utils.getSizeSafely(literalsStillToReduce.get(clause)) > 0) {
					Utils.println(  "%     Literals still to reduce:");
					for (Literal lit : literalsStillToReduce.get(clause)) { Utils.println(       "%        " + (clause.getSign(lit) ? " " : "~") + lit); } // Account for the leading '~'.	
				}
				if (Utils.getSizeSafely(variablesRemainingInClause.get(clause)) > 0) {
					Utils.println(  "%     Remaining variables: " + variablesRemainingInClause.get(clause));
				}
				if (Utils.getSizeSafely(accountedForVariables.get(clause)) > 0) {
					Utils.println(  "%     Accounted for variables: " + accountedForVariables.get(clause));
				}
				Set<AggVar> aggVarsSeen = new HashSet<AggVar>(4);
				boolean lookingForFirst = true;
				for (Variable var : variablesInClause.get(clause)) {
					VariableIndexPair pair = aggregatorMap.get(clause).get(var);
					
					if (pair != null && ! aggVarsSeen.contains(pair.aggVar)) {
						if (lookingForFirst) { Utils.println(  "%     Aggregated variables remaining:"); lookingForFirst = false; }
						Utils.println("%          " + pair.aggVar);
						aggVarsSeen.add(pair.aggVar);
					}
				}
				reportRemainingConstantsOfRemainingVariables(clause);
			}
			if (!consistencyChecked.contains(clause)) {
				checkAnswerConsistency(clause);
				consistencyChecked.add(clause);
			}
		}} else if (false) for (Clause clause : allClauses) if (countOfFALSEs.get(clause) > 0 || countOfSatisfiableGndClauses.get(clause) > 0) {
			Utils.println("\n% Results " + getSolvedAtString(clause) + " for clause #" + Utils.comma(clauseToIndex.get(clause)) + ": '" + clause.toString(Integer.MAX_VALUE) + "'.");
			Utils.println(  "%     Number of possible groundings:   " + Utils.truncPad(countOfPossibleGroundings.get(clause),        0, 15) + "."); // TODO add commas here!
			Utils.println(  "%     Count of TRUEs:                  " + Utils.truncPad(countOfTRUEs.get(clause),                  0, 15) + ".");
			Utils.println(  "%     Count of FALSEs:                 " + Utils.truncPad(countOfFALSEs.get(clause),                 0, 15) + ".");
			Utils.println(  "%     Count of SATISFIABLEs:           " + Utils.truncPad(countOfSatisfiableGndClauses.get(clause),  0, 15) + ".");
			if (countOfSatisfiableGndClauses.get(clause) > 0 && multiplierPerSatisfiedClause.get(clause) > 1) {
			  Utils.println("%     Multiplier per satisfying state: " + Utils.truncPad(multiplierPerSatisfiedClause.get(clause),  0, 15) + ".");
			}
			if (true || countOfSatisfiableGndClauses.get(clause) > 0) {
				if (Utils.getSizeSafely(literalsToKeep.get(clause)) > 0) {
					Utils.println(  "%     Literals remaining:");
					for (Literal lit : literalsToKeep.get(clause)) { Utils.println(              "%        " + (clause.getSign(lit) ? " " : "~") + lit); } // Account for the leading '~'.	
				}
				if (Utils.getSizeSafely(literalsRejectedForReduction.get(clause)) > 0) {
					Utils.println(  "%     Literals rejected for reduction:");
					for (Literal lit : literalsRejectedForReduction.get(clause)) { Utils.println("%        " + (clause.getSign(lit) ? " " : "~") + lit); } // Account for the leading '~'.	
				}
				if (Utils.getSizeSafely(literalsStillToReduce.get(clause)) > 0) {
					Utils.println(  "%     Literals still to reduce:");
					for (Literal lit : literalsStillToReduce.get(clause)) { Utils.println(       "%        " + (clause.getSign(lit) ? " " : "~") + lit); } // Account for the leading '~'.	
				}
				if (Utils.getSizeSafely(variablesRemainingInClause.get(clause)) > 0) {
					Utils.println(  "%     Remaining variables: " + variablesRemainingInClause.get(clause));
				}
				reportRemainingConstantsOfRemainingVariables(clause);
			} //Utils.waitHere("123");	
			if (!consistencyChecked.contains(clause)) {
				checkAnswerConsistency(clause);
				consistencyChecked.add(clause);
			}
		}
		
		if (createScatterPlots) {
			String fileName = (task.workingDirectory == null ? "" : task.workingDirectory) + "logOfNumberOfGroundingsScatterPlot.csv";
		    try {
		    	CondorFileOutputStream    outStream = new CondorFileOutputStream(fileName);
		    	PrintStream scatterPlotStream = new PrintStream(outStream, false); // No auto-flush (can slow down code).
		    	for (Clause clause : allClauses)  {	// Report the scatter plots on size of groundings.countOfSatisfiableGndClauses\
		    		if (countOfPossibleGroundings.get(clause) <  countOfSatisfiableGndClauses.get(clause)) {
		    			Utils.error("More satisfiable groundings than possible ones! " + Utils.truncate(countOfSatisfiableGndClauses.get(clause), 2) + " vs " + Utils.truncate(countOfPossibleGroundings.get(clause), 2));
		    		}
		    		scatterPlotStream.println(noisyLog10toString(countOfPossibleGroundings.get(   clause), 0.0) + ", " + 
		    				                  noisyLog10toString(countOfSatisfiableGndClauses.get(clause), 0.0));
    			}
		    	scatterPlotStream.close();
		    } catch (FileNotFoundException e) {
		    	Utils.error("Unable to successfully open this file for writing: " + fileName + ".  Error message: " + e.getMessage());
		    }
        }

		int size = Utils.getSizeSafely(allClauses);
		totalCountOfPossibleGroundings   = 0.0; // These are 'global' to this instance.
		totalNumberOfGroundingsRemaining = 0.0;
		maxNumberOfGroundings            = 0.0;
		maxNumberOfGroundingsRemaining   = 0.0;
		if (size > 0) {
			ClauseSortComparator clauseSorter = new ClauseSortComparator();			
			List<WrappedClause>  wrappedForSortingMostBefore = new ArrayList<WrappedClause>(allClauses.size());
			List<WrappedClause>  wrappedForSortingMostAfter  = new ArrayList<WrappedClause>(allClauses.size());
			for (Clause c : allClauses) { wrappedForSortingMostBefore.add(new WrappedClause(c, clauseToIndex.get(c), countOfPossibleGroundings.get(c), -1));    }
			for (Clause c : allClauses) { wrappedForSortingMostAfter.add( new WrappedClause(c, clauseToIndex.get(c), -1, countOfSatisfiableGndClauses.get(c))); }
			Collections.sort(wrappedForSortingMostBefore, clauseSorter);
			Collections.sort(wrappedForSortingMostAfter,  clauseSorter);
			Collections.reverse(wrappedForSortingMostBefore); // Sorting is from SMALLEST to LARGEST, so we want to reverse here.
			Collections.reverse(wrappedForSortingMostAfter);
						
			Utils.println("");
			double totalGroundingsConsidered = 0.0; // These are not 'global' to this instance, but maybe should be.
			double totalMaxStorage           = 0.0;
			for (Clause clause : allClauses) {
				totalCountOfPossibleGroundings   += countOfPossibleGroundings.get(clause);
				totalNumberOfGroundingsRemaining += countOfSatisfiableGndClauses.get(clause);
				totalGroundingsConsidered        += totalLiteralGroundingsConsidered.get(clause);
				totalMaxStorage                  += largestSizeOfStoredGroundings.get(clause);
				
				if (countOfSatisfiableGndClauses.get(clause) > warnIfNumberOfGroundingsExceedsThis) {
					if (task.warningCount < MLN_Task.maxWarnings) { Utils.println("% MLN WARNING #" + Utils.comma(++task.warningCount) + ": there are " + Utils.truncate(countOfSatisfiableGndClauses.get(clause), 0) + " groundings, even after reduction, of '" + clause + "'."); }
				}
				// Redo this as a double check on the above.
				if (countOfPossibleGroundings.get(clause) > maxNumberOfGroundings) {
					maxNumberOfGroundings = countOfPossibleGroundings.get(clause);
				}
				if (countOfSatisfiableGndClauses.get(clause) > maxNumberOfGroundingsRemaining) {
					maxNumberOfGroundingsRemaining = countOfSatisfiableGndClauses.get(clause);
				}
				if (!consistencyChecked.contains(clause)) {
					checkAnswerConsistency(clause);
					consistencyChecked.add(clause);
				}
			}
			if (maxNumberOfGroundings != wrappedForSortingMostBefore.get(0).countOfPossibleGroundings) {
				Utils.error("Mismatch: " + Utils.comma(maxNumberOfGroundings) + " vs " + Utils.comma(wrappedForSortingMostBefore.get(0).countOfPossibleGroundings));
			}
			if (maxNumberOfGroundingsRemaining != wrappedForSortingMostAfter.get(0).countOfRemainingGroundings) {
				Utils.error("Mismatch: " + Utils.comma(maxNumberOfGroundingsRemaining) + " vs " + Utils.comma(wrappedForSortingMostAfter.get(0).countOfPossibleGroundings));
			}
			
			int counter = 0;  int maxToReport = 25; Utils.println("% Largest " + maxToReport + " clauses:");
			for (WrappedClause wc : wrappedForSortingMostBefore) { Utils.println("%  BEFORE #" + (counter+1) + ": " + wc);  if (++counter >= maxToReport) break; }
			counter = 0; Utils.println("");
			for (WrappedClause wc : wrappedForSortingMostAfter)  { Utils.println("%  AFTER #"  + (counter+1) + ":  " + wc); if (++counter >= maxToReport) break; }

			int k = 0;
			for (WrappedClause wc : wrappedForSortingMostAfter) if (wc.countOfRemainingGroundings > maxNonLazyGroundingsPerClause) {
				Utils.println("% Clause too hard, will require 'lazy' inferencing: " + wc);
				k++;
			}
			if (k < 1) { k = 1; }
			double totalGroundingsMinusTopK           = totalCountOfPossibleGroundings;
			double totalRemainingMinusTopK            = totalNumberOfGroundingsRemaining;
			double totalGroundingsConsideredMinusTopK = totalGroundingsConsidered;
			for (int i = 0; i < k; i++) {
				Clause clauseIbefore = wrappedForSortingMostBefore.get(i).clause;
				Clause clauseIafter  = wrappedForSortingMostAfter.get(i).clause;
				Utils.println("\n% #" + (i+1) + " largest 'before' is clause #" + Utils.comma(clauseToIndex.get(clauseIbefore)) + ": (" + Utils.truncate(countOfPossibleGroundings.get(clauseIbefore), 0) + " -> " + Utils.truncate(countOfSatisfiableGndClauses.get(clauseIbefore), 0) + ") '" + clauseIbefore.toString(Integer.MAX_VALUE));
				Utils.println(  "% #" + (i+1) + " largest 'after'  is clause #" + Utils.comma(clauseToIndex.get(clauseIafter))  + ": (" + Utils.truncate(countOfPossibleGroundings.get(clauseIafter),  0) + " -> " + Utils.truncate(countOfSatisfiableGndClauses.get(clauseIafter),  0) + ") '" + clauseIafter.toString( Integer.MAX_VALUE));
				totalGroundingsMinusTopK                  -= countOfPossibleGroundings.get(       clauseIafter); // Drop the HARDEST AFTER.
				totalRemainingMinusTopK                   -= countOfSatisfiableGndClauses.get(    clauseIafter);
				totalGroundingsConsideredMinusTopK -= totalLiteralGroundingsConsidered.get(clauseIafter);
			}

			if (debugLevel > -10 || true) {
				Utils.println(    "\n% Total groundings:              " + Utils.truncPad(totalCountOfPossibleGroundings,      0, 14) + " over " + size + " clauses (out of " + task.allClauses.size() + ") in the current task.");
				Utils.println(      "%   w/o hardest " + k + ":               " + Utils.truncPad(totalGroundingsMinusTopK,      0, 14));
				Utils.println(      "% Total groundings considered:   " + Utils.truncPad(totalGroundingsConsidered,           0, 14));
				Utils.println(      "%   w/o hardest " + k + ":               " + Utils.truncPad(totalGroundingsConsideredMinusTopK, 0, 14));
				Utils.println(      "% Total remaining groundings:    " + Utils.truncPad(totalNumberOfGroundingsRemaining,    0, 14));
				Utils.println(      "%   w/o hardest " + k + ":               " + Utils.truncPad(totalRemainingMinusTopK,       0, 14));
				Utils.println(      "% Speedup:                       " + Utils.truncPad(totalCountOfPossibleGroundings / totalGroundingsConsidered,          3, 18));
				Utils.println(      "%   w/o hardest " + k + ":               " + Utils.truncPad(totalGroundingsMinusTopK / totalGroundingsConsideredMinusTopK, 3, 18));
				Utils.println(      "% Shrinkage:                     " + Utils.truncPad(totalCountOfPossibleGroundings / totalNumberOfGroundingsRemaining,   3, 18));
				Utils.println(      "%   w/o hardest " + k + ":               " + Utils.truncPad(totalGroundingsMinusTopK / totalRemainingMinusTopK,            3, 18));
				Utils.println(    "\n% Most per-clause bindings:      " + Utils.truncPad(maxNumberOfGroundings,               0, 14));
				Utils.println(      "% Most per-clause bindings left: " + Utils.truncPad(maxNumberOfGroundingsRemaining,      0, 14));
				if (size > 1) {
					Utils.println("\n% Average groundings:            " + Utils.truncPad(totalCountOfPossibleGroundings/size, 3, 18)); // Add 4 (3 decimals plus decimal point).
					Utils.println(  "% Average groundings considered: " + Utils.truncPad(totalGroundingsConsidered/size,      3, 18));
					Utils.println(  "% Average max storage needed:    " + Utils.truncPad(totalMaxStorage/size,                3, 18));
				} else {
					Utils.println("\n% Maximum storage needed:        " + Utils.truncPad(totalMaxStorage,                     0, 14));
				}
			}
			/*
			if (totalNumberOfGroundingsRemaining > maxTotalNumberOfRemainingGroundings) {
				throw new MLNreductionProblemTooLargeException(debugLevel > 1 ? " ***** Problem too large: totalNumberOfGroundingsRemaining > maxTotalNumberOfRemainingGroundings ("
																			+ Utils.truncate(totalNumberOfGroundingsRemaining,    0) + " > " 
																			+ Utils.truncate(maxTotalNumberOfRemainingGroundings, 0) + ")" : null);
			}
			*/
		}
	}
	
	// Since so many clause will have the same number of possible groundings, add some noise to these points to reduce the overlap.
	private String noisyLog10toString(double value, double offset) {
		double noise = (2 * Utils.random() - 1) * offset;
		return Utils.truncateNoSciNotation(noise + Math.log10(Math.max(1, value)), 3);
	}
	
	public Collection<Clause> getAllClausesThatWereGrounded() {
		return allClauses;
	}

	private void checkAnswerConsistency(Clause clause) {
		// Check that all groundings accounted for in one pot or another.
		double total  = countOfPossibleGroundings.get(clause);
		double trues  = countOfTRUEs.get(clause);
		double falses = countOfFALSEs.get(clause);
		double sats   = countOfSatisfiableGndClauses.get(clause);
		double mult   = multiplierPerSatisfiedClause.get(clause);
		
		if (Utils.diffDoubles(total, trues + falses + sats * mult)) {
			Utils.error("Should have total = " + Utils.truncate(total, 0) + " = trues + falses + (sats * mult) = " 
							+ Utils.truncate(trues + falses + sats * mult, 0) + ".   Gap = " + Utils.truncate(total - (trues + falses + sats * mult), 0) + " clause: " + clause);
		}
	}
	
	private boolean considerThisLiteralForReduction(Clause clause, Literal lit, boolean pos, int currentArity, boolean forceCollectionOfRemainingGroundings, BestLiteralInfo bestLiteralInto, double maxSizeToReduceRegardless) throws MLNreductionProblemTooLargeException {
		CacheLiteralGrounding cache = countLiteralGroundings(clause, lit, pos, null, forceCollectionOfRemainingGroundings);
		long posCount    = cache.trueCount;
		long negCount    = cache.falseCount;
		long unkCount    = cache.unknownCount;
		long goodCount   = (pos ? posCount : negCount);
		long badCount    = (pos ? negCount : posCount) + unkCount;
		long denominator = posCount + negCount + unkCount;
		
		if (debugLevel > 0) { Utils.print("%         Stats: #sat =" + Utils.padLeft(goodCount, 9) + ", #unsat =" + Utils.padLeft((pos ? negCount : posCount), 9) + ", #unknown =" + Utils.padLeft(unkCount, 9) + " for " + wrapLiteral(clause, lit)); }
		if (badCount == 0) { // Have satisfied all remaining groundings.
			if (debugLevel > 0) { Utils.println("."); }
			clauseAlwaysTrue(clause, lit);
			return true;  // Since done with clause, doesn't matter what is returned here.
		} else if (goodCount < 1 && unkCount < 1) { // Can remove this literal since it NEVER will be true.
			if (debugLevel > 0) { Utils.println(".  REMOVE! This literal will never be true."); }
			// Note: might have dropped the only literal of a given arity, but not worth the trouble to fix the minimum and maximum values (in the method that calls this one).
			noLongerNeedToKeepThisLiteral(clause, lit);
			return true; // Report that something was updated for this clause.
		} else if (unkCount == denominator) {
			if (debugLevel > 0) { Utils.println("\n%   Will no longer consider reducing " + wrapLiteral(clause, lit) + " because all of its groundings are satisfiable."); }
			noLongerConsiderThisLiteral(clause, lit);	
			return false;
		} else {
			double reduction = goodCount / (double)denominator;			
			//if (reduction < 0.0000001) { Utils.println("% Tiny reduction: " + lit + " in " + clause); }			
			if (reduction < 0.0000001 || (reduction < minimumReduction && badCount > maxSizeToReduceRegardless)) { // (badCount / denominator) > maxSizeToReduceRegardless)) { // If reduction is not much, simply keep this literal.  TODO - should we consider it again, say if some of its variables change?
				if (debugLevel > 1) { Utils.println("\n% Will no longer consider reducing " + wrapLiteral(clause, lit) 
														+ " because its reduction (" + Utils.truncate(100 * reduction, 2) + "%) is less than the minimum (" 
														+ Utils.truncate(100 * minimumReduction, 2) + "%) and its new size (" + Utils.truncate(badCount, 0) + ") will be larger than " + Utils.truncate(maxSizeToReduceRegardless, 0) + "."); }
				//noLongerConsiderThisLiteral(clause, lit);
				literalsRejectedForReduction.get(clause).add(lit);
				return false;
			}
			
			if (debugLevel > 1) { Utils.print(".  Reduction: " + Utils.comma(goodCount )+ "/" + Utils.comma(denominator) + " = " + Utils.truncate(100 * reduction, 2) + "%"); }
			if (reduction > 0 && chooseReductionOrderRandomly) { reduction = Utils.random(); } 
			if (reduction > bestLiteralInto.bestReduction) {
				bestLiteralInto.bestReduction    = reduction;
				bestLiteralInto.bestLiteral      = lit; 
				bestLiteralInto.bestSign         = pos;
				bestLiteralInto.bestLiteralArity = currentArity;
				bestLiteralInto.numberReduced    = goodCount;
				bestLiteralInto.numberUnknown    = unkCount;
				bestLiteralInto.bestDenominator  = denominator;
				if (debugLevel > 0) { Utils.println(" [new best]."); } // Mark this is a new best.
				return true; // Updated best.
			}
			if (debugLevel > 0) { Utils.println("."); }
			return false;
		}
	}
	
	// Reduced literals, that were not discarded because the were satisfiable for some groundings, need to be checked
	// again at the end, to see if any satisfiable groundings still remain.
	private void doFinalCheckOfRemainingLiterals(Clause clause) {
		for (Iterator<Literal> iter = literalsToKeep.get(clause).iterator(); iter.hasNext(); ) {
			Literal lit = iter.next();
			if (isAlwaysQuery( clause, lit)) { continue; } // These should remain, so all is fine.
			if (isAlwaysHidden(clause, lit)) { continue; } // Ditto.
			if (isAlwaysTrue(  clause, lit)) { Utils.error("Should not happen: " + wrapLiteral(clause, lit) + " in " + clause); }
			if (isAlwaysFalse( clause, lit)) { Utils.error("Should not happen: " + wrapLiteral(clause, lit) + " in " + clause); }
			CacheLiteralGrounding result = null;
			try {
				boolean   pos = clause.getSign(lit); 
				result        = countLiteralGroundings(clause, lit, pos, null, false);
				long trues    = result.trueCount;
				long falses   = result.falseCount;
				long unknowns = result.unknownCount;  
				if (debugLevel > 2) { result.describeCache(lit.toString(Integer.MAX_VALUE)); } // Since counts ignore sign, print that way as well.
				if ( pos && trues  > 0) { Utils.warning("Should not have any cases of " + wrapLiteral(clause, lit) + " = true here.");  }
				if (!pos && falses > 0) { Utils.warning("Should not have any cases of " + wrapLiteral(clause, lit) + " = false here."); }
				if (unknowns == 0) {
					if (debugLevel > 0) { Utils.println("%      Can remove " + wrapLiteral(clause, lit) + " from consideration since it no longer has any satisfiable bindings.  Clause #" + Utils.comma(clauseToIndex.get(clause)) + ": '" + clause + "'."); }
					// result.describeCache("countLiteralGroundings");
					// Utils.error("Can this happen?  lit = " + wrapLiteral(clause, lit) + " clause = " + clause);
					// TVK  Dont remove the literal as this just means that the reduction was not enough.
					// iter.remove();
				}
			} catch (MLNreductionProblemTooLargeException e) {
				// If too large, ???
				continue; // For now, just continue and deal with this later.
			}
			if (result == null) { Utils.error("Could not find any groundings for " + wrapLiteral(clause, lit) + " in clause '" + clause + "'."); }
			litsToConstantsMap.get(clause).put(lit, result);
			
		}
	}
	
	// Get rid of data structures not needed, especially long lists and large sets.  
	// If any groundings left:
	//      if literals left, then the remaining groundings go into SATISFIABLE (those remaining variables not in a literal left are aggregated into a multiplier for the satisfiables) 
	//	    otherwise the remaining grounds go into count of FALSEs (but we still need to know WHICH groundings make it false, so we keep these explicitly).
	private void doFinalCleanup(Clause clause) {
		if (debugLevel > 0) { Utils.println("\n%   Doing a final 'cleaning' of the information collected for clause #" + Utils.comma(clauseToIndex.get(clause)) + ": '" + clause + "'."); }
		countCurrentCombinatorics(clause); // Do this at the end in case missed earlier due to completing a clause.
		doFinalCheckOfRemainingLiterals(clause);
		
		for (Literal lit : litsToConstantsMap.get(clause).keySet()) {
			CacheLiteralGrounding cache = litsToConstantsMap.get(clause).get(lit);
			if (debugLevel > 0) { if (cache != null) { Utils.println("%   For " + wrapLiteral(clause, lit) + " still storing " + Utils.comma(cache.getGroundingsStillNeeded(false)) + " ground literals."); }
								  else               { Utils.println("%   For " + wrapLiteral(clause, lit) + " no literal groundings are cached."); }}
			litsToConstantsMap.get(clause).put(lit, null); // Do NOT clear here, since this might be shared.
		}
		
		for (Variable var : varsToConstantsMap.get(clause).keySet()) {
			Set<Term> setOfConstants = varsToConstantsMap.get(clause).get(var);
			if (debugLevel > 0) { if (setOfConstants != null) { Utils.println("%   For '" + var + "' still storing " + Utils.comma(setOfConstants) + " constants."); }
							      else                        { Utils.println("%   For '" + var + "' no constants are cached."); }}
			if (aggregatorMap.get(clause).get(var) != null) {
				 varsToConstantsMap.get(clause).put(var, null); // Do NOT clear here, since this might be shared.
			}
		}
		for (AggVar aggVar : aggVarsToAggregatedConstantsMap.get(clause).keySet()) {
			List<List<Term>> setOfConstants = aggVarsToAggregatedConstantsMap.get(clause).get(aggVar);
			if (debugLevel > 0) { if (setOfConstants != null) { Utils.println("%   For '" + aggVar + "' still storing " + Utils.comma(setOfConstants) + " aggregated constants."); }
							      else                        { Utils.println("%   For '" + aggVar + "' no constants are cached."); }}
		}

		Collection<Variable>              varsInClause    = variablesInClause.get( clause);
		Map<Variable,VariableIndexPair>   aggregators     = aggregatorMap.get(     clause);
		Map<Variable,Set<Term>>       oldConstants    = varsToConstantsMap.get(clause);
		Map<AggVar, List<List<Term>>> aggsToConstants = aggVarsToAggregatedConstantsMap.get(clause);
		Set<Literal>                      litsSurviving   = literalsToKeep.get(clause);
		Map<Literal,List<Variable>>       theFreeVars     = freeVarsMap.get(clause);
		double                countOfRemainingCombinations = -1.0;
		if (countOfSatisfiableGndClauses.get(clause) < 1) { // No need to keep anything other than the counts if no satisfiable groundings.
			removePointersToConstants(clause);
		} else {
			Collection<Variable> varsThatMustBeKept    = null;
			Collection<AggVar>   aggVarsThatMustBeKept = null;
			if (litsSurviving != null) for (Literal lit : litsSurviving) { // First find which variables and aggregated variables appear in surviving literals.
				Collection<Variable> freeVars = theFreeVars.get(lit);
				if (debugLevel > 1) { Utils.println("%   Free variables = " + freeVars + " for remaining literal '" + lit + "'."); }
				if (freeVars != null) for (Variable var : freeVars) {
					VariableIndexPair currentOwnerOfVar = aggregators.get(var);
					if (currentOwnerOfVar == null) {
						if (varsThatMustBeKept    == null) { varsThatMustBeKept    = new HashSet<Variable>(4); }
						varsThatMustBeKept.add(var);
					} else {
						if (aggVarsThatMustBeKept == null) { aggVarsThatMustBeKept = new HashSet<AggVar>(  4); }
						aggVarsThatMustBeKept.add(currentOwnerOfVar.aggVar);
					}
				}
			}
			if (debugLevel > 1) { Utils.println("%    VarsThatMustBeKept    = " + varsThatMustBeKept);    }
			if (debugLevel > 1) { Utils.println("%    AggVarsThatMustBeKept = " + aggVarsThatMustBeKept); }
			
			// Now look for any other variables and aggregated variables that are still in the clause, but with no possibility of helping satisfy this clause.
			Collection<AggVar> aggregatorsUsed = null;
			if (varsInClause != null) for (Variable var : varsInClause) {
				VariableIndexPair currentOwnerOfVar = aggregators.get(var);
				if (currentOwnerOfVar == null) {
					if (varsThatMustBeKept == null || !varsThatMustBeKept.contains(var)) { 
						int numberOfCombinations = oldConstants.get(var).size();
						if (countOfRemainingCombinations < 0) { countOfRemainingCombinations = 1.0; }
						countOfRemainingCombinations *= numberOfCombinations;
						if (debugLevel > 0) { Utils.println("%    Removing basic variable '" + var + "' (and accounting for its " + numberOfCombinations + " combinations), because it does not appear in the literals that remain for this clause."); }
						if (debugLevel > 1) { Utils.println("%       Removing: " + Utils.limitLengthOfPrintedList(oldConstants.get(var), 25)); }
						if (clearListsOfConstantsAtEnd) { oldConstants.put(var, null); }
						// Need to record which variables have been 'factored out' since otherwise it will have a size of 0 and mess up any later calls to compute the size of the cross product.
						accountedForVariables.get(clause).add(var);
						// Utils.waitHere("cleaningUpRegVar '" + var + "'.");
					}
				} else if (aggregatorsUsed == null || !aggregatorsUsed.contains(currentOwnerOfVar.aggVar)) { // Don't double count aggregators.
					AggVar aggVar = currentOwnerOfVar.aggVar;
					if (aggVarsThatMustBeKept == null || !aggVarsThatMustBeKept.contains(aggVar)) { 
						int numberOfCombinations = aggsToConstants.get(aggVar).size(); 
						if (countOfRemainingCombinations < 0) { countOfRemainingCombinations = 1.0; }
						countOfRemainingCombinations *= numberOfCombinations;
						if (debugLevel > 0) { Utils.println("%    Removing aggregated variable '" + aggVar + "' (and accounting for its " + numberOfCombinations + " combinations), because it does not appear in the literals that remain for this clause."); }
						if (debugLevel > 1) { Utils.println("%       Removing: " + Utils.limitLengthOfPrintedList(aggsToConstants.get(aggVar), 25)); }
						if (clearListsOfConstantsAtEnd) { aggsToConstants.put(aggVar, null); }
						accountedForVariables.get(clause).add(var);
						Utils.waitHere("cleaningUpAggVar '" + aggVar + ".");
					}
					if (aggregatorsUsed == null) { aggregatorsUsed = new HashSet<AggVar>(4); }
					aggregatorsUsed.add(aggVar);
				}
			}
		}
		if (countOfRemainingCombinations > 0) {
			if (Utils.getSizeSafely(literalsToKeep.get(clause)) > 0) {
				if (multiplierPerSatisfiedClause.get(clause) != 1.0) { Utils.error("Expecting multiplierPerSatisfiedClause.get(clause) = 1.0 but got multiplierPerSatisfiedClause.get(clause)=" + multiplierPerSatisfiedClause.get(clause)); }
				multiplierPerSatisfiedClause.put(clause, multiplierPerSatisfiedClause.get(clause) * countOfRemainingCombinations);
				countOfSatisfiableGndClauses.put(clause, countOfSatisfiableGndClauses.get(clause) / countOfRemainingCombinations);
				if (debugLevel > 1) { Utils.println("%   Cleanup completed.  Found " + Utils.truncate(countOfRemainingCombinations, 0) 
													   + " combinations involving variables not appearing in any remaining literal, so they can be factored into a multiplier for each satisfiable ground among those remaining."); }
				// Utils.waitHere("locXYZ");
			} else {
				countOfSatisfiableGndClauses.put(clause, countOfSatisfiableGndClauses.get(clause) - countOfRemainingCombinations); // Need to remove these from here, since it currently includes the variable being accounted for.
				if (countOfSatisfiableGndClauses.get(clause) != 0.0) { Utils.error("Expecting countOfSatisfiableGndClauses.get(clause)=0 but got countOfSatisfiableGndClauses.get(clause)=" + Utils.truncate(countOfSatisfiableGndClauses.get(clause), 0)); }
				double oldFALSEs = countOfFALSEs.get(clause);
				countOfFALSEs.put(clause, oldFALSEs + countOfRemainingCombinations);
				if (debugLevel > 1) { Utils.println("%   Cleanup completed.  Found " + Utils.truncate(countOfRemainingCombinations, 0) 
												      + " combinations that do not satisfy the clause since there are no literals remaining (previously there had been " +  Utils.truncate(oldFALSEs, 0) + " false combinations)."); }
				// Utils.waitHere("locABC");
			}
		} else if (debugLevel > 1) { Utils.println("%   Cleanup completed."); }
		//if (debugLevel > 0) { Utils.println("% countCurrentCombinatorics = " + computeSizeOfVariableCrossProduct(clause, null)); }
		Set<Variable> remainingVariables = null;
		for (Literal lit : litsSurviving) {
			Collection<Variable> freeVars = freeVarsMap.get(clause).get(lit);
			if (Utils.getSizeSafely(freeVars) > 0) {
				if (remainingVariables == null) { remainingVariables = new HashSet<Variable>(4); }
				remainingVariables.addAll(freeVars);
			}						
		}
		variablesRemainingInClause.put(clause, remainingVariables);
		System.gc(); // Force a garbage collection.
	}
	
	private void updateNumberOfTRUEsForClause(Clause clause, Literal lit, boolean pos, long numberSatisfiedForLit) {
		Collection<Variable> variablesToSkip = freeVarsMap.get(clause).get(lit);
		double     currentCountOfTRUEs = countOfTRUEs.get(clause);
		if (debugLevel > 0) { Utils.print("%   Size of the space of 'covered' groundings [skipping " + variablesToSkip + "]"); }
		double sizeOfRemainingSpace = computeSizeOfVariableCrossProduct(clause, variablesToSkip);
		if (debugLevel > 0) { Utils.println(" = " + Utils.truncate(sizeOfRemainingSpace, 0) 
											+ (numberSatisfiedForLit > 1 ? ", which is " + (sizeOfRemainingSpace > 0 ? "multiplied by" : "added to") + " the " + Utils.comma(numberSatisfiedForLit) + " combinations eliminated, for a total of " + Utils.truncate(numberSatisfiedForLit * Math.max(1.0, sizeOfRemainingSpace), 0) + "." : ".")); }
		double countOfTRUEsHandledAtOnce  = numberSatisfiedForLit * Math.max(1.0, sizeOfRemainingSpace);  // If NO items left, then we should ADD the combinations eliminated, so we'll let this be at least 1.
		countOfTRUEs.put(clause, countOfTRUEsHandledAtOnce + currentCountOfTRUEs);
		double  satisfiablesCount =  multiplierPerSatisfiedClause.get(clause) * countOfSatisfiableGndClauses.get(clause);
		if (countOfTRUEsHandledAtOnce > satisfiablesCount) {
			Utils.error("Have somehow counted " + Utils.truncate(countOfTRUEsHandledAtOnce, 0) + " combinations, out of " + Utils.truncate(satisfiablesCount, 0) + " possibilities!");
		}
		if (debugLevel > 0) { Utils.println("%   Have counted " + Utils.truncate(countOfTRUEsHandledAtOnce, 0) + 
								" combinations, out of " + Utils.truncate(satisfiablesCount, 0) + 
								" possibilities, by using the best reducer (previously counted " + Utils.truncate(currentCountOfTRUEs, 0) + ")."); }
	}
	
	private Set<Term> extractItemNfromListsIntoList(List<List<Term>> items, int i) {
		if (items == null) { return null; }
		Set<Term> results = new HashSet<Term>(4);
		for (List<Term> list : items) { results.add(list.get(i)); }
		return results;
	}	
	
	/*
	 * Imagine we have  aggVar1 = {A,B,C} and aggVar2 = {W,X,Y}, plus the current literal has arguments = {A,J,K,X,Y,Z}.
	 * Need to produce:	aggVar3 = {A,B,C,W,X,Y,J,K,Z} whose size is |aggVar1| x |aggVar2| x |J| x |K| x {Z|.
	 * 
	 * Note: a complication is that we might need to carry along more variables than are in literaltoUse, hence the use of intersectingAggVars.
	 * 
	 */
	private void createAggregateVariable(Clause clause, Literal literalToUse, boolean pos, long numberOfKeepers) throws MLNreductionProblemTooLargeException {
		List<Variable> freeVars = freeVarsMap.get(clause).get(literalToUse);
		int numbVarsToCombine = Utils.getSizeSafely(freeVars);
		if (numbVarsToCombine <  1) { Utils.error("Should not be called with no variablesToCombine."); }		
		if (numbVarsToCombine == 1) { Utils.error("If only one variable, simply update that variables list of possible constants!"); }

		Set<AggVar> intersectingAggVars = null;
		for (Variable var : freeVars) {
			VariableIndexPair currentOwnerOfVar = aggregatorMap.get(clause).get(var); // Note: the new aggregator will not ADD any constants not already active, so no problem if we lose the pointer to the previous aggregator.
			if (currentOwnerOfVar != null) {
				if (debugLevel > 1) { Utils.println("%     Need to join with a previous aggregator: previously '" + var + "' was aggregated by position " + currentOwnerOfVar.index + " of " + currentOwnerOfVar.aggVar + "."); }
				if (intersectingAggVars == null) { intersectingAggVars = new HashSet<AggVar>(4); }
				intersectingAggVars.add(currentOwnerOfVar.aggVar); // Since a SET, will not add duplicates.
			}
		}
		if (intersectingAggVars != null) { 
			joinTheseAggregatedVariables(clause, literalToUse, pos, intersectingAggVars);
		} else {
			CacheLiteralGrounding cache = litsToConstantsMap.get(clause).get(literalToUse);
			if (cache == null)  { Utils.error("Something went wrong with the cache for clause #" + clauseToIndex.get(clause) + ": '" + clause + "'."); }
			
			List<List<Term>> groundings = cache.getGroundingsStillNeeded();
			if (numberOfKeepers != Utils.getSizeSafely(groundings)) { Utils.error("Should have numberOfKeepers = " + numberOfKeepers + " match bindingsToKeep.size() = " + groundings); }
			if (groundings == null)  { Utils.error("The cache has no groundings."); }  // If no groundings to keep, no need to merge.
			connectVariablesToAggregateVariable(clause, literalToUse, freeVars, groundings);	
		}
	}
	
	private AggVar connectVariablesToAggregateVariable(Clause clause, Literal lit, List<Variable> variablesToConnect, List<List<Term>> bindings) {
		clearAllLiteralCachesImpactedByTheseVariables(clause, lit, variablesToConnect); // Cached calculations for other literals involving these variables are now invalid.
		AggVar aggVar = new AggVar(variablesToConnect);	// Might have name conflicts, but won't be '==' conflicts.
		aggVarsToAggregatedConstantsMap.get(clause).put(aggVar, bindings); // Need this to look up the possible groundings for those of this literal's variables that appear in another literal.
		if (debugLevel > 1) { Utils.println("%           New aggregator '" + aggVar + "' has " + Utils.comma(bindings) + " groundings."); }
		for (Variable var : variablesToConnect) {
			int position = aggVar.getPosition(var);
			VariableIndexPair varIndexPair = new VariableIndexPair(aggVar, position);

			if (debugLevel > 2) { Utils.println("%               Variable '" + var + "' will be aggregated by position " + position + " of '" + aggVar + "'."); }
			// Do not clear the OLD holder of this variable's surviving constants.  That might be shared elsewhere, and if not, Java's garbage collector will deal with it.
			aggregatorMap.get(clause).put(var, varIndexPair);
		}	
		return aggVar;
	}	
	
	/*
	 * Imagine we have aggVar1 = {A,B,C} and aggVar2 = {W,X,Y}, plus the current literal has arguments = {A,J,K,X,Y,Z}.
	 * Need to produce:	aggVar3 = {A,B,C,W,X,Y,J,K,Z} whose size is |aggVar1| x |aggVar2| x |J| x |K| x {Z|.
	 * 
	 */
	private void joinTheseAggregatedVariables(Clause clause, Literal literalToUse, boolean pos, Set<AggVar> intersectingExistingAggVars) throws MLNreductionProblemTooLargeException {
		Collection<Variable> variablesToCombine = freeVarsMap.get(clause).get(literalToUse);
		if (debugLevel > 2) { Utils.println("%      JOIN: ********** Need to create a new aggregated variable for " + variablesToCombine + ", which will use these aggregated variables: " + intersectingExistingAggVars + "."); }
		List<Variable> fullSetOfVariables = new ArrayList<Variable>(variablesToCombine.size()); // Use a LIST so we know the order of items.
		
		// First collect all the variables in existing aggregators (seems more 'readable' that way).
		for (AggVar other : intersectingExistingAggVars) { 
			List<Variable>  otherAggVarVariables = other.varsCombined;
			for (Variable var : otherAggVarVariables) {
				if (fullSetOfVariables.contains(var)) { Utils.error("Should not have intersecting aggregate variables!"); } 
				fullSetOfVariables.add(var);
			}
		}
		
		// Now collect any variables in variablesToCombine that have not yet been aggregated.
		int varsToCombineSize = variablesToCombine.size(); // variablesToCombine should never be empty.
		for (Variable var : variablesToCombine) if (!fullSetOfVariables.contains(var)) { fullSetOfVariables.add(var); }
		if (debugLevel > 3) { Utils.println("%      ********** Full set of variables = " + fullSetOfVariables + "."); }
		
		int[] positionsOfArgumentsInLiteralToUse = new int[varsToCombineSize]; // Indicate where the variables for literalToUse are in the full list of variables.
		int   varCounter = 0;
		Set<Variable> foundThisVar = new HashSet<Variable>(4);
		if (debugLevel > 3) { Utils.print("%      ********** The map of the variables of " + wrapLiteral(clause, literalToUse) + " in the full-grounding vector is: "); }
		for (Variable var : variablesToCombine) if (!foundThisVar.contains(var)) {
			int location = fullSetOfVariables.indexOf(var);
			positionsOfArgumentsInLiteralToUse[varCounter++] = location;
			if (debugLevel > 3) { Utils.print("  " + var + " -> " + location); }
		}
		if (debugLevel > 3) { Utils.println("."); }		
		
		CacheLiteralGrounding result = createFullCrossProductFromTheseVariables(clause, literalToUse, pos, true, fullSetOfVariables, positionsOfArgumentsInLiteralToUse);
		litsToConstantsMap.get(clause).put(literalToUse, result);
		connectVariablesToAggregateVariable(clause, literalToUse, fullSetOfVariables, result.getGroundingsStillNeeded());

		for (AggVar oldAggVar : intersectingExistingAggVars) { aggVarsToAggregatedConstantsMap.get(clause).remove(oldAggVar); } // No longer need this old aggregated variable.
	}
	
	
	// See how many combinations there are using all variables in this clause's variable list EXCEPT those in the skipThese list.
	private double computeSizeOfVariableCrossProduct(Clause clause, Collection<Variable> skipThese) {
		Collection<Variable>             varsInClause     = variablesInClause.get(    clause);
		if (Utils.getSizeSafely(varsInClause) < 1) { return 1.0; } // If no variables, define the size to be 1.
		Collection<Variable>             accountedForVars = accountedForVariables.get(clause);
		Map<Variable,VariableIndexPair>  aggregators      = aggregatorMap.get(        clause);
		Map<Variable,Set<Term>>      oldConstants     = varsToConstantsMap.get(   clause);
		Collection<AggVar>               aggregatorsUsed  = null; // We only want to count the size of an aggregator ONCE.
		double                           oldLargestSize   = largestSizeOfStoredGroundings.get(clause);
		double                           result           = 1.0; // Cannot use int's since could overflow.
		double                           newSize          = 0.0;
		boolean                          returnZero       = true; // See if anything still exists for this clause.
		if (debugLevel > 1) { Utils.print(" = 1"); }
		if (varsInClause == null) { return 0.0; }
		for (Variable var : varsInClause) if (!accountedForVars.contains(var) && (skipThese == null || !skipThese.contains(var))) {
			VariableIndexPair currentOwnerOfVar = aggregators.get(var);
			if (currentOwnerOfVar == null) {
				int size = Utils.getSizeSafely(oldConstants.get(var));
				returnZero = false;
				result  *= size;
				newSize += size;
				if (debugLevel > 1) { Utils.print("x" + Utils.comma(size) + "[" + var + "]"); }
			} else if (skipThisAggregatedVariable(currentOwnerOfVar.aggVar, skipThese)) { 
				if (debugLevel > 1) { Utils.print("x1[" + currentOwnerOfVar.aggVar + "]"); }			
			} else if (aggregatorsUsed == null || !aggregatorsUsed.contains(currentOwnerOfVar.aggVar)) { // Don't double count aggregators.
				int size = Utils.getSizeSafely(aggVarsToAggregatedConstantsMap.get(clause).get(currentOwnerOfVar.aggVar));
				returnZero = false;
				result  *= size;
				newSize += size;
				if (debugLevel > 1) { Utils.print("x" + Utils.comma(size)+ "[" + currentOwnerOfVar.aggVar + "]"); }
				if (aggregatorsUsed == null) { aggregatorsUsed = new HashSet<AggVar>(4); }
				aggregatorsUsed.add(currentOwnerOfVar.aggVar);
			}
			if (result <= 0.0 && debugLevel <= 1) { break; }  // Continue to end only if printing sizes.
		}
		if (newSize > oldLargestSize) {
			largestSizeOfStoredGroundings.put(clause, newSize); // Alas, cannot report since might be reporting the product.
		}
		if (returnZero) { if (debugLevel > 1) { Utils.print("x0[sinceNoItemsFound]"); } return 0.0; }
		return Math.max(0.0, result);
	}
	
	private void reportRemainingConstantsOfRemainingVariables(Clause clause) {
		Collection<Variable>               varsInClause    = variablesInClause.get( clause);
		Map<Variable,VariableIndexPair>    aggregators     = aggregatorMap.get(     clause);
		Map<Variable,Set<Term>>        oldConstants    = varsToConstantsMap.get(clause);
		Map<AggVar, List<List<Term>>>  aggsToConstants = aggVarsToAggregatedConstantsMap.get(clause);
		Collection<AggVar>                 aggregatorsUsed = null;  // We only want to report each aggregator ONCE.
		if (varsInClause == null) { return; }
		if (aggregators == null || oldConstants == null || aggsToConstants == null) { return; }  // Might have cleared these, which is fine.
		for (Variable var : varsInClause) {
			VariableIndexPair currentOwnerOfVar = aggregators.get(var);
			if (currentOwnerOfVar == null) {
				if (oldConstants.get(var) != null) { Utils.println("%     There are " + Utils.comma(oldConstants.get(var)) + " remaining constants for regular variable '" + var + "': " + Utils.limitLengthOfPrintedList(oldConstants.get(var), 10)); }
			} else if (aggregatorsUsed == null || !aggregatorsUsed.contains(currentOwnerOfVar.aggVar)) { // Don't double report aggregators.
				if (aggsToConstants.get(currentOwnerOfVar.aggVar) != null) { Utils.println("%     There are " + Utils.comma(aggsToConstants.get(currentOwnerOfVar.aggVar)) + " remaining constant lists for aggregator '" + currentOwnerOfVar.aggVar + "': " + Utils.limitLengthOfPrintedList(aggsToConstants.get(currentOwnerOfVar.aggVar), 10)); }
				if (aggregatorsUsed == null) { aggregatorsUsed = new HashSet<AggVar>(4); }
				aggregatorsUsed.add(currentOwnerOfVar.aggVar);
			}
		}
	}
	
	// Need to notice that 'agg_A_B_C' is in [X, B, Y].
	private boolean skipThisAggregatedVariable(AggVar aggVar, Collection<Variable> skipThese) {
		if (skipThese == null) { return false; }
		Collection<Variable> aggregatees = aggVar.varsCombined;
		for (Variable skip : skipThese) if (aggregatees.contains(skip)) { return true; }
		return false;		
	}
	
	// Clear the caches for this clause of those literals, except litToSkip, that share a variable with the provided list of variables.
	private void clearAllLiteralCachesImpactedByTheseVariables(Clause clause, Literal litToSkip, Collection<Variable> variables) {
		Map<Literal,CacheLiteralGrounding> caches = litsToConstantsMap.get(clause);

		if (caches != null) for (Literal lit : caches.keySet()) if (lit != litToSkip) {
			Collection<Variable> varsInLit = freeVarsMap.get(clause).get(lit);
			if (varsInLit != null) for (Variable var : varsInLit) if (variables.contains(var)) {
				if (debugLevel > 2) { Utils.println("%        Clearing the cache for " + wrapLiteral(clause, lit) + " because of its variable '" + var + "'."); }
				litsToConstantsMap.get(clause).put(lit, null);
				break;
			}
		}
	}
	
	private void handleSingleVariableLiteral(Clause clause, Literal lit, boolean pos) throws MLNreductionProblemTooLargeException {
		Variable varInLiteral = Utils.getIthItemInCollectionUnsafe(freeVarsMap.get(clause).get(lit), 0); // We know there is only one variable here.
		if (debugLevel > 0) { Utils.println("\n% Consider single-variable literal " + wrapLiteral(clause, lit) + "."); }
		CacheLiteralGrounding cache = countLiteralGroundings(clause, lit, pos, varInLiteral, true); // This calls updateCountOfTotalGroundings (so don't double count).  Force here since only a singleton literal (and so will always accept).
		List<List<Term>> groundingsToKeep = cache.getGroundingsStillNeeded();
		long posCount     = cache.trueCount;
		if (posCount < 0) { // This is only a query (or hidden) literal.  No reduction is possible.
			Utils.error("This should not happen: " + cache);
		}
		long negCount     = cache.falseCount;
		long unkCount     = cache.unknownCount;
		long goodCount    = (pos ? posCount : negCount);
		long uselessCount = (pos ? negCount : posCount);
		long keeperCount  = uselessCount + unkCount;
		if (debugLevel > 0) { Utils.print("%       Stats: #sat=" + Utils.comma(goodCount) + ", #unsat=" + Utils.comma(uselessCount) + ", #unknown=" + Utils.comma(unkCount) + " for " + wrapLiteral(clause, lit)); }
		if (keeperCount != Utils.getSizeSafely(groundingsToKeep)) { Utils.error("Have a counting mismatch for " + wrapLiteral(clause, lit) + ": |keepers|=" + keeperCount + " vs. |groundings|=" + Utils.getSizeSafely(groundingsToKeep)); }
		double reduction = keeperCount / (double)(posCount + negCount + unkCount);
		if (unkCount < 1 && goodCount < 1) {
			if (debugLevel > 0) { Utils.println(".  Discard, since never satisfied."); }
			noLongerNeedToKeepThisLiteral(clause, lit);
			return;
		}
		if (reduction >= 1.0) {
			if (debugLevel > 0) { Utils.println(".  No size reduction."); }
			return;
		}
		if (debugLevel > 2) { Utils.println(".\n%       Reduction for " + wrapLiteral(lit, pos) + ": " + Utils.comma(keeperCount) + "/" + Utils.comma(posCount + negCount + unkCount) + " = " + Utils.truncate(reduction, 6)); }
		else if (debugLevel > 0) { Utils.println("."); } // Need to terminate above print().
		// Can reduce right away! Need to unwrap the LIST of constants, though (done via extractItemNfromListsIntoList).
		if (debugLevel > 0) { Utils.println("%   Have a reduction (keepers=" + Utils.comma(keeperCount) + "/total=" + Utils.comma(posCount + negCount + unkCount) + ") in an arity-one literal, so no need to join variable-grounding lists.  Have reduced the possible constants by " + Utils.comma(goodCount) + " out of " + Utils.comma(posCount + negCount + unkCount) + "."); }
		if (keeperCount < 1) {
			clauseAlwaysTrue(clause, lit);
		}
		else {
			Set<Term> keepers = extractItemNfromListsIntoList(groundingsToKeep, 0); // Want to use SET here since we are simply looking for constants in use (and we assume that constants list do NOT contain duplicates, so no 'counts' lost).
			varsToConstantsMap.get(clause).put(varInLiteral, keepers);
			// The following doesn't save much, since the larger arity literals dominate the runtime.  But leave in for now.
			if (lit.numberArgs() == 1 && !singletonVarsInClauseProcessed.get(clause).contains(varInLiteral)) { // Was this the first time this variable has been processed in this clause?  Note: we can only cache if the literal has no other arguments, since p(x,1) and p(x,2) need not have the same coverage.  TODO - has on all arguments (but worth it?).
				List<CacheLiteralGrounding>  entry = varsToConstantsMapForSingletonLiterals.get(lit.predicateName);
				if (entry == null) { // Need to store results for negated and unnegated literals.
					entry = new ArrayList<CacheLiteralGrounding>(2); entry.add(null); entry.add(null);
				}
				if (entry.get(pos ? 1 : 0) == null) { // See if not previously cached.
					if (debugLevel > 1) { Utils.println("%    Caching arity-one literal " + wrapLiteral(lit,pos) + ".  #groundings = " + Utils.getSizeSafely(groundingsToKeep) + " T/F/U=" + cache.trueCount  + "/" + cache.falseCount + "/" + cache.unknownCount + "  " + clause); }
					entry.set(pos ? 1 : 0, cache);
				}
				varsToConstantsMapForSingletonLiterals.put(lit.predicateName, entry); // Other versions of this literal can share these results.
			}
			singletonVarsInClauseProcessed.get(clause).add(varInLiteral); // Note that this is no longer the original list (and hence cannot be shared).
			if (keeperCount != keepers.size()) { Utils.error("Should have keepersCount = " + keeperCount + " = " + keepers.size() + " = keepers.size().  groundingsToKeep = " + Utils.limitLengthOfPrintedList(groundingsToKeep, 20)); }
			updateNumberOfTRUEsForClause(clause, lit, pos, goodCount);
			
			if (unkCount < 1) { 
				if (debugLevel > 0) { Utils.println("%   Since no 'unknown' settings for this literal, can drop it from the clause."); }
				noLongerNeedToKeepThisLiteral(clause, lit);
			} else {
				if (debugLevel > 0) { Utils.println("%   Need to keep " + wrapLiteral(lit,pos) + " because it has " + Utils.comma(unkCount) + " groundings with unknown truth value.  All keepers, including those that are known to not satisfy this literal: " + Utils.limitLengthOfPrintedList(groundingsToKeep, 10)); }
			}			
		}
	}	
	
	private String wrapLiteral(Literal lit, boolean pos) {
		if (pos) { return "'" + lit + "'"; }
		return "'~" + lit + "'"; 
	}		
	private String wrapLiteral(Clause clause, Literal lit) {
		return wrapLiteral(lit, clause.getSign(lit));
	}
	
	// Record that done with this literal.
	private void recordLiteralHasBeenReduced(Clause clause, Literal lit) {
		if (!literalsStillToReduce.get(clause).contains(lit)) { return; } // OK if already removed, since other code calls this as a final cleanup, which maybe be unnecessary due to, say, the literal alwaysd being true.
		if (debugLevel > 0) { Utils.println("%   Because it has been reduced, removing " + wrapLiteral(clause, lit) + " from consideration for this clause."); }
		countCurrentCombinatorics(clause);
		noLongerConsiderThisLiteral(clause, lit);
	}
	
	private void recordDoneWithThisClause(Clause clause) {
		if (doneWithThisClause.contains(clause)) { Utils.error("Already noted that done with this clause #" + Utils.comma(clauseToIndex.get(clause)) + ": '" + clause + "', solved @ " + cycle_when_solved.get(clause)); }
		doneWithThisClause.add(clause); 
		cycle_when_solved.put(clause, 1000 * currentOverallIteration + currentCycle); // Encode two pieces of information here.		
		if (debugLevel > 2) { Utils.println("% **** Done with: '" + clause + "' [cycle_when_solved = " + cycle_when_solved.get(clause) + "]."); }
		numberOfClausesToAnalyze--;  if (numberOfClausesToAnalyze < 0) { Utils.error("Variable 'numberOfClausesToAnalyze' should never be negative!"); }
		if (Utils.getSizeSafely(literalsToKeep.get(clause)) < 1 && countOfSatisfiableGndClauses.get(clause) > 0) {
			if (debugLevel > 0) { Utils.println("%   Since this clause has no surviving literals, it is false for all " + Utils.truncate(countOfSatisfiableGndClauses.get(clause), 0) + " remaining groundings."); }
			clauseAlwaysFalse(clause);
		}
		doFinalCleanup(clause);
	}
	
	private void clauseAlwaysFalse(Clause clause) {
		if (debugLevel > 0) { Utils.println("%    DONE!  Handling a clause that is always FALSE for any remaining variables.  Setting number of satisfiable combinations to 0."); }
		countOfFALSEs.put(clause, countOfFALSEs.get(clause) + countOfSatisfiableGndClauses.get(clause));
		allCombinationsAccountedFor(clause);
	}
	private void clauseAlwaysTrue(Clause clause, Literal causingLiteral) {
		double oldTRUEs = countOfTRUEs.get(clause);
		if (debugLevel > 0) { Utils.println("%   DONE!  Handling a clause that is always TRUE " + (causingLiteral == null ? "" : "(due to " + wrapLiteral(clause, causingLiteral) + ")") + ".  Setting number of satisfiable combinations to 0."); }
		if (debugLevel > 0) { Utils.print(  "%     Size of the space of 'covered' groundings"); }
		double newTRUEs = computeSizeOfVariableCrossProduct(clause, null); // TODO make sure these are added after the any other processing for this literal.
		if (debugLevel > 0) { Utils.println(" = " + Utils.truncate(newTRUEs, 0) + ", which will be added to the number of times this clause is TRUE (new total = " + Utils.truncate(oldTRUEs + newTRUEs, 0) + ")."); }
		countOfTRUEs.put(clause, oldTRUEs + newTRUEs);
		allCombinationsAccountedFor(clause);
	}
	
	// Do some cleaning when all the possibilities for a clause have been accounted for.  TODO - clean up more?  Less? Or let GC do that?
	private void allCombinationsAccountedFor(Clause clause) {
		literalsToKeep.get(       clause).clear();
		literalsStillToReduce.get(clause).clear();
		literalsRejectedForReduction.get(clause).clear(); // Can forgot about all of these if all the combinations accounted for (i.e., by other literals).
		countOfSatisfiableGndClauses.put(clause, 0.0);
		if (variablesInClause.get(clause) != null) { accountedForVariables.get(clause).addAll(variablesInClause.get(clause)); }
		if (!doneWithThisClause.contains(clause)) { recordDoneWithThisClause(clause); }
	}
	
	private void noLongerNeedToKeepThisLiteral(Clause clause, Literal lit) {
		if (!literalsToKeep.get(clause).remove(lit)) { Utils.error("Could not find " + wrapLiteral(clause, lit) + " in " + literalsToKeep.get(clause)); }
		if (debugLevel > 2) { Utils.println("%   REMOVE  " + wrapLiteral(clause, lit) + " from literalsToKeep, since no longer needed.  Remainder: " + literalsToKeep.get(clause)); }
		recordLiteralHasBeenReduced(clause, lit);
	}
	
	private void noLongerConsiderThisLiteral(Clause clause, Literal lit) {
		if (!literalsStillToReduce.get(clause).remove(lit)) { Utils.error("Could not find " + wrapLiteral(clause, lit) + " in " + literalsStillToReduce.get(clause)); }
		if (debugLevel > 2) { Utils.println("%   REMOVE  " + wrapLiteral(clause, lit) + " from literalsStillToReduce, since no longer needed.  Remainder: " + literalsStillToReduce.get(clause)); }
		if (literalsStillToReduce.get(clause).isEmpty()) {
			if (debugLevel > 0) { Utils.println("%   This was the last literal to reduce in this clause."); }
			recordDoneWithThisClause(clause);
		}
	}
	
	private void removePointersToConstants(Clause clause) {  // Do NOT erase lists.  They might be pointed to by others.
		if (aggregatorMap != null && aggregatorMap.get(clause) != null) for (Variable var : aggregatorMap.get(clause).keySet()) {
			aggregatorMap.get(clause).put(var, null);
		}
		if (varsToConstantsMap != null && varsToConstantsMap.get(clause) != null) for (Variable var : varsToConstantsMap.get(clause).keySet()) {
			varsToConstantsMap.get(clause).put(var, null); // Don't clear() since might still be pointing to the constants stored in task.
		}
		if (aggVarsToAggregatedConstantsMap != null && aggVarsToAggregatedConstantsMap.get(clause) != null) { aggVarsToAggregatedConstantsMap.put(clause, null); }
		if (litsToConstantsMap              != null && litsToConstantsMap.get(clause)              != null) { litsToConstantsMap.put(clause, null); }
	}
	
	private double countCurrentCombinatorics(Clause clause) {
		double oldCount = countOfSatisfiableGndClauses.get(clause);
		if (debugLevel > 0) { 
			if (oldCount < 0) { Utils.print("% Initial number of variable combinations"); }
			else              { Utils.print("%   Number of remaining variable combinations"); }			 
		}
		double currentCombinatorics = computeSizeOfVariableCrossProduct(clause, null);
		if (debugLevel > 0) { 
			if (oldCount < 0) {                          Utils.print(" = " + Utils.truncate(currentCombinatorics, 0)); }
			else if (currentCombinatorics == oldCount) { Utils.print(" = " + Utils.truncate(currentCombinatorics, 0) + " [unchanged]"); }
			else {                                       Utils.print(" = " + Utils.truncate(currentCombinatorics, 0) + " [" + Utils.truncate(oldCount, 0) + " previously]"); }
			Utils.println(" for clause #" + Utils.comma(clauseToIndex.get(clause)) + ": '" + clause + ".");
		}
		countOfSatisfiableGndClauses.put(clause, currentCombinatorics);
		return currentCombinatorics;
	}
	
	private boolean matchesQueryPnameArity(     Literal lit) { return containsPnameAndArity(lit, allQueryPredNames); }
	private boolean matchesPosPnameArity(       Literal lit) { return containsPnameAndArity(lit, allPosEvidencePredNames); }
	private boolean matchesNegPnameArity(       Literal lit) { return containsPnameAndArity(lit, allNegEvidencePredNames); }
	private boolean matchesHiddenPnameArity(    Literal lit) { return containsPnameAndArity(lit, allHiddenPredNames); }
	
	private boolean matchesQuery(      Literal lit) { return (containsPnameAndArity(lit, allQueryPredNames) || containsThisLiteral(lit, allQueriesIndexed)); }
	private boolean matchesPosEvidence(Literal lit) { return (lit.equals(trueLit,  false) || containsPnameAndArity(lit, allPosEvidencePredNames) || containsThisLiteral(lit, allPosEvidenceIndexed) || evaluateProcDefinedEvidence(lit, true )); }
	private boolean matchesNegEvidence(Literal lit) { return (lit.equals(falseLit, false) || containsPnameAndArity(lit, allNegEvidencePredNames) || containsThisLiteral(lit, allNegEvidenceIndexed) || evaluateProcDefinedEvidence(lit, false)); }
	private boolean matchesHidden(     Literal lit) { return (containsPnameAndArity(lit, allHiddenPredNames) || containsThisLiteral(lit, allHiddensIndexed)); }

	// These are to be used when we know we don't need to check the Pname/Arity databases.
	private boolean matchesQueryFast(      Literal lit) { return containsThisLiteral(lit, allQueriesIndexed); }
	private boolean matchesPosEvidenceFast(Literal lit) { return (lit.equals(trueLit,  false) || containsThisLiteral(lit, allPosEvidenceIndexed) || evaluateProcDefinedEvidence(lit, true )); }
	private boolean matchesNegEvidenceFast(Literal lit) { return (lit.equals(falseLit, false) || containsThisLiteral(lit, allNegEvidenceIndexed) || evaluateProcDefinedEvidence(lit, false)); }
	private boolean matchesHiddenFast(     Literal lit) { return containsThisLiteral(lit, allHiddensIndexed); }
	
	private boolean isaFalseByCWA(     Literal lit) { return (task.isClosedWorldAssumption(lit) && !matchesPosEvidence(lit) && !matchesQuery(lit) && !matchesHidden(lit)); }
	private boolean isaFalseByCWAfast( Literal lit) { return  task.isClosedWorldAssumption(lit); } // Fast version for use when matchesPosEvidence, matchesQuery, and matchesHidden have already been checked.
	
	//private boolean keepThisNegLiteral(Literal lit) { 
		// Have something of the form ~p(x,y,z) in a clause.
		// We need to keep it if p(x,y,z) is not known to be false (i.e., not in the negative evidence) and p(x,y,z)
		//    a) matches positive evidence, since then ~p(x,y,z) is FALSE or
		//    b) matches a query or hidden literal, since we don't know its true value or
		//    c) the CWA=false
	//	return (!matchesNegEvidence(lit) && !isaFalseByCWA(lit));
	//	return !(thisNegLiteralIsSatisfied(lit)); // Alternate definition (same by DeMorgan's Law).
	//}
	private boolean thisPosLiteralIsSatisfied(Literal lit) {
		return matchesPosEvidence(lit);
	}
	private boolean thisNegLiteralIsSatisfied(Literal lit) {
		// Have something of the form ~p(x,y,z) in a clause. 
		// We know it is satisfied if p(x,y,z) is in the negative evidence.
		// We assume it is satisfied if p(x,y,z) is not in the positive evidence nor is a query, and we're using the closed-world assumption.
		// HOWEVER, if in the list of 'hidden,' the CWA is not used (see isaFalseByCWA).
		return (matchesNegEvidence(lit) || isaFalseByCWA(lit));
	}
	// Is this literal a query or hidden?  But check first if its truth value is known.
	private boolean isSatisfiable(Literal lit) {
		if (matchesPosEvidence(lit) || matchesNegEvidence(lit)) { return false; }
		if (matchesQuery(lit)       || matchesHidden(lit))      { return true;  }
		return !task.isClosedWorldAssumption(lit); // If CWA=true, then this literal is false by it.  Otherwise this literal's truth value is unknown (and hence it is satisfiable).
	}
	// See if this literal's predicate name and arity are in this index.
	private boolean containsPnameAndArity(Literal lit, Map<PredicateName,Set<Integer>> predNameArityIndex) {
		if (predNameArityIndex == null || predNameArityIndex.size() < 1) { return false; }
		Set<Integer> lookup = predNameArityIndex.get(lit.predicateName);
		if (lookup == null) { return false; }
		return lookup.contains(lit.numberArgs());
	}

	// If this literal is procedurally defined AND its value matches 'desiredValue' then return TRUE else return FALSE.
	private boolean evaluateProcDefinedEvidence(Literal lit, boolean desiredValue) {
		PredicateName pName = lit.predicateName; // Save CPU cycles, assume literal never is null (it is a bug if it is).
		if (procedurallyDefinedPredicatesInUse != null && procedurallyDefinedPredicatesInUse.contains(pName)) {
			BindingList bindings = task.prover.evaluateProcedurallyDefined(lit);
			if (desiredValue) {	return (bindings != null); } // Did it succeed?
			return (bindings == null); // See if FALSE.
		}
		return false;
	}
	// See if this ground literal is in the index.
	private boolean containsThisLiteral(Literal lit, Map<PredicateName,Map<Term,List<List<Term>>>> indexedFacts) {
		if (indexedFacts == null || indexedFacts.size() < 1) { return false; }
		Collection<Term> skolemMarkers = task.skolemsPerLiteral.get(lit); // These match anything since we're not doing any logical inference and are simply matching.
		if (skolemMarkers == null) { skolemMarkers = skolemsInLiteralUnderConsideration; } // Used for cases where unifications produced new literal instances.
		List<Term>    args  = lit.getArguments();
		Term          c1    = (Utils.getSizeSafely(args) < 1 ? null : args.get(0)); 
		PredicateName pName = lit.predicateName; // Save CPU cycles, assume literal never is null (it is a bug if it is).
		Map<Term,List<List<Term>>> lookup1 = indexedFacts.get(pName);
		if (lookup1 == null) { return false; }
		int numbArgs = lit.numberArgs();
		if (numbArgs == 0) { return true; } // Just need to match the predicate name with 0-arity predicates.
		List<List<Term>> lookup2;
		// See if this predicate appears in a fact containing variables.  If so, need to unify this literal and the facts.
		if (factsWithVariables != null && factsWithVariables.contains(pName)) {
			lookup2 = lookup1.get(variableInFactMarker);
			for (List<Term> argsInIndexedFact : lookup2) if (argsInIndexedFact.size() == numbArgs) {
				bl.theta.clear();
				if (unifier.unifyAssumingSameNumberOfArgs(argsInIndexedFact, args, bl) != null) { return true; }
			}
		}
		if (skolemMarkers == null || !skolemMarkers.contains(c1)) { // See if 'c1' is NOT a Skolem marker.
			lookup2 = lookup1.get(c1); // Get the argument lists for this pName with this first argument.
			//if (skolemMarkers != null) { Utils.println("HERE1: " + skolemMarkers + "  " + lookup2); }
			if (lookup2 == null)  { return false; } // Nothing found, so failed.
			if (numbArgs == 1)    { return true;  } // Succeeded (only 1 argument).
			return seeIfArgumentsMatch(c1, lookup2, args, skolemMarkers); // See if the rest of the arguments match.
		} else if (numbArgs == 1) { return true;   // Have matched the predicate name and the SkolemMarker (regardless of the first argument of literal), so done.
		} else { // Cannot use the first term to index (it matches ANYTHING).  So need to look at all KEYs (since they all match the Skolem).
			//if (skolemMarkers != null) { Utils.println("HERE2: " + skolemMarkers); }
			for (Term key : lookup1.keySet()) {
				lookup2 = lookup1.get(key);
				if (seeIfArgumentsMatch(key, lookup2, args, skolemMarkers)) { return true; }
			}
			return false;
		}
	}
	
	private boolean seeIfArgumentsMatch(Term firstStoredArg, List<List<Term>> storedArgLists, List<Term> litArgs, Collection<Term> skolemMarkers) {
		// In 0 or 1 Skolems, then easy to do 'variable' matching.
		if (Utils.getSizeSafely(skolemMarkers) < 2) { return  help_seeIfArgumentsMatch(storedArgLists, litArgs, (skolemMarkers == null ? null : Utils.getIthItemInCollectionUnsafe(skolemMarkers, 0))); }
		// Otherwise need to unify this literal and the facts.
		int numbOfArgs = litArgs.size();
		for (List<Term> argsInIndexedFact : storedArgLists) if (argsInIndexedFact.size() == numbOfArgs) {
			bl.theta.clear();
			if (debugLevel > 2 && skolemMarkers != null) { Utils.println("% UNIFY in seeIfArgumentsMatch: " + argsInIndexedFact + " and " + litArgs); }
			if (unifier.unifyAssumingSameNumberOfArgs(argsInIndexedFact, litArgs, bl) != null) { return true; }
		}
		return false;
	}
	// See if these arguments match something in the list of arguments.  Notice that the first argument has already been matched,
	// and that the skolemMarker can match anything.
	private boolean help_seeIfArgumentsMatch(List<List<Term>> storedArgLists, List<Term> args, Term skolemMarker) {
		if (debugLevel > 3) { Utils.println("help_seeIfArgumentsMatch: skolemMarker=" + skolemMarker + " and args=" + args + ": " + Utils.limitLengthOfPrintedList(storedArgLists, 25)); }
		int size = args.size(); 
		for (List<Term> indexList : storedArgLists) { // See if a match on the terms.
			boolean match = true;
			for (int i = 1; i < size; i++) { // Note we skip argument 0.
				Term litArg = args.get(i);
				if (litArg != indexList.get(i) && litArg != skolemMarker) {
					match = false; // Found a mismatch.
					break; // No need to look further in this argument list.
				}
			}
			if (match) { return true; } // Found a match, so done.
		}
		return false;
	}
	
	private void updateCountOfTotalGroundings(Clause clause, Literal lit, long satisfiers, long counted) {
		totalLiteralGroundingsConsideredThisLiteral.get(clause).put(lit, counted + totalLiteralGroundingsConsideredThisLiteral.get(clause).get(lit));
		totalLiteralGroundingsConsidered.put(clause,                     counted + totalLiteralGroundingsConsidered.get(clause));
		if (debugLevel > 2) { Utils.println("%      ********** Considered " + Utils.padLeft(counted, 9) + " groundings and found " 
											+ Utils.padLeft(satisfiers, 7) + " that satisfy the clause.  [Total for " + wrapLiteral(clause, lit) + " = " 
											+ Utils.comma(totalLiteralGroundingsConsideredThisLiteral.get(clause).get(lit)) + " and total for this clause = "
											+ Utils.comma(totalLiteralGroundingsConsidered.get(clause)) + ".]"); }
	}	
	
	// Use Terms here so can do later due lookups without needing to cast as Constants.  
	// Also, some facts might contain variables.  For those that do, use variableInFactMarker as the Term for indexing.
	// Put ALL arguments in the list, even though hashing on the first, since sometimes later code needs to match the first arguments (e.g., if it is a variable).
	private void hashSetOfFacts(Collection<GroundLiteral> facts, Map<PredicateName,Map<Term,List<List<Term>>>> hasher) {
		if (facts != null) for (Literal lit : facts) {
			PredicateName pName = lit.predicateName;
			List<Term>    args  = lit.getArguments();
			Term          term1 = (lit.numberArgs() < 1 ? null : args.get(0));
			Map<Term,List<List<Term>>> lookup1 = hasher.get(pName);
			
			// See if any facts containing variables are in use.
			if (lit.numberArgs() > 0) for (Term term : args) if (!(term instanceof Term)) {
				if (term instanceof Function) { Utils.error("Need to handle functions (before getting) here!"); }
				if (factsWithVariables == null) { factsWithVariables = new HashSet<PredicateName>(4); }
				// TODO - use arity as well?  Or assume the overall cost is minor?
			 	//if (!factsWithVariables.contains(pName)) {
			 		//Utils.println("% Fact with variable(s) in use: " + lit); // Already reported when read (search for reportFactsWithVariables).
			 		//factsWithVariables.add(lit.predicateName);
			 	//}
			 	factsWithVariables.add(lit.predicateName);
				term1 = variableInFactMarker; 
			}
			
			if (lookup1 == null) { 
				lookup1 = new HashMap<Term,List<List<Term>>>(4);
				hasher.put(pName, lookup1);
			}
			List<List<Term>> lookup2 = lookup1.get(term1);
			if (lookup2 == null) {
				lookup2 = new ArrayList<List<Term>>(4);
				lookup1.put(term1, lookup2);
			}
			lookup2.add(args); // DO NOT REMOVE DUPLICATES, since we want to count groundings.
		}
	}
	
	// Allow fast lookups of PredNameArityPair's.
	private void hashPredNames(Collection<PredNameArityPair> predNames, Map<PredicateName,Set<Integer>> hash) {
		if (predNames != null) { // Convert the PredNameArityPair's to a quick lookup data structure.
			for (PredNameArityPair pNameArityPair : predNames) {
				Set<Integer> lookup = hash.get(pNameArityPair.pName);				
				if (lookup == null) {
					lookup = new HashSet<Integer>(4);
					hash.put(pNameArityPair.pName, lookup);
				}
				lookup.add(pNameArityPair.arity);
			}
		}
	}

	/* TVK : Not used here.
	private CacheLiteralGrounding collectAndCacheRemainingGroundings(Clause clause, Literal lit) throws MLNreductionProblemTooLargeException {
		CacheLiteralGrounding cache = litsToConstantsMap.get(clause).get(lit);
		if (cache != null && cache.getGroundingsStillNeeded() != null) { return cache; }
		// In the call below, set the first argument to true so no time spent trying to see if these groundings are satisfiable since that has already been done.
		CacheLiteralGrounding result = help_createFullCrossProductFromTheseVariables(true, clause, lit, clause.getSign(lit), true, freeVarsMap.get(clause).get(lit), emptyIntList);
		if (result == null) { Utils.error("Could not find any groundings for " + wrapLiteral(clause, lit) + " in clause '" + clause + "'."); }
		litsToConstantsMap.get(clause).put(lit, cache); // Might not want to cache this, since (may be?) only called once.
		return result;
	}
	*/
	
	// This group of methods deals with post-reduction inference.
	protected void collectAllRemainingGroundings(TimeStamp timeStamp) {
		if (debugLevel > 0) { Utils.println("\n% Explicitly collecting all remaining groundings for reduced groundings that are small enough."); }
		int counter = 0;
		for (Clause clause : allClauses) {
			if (debugLevel > 1 || ++counter % 500 == 0) { Utils.println("%  Collecting all remaining groundings for clause #" + Utils.comma(counter) + "."); }
			if (countOfSatisfiableGndClauses.get(clause) > maxNumberClauseGroundings) {
				checkForUnacceptableLazyClause(clause);
				if (debugLevel > -110) { Utils.println("%    This clause has too many groundings (" + Utils.truncate(countOfSatisfiableGndClauses.get(clause), 0) + ") and will not be grounded: '" + clause + "'."); }
				if (stillTooLargeAfterReduction == null) { stillTooLargeAfterReduction = new HashSet<Clause>(4); }
				stillTooLargeAfterReduction.add(clause);
				continue;
			}
			try {
				getAllClauseGroundings(clause, timeStamp);
			} catch (MLNreductionProblemTooLargeException e) {
				checkForUnacceptableLazyClause(clause);
				if (debugLevel > -110) { Utils.println("% Clause #" + Utils.comma(clauseToIndex.get(clause)) + " is too large to fully ground, so it will require lazy evaluation."); }
				if (stillTooLargeAfterReduction == null) { stillTooLargeAfterReduction = new HashSet<Clause>(4); }
				stillTooLargeAfterReduction.add(clause);
				continue;
			}
			//if (Utils.getSizeSafely(literalsRejectedForReduction.get(clause)) > 0) {
			//	Utils.error("Think this code through to see if it makes sense with 'reject's: " + literalsRejectedForReduction.get(clause)); 
			////remainingUnsatisfiedLiteralGroundings = new HashMap<Clause,Map<Literal,Collection<GroundLiteral>>>(4);
			//}
		}
		collectAllGroundClauses();
		collectAllGroundLiterals();
		if (Utils.getSizeSafely(stillTooLargeAfterReduction) > 0) {
			Utils.writeMe("Lazy inference not implemented here");
			doingLazyInference = true;
			/*  THIS CAN STILL GROW TO BE TOO LARGE.
			if (debugLevel > -110) { Utils.println("% Connecting the lazy ground clauses with the existing ground literals."); }
			int totalCountOfNewClausegroundings = 0;
			int counter2                        = 0;
			for (GroundLiteral gLit : allGroundLiteralsOrig) {
				totalCountOfNewClausegroundings += activateLazyGroundClausesContainingThisGroundLiteral(gLit, true, stillTooLargeAfterReduction, true, timeStamp); // These lazy clauses collected are 'permanent' since they use ground literals that are permanent.
				if (debugLevel > -110 && ++counter2 % 10 == 0) {  Utils.println("%     Have added " + Utils.comma(totalCountOfNewClausegroundings) + " new lazy ground clauses by processing  " + Utils.comma(counter2) + " of the existing ground literals."); }
			}
			if (debugLevel > -110) { 
				Utils.println("%   Connecting the lazy ground clauses with the regular ground clauses created " + Utils.comma(totalCountOfNewClausegroundings) + " new ground clauses.");
				Utils.println("%     On average, " + Utils.truncate(totalCountOfNewClausegroundings/ allGroundLiteralsOrig.size(), 3) + " ground clauses were added for each of the regular ground literls.");
				Utils.println("%     The number of permanent ground clauses is " + Utils.comma(numberOfPermanentLazyGroundClauses) + ".");
				Utils.println("%     Total count of materialized ground clauses = " + Utils.comma(totalNumberOfGroundClauses) + " and ground literals = " + Utils.comma(totalNumberOfGroundLiterals) + ".");
			}			
			*/
		} else { doingLazyInference = false; }
		if (Utils.getSizeSafely(allGroundClauses) > 0) {
			computeAllBlocks(timeStamp); // Need all the ground literals before this can be done.
		}
	}
	
	private void checkForUnacceptableLazyClause(Clause clause) {
		if (!task.isClosedWorldAssumption(null)) {
			Utils.error("The closed-world assumption is not being used, and without it large clauses cannot be handled:\n   " + clause + "\n" + 
						"Reset your use of FROG and try again.");
		}
		if (Utils.getSizeSafely(clause.negLiterals) < 1) {
			Utils.error("This clause has no negated literals and too many groundings (" + Utils.comma(countOfSatisfiableGndClauses.get(clause)) + "), all of which need to be explicitly represented \n" +
						"because the default value of clauses (true) cannot be used.  Please remove or edit this clause, or change default settings in FROG, and try again:\n    " +
						clause);
		}
		if (!isSatisfiableViaDefaults(clause)) {
			Utils.error("This clause has no negated literals where the closed-world assumption appplies and too many groundings (" + Utils.comma(countOfSatisfiableGndClauses.get(clause)) + "), all of which need to be explicitly represented \n" +
						"because the default value of clauses (true) cannot be used.  Please remove or edit this clause, or change default settings in FROG, and try again:\n    " +
						clause);
		}		
	}
	
	private boolean isSatisfiableViaDefaults(Clause clause) {
		if (clause.negLiterals != null) for (Literal nLit : clause.negLiterals) {
			if (task.isClosedWorldAssumption(nLit)) { return true; }
		}
		return false;
	}
		
	// Collect all the remaining groundings of this clause.  EXPAND ANY REMAINING SKOLEM VARIABLES HERE.
	// TODO should this be computed on the fly?  For now, let's cache it.
	// TODO - too much repeated code with help_createFullCrossProductFromTheseVariables, clean up once stable
	private Set<GroundClause> collectRemainingClauseGroundings(Clause clause, TimeStamp timeStamp) throws MLNreductionProblemTooLargeException {
		return collectRemainingClauseGroundings(clause, variablesInClause.get(clause), null, timeStamp);
	}
	@SuppressWarnings("unchecked")
	private Set<GroundClause> collectRemainingClauseGroundings(Clause clause, Collection<Variable> freeVariables, BindingList existingBindings, TimeStamp timeStamp) throws MLNreductionProblemTooLargeException {
		long start = System.currentTimeMillis();
		int countGroundingsDiscarded = 0;
		if (debugLevel > 0) { Utils.println("\n% Collect remaining groundings, using free variables " + freeVariables + (existingBindings == null ? "" : " and existingBindings " + existingBindings) + ", for clause #" + Utils.comma(clauseToIndex.get(clause)) + ": '" + clause + "'."); }
		Set<GroundClause>    results       = null;	
		if (Utils.getSizeSafely(freeVariables) < 1) {
			if (debugLevel > 0) { Utils.println("%   No variables in '" + clause + "' so it is its own ground clause."); }
			// Recall that ground clauses can represent SETS of groundings, and need to account for that when calculating weights.
			bl.theta.clear();
			GroundClause groundClause = getGroundClause(task, clause, getFreeVarMap(variablesRemainingInClause.get(clause), bl, existingBindings), timeStamp);
			if (results == null) { results = new HashSet<GroundClause>(4); }
			results.add(groundClause);
			return results; // Added (11/2/09) by JWS.
		}
		if (existingBindings != null) for (Variable var : freeVariables) if (existingBindings.theta.containsKey(var)) {
			Utils.error("Provided free variable '" + var + " should not be in the provided bindings: " + existingBindings);
		}
		Collection<Literal>        keeperLiterals         = literalsToKeep.get(clause);
		if (Utils.getSizeSafely(keeperLiterals) < 1) { return null; }
		double                     size                   = 1.0;
		Set<Variable>              unAggregatedVars       = null;  // Used to watch for errors.
		Set<Variable>                aggregatedVars       = null;  // Used to watch for errors.
		List<AggVar>               aggregatorsNeeded      = null;
		List<Set<Term>>        allArgPossibilities    = new ArrayList<Set<Term>>(1);
		List<List<List<Term>>> allAggArgPossibilities = null;
		int                        numbFreeVariables      = Utils.getSizeSafely(freeVariables);
		Map<Variable,Integer>      mapVariablesToPositionInAggregatorList = null; // If there are aggregators, we need to know their position in aggregatorsNeeded.
		for (Variable var : freeVariables) {
			VariableIndexPair currentOwnerOfVar = aggregatorMap.get(clause).get(var);
			if (currentOwnerOfVar == null) {
				if (debugLevel > 0) { Utils.println("% VAR '" + var + "' has these constants " + Utils.limitLengthOfPrintedList(varsToConstantsMap.get(clause).get(var), 25)); }
				if (unAggregatedVars == null) { unAggregatedVars  = new HashSet<Variable>(4); }
				if (unAggregatedVars.contains(var)) { Utils.error("Already have '" + var + "' in unAggregatedVars=" + unAggregatedVars); } // Should never happen, but check anyway.
				unAggregatedVars.add(var);
				size *= Utils.getSizeSafely(varsToConstantsMap.get(clause).get(var));
				allArgPossibilities.add(varsToConstantsMap.get(clause).get(var));
			} else { // This else might be called multiple times with the same aggVar, so keep track.
				if (aggregatedVars == null) { aggregatedVars  = new HashSet<Variable>(4); }
				if (aggregatedVars.contains(var)) { Utils.error("Already have '" + var + "' in aggregatedVars=" + aggregatedVars); } // Should never happen, but check anyway.
				aggregatedVars.add(var);
				AggVar aggVar = aggregatorMap.get(clause).get(var).aggVar;
				if (aggregatorsNeeded == null || !aggregatorsNeeded.contains(aggVar)) {
					if (debugLevel > 0) { Utils.println("% VAR '" + var + "' is aggregated by '"      + aggVar + "', which has these " + Utils.comma(aggVarsToAggregatedConstantsMap.get(clause).get(aggVar))+ " constants " + Utils.limitLengthOfPrintedList(aggVarsToAggregatedConstantsMap.get(clause).get(aggVar), 10)); }
					if (aggregatorsNeeded == null) { aggregatorsNeeded = new ArrayList<AggVar>(1); }
					aggregatorsNeeded.add(aggVar);
					if (allAggArgPossibilities == null) { allAggArgPossibilities = new ArrayList<List<List<Term>>>(1); }
					allAggArgPossibilities.add( aggVarsToAggregatedConstantsMap.get(clause).get(aggVar));				
					size *= Utils.getSizeSafely(aggVarsToAggregatedConstantsMap.get(clause).get(aggVar));
					if (mapVariablesToPositionInAggregatorList == null) { mapVariablesToPositionInAggregatorList = new HashMap<Variable,Integer>(4); }
					if (mapVariablesToPositionInAggregatorList.containsKey(var)) { Utils.error("Already have '" + var + "' in " + mapVariablesToPositionInAggregatorList); }
					mapVariablesToPositionInAggregatorList.put(var, aggregatorsNeeded.size() - 1);
				} else {
					if (debugLevel > 0) { Utils.println("% VAR '" + var + "' is also aggregated by '" + aggVar + "'."); }
					int numbExistingAggVars = aggregatorsNeeded.size();
					if (numbExistingAggVars == 1) { mapVariablesToPositionInAggregatorList.put(var, 0); }
					else { 
						for (int i = 0; i < numbExistingAggVars; i++) { 
							if (aggVar == aggregatorsNeeded.get(i)) { mapVariablesToPositionInAggregatorList.put(var, i); break; }
						}
					}
				}
				allArgPossibilities.add(dummySingletonSetOfConstants); // Need to keep the arity the same.
			}
		}
		if (debugLevel > 0) { Utils.println("% TOTAL SIZE: " + Utils.truncate(size, 0) + " for " + freeVariables); }

		if (size > maxNumberClauseGroundings) { throw new MLNreductionProblemTooLargeException(debugLevel > 2 ? "**** Too many groundings (" + Utils.comma(size) + ") for clause #" + Utils.comma(clauseToIndex.get(clause)) + ": '" + clause + "'." : ""); }
		if (debugLevel > 3) {
			Utils.println("allArgPossibilities    = " + Utils.limitLengthOfPrintedList(allArgPossibilities,    25));
			Utils.println("allAggArgPossibilities = " + Utils.limitLengthOfPrintedList(allAggArgPossibilities, 25));
		}
		// I cannot figure out how to get rid of the type checking errors ...
		CrossProductViaContinuation<Term>               basicVarCrossProduct = new CrossProductViaContinuation(allArgPossibilities);
		CrossProductViaContinuation<List<Term>> crossProductOfAggregatedVars = new CrossProductViaContinuation(allAggArgPossibilities);
		while (!basicVarCrossProduct.isEmpty()) {
			List<Term> bindings  = basicVarCrossProduct.getNextCrossProduct(); // Expand this binding using all the items in aggregatorListOfLists.
			boolean        firstTime = true; // If crossProductOfAggregatedVars is empty, we still need to do through the WHILE once.
			crossProductOfAggregatedVars.reset(); // Need to start this 'inner loop' afresh each time the outer loop is called.
			while (firstTime || !crossProductOfAggregatedVars.isEmpty()) { // Collect all the combinations for the aggregated variables.
				List<List<Term>> argVarLists = crossProductOfAggregatedVars.getNextCrossProduct();
				List<Term>       newBindings = new ArrayList<Term>(Utils.getSizeSafely(bindings)); // Get a fresh COPY. Do not REUSE, since getNextCrossProduct reuses the same memory cells.
				
				if (bindings != null) { newBindings.addAll(bindings); }
				if (debugLevel > 3) { Utils.println("  newBindings: " + newBindings + " for freeVariables = " + freeVariables); }
				if (firstTime) { firstTime = false; }
				// Now walk through each aggregator and correctly fill in the positions in newBindings.
				if (argVarLists != null) for (int argNumber = 0; argNumber < numbFreeVariables; argNumber++) { // Walk through the variables in this literal and see which need to get their values from an aggregator.
					Variable basicVar                      = Utils.getIthItemInCollectionUnsafe(freeVariables, argNumber);
					Integer  aggVarPositionForThisBasicVar = mapVariablesToPositionInAggregatorList.get(basicVar);	// Indexes into argVarList.				
					
					if (aggVarPositionForThisBasicVar != null) { // See if this variable is owned by some aggregator.
						VariableIndexPair pair                 = aggregatorMap.get(clause).get(basicVar);
						List<Term>    argVarListForThisVar = argVarLists.get(aggVarPositionForThisBasicVar);
						if (debugLevel > 3) { Utils.println(" freeVariables = " + freeVariables + "  basicVar = " + basicVar + "  argVarListForThisVar = " + argVarListForThisVar + "  pair = " + pair); }
						if (pair.index < Utils.getSizeSafely(argVarListForThisVar)) {
							newBindings.set(argNumber, argVarListForThisVar.get(pair.index));
						} else { Utils.warning(" pair.index = " + pair.index + " argVarListForThisVar.size() = " + Utils.getSizeSafely(argVarListForThisVar)); }
					}
				}
				bl.theta.clear();
				if (existingBindings != null) { bl.theta.putAll(existingBindings.theta); }  // Merge the two binding lists.
				if (debugLevel > 3) { Utils.println("  newBindings: " + newBindings + " for freeVariables = " + freeVariables); }
				int counter = 0;
				for (Variable var : freeVariables) { // NOTE: should be safe to assume the order through the freeVariables is correct even though freeVariables is a Collection.
					bl.addBinding(var, newBindings.get(counter++));
				}
				// Now need to create a grounded clause USING ONLY THOSE LITERALS STILL REMAINING.
				List<Literal> posLitsRemaining         = null;
				List<Literal> negLitsRemaining         = null;
				boolean       thisGroundingIsSatisfied = false;
				for (Literal lit : keeperLiterals) {
					boolean containsSkolem = false;
					Literal gLit = null; // If contains a Skolem, need to expand now (assuming it is satisfiable).
					if (task.skolemsPerLiteral.get(lit) != null) {
						containsSkolem = true;
						gLit = lit.applyTheta(bl.theta); // Since a Skolem, need to handle separately, but still want any bindings.  JWSJWSJWS
						skolemsInLiteralUnderConsideration = task.skolemsPerLiteral.get(lit); // Using a 'global' instead of passing another argument everywhere.
						if (debugLevel > 3) { Utils.println(lit + " -> " + skolemsInLiteralUnderConsideration); } 
					} else {
						gLit = task.getCanonicalRepresentative(lit.applyTheta(bl.theta), true, postponeSavingGroundLiterals);
					}
					if (clause.getSign(lit)) {
						//Utils.println("    POS gLit=" + gLit + " in? " + allPosEvidenceIndexed);
						if (thisPosLiteralIsSatisfied(gLit)) {
							Utils.println("    POS gLit=" + gLit + " is already satisfied!  Bug??");  // Utils.waitHere("bug?"); // TVK Not a bug. Would happen if insufficient reduction.
							thisGroundingIsSatisfied = true;
							break;
						} else if (isSatisfiable(gLit)) {
							if (posLitsRemaining == null) { posLitsRemaining = new ArrayList<Literal>(1); }
							if (containsSkolem) {
								Collection<GroundLiteral> expandedSkolems = expandSkolems(gLit, task.skolemsPerLiteral.get(lit));
								posLitsRemaining.addAll(expandedSkolems);
							} else {
								if (postponeSavingGroundLiterals) { task.storeGroundLiteralBeingHeld(); } 
								posLitsRemaining.add(gLit);
							}
						} else if (debugLevel > 0) { // Simply discard since since it cannot be satisfied.
							Utils.println("%   Discard an unsatisfiable ground literal: '" + gLit + "'.");
						}
					} else {
						//Utils.println("    NEG gLit=" + gLit + " not in? " + allQueriesIndexed);
						if (thisNegLiteralIsSatisfied(gLit)) {
							Utils.println("    NEG gLit=" + gLit + " is already satisfied!  Bug??"); // Utils.waitHere("bug??");
							thisGroundingIsSatisfied = true;
							break;
						} else if (isSatisfiable(gLit)) {
							if (negLitsRemaining == null) { negLitsRemaining = new ArrayList<Literal>(); }
							if (containsSkolem) {
								Utils.error("There should not be Skolems in NEGATIVE literals."); // TODO figure out what to do here if this does happen.
							} else {
								if (postponeSavingGroundLiterals) { task.storeGroundLiteralBeingHeld(); } 
								negLitsRemaining.add(gLit);
							}
						} else if (debugLevel > 0) { // Simply discard since since it cannot be satisfied.
							Utils.println("%   Discard an unsatisfiable ground literal: '~" + gLit + "'.");
						}
					}
				}
				skolemsInLiteralUnderConsideration = null; // Need to erase this 'global' when done (clean up this fragile code?).
				if (thisGroundingIsSatisfied) {
					if (debugLevel > 0) { Utils.println("%  Incrementing TRUE count.  No need to save the ground clause that results from bindings " + bl + " since it is known to be satisfied."); }
					countGroundingsDiscarded++;
					double multiplier = multiplierPerSatisfiedClause.get(clause);
					countOfSatisfiableGndClauses.put(clause, countOfSatisfiableGndClauses.get(clause) - 1);
					countOfTRUEs.put(clause, countOfTRUEs.get(clause) + multiplier);
				} else if (posLitsRemaining == null && negLitsRemaining == null) {
					if (debugLevel > 0) { Utils.println("%  Incrementing FALSE count.  No need to save the ground clause that results from bindings " + bl + " since no literals are satisfiable."); } // TODO - add something to the counts of FALSEs?
					countGroundingsDiscarded++;
					countOfSatisfiableGndClauses.put(clause, countOfSatisfiableGndClauses.get(clause) - 1);
					double multiplier = multiplierPerSatisfiedClause.get(clause);
					countOfFALSEs.put(clause, countOfFALSEs.get(clause) + multiplier);
				} else {
					List<Term> freeVarMap = getFreeVarMap(variablesRemainingInClause.get(clause), bl, existingBindings);
					if (freeVarMap == null && existingBindings != null) { Utils.error("freeVarMap=null: bl=" + bl + " existing=" + existingBindings + " clause " + clause); }
					// Recall that ground clauses can represent SETS of groundings, and need to account for that when calculating weights.
					GroundClause gndClause = getGroundClause(clause, posLitsRemaining, negLitsRemaining, freeVarMap, timeStamp);
					if (results == null) { results = new HashSet<GroundClause>(4); } // We don't want to remove duplicates here.  (TODO - if lots of duplicates, could count them up and keep only one, along with a count of duplicates.)
					results.add(gndClause);
					if (debugLevel > 3) { Utils.println("  bindings: " + bl + " produced ground clause #" + Utils.comma(results) + " '" + gndClause + "'."); }
					// This should have been checked above, but leave here nevertheless.
					if (results.size() > maxNumberClauseGroundings) { throw new MLNreductionProblemTooLargeException(debugLevel > 2 ? "**** Too many groundings (" + Utils.comma(results.size()) + ") for '" + clause + "'." : ""); }
				}
			}
		}
		if (debugLevel > 0) {
			long   end       = System.currentTimeMillis();
			double timeTaken = (end - start) / 1000.0;
			Utils.println("%   Took " + Utils.truncate(timeTaken, 3) + " seconds to perform the grounding of clause #" + Utils.comma(clauseToIndex.get(clause)) + ".  Produced " + Utils.comma(results) + " ground clauses and could ignore " + Utils.comma(countGroundingsDiscarded) + " ground clauses.");
		}		
		return results;
	}
	
	// Each ground clause needs to record the variable bindings that created it (so duplicates can be detected).
	// If ALL groundings are created at once, there is no need for this extra info. but it is needed for lazy evaluation.
	private List<Term> getFreeVarMap(Set<Variable> set, BindingList newBindings, BindingList existingBindings) {
		if (existingBindings == null) { return null; } // When no existing bindings, that indicates we don't want to bother saving (since we're creating ALL ground clauses)>
		if (set == null) { return new ArrayList<Term>(0); } // Need to indicate that there were no bindings.  TODO - or can this also be null?
		List<Term> results = new ArrayList<Term>(set.size());
		for (Variable var : set) {
			Term one = (newBindings == null ? null : newBindings.lookup(var)); // OK if newBindings not set.
			if (one != null) { results.add((Term) one); }
			else {
				Term two = (existingBindings == null ? null : existingBindings.lookup(var)); // Could save a lookup, but do some error checking.  
				if      (one == two  && one != null)  { results.add((Term) one); }
				else if (one != null && two == null)  { results.add((Term) one); }
				else if (one == null && two != null)  { results.add((Term) two); }
				else { Utils.error("odd state for getFreeVarMap: set=" + set + " one=" + one + " two=" + two + " newBindings=" + newBindings + " existingBindigs=" + existingBindings); }
			}
		}
		return results;
	}

	// Expand all the Skolems in this literal.  Do this by looking up all possible constants for each Skolem, doing a cross product if necessary.
	private Collection<GroundLiteral> expandSkolems(Literal lit, Collection<Term> skolemsToExpand) throws MLNreductionProblemTooLargeException {
		Collection<GroundLiteral> results = new HashSet<GroundLiteral>(4);
		List<TypeSpec> typeSpecs = task.collectLiteralArgumentTypes(lit);
		int counter = 0;
		double size = 1.0;
		List<Set<Term>> allArgPossibilities = new ArrayList<Set<Term>>(skolemsToExpand.size());
		for (Term term : lit.getArguments()) {
			if (skolemsToExpand.contains(term)) {
				TypeSpec typeSpec = typeSpecs.get(counter);
				Set<Term> existingConstants = task.getReducedConstantsOfThisType(typeSpec.isaType);
				if (existingConstants == null) { return null; }
				allArgPossibilities.add(existingConstants);
				size *= Utils.getSizeSafely(existingConstants);
			} else { // Also need to fold in the non-Skolems.
				Set<Term> termInSet = new HashSet<Term>(4);
				termInSet.add(term);
				allArgPossibilities.add(termInSet);
			}
			counter++;
		}
		if (debugLevel > 2) { Utils.println("% Have " + Utils.truncate(size, 0) + " expansions of '" + lit + "' due to its Skolems " + skolemsToExpand + "."); }
		if (size > maxSkolemExpansionPerLiteral) {
			throw new MLNreductionProblemTooLargeException(debugLevel > 2 ? "**** Too many Skolem expansions (" + Utils.truncate(size, 0) + ") for '" + lit + "'." : ".");
		}
		List<List<Term>> crossProduct = Utils.computeCrossProduct(allArgPossibilities, Integer.MAX_VALUE);
		for (List<Term> argList : crossProduct) {
			Literal newLit = task.stringHandler.getLiteral(lit.predicateName);
			List<Term> arguments2 = new ArrayList<Term>(lit.numberArgs());
			arguments2.addAll(argList);
			newLit.setArguments(arguments2);
			results.add(task.getCanonicalRepresentative(newLit));
		}
		if (debugLevel > 2
				) { Utils.println("%   Expansion: " + Utils.limitLengthOfPrintedList(results, 15)); }
		return results;
	}

	// Collect all the remaining ground literals.  EXPAND ANY REMAINING SKOLEM VARIABLES HERE.
	/* TVK : Not used here.
	private Set<GroundLiteral> collectRemainingSatisfiableLiteralGroundings(Clause clause, Literal lit) {
		Set<GroundLiteral>  results = null;
		if (lit.numberArgs() < 1) { // Handle zero-arity predicates.
			GroundLiteral gLit = task.getCanonicalRepresentative(lit, true, postponeSavingGroundLiterals);
			if (!isSatisfiable(gLit)) { return null; } // This case shouldn't happen (I think) with zero-arity literals, but check if it is still satisfiable (see comments below for the reason for this check).
			results = new HashSet<GroundLiteral>(4);
			if (postponeSavingGroundLiterals) { task.storeGroundLiteralBeingHeld(); } 
			results.add(gLit);
			return results;
		}
		CacheLiteralGrounding cache = null;		
		try { 
			cache = collectAndCacheRemainingGroundings(clause, lit);
		} catch (MLNreductionProblemTooLargeException e) {
			Utils.error("cross product too large - code to handle this needs to be written");
		}
		if (debugLevel > 1) { Utils.println("%     Remaining groundings for " + wrapLiteral(clause, lit) + ": " + Utils.limitLengthOfPrintedList(cache.getGroundingsStillNeeded(), 25)); }
		for (List<Term> terms : cache.getGroundingsStillNeeded()) {
			Literal litToGround = task.stringHandler.getLiteral(lit.predicateName);
		//	litToGround.setPrintUsingInFixNotation(lit.getPrintUsingInFixNotation());
			litToGround.setWeightOnSentence(lit.getWeightOnSentence()); // Might be BUGGY - since only the FIRST weight will be used in the canonical form.
			Literal gLit = null; // If contains a Skolem, need to expand it, assuming it is still satisfiable.
			boolean containsSkolem = false;
			if (Utils.getSizeSafely(terms) != lit.numberArgs()) { // Need to figure out how to build the new argument list.
				//  Might have something like 'p(x,y,x).'  Or might have some Skolems (which need to be expanded).  Or a combination.
				List<Term> arguments2 = new ArrayList<Term>(lit.numberArgs());
				int termCounter = 0;
				Collection<Term>  skolems = task.getSkolemsInThisNewLiteral(lit);
				Map<Term,Term> varMap = null;
				if (lit.numberArgs() > 0) { for (Term litTerm : lit.getArguments()) {
						//Utils.println("litTerm: " + litTerm + "  lit: " + lit + "  terms: " + terms);
						if      (skolems != null && skolems.contains(  litTerm)) { arguments2.add(litTerm); containsSkolem = true; } // Skolems handled elsewhere.
						else if (litTerm instanceof Term)                    { arguments2.add(litTerm); } // Just pass a constant along.
						else if (varMap  != null && varMap.containsKey(litTerm)) { arguments2.add(varMap.get(litTerm)); } // Already have seen this variable.
						else 						   {                           arguments2.add(terms.get(termCounter));
							if (litTerm instanceof Variable) { // Need to remember this binding.
								if (varMap == null) { varMap = new HashMap<Term,Term>(4); }
								varMap.put(litTerm, terms.get(termCounter));
							}
							termCounter++;
						}
					}
					if (termCounter != terms.size()) { Utils.error("Have termCounter = " + termCounter + " but terms = " + terms); }
					gLit = litToGround; // Since contains a Skolem, need to handle separately. 
					skolemsInLiteralUnderConsideration = skolems; // Using a 'global' instead of passing another argument everywhere.
					if (debugLevel > 3) { Utils.println(lit + " -> " + skolemsInLiteralUnderConsideration); }
				} 
				litToGround.setArguments(arguments2);
			} else {
				litToGround.setArguments(new ArrayList<Term>(terms));
				gLit = task.getCanonicalRepresentative(litToGround, true, postponeSavingGroundLiterals);
			}
			if (isSatisfiable(gLit)) {  // Due to the nature and order of the joins, some specific cases can remain where we know the truth value.
				if (results == null) { results = new HashSet<GroundLiteral>(4); }
				if (containsSkolem) {
					Collection<GroundLiteral> expandedSkolems;
					try {
						expandedSkolems = expandSkolems(gLit, task.skolemsPerLiteral.get(lit));
						results.addAll(expandedSkolems);
					} catch (MLNreductionProblemTooLargeException e) {
						Utils.error("Have too many Skolems for " + lit + " and " + gLit);
					}
				} else {
					GroundLiteral gLitToUse = (gLit instanceof GroundLiteral ? (GroundLiteral) gLit : task.getCanonicalRepresentative(gLit)); // There should NOT be any duplicates here ...
					if (postponeSavingGroundLiterals) { task.storeGroundLiteralBeingHeld(); } 
					results.add(gLitToUse);
				}
			} else if (debugLevel > 2) {
				Utils.println("%  Still have '" + gLit + "' but it is not satisfiable.  Discard.");
			}
			skolemsInLiteralUnderConsideration = null; // Need to erase this 'global' when done (clean up this fragile code?).
		}
		return results;
	}
	*/
	
	/* TVK : Not used here.
	private Set<GroundLiteral> collectSatisfiableLiterals(Collection<Clause> candidateClauses) {
		if (candidateClauses == null) { return null; }
		Set<GroundLiteral> results = null;
		for (Clause clause : candidateClauses) if (Utils.getSizeSafely(allGroundClausesPerClause.get(clause)) > 0) {
			for (GroundClause gndClause : allGroundClausesPerClause.get(clause)) if (gndClause.getLength() > 0) {
				for (int i = 0; i < gndClause.getLength(); i++) {
					if (results == null) { results = new HashSet<GroundLiteral>(4); }
					results.add(gndClause.getIthLiteral(i));
				}
				
			}
		}
		return results;
	}
	*/
	
	
	// Collect all those clauses that involve this literal and are satisfiable. 
	// NOTE: this literal is probably a new instance, and wont match via '==' or equals (which has a flag overriding it).
	/* TVK : Not used here.
	private Set<Clause> collectMatchingClausesThatAreSatisfiable(Literal queryGroundLiteral) {
		Set<Clause> results = null;		
		for (Literal candidate : task.getLiteralsContainingThisPredNameAndArity(queryGroundLiteral.predicateName, queryGroundLiteral.numberArgs())) {
			if (unifier.unify(candidate, queryGroundLiteral) != null) {
				if (results == null) { results = new HashSet<Clause>(4); }
				Clause clause = task.literalToClauseMap.get(candidate);
				if (debugLevel > 3) { Utils.println("% task.literalToClauseMap.get(" + candidate + ") = '" + clause + "'"); }
				if (Utils.getSizeSafely(literalsToKeep.get(clause)) > 0) { results.add(clause); }
			} else if (debugLevel > 3) { Utils.println("% Do not unify: " + candidate + " and " + queryGroundLiteral); }
		}	
		return results;
	}
	*/
	private Set<GroundClause> collectMatchingGroundClauses(GroundLiteral queryGroundLiteral) {
		Set<GroundClause> results = null;		
		for (GroundClause gndClause : allGroundClauses) {
			int size = gndClause.getLength();
			if (size > 0) for (int i = 0; i < size; i++) {
				GroundLiteral gLit = gndClause.getIthLiteral(i);
				if (gLit == queryGroundLiteral) {
					if (results == null) { results = new HashSet<GroundClause>(4); }
					results.add(gndClause); }
			}
		}	
		return results;
	}

	protected boolean haveCollectedAllGroundLiterals = false;
	protected boolean haveCollectedAllGroundClauses  = false;

	/*
	public void freezeAllGroundLiterals() {
		freezeAllGroundLiterals(true);
	}
	public void freezeAllGroundLiterals(boolean freezeValue) {
		for (GroundLiteral gLit     : allGroundLiterals) {  gLit.setFreeze(freezeValue); } 
	}
	*/
	// TVK:GMN Copied to GroundedMarkovNetowork. Can be removed
	@Deprecated
	public void clearAllMarkers() {
		setAllMarkers(null);
		//freezeAllGroundLiterals(false);// TODO - combine with setAllMarker to save some cycles?
	}

	// TVK:GMN Copied to GroundedMarkovNetowork. Can be removed
	@Deprecated
	public void setAllMarkers(Object marker) {
		setAllClauseMarkers( marker);
		setAllLiteralMarkers(marker);
		markerInUse = marker;
	}
	// TVK:GMN Copied to GroundedMarkovNetowork. Can be removed
	@Deprecated
	public void setAllClauseMarkers(Object marker) {
		if (!haveCollectedAllGroundClauses) {
			Utils.error("Cannot set all the  markers until all the gound clauses have been collected.");
		}
		GroundClause gndClause = getFirstGroundClause();
		while (gndClause != null) {
			gndClause.setMarker(marker);
			gndClause = getNextGroundClause();
		}
		markerInUse = marker;
	}
	// TVK:GMN Copied to GroundedMarkovNetowork. Can be removed
	@Deprecated
	public void setAllLiteralMarkers(Object marker) {
		if (!haveCollectedAllGroundLiterals) {
			Utils.error("Cannot set all the markers until all the gound literals have been collected.");
		}
		GroundLiteral gLit = getFirstGroundLiteral();
		while (gLit != null) {
			gLit.setMarker(marker);
			gLit = getNextGroundLiteral();
		}
		markerInUse = marker;
	}
	// TVK:GMN Copied to GroundedMarkovNetowork. Can be removed
	@Deprecated
	public void clearMarkedClauses() {
		GroundClause gndClause = getFirstMarkedGroundClause();
		while (gndClause != null) { 
			gndClause.setMarker(null);
			gndClause = getNextMarkedGroundClause();
		}
	}
	
	private void collectAllGroundLiterals() {
		if (debugLevel > 1) { Utils.println("%     Collecting all ground literals."); }
		if (allGroundLiteralsOrig != null) { Utils.error("Need to have allGroundLiteralsOrig=null when this is called."); }
		if (allGroundLiterals     != null) { Utils.error("Need to have allGroundLiterals=null when this is called."); }
		if (Utils.getSizeSafely(allGroundClausesOrig) < 1) { return; }
		if (Utils.getSizeSafely(allGroundClausesOrig) < 1) { 
			if (debugLevel > 1) { Utils.println("%       There are no remaining satisfiable literal groundings, so no ground literals to collect."); }
			allGroundLiteralsOrig  = null;
			help_collectAllGroundLiterals();
			return; 
		}
		Set<GroundLiteral> allGroundLiteralsAsSet = new HashSet<GroundLiteral>(4); // Initially use a set, so duplicates will be removed.
		for (GroundClause gndClause : allGroundClausesOrig) {
			//Utils.println("% There are " + Utils.comma(allLits) + " remaining literals in '" + clause.toString(Integer.MAX_VALUE) + "': " + Utils.limitLengthOfPrintedList(allLits, 25));
			if (gndClause.getLength() > 0) for (int i = 0; i < gndClause.getLength(); i++) {
				allGroundLiteralsAsSet.add(gndClause.getIthLiteral(i)); // Duplicates will be removed because this is a set.
			}			
		}
		// Now we need to have the ground literals point back to the ground clauses that contain them.
		if (allGroundLiteralsAsSet != null) {
			allGroundLiteralsOrig = new ArrayList<GroundLiteral>(allGroundLiteralsAsSet);
			allGroundLiteralsAsSet = null;
			for (GroundLiteral gLit : allGroundLiteralsOrig) {
				//		Utils.println("cleared " + gLit.toString(Integer.MIN_VALUE));
				gLit.clearGndClauseSet(); }
			for (GroundClause gndClause : allGroundClausesOrig) {
				if (gndClause.getLength() > 0)
					for (int i = 0; i < gndClause.getLength(); i++) {
						// Utils.println("% GTMN: Added " + gndClause.getIthLiteral(i).toString(Integer.MIN_VALUE) + " to " + gndClause.toPrettyString());
						gndClause.getIthLiteral(i).addGndClause(gndClause);
					}
			}
		} else {allGroundLiteralsOrig = null; }
		if (debugLevel > 1) { Utils.println("%       Collected " + Utils.comma(allGroundLiteralsOrig) + " ground literals."); }
		if (debugLevel > 2 && allGroundLiteralsOrig != null) {
			double total = 0.0;
			for (GroundLiteral gLit : allGroundLiteralsOrig) { total += Utils.getSizeSafely(gLit.getGndClauseSet()); }
			Utils.println("%       On average, each ground literal is in " + Utils.truncate(total / allGroundLiteralsOrig.size(), 1) + " ground clauses.");
			//Utils.waitHere("ijk");
		}
		help_collectAllGroundLiterals(); 
	}
	private void help_collectAllGroundLiterals() {
		allGroundLiterals         = allGroundLiteralsOrig;
		allGroundLiteralsOrigSize = Utils.getSizeSafely(allGroundLiteralsOrig);
		collectQueryGroundLiteralsNotInReducedNetwork();
		groundQueryLiteralNotInReducedNetworkOrig = new HashSet<GroundLiteral>(4);
		groundQueryLiteralNotInReducedNetworkOrig.addAll(groundQueryLiteralNotInReducedNetwork);
		numberOfNonLazyGroundLiterals = Utils.getSizeSafely(allGroundLiterals);
		resetNextGroundLiteral();
		haveCollectedAllGroundLiterals = true;		
	}

	private Set<GroundLiteral> groundQueryLiteralNotInReducedNetwork     = null;
	private Set<GroundLiteral> groundQueryLiteralNotInReducedNetworkOrig = null;
	private void collectQueryGroundLiteralsNotInReducedNetwork() {
		groundQueryLiteralNotInReducedNetwork = new HashSet<GroundLiteral>(4); // Make anew, so groundQueryLiteralNotInReducedNetworkOrig not touched.
		Set<GroundLiteral> qLits = task.getQueryLiterals();
		if (qLits == null) { Utils.error("Should have some query literals?"); }
		Set<GroundLiteral> tempGndLits = new HashSet<GroundLiteral>(2 * allGroundLiterals.size());
		tempGndLits.addAll(allGroundLiterals); // Use space to create this to save time with lookups.
		for (GroundLiteral gLit : qLits) if (!tempGndLits.contains(gLit)) {
			groundQueryLiteralNotInReducedNetwork.add(gLit);
		}
		if (debugLevel > -110) { Utils.println("% Of the " + Utils.comma(allGroundLiterals) + " ground literals, " + Utils.comma(groundQueryLiteralNotInReducedNetwork) + " are not in the reduced network."); }
	}
	public boolean isaQueryLiteralNotInReducedNetwork(GroundLiteral gLit) { // Use this 'double negative' to make it clear where we're looking.
		return (groundQueryLiteralNotInReducedNetwork != null && groundQueryLiteralNotInReducedNetwork.contains(gLit));
	}

	public void initializeForTheseQueries(Collection<GroundLiteral> queries) {
		if (queries == task.getQueryLiterals()) {
			allGroundClauses             = allGroundClausesOrig;
			numberOfNonLazyGroundClauses = Utils.getSizeSafely(allGroundClauses);
			allGroundLiterals            = allGroundLiteralsOrig;
			groundQueryLiteralNotInReducedNetwork = groundQueryLiteralNotInReducedNetworkOrig;
			resetNextGroundClause();
			resetNextGroundLiteral();
			return; 
		}
		// If different from the queries for which the MLN was grounded:
		//   a) see if any queries not in the task's query literals
		//   b) reduce allGroundLiterals and allGroundClauses, using the KBMC (Knowledge-based model construction) principle
		//      (if difference is slight, simply keep allGroundLiterals and allGroundClauses as is)
		Set<GroundLiteral> allQueries = task.getQueryLiterals();
		if (allQueries == null) { Utils.error("Should not have allQueries = null."); }
		int countOfExistingQueries = 0;
		List<GroundLiteral> evidence = null;
		List<GroundLiteral> unknowns = null;
		for (GroundLiteral qLit : queries) {
			if (allQueries.contains(qLit))     { countOfExistingQueries++; continue; }
			if (task.isaEvidenceLiteral(qLit)) { 
				if (evidence == null) { evidence = new ArrayList<GroundLiteral>(1); }
				evidence.add(qLit);
			}
			if (unknowns == null) { unknowns = new ArrayList<GroundLiteral>(1); }
			unknowns.add(qLit);
			Utils.warning("% Unknown query literal #" + Utils.comma(unknowns) + ": " + qLit);
			if (unknowns.size() > 10) { break; }
		}
		if (unknowns.size() > 0) { Utils.error("Fix the problem with the unknown ground literals."); }
		for (GroundLiteral gLit : evidence) { // The knowns will be handled separately (after all, their truth values are known).
			if (!queries.remove(gLit)) { Utils.error("Could not find " + gLit); }
		}
		if (countOfExistingQueries < 0.5 * allQueries.size()) { // See if only a small fraction of all the queries are needed.
			Utils.writeMe("Need to implement KBMC here."); // Already implemented for BruteForce???
			// Walk through the remaining queries, for each find which ground clauses they match.
			// Keep these clauses, as well as all the other ground literals in these clauses.
			// Notice that these changes will not be reset until the next call to initializeForTheseQueries.
			collectQueryGroundLiteralsNotInReducedNetwork();
		} else { // Simply use all the ground clauses.
			allGroundClauses                      = allGroundClausesOrig;
			numberOfNonLazyGroundClauses          = Utils.getSizeSafely(allGroundClauses);
			allGroundLiterals                     = allGroundLiteralsOrig;
			groundQueryLiteralNotInReducedNetwork = groundQueryLiteralNotInReducedNetworkOrig;
		}
		resetNextGroundClause();
		resetNextGroundLiteral();
	}

	private Collection<GroundClause> getAllClauseGroundings(Clause clause, TimeStamp timeStamp) throws MLNreductionProblemTooLargeException {
		if (allGroundClausesPerClause == null) { allGroundClausesPerClause = new HashMap<Clause,Set<GroundClause>>(4); }
		Set<GroundClause> results = allGroundClausesPerClause.get(clause);
		if (Utils.getSizeSafely(results) == countOfSatisfiableGndClauses.get(clause)) { return results; }
		if (results != null) { Utils.writeMe("Already have some groundings here ..."); } // If we simply overwrite these, might mess up other data structures.
		results = collectRemainingClauseGroundings(clause, timeStamp);
		if (countOfSatisfiableGndClauses.get(clause) != Utils.getSizeSafely(results)) {
			Utils.error("countOfSatisfiableGndClauses.get(clause) = " + Utils.truncate(countOfSatisfiableGndClauses.get(clause), 0) +
						" but generated " + Utils.comma(results) + " groundings.");
		}
		allGroundClausesPerClause.put(clause, results);
		// Utils.println("% GTMN: Size: " + Utils.getSizeSafely(allGroundClausesPerClause.get(clause)) + " of " + clause.toPrettyString(Integer.MIN_VALUE));
		clausesFullyGrounded.add(clause);
		removePointersToConstants(clause); // No longer need these lists once all groundings have been created, so release to Java's garbage collector.
		return results;
	}
	private void collectAllGroundClauses() {
		if (debugLevel > -110) { Utils.println("%     Collecting all ground clauses."); }
		if (allGroundClausesOrig != null) { Utils.error("Need to have allGroundClausesOrig=null when this is called."); }
		if (allGroundClauses     != null) { Utils.error("Need to have allGroundClauses=null when this is called.");     }
		// TVK: allGroundClausesPerClause should already be set here.
		if (allGroundClausesPerClause == null) { Utils.error("Need to have allGroundClausesPerClause!=null when this is called.");     }

		if (countofUniqueGroundClauses < 1) { 
			if (debugLevel > -110) { Utils.println("%       There are no remaining satisfiable clause groundings, so no ground clauses to collect."); }
			haveCollectedAllGroundClauses = true;
			resetNextGroundClause();
			return; 
		}
		allGroundClausesOrig      = new ArrayList<GroundClause>();
		// Initializing here, causes it to reset the values and it is not necessary to initialize it here.
		// allGroundClausesPerClause = new HashMap<Clause,Set<GroundClause>>(4); // Does this need to also be PerClause??? MOD TVK. Not used
		for (Integer code : hashOfGroundClauses.keySet()) {
			allGroundClausesOrig.addAll(hashOfGroundClauses.get(code));
		}
		if (debugLevel > -110) { Utils.println("%       Collected " + Utils.comma(allGroundClausesOrig) + " ground clauses."); }
		allGroundClauses             = allGroundClausesOrig;
		allGroundClausesOrigSize     = Utils.getSizeSafely(allGroundClausesOrig);
		numberOfNonLazyGroundClauses = Utils.getSizeSafely(allGroundClauses);
		resetNextGroundClause();
		haveCollectedAllGroundClauses = true;
	}
	
	/* TVK : Not used here.
	public ArrayList<GroundClause> OLD_getAllGroundClausesWhenNoLazy() {
		if (haveCollectedAllGroundLiterals) { return allGroundClauses; }
		Utils.error("Calling getAllGroundClauses(), but haveCollectedAllGroundLiterals=false!");
		return null;
	}*/
	
	///////////////////////////////////////////////////////////////////////////////////////////////////////////
	// Note: these are added by MCSAT.  Need to be careful since we now have duplicates.
	// MCSAT makes sure only these, and never their 'parent' negated ground clause, is in use at any point.
	private List<GroundClause> allGroundUnitClausesFromNegWgtClauses = new ArrayList<GroundClause>(0);
	/* TVK : Not used here.
	public void addTheseUnitClauseFromNegWgtClauses(List<GroundClause> gndClauses) {
		if (!allGroundUnitClausesFromNegWgtClauses.addAll(gndClauses))    { Utils.error("Problem adding "   + Utils.comma(gndClauses) + " unit clauses."); }
		numberOfUnitClauseFromNegWgtClauses = allGroundUnitClausesFromNegWgtClauses.size();
		resetNextGroundClause();
	}
	public void removeTheseUnitClauseFromNegWgtClauses(List<GroundClause> gndClauses) {
		if (!allGroundUnitClausesFromNegWgtClauses.removeAll(gndClauses)) { Utils.error("Problem removing " + Utils.comma(gndClauses) + " unit clauses."); }
		numberOfUnitClauseFromNegWgtClauses = allGroundUnitClausesFromNegWgtClauses.size();
		resetNextGroundClause();
	}*/
	
	private List<GroundClause> allPermanentLazyGroundClauses = new ArrayList<GroundClause>(0); // These are the lazy ground clauses that 'touch' (intersect with the regular ground literals).
	/* TVK : Not used here.
	private void addThesePermanentLazyClauses(Collection<GroundClause> gndClauses) {
		if (gndClauses == null) { return; }
		if (!doingLazyInference) { Utils.error("Should not call when doingLazyInference=false."); }
		if (!allPermanentLazyGroundClauses.addAll(gndClauses))   { Utils.error("Problem adding " + Utils.comma(gndClauses) + " permanent lazy clauses."); }
		numberOfPermanentLazyGroundClauses = allPermanentLazyGroundClauses.size();
		resetNextGroundClause();
	}
	 */	
	private List<GroundClause> allLazyGroundClauses = new ArrayList<GroundClause>(0);
	/* TVK : Not used here.
	private void addTheseLazyClauses(Collection<GroundClause> gndClauses) {
		if (gndClauses == null) { return; }
		if (!doingLazyInference) { Utils.error("Should not call when doingLazyInference=false."); }
		if (!allLazyGroundClauses.addAll(gndClauses))   { Utils.error("Problem adding " + Utils.comma(gndClauses) + " lazy clauses."); }
		numberOfLazyGroundClauses = allLazyGroundClauses.size();
		for (GroundClause gndClause : gndClauses) { gndClause.age = 0; }
		resetNextGroundClause();
	}
	*/
	public void removeOldLazyClauses(short maxAge) {
		if (!doingLazyInference) { return; }
		boolean resetNeeded = false;
		if (numberOfLazyGroundClauses > 0) for (GroundClause gndClause : allLazyGroundClauses) {
			gndClause.age++;
			if (gndClause.age > maxAge) { 
				resetNeeded = true;
				removeThisLazyClause(gndClause, false);
				for (int i = 0; i < gndClause.getLength(); i++) {
					GroundLiteral   gLit = gndClause.getIthLiteral(i);
					gLit.hasBeenInterned = false; // Note that for this literal, some ground clauses are not materialized.
				}
			}
		}
		if (resetNeeded) { removeThisLazyClause(null, true); }
	}
	/* TVK : Not used here.
	public void removeTheseLazyClausesFromNegWgtClauses(List<GroundClause> gndClauses) {
		if (allLazyGroundClauses.removeAll(gndClauses)) { Utils.error("Problem removing " + Utils.comma(gndClauses) + " lazy clauses."); }
		numberOfLazyGroundClauses = allLazyGroundClauses.size();
		resetNextGroundClause();
	}	
	*/
	/* TVK : Not used here.
	public void addThisLazyClause(GroundClause gndClause) {
		if (!doingLazyInference) { Utils.error("Should not call when doingLazyInference=false."); }
		if (!allLazyGroundClauses.add(gndClause))    { Utils.error("Problem adding this lazy clause: '"   + gndClause + "'."); }
		numberOfLazyGroundClauses = allLazyGroundClauses.size();
		resetNextGroundClause();
	}
	*/
	private void removeThisLazyClause(GroundClause gndClause, boolean doReset) {
		if (!doingLazyInference) { Utils.error("Should not call when doingLazyInference=false."); }
		if (gndClause != null && !allLazyGroundClauses.remove(gndClause)) { Utils.error("Problem removing this lazy clause: '" + gndClause + "'."); }
		if (doReset) {
			numberOfUnitClauseFromNegWgtClauses = allLazyGroundClauses.size();
			resetNextGroundClause();
		}
	}	

	public void makeSureAllGroundClausesAreMaterialized(GroundLiteral lit) {
		if (!doingLazyInference) { return; }
		Utils.writeMe();
	}
	
	private int counterIntoGroundClauses            = 0;
	private int numberOfNonLazyGroundClauses        = 0; // Does NOT include the UnitClause ones.
	private int numberOfUnitClauseFromNegWgtClauses = 0; // Instead, they are in this list.
	private int numberOfPermanentLazyGroundClauses  = 0;
	private int numberOfLazyGroundClauses           = 0;
	private int totalNumberOfGroundClauses          = 0;
	private List<GroundClause> allGroundClauses_ExpensiveVersion = new ArrayList<GroundClause>(0);
	public  List<GroundClause> getAllGroundClauses_ExpensiveVersion() { // This version wastes space, but makes for easier calling code.
		if (!haveCollectedAllGroundClauses) { Utils.error("Calling getAllGroundClauses(), but haveCollectedAllGroundClauses=false!"); }
		if (numberOfUnitClauseFromNegWgtClauses + numberOfLazyGroundClauses == 0) {
			if (debugLevel > 2) { Utils.println("getAllGroundClauses_ExpensiveVersion: allGroundClauses = " + Utils.limitLengthOfPrintedList(allGroundClauses, 25)); }
			return allGroundClauses;
		}
		if (allGroundClauses_ExpensiveVersion.size() == totalNumberOfGroundClauses) {
			return allGroundClauses_ExpensiveVersion; // A bit risky if same size, but different objects (i.e., should always call resetNextGroundClause when making changes).
		}
		allGroundClauses_ExpensiveVersion.clear();
		allGroundClauses_ExpensiveVersion.addAll(allGroundClauses);
		allGroundClauses_ExpensiveVersion.addAll(allGroundUnitClausesFromNegWgtClauses);
		allGroundClauses_ExpensiveVersion.addAll(allPermanentLazyGroundClauses);
		allGroundClauses_ExpensiveVersion.addAll(allLazyGroundClauses);
		return allGroundClauses_ExpensiveVersion;
	}
	public int getNumberOfGroundClauses() {
		if (debugLevel > 2) { 
			Utils.println("% numberOfNonLazyGroundClauses = "        + Utils.comma(numberOfNonLazyGroundClauses)        + 
						  "  numberOfUnitClauseFromNegWgtClauses = " + Utils.comma(numberOfUnitClauseFromNegWgtClauses) + 
						  "  numberOfPermanentLazyGroundClauses  = " + Utils.comma(numberOfPermanentLazyGroundClauses)  + 
						  "  numberOfLazyGroundClauses = "           + Utils.comma(numberOfLazyGroundClauses)); 
		}
		if (!haveCollectedAllGroundClauses) { Utils.error("haveCollectedAllGroundClauses = false"); }
		return totalNumberOfGroundClauses;
	}
	public  void resetNextGroundClause() { 
		allGroundClauses_ExpensiveVersion.clear(); 
		counterIntoGroundClauses   = 0;
		totalNumberOfGroundClauses = numberOfNonLazyGroundClauses + numberOfUnitClauseFromNegWgtClauses + numberOfPermanentLazyGroundClauses + numberOfLazyGroundClauses; 
	}
	public GroundClause getNextGroundClause() {
		int currentCount = counterIntoGroundClauses++;
		if (currentCount >= getNumberOfGroundClauses()) {
			counterIntoGroundClauses = 0; // Next time start at front of list.
			return null; // Note at end of list.
		}
		if (currentCount >= 0 && currentCount < numberOfNonLazyGroundClauses) { 
			// These prints are here to track down a bug (11/09) - JWS
		//	Utils.println("numberOfNonLazyGroundClauses = " + Utils.comma(numberOfNonLazyGroundClauses));
		//	Utils.println("|allGroundClauses|           = " + Utils.comma(allGroundClauses));
		//	Utils.println("numberOfNonLazyGroundClauses = "             + Utils.comma(numberOfNonLazyGroundClauses)        +
		//				  ", numberOfUnitClauseFromNegWgtClauses = "    + Utils.comma(numberOfUnitClauseFromNegWgtClauses) +
		//				  ", numberOfLazyGroundClauses = "              + Utils.comma(numberOfLazyGroundClauses)           +
		//				  ", totalNumberOfGroundClauses = "             + Utils.comma(totalNumberOfGroundClauses));
			return allGroundClauses.get(currentCount); 
		}
		currentCount -= numberOfNonLazyGroundClauses;
		if (currentCount >= 0 && currentCount < numberOfUnitClauseFromNegWgtClauses) {
			return allGroundUnitClausesFromNegWgtClauses.get(currentCount); 
		}
		currentCount -= numberOfUnitClauseFromNegWgtClauses;
		if (currentCount >= 0 && currentCount < numberOfPermanentLazyGroundClauses) {
			return allPermanentLazyGroundClauses.get(currentCount); 
		}
		currentCount -= numberOfPermanentLazyGroundClauses;
		if (currentCount >= 0 && currentCount < numberOfLazyGroundClauses) {
			return allLazyGroundClauses.get(currentCount); 
		}
		errorWithGroundClauses("Error in getNextGroundClause.");
		return null;
	}
	public void errorWithGroundClauses(String msg) {
		Utils.println("\n% " + msg);
		Utils.error(" Should not reach here: counterIntoGroundClauses = " + Utils.comma(counterIntoGroundClauses)      +
					" numberOfNonLazyGroundClauses = "             + Utils.comma(numberOfNonLazyGroundClauses)        +
					" numberOfUnitClauseFromNegWgtClauses = "      + Utils.comma(numberOfUnitClauseFromNegWgtClauses) +
					" numberOfPermanentLazyGroundClauses = "       + Utils.comma(numberOfPermanentLazyGroundClauses)  +
					" numberOfLazyGroundClauses = "                + Utils.comma(numberOfLazyGroundClauses)           +
					" totalNumberOfGroundClauses = "               + Utils.comma(totalNumberOfGroundClauses));
	}
	public GroundClause getRandomGroundClause() {
		return getIthGroundClause(Utils.random0toNminus1(totalNumberOfGroundClauses));
	}
	public GroundClause getIthGroundClause(int i) {
		if (i >= totalNumberOfGroundClauses) { Utils.error("Only have " + Utils.comma(totalNumberOfGroundClauses) + " ground clauses, but i = " + Utils.comma(i));}
		if (i < numberOfNonLazyGroundClauses) { 
			return allGroundClauses.get(i); 
		}
		i -= numberOfNonLazyGroundClauses;
		if (i < numberOfUnitClauseFromNegWgtClauses) {
			return allGroundUnitClausesFromNegWgtClauses.get(i); 
		}
		i -= numberOfUnitClauseFromNegWgtClauses;
		if (i < numberOfPermanentLazyGroundClauses) {
			return allPermanentLazyGroundClauses.get(i); 
		}
		i -= numberOfPermanentLazyGroundClauses;
		if (i < numberOfLazyGroundClauses) {
			return allLazyGroundClauses.get(i); 
		}
		Utils.error("Should not reach here: i = "                  + Utils.comma(i) +
					" numberOfNonLazyGroundClauses = "             + Utils.comma(numberOfNonLazyGroundClauses) +
					" numberOfUnitClauseFromNegWgtClauses = "      + Utils.comma(numberOfUnitClauseFromNegWgtClauses) +
					" numberOfLazyGroundClauses = "                + Utils.comma(numberOfLazyGroundClauses) +
					" totalNumberOfGroundClauses = "               + Utils.comma(totalNumberOfGroundClauses));
		return null;
	}
	public int countMarkedClauses() {
		int count = 0;
		GroundClause gndClause = getFirstGroundClause();
		while (gndClause != null) { if (gndClause.getMarker() != null) { count++; } gndClause = getNextGroundClause(); }
		return count;
	}
	public GroundClause getNextMarkedGroundClause() {
		GroundClause result = getNextGroundClause();
		while (result != null && !isaMarkedGroundClause(result)) { result = getNextGroundClause(); }
		return result;
	}
	public GroundClause getNextUnMarkedGroundClause() {
		GroundClause result = getNextGroundClause();
		while (result != null &&  isaMarkedGroundClause(result)) { result = getNextGroundClause(); }
		return result;
	}
	public GroundClause getFirstGroundClause()  {
		if (!haveCollectedAllGroundClauses) { Utils.error("Calling getAllGroundClauses(), but haveCollectedAllGroundClauses=false!"); }
		counterIntoGroundClauses = 0;
		return getNextGroundClause();
	}
	public GroundClause getFirstMarkedGroundClause()  {
		counterIntoGroundClauses = 0;
		return getNextMarkedGroundClause();
	}
	public GroundClause getFirstUnMarkedGroundClause()  {
		counterIntoGroundClauses = 0;
		return getNextUnMarkedGroundClause();
	}

	// Same stuff, but for literals.

	private List<GroundLiteral> allLazyGroundLiterals = new ArrayList<GroundLiteral>(0);
	public void addThisLazyLiteral(GroundLiteral gLit) {
		if (!doingLazyInference) { Utils.error("Should not call when doingLazyInference=false."); }
		if (!allLazyGroundLiterals.add(gLit))    { Utils.error("Problem adding this lazy Literal: '"   + gLit + "'."); }
		numberOfLazyGroundLiterals = allLazyGroundLiterals.size();
		resetNextGroundLiteral();
	}
	/* TVK : Not used here.
	public void removeThisLazyLiteral(GroundLiteral gLit) {
		if (!doingLazyInference) { Utils.error("Should not call when doingLazyInference=false."); }
		if (!allLazyGroundLiterals.remove(gLit)) { Utils.error("Problem removing this lazy Literal: '" + gLit + "'."); }
		numberOfLazyGroundLiterals = allLazyGroundLiterals.size();
		resetNextGroundLiteral();
	}	
	*/
	private int counterIntoGroundLiterals     = 0;
	private int numberOfNonLazyGroundLiterals = 0; 
	private int numberOfLazyGroundLiterals    = 0;
	private int totalNumberOfGroundLiterals   = 0;
	private List<GroundLiteral> allGroundLiterals_ExpensiveVersion = new ArrayList<GroundLiteral>(0);

	public  void resetNextGroundLiteral() { 
		allGroundLiterals_ExpensiveVersion.clear(); 
		counterIntoGroundLiterals = 0;
		totalNumberOfGroundLiterals = numberOfNonLazyGroundLiterals + numberOfLazyGroundLiterals; 
	}
	public int getNumberOfGroundLiterals() {
		if (!haveCollectedAllGroundLiterals) { Utils.error("haveCollectedAllGroundLiterals = false"); }
		if (debugLevel > 2) { 
			Utils.println("% numberOfNonLazyGroundLiterals = " + Utils.comma(numberOfNonLazyGroundLiterals) + 
					      "  numberOfLazyGroundLiterals = "  + Utils.comma(numberOfLazyGroundLiterals)); 
		}	
		return totalNumberOfGroundLiterals;
	}
	public List<GroundLiteral> getAllGroundLiterals_ExpensiveVersion() { // This version wastes space, but makes for easier calling code.
		if (!haveCollectedAllGroundLiterals) { Utils.error("Calling getAllGroundLiterals(), but haveCollectedAllGroundLiterals=false!"); }
		if (numberOfLazyGroundLiterals == 0) {
			return allGroundLiterals;
		}
		if (allGroundLiterals_ExpensiveVersion.size() == totalNumberOfGroundLiterals) {
			return allGroundLiterals_ExpensiveVersion; // A bit risky if same size, but different objects (i.e., should always call resetNextGroundLiteral when making changes).
		}
		allGroundLiterals_ExpensiveVersion.clear();
		allGroundLiterals_ExpensiveVersion.addAll(allGroundLiterals);
		allGroundLiterals_ExpensiveVersion.addAll(allLazyGroundLiterals);
		return allGroundLiterals_ExpensiveVersion;
	}
	public GroundLiteral getRandomGroundLiteral() {
		if (!haveCollectedAllGroundLiterals) { Utils.error("Calling getAllGroundLiterals(), but haveCollectedAllGroundLiterals=false!"); }
		return getIthGroundLiteral(Utils.random0toNminus1(totalNumberOfGroundLiterals));
	}
	public GroundLiteral getNextGroundLiteral() {
		int currentCount = counterIntoGroundLiterals++;
		if (currentCount >= totalNumberOfGroundLiterals)  {
			counterIntoGroundLiterals = 0; // Next time start at front of list.
			return null; // Note at end of list.
		}
		if (currentCount < numberOfNonLazyGroundLiterals) { 
			return allGroundLiterals.get(currentCount); 
		}
		currentCount -= numberOfNonLazyGroundLiterals;
		if (currentCount < numberOfLazyGroundLiterals)    {
			return allLazyGroundLiterals.get(currentCount); 
		}
		Utils.error("Should not reach here: counterIntoGroundLiterals = " + Utils.comma(counterIntoGroundLiterals)     +
					" numberOfNonLazyGroundLiterals = "                   + Utils.comma(numberOfNonLazyGroundLiterals) +
					" numberOfLazyGroundLiterals = "                      + Utils.comma(numberOfLazyGroundLiterals)    +
					" totalNumberOfGroundLiterals = "                     + Utils.comma(totalNumberOfGroundLiterals));
		return null;
	}
	public GroundLiteral getIthGroundLiteral(int i) {
		if (i >= totalNumberOfGroundLiterals) { Utils.error("Only have " + Utils.comma(totalNumberOfGroundLiterals) + " ground Literals, but i = " + Utils.comma(i));}
		if (i < numberOfNonLazyGroundLiterals) { 
			return allGroundLiterals.get(i); 
		}
		i -= numberOfNonLazyGroundLiterals;
		if (i < numberOfLazyGroundLiterals) {
			return allLazyGroundLiterals.get(i); 
		}
		Utils.error("Should not reach here: i = "       + Utils.comma(i) +
					" numberOfNonLazyGroundLiterals = " + Utils.comma(numberOfNonLazyGroundLiterals) +
					" numberOfLazyGroundLiterals = "    + Utils.comma(numberOfLazyGroundLiterals) +
					" totalNumberOfGroundLiterals = "   + Utils.comma(totalNumberOfGroundLiterals));
		return null;
	}
	public GroundLiteral getNextMarkedGroundLiteral() {
		GroundLiteral result = getNextGroundLiteral();
		while (result != null && !isaMarkedGroundLiteral(result)) { result = getNextGroundLiteral(); }
		return result;
	}
	public GroundLiteral getNextUnMarkedGroundLiteral() {
		GroundLiteral result = getNextGroundLiteral();
		while (result != null &&  isaMarkedGroundLiteral(result)) { result = getNextGroundLiteral(); }
		return result;
	}
	public GroundLiteral getFirstGroundLiteral()  {
		counterIntoGroundLiterals = 0;
		return getNextGroundLiteral();
	}
	public GroundLiteral getFirstMarkedGroundLiteral()  {
		if (!haveCollectedAllGroundLiterals) { Utils.error("Calling getAllGroundLiterals(), but haveCollectedAllGroundLiterals=false!"); }
		counterIntoGroundLiterals = 0;
		return getNextMarkedGroundLiteral();
	}
	public GroundLiteral getFirstUnMarkedGroundLiteral()  {
		counterIntoGroundLiterals = 0;
		return getNextUnMarkedGroundLiteral();
	}

	public void reportGroundLiteralState(int i) {
		int counter = 0;
		GroundLiteral gLit = getFirstGroundLiteral();
		while (gLit != null) {
			if (++counter > i) { Utils.println("% ... will not print the rest of the ground literals."); return; }
			Utils.println("%  "  + gLit + ": " + gLit.getValue());
			gLit = getNextGroundLiteral();
		}
	}

	private boolean[]          savedGroundLiteralState     = null;
	private Set<GroundLiteral> savedLazyGroundLiteralState = null; // Will hold lazy ground literals that are TRUE.
	public void saveCurrentStateOfGroundLiterals(TimeStamp timeStamp) {
		if (!haveCollectedAllGroundLiterals) { Utils.error("Calling getAllGroundLiterals(), but haveCollectedAllGroundLiterals=false!"); }
		if (savedGroundLiteralState == null) {
			savedGroundLiteralState = new boolean[Utils.getSizeSafely(allGroundLiterals)];
		}
		int counter = 0;
		if (allGroundLiterals != null) for (GroundLiteral gLit : allGroundLiterals) {
			savedGroundLiteralState[counter++] = gLit.getValue();
		}
		if (savedLazyGroundLiteralState == null) {
			savedLazyGroundLiteralState = new HashSet<GroundLiteral>(4);
		}
		if (allLazyGroundLiterals != null) for (GroundLiteral gLit : allLazyGroundLiterals) {
			boolean truthValue = gLit.getValue();
			if ( truthValue) { savedLazyGroundLiteralState.add(   gLit); } // Need to record lazy ground literals with non-default values.
			if (!truthValue) { savedLazyGroundLiteralState.remove(gLit); }
		}		
	}

	public void restoreSavedStateOfGroundLiterals(TimeStamp timeStamp) {
		if (savedGroundLiteralState == null) { Utils.error("Calling getAllGroundLiterals(), but have never called saveCurrentStateOfGroundLiterals."); }
		int counter = 0;
		if (allGroundLiterals != null) for (GroundLiteral gLit : allGroundLiterals) {
			gLit.setValue(savedGroundLiteralState[counter++], null, timeStamp); // Use null as the 2nd argument here, since we need to fully recompute the isSatisfied of clauses if we want a final 'actives' count (below).
		}
		Set<GroundLiteral> usedThisLazyGlit = new HashSet<GroundLiteral>(4);
		if (allLazyGroundLiterals != null) for (GroundLiteral gLit : allLazyGroundLiterals) {
			gLit.setValue(savedLazyGroundLiteralState.contains(gLit), null, timeStamp);	
			usedThisLazyGlit.add(gLit);
		}
		// Check for any saved lazy ground literals that is no longer present.
		for (GroundLiteral gLit : savedLazyGroundLiteralState) if (!usedThisLazyGlit.contains(gLit)) {
			gLit.setValue(true, null, timeStamp);
			addThisLazyLiteral(gLit); // Need to add this back into the 'lazy' collection.
		}
	}
	
	///////////////////////////////////////////////////////////////////////////////////////////////////////////
	
	private int countOfMarkedGroundClauses = -1; // See how many of the grounded clauses are in play for this instance.
	public int countOfMarkedGroundClauses() {
		if (countOfMarkedGroundClauses >= 0) { return countOfMarkedGroundClauses; }
		countOfMarkedGroundClauses = 0;
		
		GroundClause gndClause = getFirstMarkedGroundClause();
		while (gndClause != null) {
			countOfMarkedGroundClauses++;
			gndClause = getNextMarkedGroundClause();
		}
		return countOfMarkedGroundClauses;
	}

	public boolean lookForDuplicateGroundClauses() {
		GroundClause gndClause = getFirstGroundClause();
		if (gndClause == null) { return false; }
		int numbDups = 0;
		Utils.println("% Searching for duplicate clauses.");  Utils.waitHere("dups?");
		while (gndClause != null) {  // First clear all marks.
			gndClause.setActive(false);
			gndClause = getNextGroundClause();
		}
		gndClause = getFirstGroundClause();
		while (gndClause != null) { // The see if anything already marked when reached.
			if (gndClause.isActive()) { ++numbDups; if (numbDups < 100) Utils.println(" DUP #" + Utils.comma(numbDups) + ": " + gndClause); }
			gndClause.setActive(true);
			gndClause = getNextGroundClause();
		}
		Utils.println("% Done searching for duplicate clauses.");
		return (numbDups > 0);
	}
	
	public Collection<GroundClause> getAllGroundClauses(Clause clause) {
		if (!haveCollectedAllGroundClauses) { Utils.error("Calling getAllGroundClauses(clause), but haveCollectedAllGroundClauses=false!"); }
		return allGroundClausesPerClause.get(clause);
	}

	// Compute the Markov Blanket for this ground literal, pushing the old versions of allGroundLiterals and allGroundClauses.
	public Object pushCurrentMarkovBlanket(GroundLiteral gLit, Object marker) {
		if (gLit == null) { Utils.error("Cannot have gLit==null"); }
		if (Utils.getSizeSafely(allGroundLiterals) < 1 || Utils.getSizeSafely(allGroundClauses) < 1) { return getMarkerInUse(); } // Have no groundings left, so done.
		
		Set<GroundLiteral>        newGroundLiterals = new HashSet<GroundLiteral>(4); // Use sets here for fast contains() calls.  Later these wil be come array lists (for fast sampling).
		Set<GroundClause>         newGroundClauses  = new HashSet<GroundClause>( 4);
		Set<GroundLiteral> gndLiteralsToBeExplored  = new HashSet<GroundLiteral>(4);
		Set<GroundLiteral> groundLiteralsConsidered = new HashSet<GroundLiteral>(4);
		newGroundLiterals.add(      gLit);
		gndLiteralsToBeExplored.add(gLit);
		groundLiteralsConsidered.add(gLit);
		while (!gndLiteralsToBeExplored.isEmpty()) {
			GroundLiteral currGroundLiteral = gndLiteralsToBeExplored.iterator().next();
			gndLiteralsToBeExplored.remove(currGroundLiteral);
			Set<GroundClause> currentSatisfiableClauses = collectMatchingGroundClauses(currGroundLiteral);
			if (debugLevel > 1) { Utils.println("% clauses for '" + currGroundLiteral + "': " + Utils.limitLengthOfPrintedList(currentSatisfiableClauses, 10)); }
			if (currentSatisfiableClauses != null) for (GroundClause gndClause : currentSatisfiableClauses) if (!newGroundClauses.contains(gndClause)) {
				int size = gndClause.getLength();
				if (size > 0) for (int i = 0; i < size; i++) {
					GroundLiteral gLit2 = gndClause.getIthLiteral(i);
					if (!groundLiteralsConsidered.contains(gLit2)) {
						newGroundLiterals.add(       gLit2);
						gndLiteralsToBeExplored.add( gLit2);
						groundLiteralsConsidered.add(gLit2);
					}
				}
				newGroundClauses.add(gndClause);
			}
		} // TODO - add the multipliers so the total count known!
		if (debugLevel > 1) { Utils.println("\n% The Markov Blanket of '" + gLit + "' contains " + Utils.comma(newGroundClauses) 
												+ " ground clauses involving "                   + Utils.comma(newGroundLiterals) 
												+ " ground literals."); }
		return pushGroundThisMarkovNetwork(newGroundLiterals, newGroundClauses, marker);
	}
	
	private Object pushGroundThisMarkovNetwork(Set<GroundLiteral> gLits, Set<GroundClause> gndClauses, Object marker) {
		allGroundClauses  = new ArrayList<GroundClause>(gndClauses); // TODO - would it make sense to hold this array list and then clear as needed?  Less GC'ing, but would hold the largest version, which would waste space.
		allGroundLiterals = new ArrayList<GroundLiteral>(gLits);
		numberOfNonLazyGroundClauses = Utils.getSizeSafely(allGroundClauses);
		return marker;
	}
	public Object popGroundThisMarkovNetwork(Object marker) {
		if (allGroundClausesOrigSize != Utils.getSizeSafely(allGroundClausesOrig)) { 
			Utils.error("The number of original ground clauses is now "  + Utils.comma(allGroundClausesOrig)  + " but it should be " + Utils.comma(allGroundClausesOrigSize)  + "."); 
		}
		if (allGroundLiteralsOrigSize != Utils.getSizeSafely(allGroundLiteralsOrig)) { 
			Utils.error("The number of original ground Literals is now " + Utils.comma(allGroundLiteralsOrig) + " but it should be " + Utils.comma(allGroundLiteralsOrigSize) + "."); 
		}
		allGroundClauses  = allGroundClausesOrig;
		allGroundLiterals = allGroundLiteralsOrig;
		numberOfNonLazyGroundClauses = Utils.getSizeSafely(allGroundClauses);
		return marker;
	}

	// Collect all the literals in these clauses that are satisfiable.  These clauses should be original, so can use to index into hash tables, etc.
	public Set<Literal> collectQueryAndHiddenLiterals(Set<Clause> currentClauses) {
		Set<Literal> results = null;		
		Utils.writeMe();		
		return results;
	}

	// Collect all the literals in these clauses that make a clause FALSE.  ?????
	public Set<Literal> collectUnsatisfyingLiterals(Set<Clause> currentClauses) {
		// TODO Auto-generated method stub
		Utils.writeMe();
		return null;
	}

	
	/**
	 * @return the weightsLearnt
	 */
	public boolean isWeightsLearnt() {
		return weightsLearnt;
	}

	/**
	 * @param weightsLearnt the weightsLearnt to set
	 */
	public void setWeightsLearnt(boolean weightsLearnt) {
		this.weightsLearnt = weightsLearnt;
	}

	// We get the weighted sum WITH RESPECT TO THE ASSUMPTION THAT *ALL* GROUNDINGS SATISFY THE CLAUSE (i.e., returning 0 is the baseline).
	public double getWeightShortageOfCurrentlySatisfiedClauses(boolean computeIsSatisfied) { // If arg=false, then use the cached version (for speed).
		double weightSatisfiedClauses = 0;
		if (debugLevel > 0) {
			Utils.print("\n% In getWeightShortageOfCurrentlySatisfiedClauses with #currentGroundLiterals = " + Utils.comma(allGroundLiterals) + " and settings = [");
			for (GroundLiteral gLit : allGroundLiterals) { Utils.print(gLit.getValue() ? "1" : "0"); }
			Utils.println("]");
		}
		// Compute weight of satisfied clauses.
		for (GroundClause gndClause : allGroundClauses) {
			if (debugLevel > 2) { Utils.print("%          Consider ground clause: '" + gndClause + "'"); }
			if ((computeIsSatisfied ? !gndClause.checkIfSatisfied(null) : !gndClause.isSatisfiedCached())) { // Be sure that these were all updated before this code was called.
				weightSatisfiedClauses -= gndClause.getWeightOnSentence(); // The multiplier was already multiplied into the weights.
				if    (debugLevel > 2) { Utils.println(": Unsatisfied, so add wgt = -" + Utils.truncate(gndClause.getWeightOnSentence() ,3) + "."); }
			} else if (debugLevel > 2) { Utils.println(": Satisfied (and weight already factored in)."); }
		}
		return weightSatisfiedClauses;
	}

	
	// This is called when looking at the ground clauses pointed to be ground literals.
	// To make sure there is no unintentional 'cross talk,' make sure this clause is marked
	// as being 'current,' which is done by the marker property on the ground clause.
	public boolean isaMarkedGroundClause(GroundClause gndClause) {
		return (gndClause.getMarker() == markerInUse);
	}
	public boolean isaMarkedGroundLiteral(GroundLiteral gLit) {
		return (gLit.getMarker()      == markerInUse);
	}
	
	public Object getMarkerInUse() {
		return markerInUse;
	}
	public void setMarkerInUse(Object marker) {
		markerInUse = marker;
		countOfMarkedGroundClauses = -1;
		countOfMarkedGroundClauses(); 
	}
	public void clearMarkerInUse() {
		markerInUse = null; // Matches all markers.
	}
	
	public void reportGroundings(Clause clause) {
		if (Utils.getSizeSafely(allGroundClauses) < 1) { return; }
		Collection<GroundClause> remainingGroundClauses = allGroundClausesPerClause.get(clause);
		if (Utils.getSizeSafely(remainingGroundClauses) < 1) { Utils.println("%        There are NO groundings for this clause."); return; }
		int counter = 0;
		for (GroundClause gndClause : remainingGroundClauses) {
			Utils.println("%        " + gndClause);
			if (++counter >= 100) { Utils.println("%       ... [will only print the first 100]" + gndClause); return; } 
		}
	}

	// This count does INCLUDE the number reduced to 'true.'
	public double numberOfSatisfiedGroundClauses(Clause clause) {
		double total = numberOfGroundings(clause); // Start by assuming ALL groundings are satisfied, then subtract those found not to be so. 
		// Utils.println(Utils.truncate(total, 0) + " numberOfSatisfiedGroundClauses: " + clause.toPrettyString());
		int countOfSatGrounds = Utils.getSizeSafely(allGroundClausesPerClause.get(clause));
		if (countOfSatGrounds > 0) for (GroundClause gndClause : allGroundClausesPerClause.get(clause)) {
		if (!gndClause.isSatisfiedCached()) {  // Be sure that these were all updated before this code was called.
				total -= multiplierPerSatisfiedClause.get(clause);
     			// Utils.println("% GTMN GndClause not satisified:" + gndClause.toPrettyString());
			} else {
	     		//	Utils.println("% GTMN GndClause satisified:" + gndClause.toPrettyString());
			}
		} else { total -= countOfFALSEs.get(clause); }
		if (countOfFALSEs.get(clause) > 0 && countOfSatGrounds > 0) {
			Utils.error("Clause '" + clause + "' has countOfFALSEs=" + Utils.comma(countOfFALSEs.get(clause)) + " and |remainingSatisfiableClauseGroundings|=" + Utils.comma(countOfSatGrounds));
		}
		return total;
	}
	
	public double numberOfGroundings(Clause clause) {
		return countOfPossibleGroundings.get(clause);
	}	
	public double numberOfSatisfiedGroundings(Clause clause) {
		return countOfTRUEs.get(clause);
	}	
	public double numberOfSatisfiableGroundings(Clause clause) {
		return multiplierPerSatisfiedClause.get(clause) * countOfSatisfiableGndClauses.get(clause);
	}	
	public double numberOfUnsatisfiedGroundings(Clause clause) {
		return countOfFALSEs.get(clause);
	}

	
	// End of group that deals with methods for post-reduction inference.
	
	///////////////////////////////////////////////////////////////////////////////////////////////
	
	// This next group deals with "blocks" of variables.

	private Map<GroundLiteral,Block>                    allBlocks = null;
	private Map<PredicateName,Map<Integer,List<Block>>> predNameArityToBlockList;
	
	public void computeAllBlocks(TimeStamp timeStamp) {
		initPredNameArityToBlock(timeStamp);
		populateBlocks(timeStamp);
		if (debugLevel > 2) { Utils.println("% GroundThisMarkovNetwork: #blocks = " + Utils.getSizeSafely(getAllBlocks())); }
	}
	
	public Map<GroundLiteral,Block> getAllBlocks() {
		return allBlocks;
	}
	
	/**
	 * Creates a Map where the keys are all the literals which have block constraints.
	 * At the end of this method, the map's values are an empty list of blocks.
	 * 
	 * @param predNameToLiteral
	 */
	private void initPredNameArityToBlock(TimeStamp timeStamp) {
		Map<PredicateName,Set<Integer>> predNameArityPairsSeen = new HashMap<PredicateName,Set<Integer>>(4);
		predNameArityToBlockList = new HashMap<PredicateName,Map<Integer,List<Block>>>(4);
		if (debugLevel > 0) { Utils.println("\n% Initialize the predicate-name blocks."); }
		for (GroundLiteral gLit : allGroundLiterals) if (gLit.numberArgs() > 0) {			
			PredicateName predName = gLit.predicateName;
			int           arity    = gLit.numberArgs();
			Set<Integer>  lookup   = predNameArityPairsSeen.get(predName);
			if (lookup == null) { 
				lookup =  new HashSet<Integer>(4);
				predNameArityPairsSeen.put(predName,lookup);
			}
			if (lookup.contains(arity)) { continue; }
			lookup.add(arity);
			List<TypeSpec> listOfTypeSpecs = task.collectLiteralArgumentTypes(predName, arity);
			for (TypeSpec typeSpec : listOfTypeSpecs) {
				if (typeSpec.truthCounts != 0) { // If this is non zero, then have a blocked literal.
					if (debugLevel > 0) { Utils.println("% Have truth counts = " + typeSpec.truthCounts + " in " + typeSpec); }
					addPredNameAndArityToBlockList(predName, arity, new ArrayList<Block>(1), predNameArityToBlockList);
					break;
				}
			}
		}
	}
	
	// Add this block list to predNameArityToBlockList for pName/arity.  If something already stored for this pair, do nothing.
	private void addPredNameAndArityToBlockList(PredicateName pName, int arity, List<Block> blockList, Map<PredicateName,Map<Integer,List<Block>>> map) {
		Map<Integer,List<Block>> lookup1 = predNameArityToBlockList.get(pName);
		if (lookup1 == null) {
			lookup1 = new HashMap<Integer,List<Block>>(4);
			map.put(pName, lookup1);
		}
		List<Block> lookup2 = lookup1.get(arity);
		if (lookup2 == null) {
			lookup1.put(arity, blockList);
		}
	}
	
	private List<Block> getBlockListFromPredNameAndArity(Literal lit, Map<PredicateName,Map<Integer,List<Block>>> map) {
		return getBlockListFromPredNameAndArity(lit.predicateName, lit.numberArgs(), map);
	}
	private List<Block> getBlockListFromPredNameAndArity(PredicateName pName, int arity, Map<PredicateName,Map<Integer,List<Block>>> map) {
		Map<Integer,List<Block>> lookup1 = map.get(pName);
		if (lookup1 == null) { return null; } // OK to not be present.
		List<Block> lookup2 = lookup1.get(arity);
		if (lookup2 == null) { return null; }
		return lookup2;
	}
	
	private void populateBlocks(TimeStamp timeStamp) {
		allBlocks = null;
		for (GroundLiteral gLit : allGroundLiterals) {
			List<Block> blockList = getBlockListFromPredNameAndArity(gLit, predNameArityToBlockList);
			if (blockList == null) continue;
			boolean addedToBlock = false;
			for (Block block : blockList) {
				if (block.addGndLiteral(gLit)) {
					gLit.setBlock(block);
					addedToBlock = true;
					break;
				}
			}
			if (!addedToBlock) {
				List<GroundLiteral> temp = new ArrayList<GroundLiteral>();
				temp.add(gLit);
				Block block = new Block(gLit, temp, timeStamp);
				gLit.setBlock(block);
				blockList.add(block);
				if (allBlocks == null) { allBlocks = new HashMap<GroundLiteral,Block>(4); }
				allBlocks.put(gLit, block);
			}
		}		
		if (allBlocks != null && !task.isClosedWorldAssumption(null)) { setEvidenceInBlocks(task.getPosEvidenceLiterals(), predNameArityToBlockList, timeStamp); } // NOT SURE WHY THIS IS CONDITIONAL ... TODO
	}
	
	private void setEvidenceInBlocks(Collection<GroundLiteral> evidence, Map<PredicateName,Map<Integer,List<Block>>> map, TimeStamp timeStamp) {
		if (evidence == null) { return; }
		for (GroundLiteral gLit : evidence) {
			List<Block> blockList = getBlockListFromPredNameAndArity(gLit, map);
			if (blockList == null) continue;
			for (Block block : blockList) {
				if (block.canAddGndLiteral(gLit)) {
					block.addEvidence(timeStamp);
					break;
				}
			}
		}
	}
	
	// End of group that deals with methods for processing blocks.
	

	
	// Is this ground literal in this set of constants for this literal in this clause?
	// More specifically, would this ground literal be generated by these cross products?
	// Input positionsOfArgumentsInLiteralToUse is needed when more literals are needed (due to aggregators) than those variables in a literal.
	// Input mapVariablesToPositionInAggregatorList maps variables in the literal to items in crossProductOfAggregatedVars.
	// Input basicVarCrossProduct will have as many items as there are free variables in this literal, but the aggregated ones will have a generic filler.
	// Input crossProductOfAggregatedVars will contain an item for each aggregator in this literal.
	// Input aggVarIndexes maps each constant to the List<Constants> in which it appears as the first item (for faster lookup).
	private boolean gLitArgumentsStillExistInVariableCrossProducts(Clause clause, Literal lit, int[] positionsOfArgumentsInLiteralToUse, Map<Term,Integer> mapVariablesToPositionInAggregatorList, GroundLiteral gLit,
																   CrossProductViaContinuation<Term> basicVarCrossProduct, List<AggVar> aggregatorsNeeded, CrossProductViaContinuation<List<Term>> crossProductOfAggregatedVars, List<Map<Term,Set<List<Term>>>> aggVarIndexes) {
		if (literalsContainingConstants.get(clause) != null && literalsContainingConstants.get(clause).contains(lit)) { // If there are constants in here, then need to first see if lit and gLit unify.  If only variables, no need to do the unification.
			bl.theta.clear(); // Save new'ing a binding list.
			if (unifier.unify(lit, gLit, bl) == null) { /* Utils.println("% *** DO NOT UNIFY: " + wrapLiteral(clause, lit) + " and '" + gLit + "'."); */ return false; }
			// These MAY or MAY NOT have been excess, but not worth spending cycles just to see if the assignments to variables is an existing cross product.
			// So assume NOT (i.e., assume that this check here is 'free.'
		}
		Collection<Integer> map = firstVariableAppearance.get(clause).get(lit);  // See original comment for what this encodes.
		// Should never reach here with map=null, so don't waste cycles testing.  Instead, let Java catch bugs.
		List<Term>  litArgs =  lit.getArguments();
		List<Term> gLitArgs = gLit.getArguments();
		Map<Integer,                 List<Term>>   constantsForAggVars      = null;
		Map<Integer,                 List<Integer>>    locationsInAggVars       = null;
		Map<Integer,Map<Term,Set<List<Term>>>> constantsForAggVarsINDEX = null;
		
		int varCounter = 0;
		
		if (debugLevel > 3) {
			Utils.println("\n clause = " + clause);
			Utils.println(  "  lit   = " + lit);
			Utils.println(  " gLit   = " + gLit);
			Utils.println(  " mapVariablesToPositionInAggregatorList = " + mapVariablesToPositionInAggregatorList);
			Utils.println(  " map    = " + map);
			Utils.print(    " positionsOfArgumentsInLiteralToUse =");
			for (int i = 0; i < positionsOfArgumentsInLiteralToUse.length; i++) { Utils.print(" " + positionsOfArgumentsInLiteralToUse[i]); }
			Utils.println(  "");
			Utils.println(  " variables in clause: " + variablesInClause.get(clause));
			Utils.println(  " variables in lit:    " + freeVarsMap.get(clause).get(lit));
			Utils.println(  " aggVarIndexes = "      + aggVarIndexes);
			Utils.println(  " basicVarCrossProduct: "         + basicVarCrossProduct);
			Utils.println(  " crossProductOfAggregatedVars: " + crossProductOfAggregatedVars);
			Utils.println(  "");
		}
		
		for (Integer item : map) { // Look at each argument in the ground literal. 
			if (item > 0) { // Only need to check these entries.  These are the first occurrences of variables.
				Term gLitArg = (Term) gLitArgs.get(item - 1);  // Remember the map counts from 1, not 0.
				Term      litArg =             litArgs.get(item - 1);
				Integer aggVarPositionForThisBasicVar = (mapVariablesToPositionInAggregatorList == null ? null : mapVariablesToPositionInAggregatorList.get(litArg));	// Indexes into argVarList.				
				
				if (aggVarPositionForThisBasicVar != null) { // See if this variable is owned by some aggregator.
					if (debugLevel > 3) { Utils.println("% *** Checking if aggregated constant '" + gLitArg + "' still exists (for position " + varCounter + ")."); }
					// If so, need to collect ALL gLitArgs that are in this same aggregator, so we can check for the existence of the tuple all together.
					if (constantsForAggVars      == null)                          { constantsForAggVars      = new HashMap<Integer,List<Term>>(4); } // Wait to create until needed.
					if (locationsInAggVars       == null)                          { locationsInAggVars       = new HashMap<Integer,List<Integer>>(4);  }
					if (constantsForAggVarsINDEX == null && aggVarIndexes != null) { constantsForAggVarsINDEX = new HashMap<Integer,Map<Term,Set<List<Term>>>>(4); }
					List<Term> lookup1 = constantsForAggVars.get(aggVarPositionForThisBasicVar);
					List<Integer>  lookup2 = locationsInAggVars.get( aggVarPositionForThisBasicVar);
					if (lookup1 == null) { // First time for this aggregated variable.
						lookup1 = new ArrayList<Term>(2); // Must be at least two since an aggregated variable, though could find exact size in crossProductOfAggregatedVars (but minor savings).
						constantsForAggVars.put(aggVarPositionForThisBasicVar, lookup1);
						if (aggVarIndexes != null) { constantsForAggVarsINDEX.put(aggVarPositionForThisBasicVar, aggVarIndexes.get(aggVarPositionForThisBasicVar)); }
						lookup2 = new ArrayList<Integer>(2);
						locationsInAggVars.put(aggVarPositionForThisBasicVar, lookup2);
					}
					lookup1.add(gLitArg);
					// Now need to find the position for this argument in the aggregator (eg, we might need 2 of the 3 aggregated variables, and we need to know which 2).
					AggVar aggVar = aggregatorsNeeded.get(aggVarPositionForThisBasicVar);
					lookup2.add(aggVar.getPosition((Variable) litArg));
					if (debugLevel > 3) { Utils.println("%  need to find " + gLitArg + " in " + aggVar + " at position " + aggVar.getPosition((Variable) litArg)); }
				} else { // This variable has not been aggregated yet.  So simply see if it is in the list for the corresponding cross product (which are ordered by the variables location in the literal, so the varCounter represents this).
					if (debugLevel > 3) { Utils.println("% *** Checking if unaggregated constant '" + gLitArg + "' still exists (for position " + varCounter + ")."); }
					int index = varCounter;
					if (positionsOfArgumentsInLiteralToUse.length > 0) { // Pull out the variables for this literal from the possibly longer fullSetOfVariables, using the provided 'map.'
						index = positionsOfArgumentsInLiteralToUse[varCounter];
					}
					if (!basicVarCrossProduct.containsThisEntry(index, gLitArg)) { currentExcessChecks++; return false; }  // If not, we're done.
					else if (debugLevel > 3) { Utils.println("% ***     found it!"); }
				}					
				varCounter++;
			}
		}
		
		//Utils.println("constantsForAggVars = " + constantsForAggVars);
		//Utils.println("locationsInAggVars = "  + locationsInAggVars);		
		// Now process any constantsForAggVars (needed to wait to collect everything).  Recall that these are LISTS of constants, and we need to see if this combination is still under consideration.
		if (debugLevel > 3) { Utils.println("mapVariablesToPositionInAggregatorList=" + mapVariablesToPositionInAggregatorList + " constantsForAggVars=" + constantsForAggVars + "  constantsForAggVarsINDEX=" + constantsForAggVarsINDEX); }
		if (constantsForAggVars != null) {
			for (Integer item : constantsForAggVars.keySet()) {
				List<Term> args   = constantsForAggVars.get(item);
				List<Integer>  argMap = locationsInAggVars.get( item);
				if (debugLevel > 3) { Utils.println("% *** Looking for aggregated constant(s) " + args + " in positions " + argMap + " of aggregator #" + item + " for gLit '" + gLit + "', a  grounding of " + wrapLiteral(clause, lit) + " whose map = " + map + " and where mapVariablesToPositionInAggregatorList=" + mapVariablesToPositionInAggregatorList); }
				Map<Term,Set<List<Term>>> index = (constantsForAggVarsINDEX == null ? null : constantsForAggVarsINDEX.get(item));
				if (index != null) { // See if this was indexed (might not have been if the cross product is small).
					Utils.writeMe();
				} else if (argsContainedInThisAggregation(args, argMap, crossProductOfAggregatedVars.getThisEntry(item))) {
					if (debugLevel > 3) { Utils.println("% ***     found it!"); }}
				else { if (debugLevel > 3) { Utils.println("% ***     FAILED"); } currentExcessChecks++; return false; }
			}
		}
		if (debugLevel > 3) { Utils.println("% *** found " + gLit + " still exists as a grounding of " + lit); }
		return true;
	}
	
	// NEED TO FIND *SOME* ARGS IN A POSSIBLY LONGER LIST!  Eg, [x,z] in [ ... [ x, y, z], ...].
	private boolean argsContainedInThisAggregation(List<Term> args, List<Integer> argMap, Collection<List<Term>> aggregation) {
		if (aggregation == null)        { return false; }
		if (debugLevel > 3) { Utils.println("% ***     " + Utils.limitLengthOfPrintedList(aggregation, 25)); }
		for (List<Term> oneAgg : aggregation) {
			for (int i = 0; i < args.size(); i++) {
				if (args.get(i) != oneAgg.get(argMap.get(i))) { // Need to pull out the specified item.
					continue;
				}
			}
			return true;
		}
		return false;
	}

	// Pull out (in order) the constants in this ground literal that replaced the variables in this literal.
	// Note: this is NOT the same as the gLit's arguments!  
	// For example, if lit=p(1,X,Y,X) and gLit=p(1,2,3,2) then should return {2,3}.
	// See comments about firstVariableAppearance's "semantics."
	private List<Term> extractConstants(Clause clause, Literal lit, GroundLiteral gLit) {
		Collection<Integer> map = firstVariableAppearance.get(clause).get(lit);
		if (map == null) { return null; }
		List<Term>   result = new ArrayList<Term>(map.size());
		List<Term>     gLitArgs = gLit.getArguments();
		for (Integer item : map) { if (item > 0) result.add(gLitArgs.get(item - 1)); } // Note that firstVariableAppearance's counting starts at 1 (since 0 means "isa constant in the original literal."
		return result;
	}

	
	// %%%%%%%%%%%%%%%%%%%   Start of Managing the Grounded Network, Lazy Evaluation, etc.   %%%%%%%%%%%%%%%%%%%%%

	// TVK:GMN Copied to GroundedMarkovNetowork. Can be removed
	@Deprecated
	public boolean prepareForInference(TimeStamp timeStamp) { // Return TRUE if LAZY inference needed.
		if (debugLevel > -110) { Utils.println("\n% Create all the query literals."); }
		task.createAllQueryLiterals();  // Need all of these to be expanded (TODO - keep statistics in a sparse array), since we're assuming inference will be done soon.
	//	task.createAllHiddenLiterals(); // TODO do we need to create these, or can we simply assume any non-query that has survived is a hidden?  seems so ...
		if (debugLevel > -110) { Utils.println("\n% There are " + Utils.comma(task.getQueryLiterals()) + " query literals."); }
		collectAllRemainingGroundings(timeStamp);
		if (debugLevel > -110 && Utils.getSizeSafely(stillTooLargeAfterReduction) < 1) { Utils.println("\n% Because there are only " + Utils.truncate(totalNumberOfGroundingsRemaining, 0) + " clause groundings remaining, will perform standard inference."); }
		else if (debugLevel > -110)                                                    { Utils.println("\n% Due to the large number of groundings they have remaining, " + Utils.comma(stillTooLargeAfterReduction) + " clauses need to be handled lazily."); }
		return (Utils.getSizeSafely(stillTooLargeAfterReduction) < 1);
	}
	protected long countofUniqueGroundClauses = 0;
	protected long countOfMergedGroundClauses = 0;
	private GroundClause getGroundClause(MLN_Task task, Clause clause, List<Term> freeVarBindings, TimeStamp timeStamp) {
		GroundClause newGndClause = new GroundClause(task, clause, multiplierPerSatisfiedClause.get(clause), freeVarBindings, timeStamp);
		addToGroundClauseIndex(newGndClause);
		return newGndClause; // For now, let's just see how many can be reduced.
	}
	private GroundClause getGroundClause(Clause clause, List<Literal> posLits, List<Literal> negLits, List<Term> freeVarBindings, TimeStamp timeStamp) {
		GroundClause newGndClause = new GroundClause(clause, posLits, negLits, multiplierPerSatisfiedClause.get(clause), freeVarBindings, timeStamp);
		addToGroundClauseIndex(newGndClause);
		return newGndClause; // For now, let's just see how many can be reduced.
	}
	

	private LiteralComparator litComparator = new LiteralComparator();

	// Return true if this is a NEW ground clause.
	private boolean addToGroundClauseIndex(GroundClause gndClause) {
		// Put in a canonical form.
		if (gndClause.getLength() < 1) {
			Utils.warning("Have a ground clause with no literals: "    + gndClause.groundClauseSettingToString(this) + ".  It will be ignored.");
			return false; 
		}
		if (gndClause.getWeightOnSentence() == 0.0) {
			Utils.warning("Have a ground clause with weight of zero: " + gndClause.groundClauseSettingToString(this) + ".  It will be ignored.");
			return false; 
		}
		// If a singleton clause with a negative weight, convert to the equivalent version (negate the weight and the literal.
		// TVK 8/28 : Flipping before learning weights would add q(x) instead of !q(x) to allGroundClausesPerClause
		// if the initial weights are negative. Only flip the weights if they are learnt.
		if (weightsLearnt && gndClause.getWeightOnSentence() < 0 && gndClause.getLength() < 2) {
			List<Literal>    temp = gndClause.negLiterals;
			gndClause.negLiterals = gndClause.posLiterals;
			gndClause.posLiterals = temp;
			gndClause.setWeightOnSentence(-gndClause.getWeightOnSentence());
		}
		if (gndClause.negLiterals != null) { Collections.sort(gndClause.negLiterals, litComparator); }
		if (gndClause.posLiterals != null) { Collections.sort(gndClause.posLiterals, litComparator); }
		int hashcode = getNonFastHashCode(gndClause);
		List<GroundClause> hits = hashOfGroundClauses.get(hashcode);
		if (hits != null) {
			if (weightsLearnt) {  // Only add the weights, if they are learnt.
				for (GroundClause hit : hits) if (hit.sameClause(gndClause)) {
					hit.setWeightOnSentence(hit.getWeightOnSentence() + gndClause.getWeightOnSentence());
					countOfMergedGroundClauses++;
					return false;
				}
			}
			// If reached the end of the for loop, have a collision that must be kept.			
		} else { hits = new ArrayList<GroundClause>(1); }
		countofUniqueGroundClauses++;
		hits.add(gndClause);
		hashOfGroundClauses.put(hashcode, hits);
		return true;
	}
	private int getNonFastHashCode(GroundClause gndClause) {
		boolean holdLiteral = task.stringHandler.useFastHashCodeForLiterals;
		boolean holdClause  = task.stringHandler.useFastHashCodeForClauses;
		task.stringHandler.useFastHashCodeForLiterals = false; // Need this setting in order to get proper matching of equivalent literals.
		task.stringHandler.useFastHashCodeForClauses  = false; // Ditto for clauses.
		int hashcode = gndClause.hashCode();
		task.stringHandler.useFastHashCodeForLiterals = holdLiteral;
		task.stringHandler.useFastHashCodeForClauses  = holdClause;
		return hashcode;
	}

	// TVK:GMN Copied to GroundedMarkovNetowork. Can be removed
	@Deprecated
	public long getCountOfUniqueGroundClauses() {
		int counter  = 0;
		int counter2 = 0;
		int max      = 0;
		Integer indexOfMax = 0;
		for (Integer index : hashOfGroundClauses.keySet()) {
			int size = hashOfGroundClauses.get(index).size();
			counter += size;
			if (size > max) { max = size; indexOfMax = index; }
			if (size > 1)   { counter2++; }
		}
		Utils.println("\n% There are " + Utils.comma(countofUniqueGroundClauses) + " unique ground clauses; " + Utils.comma(countOfMergedGroundClauses) + " have had their weights merged.");
		Utils.println("%  |canonical ground-clause hash codes| = " + Utils.comma(hashOfGroundClauses.keySet().size()) + 
					   ", |hash of ground clauses| = "             + Utils.comma(counter)  +
					   ", |with collisions| = "                    + Utils.comma(counter2) +
					   ", max # of collisions = "                  + Utils.comma(max));
		Utils.println("%    max collisions: " + Utils.limitLengthOfPrintedList(hashOfGroundClauses.get(indexOfMax), 25));
		return countofUniqueGroundClauses;
	}

	// Unless in the provided collection, give the query and hidden literals a random value.
	// TODO could save one pass through the query literals if this were done when calling countLazyTrueQueryLiterals,
	//      but that would mean we need to store lazyGroundLiteralsUnderConsideration.
	/* TVK : Not used here.
	public int randomizeTruthValuesOfQueryAndHiddenLiteralsForLazy(Set<GroundLiteral> exceptions, TimeStamp timeStamp) {
		Collection<GroundLiteral> qLits = task.getQueryLiterals();
		if (Utils.getSizeSafely(qLits) < 1) { Utils.error("Have no query literals!"); }
		int counterRandom    = 0;
		int counterException = 0;
		int numberExceptions = Utils.getSizeSafely(exceptions);
		for (GroundLiteral gLit : qLits) { // Need to do the query literals even if they won't be interned, since we need to calculate numTrue's for them.
			if (numberExceptions < 1 || !exceptions.contains(gLit)) { 
				counterRandom++; gLit.setValueOnly(Utils.random() < 0.5, timeStamp); // This assumes some other code will check the state of the ground clauses in which this literal appears. 
			} else { counterException++; }
		}
		Collection<GroundLiteral> hLits = (internHiddenLiterals ? task.getHiddenLiterals() : null); // No need to assign these unless they'll later be interned.
		if (Utils.getSizeSafely(hLits) > 0) for (GroundLiteral gLit : hLits) { // OK if no hidden literals.
			if (numberExceptions < 1 || !exceptions.contains(gLit)) { 
				counterRandom++; gLit.setValueOnly(Utils.random() < 0.5, timeStamp); // Ditto.
			} else { counterException++; }
		}
		if (debugLevel > 0) { Utils.println("%  " + Utils.comma(counterRandom) + " of the " + Utils.comma(qLits) + " query " + (internHiddenLiterals ? "and " + Utils.comma(hLits) + " hidden " : "") + "literals have been given random values, while " + Utils.comma(counterException) + " are in the list of " + Utils.comma(exceptions) + " exceptions."); }
		return counterRandom;
	}
	*/
	/* TVK : Not used here.
	private GroundClause tryNtimesToFindUnsatisfiedClause(List<GroundClause> candidates, int N) {
		for (int i = 0; i < N; i++) {
			GroundClause randomChoice = Utils.chooseRandomFromThisCollection(candidates);
			if (!randomChoice.isSatisfiedCached()) { return randomChoice; }
		}
		return null;
	}
	*/
	// Activate all those groundings of this clause that contain this ground literal.
	// Also do bookkeeping to note when all groundings have been collected.
	// Return the number of new ground clauses created.
	/* TVK : Not used anywhere.
	public int activateLazyGroundClausesContainingThisGroundLiteral(GroundLiteral gLit, boolean onlyConsiderNegatedLiterals, Collection<Clause> clausesToConsider, boolean isaPermLazy, TimeStamp timeStamp) {
		if (gLit.hasBeenInterned) { return 0; }
		int total = 0;
		for (Clause clause : clausesToConsider) { 
			Collection<GroundClause> newGroundings = help_activateLazyGroundClausesContainingThisGroundLiteral(clause, gLit, onlyConsiderNegatedLiterals, timeStamp);
			if (Utils.getSizeSafely(newGroundings) < 1) { continue; }
			if (isaPermLazy) { addThesePermanentLazyClauses(newGroundings); } else { addTheseLazyClauses(newGroundings); }
			// We don't need to collect the literals in these new ground clauses until these clauses are selected by MCSAT.
			//for (GroundClause gndClause : newGroundings) for (int i = 0; i < gndClause.getLength(); i++) {
			//	GroundLiteral gLit gndClause.getIthLiteral(i);
			//}
			total += Utils.getSizeSafely(newGroundings);
		}
		if (debugLevel > 2) { 
			Utils.println("%   Activating '" + gLit + "' created " + Utils.comma(total) + " new ground clauses.  Total count of materialized ground clauses = " + Utils.comma(totalNumberOfGroundClauses) + " and ground literals = " + Utils.comma(totalNumberOfGroundLiterals) + ".");
		}
		gLit.hasBeenInterned = true;
		return total;
	}
	*/
	/* TVK : Not used here.
	private Set<GroundClause> help_activateLazyGroundClausesContainingThisGroundLiteral(Clause clause, GroundLiteral gLit, boolean onlyConsiderNegatedLiterals, TimeStamp timeStamp) {
		// Look at literals remaining, collect all possible unifications, and then do all possible groundings for the remaining variables.
		Set<Literal>            keepers = literalsToKeep.get(clause);
		if (Utils.getSizeSafely(keepers) < 1) { clausesFullyGrounded.add(clause); return null; } // Probably already done elsewhere, but play it safe.
		Set<Variable>      varsInClause = variablesRemainingInClause.get(clause);
		Set<Variable>  accountedForVars = accountedForVariables.get(clause);
		Set<GroundClause> newGroundings = null;
		int dupGroundCounter = 0; // Count times a duplicate ground clause was found.
		
		// Only negated literals can change the default truth value of a clause (since we assume clauses are true because
		// at least one negated literal is false by the CWA).  There might be more than one negated literal, but
		// bookkeeping to keep track of when all are materialized is too complicated and not (yet) done (TODO).
		for (Literal lit : keepers) if (!onlyConsiderNegatedLiterals || !clause.getSign(lit)) {
			bl2.theta.clear(); // Use bl2 since collectRemainingClauseGroundings uses bl.
			BindingList bindings = unifier.unify(lit, gLit, bl2);
			if (bindings == null) { continue; }
			Collection<Variable> extraVars = null;
			for (Variable var : varsInClause) if (!accountedForVars.contains(var) && !bindings.theta.containsKey(var)) {
				if (extraVars == null) { extraVars = new ArrayList<Variable>(1); }
				extraVars.add(var);
			}
			if (extraVars != null) { 
				if (debugLevel > 2) { Utils.println("\n% There are some extra variables " + extraVars + " for '" + gLit + "' in clause #" + Utils.comma(clauseToIndex.get(clause)) + ": '" + clause + "' with bindings=" + bindings + " and accountedForVars=" + accountedForVars + "."); }
				// Need to collect all the remaining groundings of these extra variables.
				Set<GroundClause> newGroundClauses = null;
				try {
					newGroundClauses = collectRemainingClauseGroundings(clause, extraVars, bindings, timeStamp);
				} catch (MLNreductionProblemTooLargeException e) {
					Utils.error("Dealing with grounding with extra variables " + extraVars + " led to too many ground clauses.  Consider removing: '" + clause + "'.");
				}
				if (debugLevel > 2) { Utils.println("% Have collected " + Utils.comma(newGroundClauses) + " bindings from these extra variables."); }
				if (Utils.getSizeSafely(newGroundClauses) > 0) {
					if (newGroundings == null) { newGroundings = new HashSet<GroundClause>(4); }
					if (debugLevel > 0) {
						for (GroundClause newGndClause : newGroundClauses) if (!addGroundingUnlessAlreadyExists(newGndClause, newGroundings)) {	dupGroundCounter++; }
					} else { addGroundingUnlessAlreadyExists(newGroundClauses, newGroundings); }
				}
			}
			else { // Only one candidate, so create it here.  TODO - let collectRemainingClauseGroundings handle this as well?
				List<Literal> posLitsRemaining = null;
				List<Literal> negLitsRemaining = null;
				if (clause.posLiterals != null) for (Literal pLit : clause.posLiterals) if (keepers.contains(pLit)) {
					if (posLitsRemaining == null) { posLitsRemaining = new ArrayList<Literal>(1); }
					GroundLiteral gLitNew = task.getCanonicalRepresentative(pLit.applyTheta(bindings.theta));
					posLitsRemaining.add(gLitNew);
				}
				if (clause.negLiterals != null) for (Literal nLit : clause.negLiterals) if (keepers.contains(nLit)) {
					if (negLitsRemaining == null) { negLitsRemaining = new ArrayList<Literal>(1); }
					GroundLiteral gLitNew = task.getCanonicalRepresentative(nLit.applyTheta(bindings.theta));
					negLitsRemaining.add(gLitNew);
				}
				GroundClause newGndClause = getGroundClause(clause, posLitsRemaining, negLitsRemaining, getFreeVarMap(variablesRemainingInClause.get(clause), null, bindings), timeStamp);
				if (newGroundings == null) { newGroundings = new HashSet<GroundClause>(4); }
				if (addGroundingUnlessAlreadyExists(newGndClause, newGroundings)) { dupGroundCounter++; }
			}
		}		
		if (newGroundings == null) { return null; }
		if (debugLevel > 2) { Utils.println("%    Adding " + Utils.comma(newGroundings) + " new clause groundings (and " + Utils.comma(dupGroundCounter) + "duplicates) from '" + gLit + "' from '" + clause + "'."); }
		Set<GroundClause> groundingsSoFar = allGroundClausesPerClause.get(clause);
		if (groundingsSoFar == null) {
			groundingsSoFar = new HashSet<GroundClause>(newGroundings.size() + 4);
			allGroundClausesPerClause.put(clause, groundingsSoFar);
		}
		groundingsSoFar.addAll(newGroundings);
		// Utils.println("% GTMN: groundingsSoFar=" + groundingsSoFar.size());
		//processNewlyMaterializedGroundClause(newGroundings, timeStamp);
		if (groundingsSoFar.size() > maxNonLazyGroundingsPerClause) { 
			Utils.error("Too many lazy groundings!   [" + Utils.comma(groundingsSoFar) + "]   '" + clause + "'");
		}
		
		if (groundingsSoFar.size() >= countOfSatisfiableGndClauses.get(clause)) {
			if (groundingsSoFar.size() > countOfSatisfiableGndClauses.get(clause)) { Utils.error("Have |groundingsSoFar|=" + groundingsSoFar.size() + " but |countOfSatisfiableGndClauses|=" + countOfSatisfiableGndClauses.get(clause)); }
			if (debugLevel > 0) { Utils.println("%    All " + Utils.comma(countOfSatisfiableGndClauses.get(clause)) + " possible groundings for this literal have been added."); }
			clausesFullyGrounded.add(clause);
		}
		return newGroundings;
	}	
	*/
	// Play with task.stringHandler.useStrictEqualsForClauses so that in this narrow context, equality is more than '==' (but in general we cannot do that - can only do so when dealing with ONE general clause).
	/* TVK : Not used here.
	private boolean addGroundingUnlessAlreadyExists(GroundClause gndClause, Collection<GroundClause> existingGroundClauses) {
		boolean hold = task.stringHandler.usingStrictEqualsForClauses();
		task.stringHandler.setUseStrictEqualsForClauses(false);
		boolean result = existingGroundClauses.add(gndClause);
		task.stringHandler.setUseStrictEqualsForClauses(hold);
		return result;
	}
	private boolean addGroundingUnlessAlreadyExists(Collection<GroundClause> gndClauses, Collection<GroundClause> existingGroundClauses) {
		boolean hold = task.stringHandler.usingStrictEqualsForClauses();
		task.stringHandler.setUseStrictEqualsForClauses(false);
		boolean result = existingGroundClauses.addAll(gndClauses);
		task.stringHandler.setUseStrictEqualsForClauses(hold);
		return result;
	}
	 */
	// For a new ground clause:
	//		a) add to lazyGroundClauses
	//		b) update lazyGroundClausesPerGroundLiteral
	//		c) connectGroundLiteralsToTheseGroundClauses (this accomplishes b)
	//		d) update blocks
	//		e) incrementally call countExceptionsToCurrentLazys
	
	/* TVK : Not used here.
	private void processNewlyMaterializedGroundClause(Collection<GroundClause> gndClauses, TimeStamp timeStamp) {
		addTheseLazyClauses(gndClauses);
		connectGroundLiteralsToTheseGroundClauses(gndClauses);
		for (GroundClause gndClause : gndClauses) {
			gndClause.checkIfSatisfied(timeStamp);
			if (debugLevel > 2) { Utils.println(" processNewlyMaterializedGroundClause DELTA: -" + gndClause.getWeightOnSentence()); }
			// totalWeightOfUnmaterializedGroundClauses -= gndClause.getWeight(); // Keep track of the amount of weight on clauses that are implicit (which means they are true).
			for (int i = 0; i < gndClause.getLength(); i++) {
				GroundLiteral gLit = gndClause.getIthLiteral(i);				
				initForLazyBlock( gLit, timeStamp);
				populateLazyBlock(gLit, timeStamp);
			}
		}
	}
	*/
	// Connect all the ground literals to the ground clauses in which they appear.
	/* TVK : Not used here.
	private void connectGroundLiteralsToTheseGroundClauses(Collection<GroundClause> groundClausesToConsider) {
		for (GroundClause gndClause : groundClausesToConsider) {
			for (int i = 0; i < gndClause.getLength(); i++) {
				GroundLiteral gLit = gndClause.getIthLiteral(i);				
				gLit.addGndClause(gndClause);
			}
		}
	}
	*/
	/* TVK : Not used here.
	private void computeAllLazyBlocks(TimeStamp timeStamp) {
		initLazyPredNameArityToBlock(timeStamp);
		populateLazyBlocks(timeStamp);
		if (debugLevel > 2) { Utils.println("% GroundThisMarkovNetwork: #lazyBlocks = " + Utils.getSizeSafely(getAllLazyBlocks())); }
	}
	 */
	/* TVK : Not used here.
	private Map<GroundLiteral,Block>                    allLazyBlocks = null;
	private Map<PredicateName,Map<Integer,List<Block>>> lazyPredNameArityToBlockList;
	*/
	/* TVK : Not used here.
	private Map<GroundLiteral,Block> getAllLazyBlocks() {
		return allLazyBlocks;
	}
	*/
	/**
	 * Creates a Map where the keys are all the literals which have block constraints.
	 * At the end of this method, the map's values are an empty list of blocks.
	 * 
	 * @param predNameToLiteral
	 */
	/* TVK : Not used here.
	private void initLazyPredNameArityToBlock(TimeStamp timeStamp) {
		if (numberOfLazyGroundLiterals < 1) { return; }
		if (debugLevel > 0) { Utils.println("\n% Initialize the lazy predicate-name blocks."); }
		for (GroundLiteral gLit : allLazyGroundLiterals) { initForLazyBlock(gLit, timeStamp); }
	}
	*/
	/* TVK : Not used here.
	private void initForLazyBlock(Literal gLit, TimeStamp timeStamp) {
		initForLazyBlock(gLit, gLit.predicateName, gLit.numberArgs(), timeStamp);
	}
	*/
	/* TVK : Not used here.
	private void initForLazyBlock(Literal gLit, PredicateName pName, int arity, TimeStamp timeStamp) {
		if (gLit.numberArgs() > 0) {	
			List<TypeSpec> listOfTypeSpecs = task.collectLiteralArgumentTypes(pName, arity);
			for (TypeSpec typeSpec : listOfTypeSpecs) {
				if (typeSpec.truthCounts != 0) { // If this is non zero, then have a blocked literal.
					if (debugLevel > 0) { Utils.println("% Have truth counts = " + typeSpec.truthCounts + " in " + typeSpec); }
					addPredNameAndArityToBlockList(pName, arity, new ArrayList<Block>(1), lazyPredNameArityToBlockList);
					break;
				}
			}
		}		
	}
	*/
	/* TVK : Not used here.
	private void populateLazyBlocks(TimeStamp timeStamp) {
		allLazyBlocks = null;
		if (numberOfLazyGroundLiterals < 1) { return; }
		for (GroundLiteral gLit : allLazyGroundLiterals) { populateLazyBlock(gLit, timeStamp); } 
		
		if (allLazyBlocks != null && !task.isClosedWorldAssumption(null)) { 
			Utils.writeMe("also fix populateLazyBlock when called by processNewlyMaterializedGroundClause");
			setEvidenceInBlocks(task.getPosEvidenceLiterals(), lazyPredNameArityToBlockList, timeStamp);  // NOT SURE WHY THIS IS CONDITIONAL ... TODO
		}
	}
	*/
	
	/* TVK : Not used here.
	private void populateLazyBlock(GroundLiteral gLit, TimeStamp timeStamp) {
		List<Block> blockList = getBlockListFromPredNameAndArity(gLit, lazyPredNameArityToBlockList);
		if (blockList == null) { return; }
		boolean addedToBlock = false;
		for (Block block : blockList) {
			if (block.addGndLiteral(gLit)) {
				gLit.setBlock(block);
				addedToBlock = true;
				break;
			}
		}
		if (!addedToBlock) {
			List<GroundLiteral> temp = new ArrayList<GroundLiteral>();
			temp.add(gLit);
			Block block = new Block(gLit, temp, timeStamp);
			gLit.setBlock(block);
			blockList.add(block);
			if (allLazyBlocks == null) { allLazyBlocks = new HashMap<GroundLiteral,Block>(4); }
			allLazyBlocks.put(gLit, block);
		}
	}
	*/
	/* TVK : Not used here.
	private boolean internQueryLiterals  = true;
	private boolean internHiddenLiterals = false;
*/

	/* TVK : Not used here.
	public void internAllLiteralsThatAreTrue(Collection<GroundLiteral> gLits, TimeStamp timeStamp) {
		if (debugLevel > 0) { Utils.print("%  Interning all the ground literals that have become true"); }
		help_internAllLiteralsThatAreTrue(gLits, ".", timeStamp);
		if (internQueryLiterals) {
			help_internAllLiteralsThatAreTrue(task.getQueryLiterals(),  "q", timeStamp);
		}
		if (internHiddenLiterals) {
			help_internAllLiteralsThatAreTrue(task.getHiddenLiterals(), "h", timeStamp); 
		}
		if (debugLevel > 0) { Utils.println(".  Done."); }
	}*/
	/* TVK : Not used here.

	private void help_internAllLiteralsThatAreTrue(Collection<GroundLiteral> gLits, String msg, TimeStamp timeStamp) {
		if (gLits == null) { return; }
		int counter = 0; int countActualInterns = 0;
		for (GroundLiteral gLit : gLits) if (gLit.getValue()) { 
			gLit.setValue(true, null, timeStamp);
			countActualInterns++; 
			if (debugLevel > 0 && ++counter % 10000 == 0) { Utils.print(msg); }
		}
	}
*/	
	// TVK:GMN Copied to GroundedMarkovNetowork. Can be removed
	@Deprecated
	public void printLiteralsAndClauses() {
		List<GroundLiteral> gndLiterals = getAllGroundLiterals_ExpensiveVersion();
		for(GroundLiteral gndL : gndLiterals) {
			Utils.println("Literal: " + gndL.toPrettyString());
			Set<GroundClause> gndClauses = gndL.getGndClauseSet();
			for(GroundClause gndC : gndClauses) {
				Utils.println("Clause: " + gndC.toPrettyString());
			}
		}
	}

	// %%%%%%%%%%%%%%%%%%%   End of Processing grounded network, lazy evaluation, etc.   %%%%%%%%%%%%%%%%%%%%%
	
}

// A special variable that aggregates normal variables.
class AggVar {
	List<Variable> varsCombined; // Order matters, so use a list.  Might want to use a LinkedListSet here, but these lists should be short, so walking through then should be faster than that dealing with hashing.
	
	protected AggVar(List<Variable> varsCombined) {
		this.varsCombined = varsCombined;
	}
	protected AggVar(Set<Variable> varsCombined) {
		this.varsCombined = new ArrayList<Variable>(varsCombined);
	}
	
	public int getPosition(Variable var) {
		int index = varsCombined.indexOf(var);
		if (index < 0) { Utils.error("Cannot find '" + var + "' in " + this); }
		return index;
	}
	
	public String toString() {
		String result = ""; // "agg";
		for (Variable var : varsCombined) { result += "_" + var; }
		return result.substring(1); // Drop the leading "_".
	}
}

// A data structure used to map a normal variable into a position in an aggregated variable.
class VariableIndexPair {
	protected AggVar aggVar; 
	protected int    index; // The 'var' indexes into a Set of List<Term> and this says which position in these lists is being referenced.
	
	protected VariableIndexPair(AggVar aggVar, int index) {
		this.aggVar = aggVar;
		this.index  = index;
	}
	
	public String toString() {
		return aggVar + "@" + index;
	}
	
}

// Hold information produced during a grounding of a literal.
class CacheLiteralGrounding {
	private   List<List<Term>> groundingsStillNeeded     = null;  // These are the groundings still needed for this literal.
	protected long trueCount    = -1; // Indicate these have no been set.
	protected long falseCount   = -1; // NOTE: these counts are for literals IGNORING THEIR sign.
	protected long unknownCount = -1;
	
	protected CacheLiteralGrounding() { // This is used when a literal is ONLY a query literal.		
	}
	protected CacheLiteralGrounding(List<List<Term>> groundingsStillNeeded, long trueCount, long falseCount, long unknownCount) {
		this.groundingsStillNeeded = groundingsStillNeeded;
		this.trueCount             = trueCount;
		this.falseCount            = falseCount;
		this.unknownCount          = unknownCount;
	}

	public void describeCache(String msg) {
		Utils.println("%   Cache Report: " + msg);
		Utils.println("%          #true: " + Utils.comma(trueCount));
		Utils.println("%         #false: " + Utils.comma(falseCount));
		Utils.println("%           #unk: " + Utils.comma(unknownCount));
		Utils.println("%     groundings: " + Utils.limitLengthOfPrintedList(groundingsStillNeeded, 25));	
	}

	public boolean groundingsRecorded() {
		return groundingsStillNeeded != null;
	}
	public List<List<Term>> getGroundingsStillNeeded() {
		return getGroundingsStillNeeded(true);
	}
	public List<List<Term>> getGroundingsStillNeeded(boolean complainIfGroundingsNotSaved) {
		if (groundingsStillNeeded != null) { return groundingsStillNeeded; }
		if (complainIfGroundingsNotSaved) { describeCache(""); Utils.error("Did not save the groundings in this CacheLiteralGrounding instance."); }
		return null;
	}
}

// Hold information for use when deciding the best literal to 'reduce.'
class BestLiteralInfo {
	protected double  bestReduction;
	protected long    numberReduced;
	protected long    numberUnknown;
	protected long    bestDenominator;
	protected int     bestLiteralArity;
	protected Literal bestLiteral;
	protected boolean bestSign;
	
	protected BestLiteralInfo() { // Instead of passing in all the parameters, simply let them be set directly.	
		reset();
	}
	
	protected void reset() {
		bestReduction        = 0.0; // Need to get a reduction great than zero.
		numberReduced        = Integer.MIN_VALUE;
		numberUnknown        = Integer.MIN_VALUE;
		bestDenominator      =  1;
		bestLiteralArity     = -1;
		bestLiteral          = null; // The literal that reduces combinatorics the most.
		bestSign             = true; // True if a POS literal; false otherwise.	
	}
}

// Sort by arity.
class LiteralSortComparator implements Comparator<Literal> {

    public int compare(Literal lit0, Literal lit1) {
    	int compare = lit0.numberArgs() - lit1.numberArgs();
    	
    	if (compare == 0) { return lit0.predicateName.hashCode() - lit1.predicateName.hashCode(); } // Break ties if possible.
    	return compare;
    }
}

// Wrap a clause with some other information (e.g., for use in sorting).
class WrappedClause {
    Clause clause;
    int    index;
    double countOfPossibleGroundings; // Use this first to sort.  (Set all values to, say, -1, to only use the second value.)
    double countOfRemainingGroundings; // Then this.

    protected WrappedClause(Clause c, int index, double countOfPossibleGroundings, double countOfRemainingGroundings) {
        clause                          = c;
        this.index                      = index;
        this.countOfPossibleGroundings  = countOfPossibleGroundings;
        this.countOfRemainingGroundings = countOfRemainingGroundings;
    }
    
    public String toString() {
    	return "Clause #" + Utils.comma(index) + " has" + 
    		    (countOfPossibleGroundings  >= 0 ? " " + Utils.truncate(countOfPossibleGroundings,  0) + " possible groundings" : "") +
    		    (countOfPossibleGroundings  >= 0 && countOfRemainingGroundings >= 0 ? " and" : "") +
    		    (countOfRemainingGroundings >= 0 ? " " + Utils.truncate(countOfRemainingGroundings, 0) + " remaining groundings" : "") + ": '" + clause.toString(Integer.MAX_VALUE);
    }
}

// Used to sort clauses by the number of groundings, from SMALLEST to LARGEST.
class ClauseSortComparator implements Comparator<WrappedClause> {

    public int compare(WrappedClause c0, WrappedClause c1) {
        if (c0.countOfPossibleGroundings  < c1.countOfPossibleGroundings)  { return -1; }
        if (c0.countOfPossibleGroundings  > c1.countOfPossibleGroundings)  { return  1; }
        if (c0.countOfRemainingGroundings < c1.countOfRemainingGroundings) { return -1; }
        if (c0.countOfRemainingGroundings > c1.countOfRemainingGroundings) { return  1; }
        return 0;
    }
}