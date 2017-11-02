/**
 * 
 */
package edu.wisc.cs.will.MLN_Task;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Constant;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.FunctionName;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateSpec;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Type;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.ResThmProver.HornClauseProver;
import edu.wisc.cs.will.Utils.Utils;

/**
 *   Richardson, M. and Domingos, P.,
 *   Markov logic networks,
 *   Machine Learning, 62, pp. 107-136, 2006.
 *   http://alchemy.cs.washington.edu/papers/richardson06/
 *   
 *   Note: literals in clauses will be processed faster if any constant arguments are the FIRST argument (of course might not always be possible).
 *         Could index on ALL positions (or the first K), but might not be worth the increase in space.
 * 
 * @author shavlik
 *
 */
public class MLN_Task {	
	private static final int debugLevel = 2; //Integer.MIN_VALUE;
	
	public boolean useAllClauses = false; // JWSJWSJWS If false, only use those that unify with a query or hidden literal.  (Might want all for some sorts of experiments.)
	
	protected final static int maxWarnings  = 100;
	protected              int warningCount =   0;  // Count how many warnings provided to user; stop when some maximum number reached. 
	
	public  double             maxNumberOfQueryLiterals  = 1e8;
	public  double             maxNumberOfHiddenLiterals = 1e8;
	
	private boolean            checkForNewConstants = true; // Turn off when done to save time, plus once starting grounding a network, new constants would mess up things.
	
	public  boolean            haveEliminatedNegativeWeightClauses = false; // Record this in case other (non-MCSAT) inference methods want to complain.
	public  double             minWgtToBeHardClause = 0.75 * Sentence.maxWeight; // Used by some algorithms (e.g., MCSAT) to see if 'hard' clauses are satisfied.

	public  HandleFOPCstrings  stringHandler;
	public  Unifier            unifier;
	public  HornClauseProver   prover;
	public  int                maxConstantsOfGivenType =    1000000; // When more than this many constants of a given type, discard randomly until this many.
	public  int                maxGroundingsOfLiteral  = 1000000000; // When finding the groundings of a LITERAL, limit to this many.  This is also the max size of JOINED argument lists.
	public  int                maxGroundingsOfClause   = 1000000000; // When finding the groundings of a CLAUSE,  limit to this many.
	
	protected String             workingDirectory;
	protected Collection<Clause> allClauses; // Not many of these, so no need to hash.
	private   Set<GroundLiteral> queryLiterals;   // Make these sets since we don't want any duplicates.
	private   Set<GroundLiteral> hiddenLiterals;  // Do NOT apply the closed-world assumption to these.
	private   Set<GroundLiteral> posQueryLiteralsForTraining;
	private   Set<GroundLiteral> negQueryLiteralsForTraining;
	private   Set<GroundLiteral> posEvidenceLiterals; // No need to allow this to be given as PredName as well, since presumably we do not want to say ALL are positive (or negative).
	private   Set<GroundLiteral> negEvidenceLiterals;
	public	  Set<GroundLiteral> posEvidenceInQueryLiterals;// These are the query literals that were present in the positive evidence. They must be returned with probability 1.
	public    Set<GroundLiteral> negEvidenceInQueryLiterals;// These are the query literals that were present in the negative evidence. They must be returned with probability 0.
	private   boolean            closedWorldAssumption = true; // Assume a literal is false if its truth value is not known.
	
	// All literals that meet one of these spec's is a literal of the associated type.  
	// More compact that creating all such literals, but might be expanded later in any case (also, one might not want ALL groundings to be in the given class, and in that case explicit lits of grounded literals should be used).
	// Also, can add something like 'p(x,y)' to a literal collection, which is the same (???) as putting 'p/2' in a Collection<PredNameArityPair>.
	private Set<PredNameArityPair> queryPredNames; // TODO - if these are used with GroundThisMarkovNetwork, then need to ground before inference?
	private Set<PredNameArityPair> hiddenPredNames; // These need to be SETs (at least in the creators) so that duplicates are not added.
	private Set<PredNameArityPair> posEvidencePredNames; // Probably rarely used, since can then remove from clauses, but allow them anyway.
	private Set<PredNameArityPair> negEvidencePredNames; // Ditto.
	
	private Map<PredicateName,Map<Integer,Map<Term,Collection<GroundLiteral>>>> knownQueriesThisPnameArity;
	private Map<PredicateName,Map<Integer,Map<Term,Collection<GroundLiteral>>>> knownHiddensThisPnameArity;
	private Map<PredicateName,Map<Integer,Map<Term,Collection<GroundLiteral>>>> knownPosEvidenceThisPnameArity;
	private Map<PredicateName,Map<Integer,Map<Term,Collection<GroundLiteral>>>> knownNegEvidenceThisPnameArity;
	private boolean knownQueriesThisPnameArityHasVariables     = false;
	private boolean knownHiddensThisPnameArityHasVariables     = false;
	private boolean knownPosEvidenceThisPnameArityHasVariables = false;
	private boolean knownNegEvidenceThisPnameArityHasVariables = false;
	
	// Can override the default value for closed-world assumption.
	private Map<PredicateName,Set<Integer>>  neverCWAonThisPredNameArity;
	private Map<PredicateName,Set<Integer>> alwaysCWAonThisPredNameArity;
			
	private Literal trueLiteral, falseLiteral;
	
	protected Set<FunctionName>               skolemFunctions  = null; // Record which functions are Skolems (Skolems need to be created by the stringHandler, not based on strings entered by the user).
	protected Map<PredicateName,Set<Integer>> skolemsPresent   = null; // Record which literals are associated with Skolem functions.
	private   Variable                        skolemMarker1    = null; // Skolem arguments are replaced with this marker, so it can be used to match any fact (no logical inference is done, so this works, but be careful of 'unit propagation' or the like is used).
	private   Variable                        skolemMarker2    = null; // A given literal can have more than one skolem variable,
	private   Variable                        skolemMarker3    = null; // so allow up to five in a clause (if more throw error, suggesting code be extended).
	private   Variable                        skolemMarker4    = null;
	private   Variable                        skolemMarker5    = null;
	private   Variable[]                      allSkolemMarkers = new Variable[5];
	protected Set<Variable>                   setOfSkolemMarkers; // Duplicate for fast lookup.
	protected Map<Literal,Set<Term>>          skolemsPerLiteral;  // Be sure to not COPY literals or this will be screwed up!
	
	private Map<Type,Set<Term>> hashOfTypeToConstants;        // Record all the constants of a given type.  Use Term here so can become argument lists without copying.
	private Map<Type,Set<Term>> hashOfTypeToReducedConstants; // A subset of the above, used for reducing the size of the ground Markov network via sampling.

	// TODO is the following still used?
	private Map<PredicateName,Map<Integer,Set<Clause>>> predNameToClauseList; // A hash table which gives all the clauses a literal (specified by predicateName/arity) appears in.

	private Map<Integer,List<GroundLiteral>> hashOfGroundLiterals;
 //	private Map<PredicateName,Map<Integer,Map<Constant,Map<Constant,List<GroundLiteral>>>>> hashOfGroundLiterals2; // A hash table for quickly finding literals given a predicateName/arity pair.
	
	// The next two are used after reductions to answer queries.
	private   Map<PredicateName,Map<Integer,Set<Literal>>> pNameArityToLiteralMap; // Record for each predicateName/arity, the literals in which it appears.  NOTE: each literal is assumed to be UNIQUE (and not further copying can be done).  MLN_Task does create copies of each literal in pre-processing, so that should suffice.
	protected Map<Literal,Clause>                          literalToClauseMap;     // Map literals to the clauses in which they appear. NOTE: this assumes that literals are NOT canonically represented.
		
	private   Map<Type,Set<Constant>> constantTypePairsHandled = new HashMap<Type,Set<Constant>>(4); // Used to prevent unnecessary calls to the stringHandler.  TODO - move this to the string handler, as a space-time tradeoff.
	
	private   TimeStamp timeStamp;
	
	/**
	 * Instances of this class hold all the common information in an MNL task.
	 */
	public MLN_Task(HandleFOPCstrings stringHandler) {
		this(stringHandler, new Unifier(), new HornClauseProver(stringHandler));
	}
	// The next variant is called by the others to set up various things.
	public MLN_Task(HandleFOPCstrings stringHandler, Unifier unifier, HornClauseProver prover) {
		this.stringHandler           = stringHandler;
		this.unifier                 = unifier;
		this.prover                  = prover;
		stringHandler.setUseStrictEqualsForLiterals(false); // The MLN code does a lot of indexing on literals, and sometimes on clauses, and we don't want spurious matches (even though due to variables being separately named per literal, this probably isn't necessary).
		stringHandler.setUseStrictEqualsForClauses( true); 
		//Utils.println("% The procedurallyDefinedPredicates = " + prover.getProcedurallyDefinedPredicates()); Utils.waitHere();
		hashOfTypeToConstants          = new HashMap<Type,Set<Term>>(4);
		hashOfTypeToReducedConstants   = new HashMap<Type,Set<Term>>(4);
		hashOfGroundLiterals           = new HashMap<Integer,List<GroundLiteral>>(4);
	//	hashOfGroundLiterals2          = new HashMap<PredicateName,Map<Integer,Map<Constant,Map<Constant,List<GroundLiteral>>>>>(4);
		knownQueriesThisPnameArity     = new HashMap<PredicateName,Map<Integer,Map<Term,Collection<GroundLiteral>>>>(4);
		knownHiddensThisPnameArity     = new HashMap<PredicateName,Map<Integer,Map<Term,Collection<GroundLiteral>>>>(4);
		knownPosEvidenceThisPnameArity = new HashMap<PredicateName,Map<Integer,Map<Term,Collection<GroundLiteral>>>>(4);
		knownNegEvidenceThisPnameArity = new HashMap<PredicateName,Map<Integer,Map<Term,Collection<GroundLiteral>>>>(4);
	}
	// Can only pass in predicateName/arity information.
	public MLN_Task(HandleFOPCstrings stringHandler, Unifier unifier, HornClauseProver prover, 
					Collection<Clause>     allClauses,
					Set<PredNameArityPair> queryPredNames, 
					Set<PredNameArityPair> posEvidencePredNames,
					Set<PredNameArityPair> negEvidencePredNames,
					Set<PredNameArityPair> hiddenPredNames,
					boolean                closedWorldAssumption) {
		this(stringHandler, unifier, prover);
		if (allClauses           != null) { setAllClauses(allClauses); }
		if (queryPredNames       != null) { setQueryPredNames(queryPredNames); }
		if (hiddenPredNames      != null) { setHiddenPredNames(hiddenPredNames); }
		if (posEvidencePredNames != null) { setPosEvidencePredNames(posEvidencePredNames); }
		if (negEvidencePredNames != null) { setNegEvidencePredNames(negEvidencePredNames); }
		setClosedWorldAssumption(closedWorldAssumption);
	}
	// Or can pass in collections of groundings.  NOTE: closedWorldAssumption is in a different position here so that this doesn't match the above (since the types of the Collections don't matter to this aspect of the compiler).
	public MLN_Task(HandleFOPCstrings   stringHandler, Unifier unifier, HornClauseProver prover, boolean closedWorldAssumption,
					Collection<Clause>  allClauses,
					Collection<Literal> queryLiterals,
					Collection<Literal> posEvidenceLiterals,
					Collection<Literal> negEvidenceLiterals,
					Collection<Literal> hiddenLiterals) {
		this(stringHandler, unifier, prover);
		if (allClauses          != null) { setAllClauses(allClauses); }
		if (queryLiterals       != null) { setQueryLiterals(queryLiterals); }
		if (hiddenLiterals      != null) { setHiddenLiterals(hiddenLiterals); }
		if (posEvidenceLiterals != null) { setPosEvidenceLiterals(posEvidenceLiterals); }
		if (negEvidenceLiterals != null) { setNegEvidenceLiterals(negEvidenceLiterals); }
		setClosedWorldAssumption(closedWorldAssumption);
	}
	// Or can mix-and-match (but cannot include both PredNameArityPair's and Literal's for the same category.)
	public MLN_Task(HandleFOPCstrings      stringHandler, Unifier unifier, HornClauseProver prover,
					Collection<Clause>     allClauses,
 					Collection<Literal>    queryLiterals,   // Can directly provide the literals of a given category.
 					Set<PredNameArityPair> queryPredNames,  // Or can give their predicateName/arity pairs (but not both).
 					Collection<Literal>    posEvidenceLiterals,
 					Set<PredNameArityPair> posEvidencePredNames,
 					Collection<Literal>    negEvidenceLiterals,
 					Set<PredNameArityPair> negEvidencePredNames,
		 			Collection<Literal>    hiddenLiterals,
		 			Set<PredNameArityPair> hiddenPredNames,
		 			boolean                closedWorldAssumption) {
		this(stringHandler, unifier, prover);
		if (allClauses           != null) { setAllClauses(allClauses); }
		if (queryLiterals        != null) { setQueryLiterals(queryLiterals); }
		if (hiddenLiterals       != null) { setHiddenLiterals(hiddenLiterals); }
		if (posEvidenceLiterals  != null) { setPosEvidenceLiterals(posEvidenceLiterals); }
		if (negEvidenceLiterals  != null) { setNegEvidenceLiterals(negEvidenceLiterals); }
		if (queryPredNames       != null) { setQueryPredNames(queryPredNames); }
		if (hiddenPredNames      != null) { setHiddenPredNames(hiddenPredNames); }
		if (posEvidencePredNames != null) { setPosEvidencePredNames(posEvidencePredNames); }
		if (negEvidencePredNames != null) { setNegEvidencePredNames(negEvidencePredNames); }
		setClosedWorldAssumption(closedWorldAssumption);
	}
	
	public void setPosQueryLiteralsForTraining(Set<GroundLiteral> lits) {
		if (lits != null) { setQueryLiteralsForTraining(lits, true);  }
	}	
	public void setNegQueryLiteralsForTraining(Set<GroundLiteral> lits) {
		if (lits != null) { setQueryLiteralsForTraining(lits, false); }
	}
	
	private void createTrueLiteralAndClause() {		
		if (trueLiteral  == null) { trueLiteral = stringHandler.trueLiteral;  }
		if (falseLiteral == null) {falseLiteral = stringHandler.falseLiteral; }
	}	
	public Literal getTrueLiteral()  { return trueLiteral;  }	
	public Literal getFalseLiteral() { return falseLiteral; }
	
	private Set<Type>    warningNoConstantsThisType;
	public Set<Term> getReducedConstantsOfThisType(Type type) {
		if (!hashOfTypeToConstants.containsKey(type)) {
			Set<Term> allConstantsOfThisType = stringHandler.isaHandler.getAllInstances(type);
			if (allConstantsOfThisType == null) { 
				if (warningNoConstantsThisType == null || !warningNoConstantsThisType.contains(type)) { 
						if (warningNoConstantsThisType == null) { warningNoConstantsThisType = new HashSet<Type>(4); }
						warningNoConstantsThisType.add(type);
						Utils.warning("Have no constants of type '" + type + "'."); 
				}
				return null;
			}
			hashOfTypeToConstants.put(type, allConstantsOfThisType);
			if (allConstantsOfThisType.size() > maxConstantsOfGivenType) {
				Set<Term> reducedSet = new HashSet<Term>(4);
				reducedSet.addAll(allConstantsOfThisType); // A bit inefficient to copy (especially if lots discarded), but this way we get exactly the desired number.
				hashOfTypeToReducedConstants.put(type, Utils.reduceToThisSizeByRandomlyDiscardingItemsInPlace(reducedSet, maxConstantsOfGivenType));
			} else { hashOfTypeToReducedConstants.put(type, allConstantsOfThisType); }
			if (debugLevel > -10) {
				Utils.println("% Have " + Utils.padLeft(allConstantsOfThisType.size(), 7) + " constants of type = '" + type  + "'"
								+ (allConstantsOfThisType.size() > maxConstantsOfGivenType ? ", reduced to " + Utils.comma(hashOfTypeToReducedConstants.get(type).size()) : "") 
								+ ".");
			}
		}
		return hashOfTypeToReducedConstants.get(type);
	}
	
	public void setQueryPredNames(Set<PredNameArityPair> queryPredNames) {
		if (this.queryPredNames == null) { this.queryPredNames = queryPredNames; }
		else { Utils.error("Already have some query predicateNames/arities: " + Utils.limitLengthOfPrintedList(this.queryPredNames, 25)); }
	}
	private boolean calledCreateAllQueryLiterals = false;
	protected void createAllQueryLiterals() {
		if (calledCreateAllQueryLiterals) { return; }
		calledCreateAllQueryLiterals = true;
		if (queryPredNames == null) { return; }
		if (queryLiterals  != null) { Utils.error("Already have some query literals: " + Utils.limitLengthOfPrintedList(queryLiterals, 25)); }
		queryLiterals = new HashSet<GroundLiteral>(4);
		if (debugLevel > -10) { Utils.println("%  queryPredNames = " + Utils.limitLengthOfPrintedList(queryPredNames, 25)); }
		for (PredNameArityPair predNameArityPair : queryPredNames) {
			Set<GroundLiteral> groundings = groundThisLiteral(predNameArityPair);
			if (true) { Utils.println("% Have " + Utils.comma(groundings) + " groundings for query " + predNameArityPair+ "."); }
			if (groundings != null) { queryLiterals.addAll(groundings); }
			else { Utils.error("Have no groundings for query: " + predNameArityPair); }
		}
		int numbQueries = Utils.getSizeSafely(queryLiterals);
		if (debugLevel  > 0)   { Utils.println("% Number of query literals generated from queryPredNames: " + Utils.comma(numbQueries)); }
		if (numbQueries > maxNumberOfQueryLiterals) { Utils.error("Too many query literals.  Note that the current code requires they all be explicitly grounded, even with lazy inference, since statistics need to be collected for each."); }
	}
	
	public void setHiddenPredNames(Set<PredNameArityPair> hiddenPredNames) {
		if (this.hiddenPredNames == null) { this.hiddenPredNames = hiddenPredNames; }
		else { Utils.error("Already have some hidden predicateNames/arities: " + Utils.limitLengthOfPrintedList(this.hiddenPredNames, 25)); }
	}
	private boolean calledCreateAllHiddenLiterals = false;
	protected void createAllHiddenLiterals() {
		if (calledCreateAllHiddenLiterals) { return; }
		calledCreateAllHiddenLiterals = true;
		if (hiddenPredNames == null) { return; }
		if (hiddenLiterals != null) { Utils.error("Already have some hidden literals: " + Utils.limitLengthOfPrintedList(hiddenLiterals, 25)); }
		hiddenLiterals = new HashSet<GroundLiteral>(4);
		if (debugLevel > 0) { Utils.println("%  hiddenPredNames = " + hiddenPredNames); }
		for (PredNameArityPair predNameArityPair : hiddenPredNames) {
			Set<GroundLiteral> groundings = groundThisLiteral(predNameArityPair);
			if (true) { Utils.println("% Have " + Utils.comma(groundings) + " groundings for hidden " + predNameArityPair+ "."); }
			if (groundings != null) { hiddenLiterals.addAll(groundings); }
			else { Utils.error("Have no groundings for hidden: " + predNameArityPair); }
		}
		int numbQueries = Utils.getSizeSafely(hiddenLiterals);
		if (debugLevel > 0) { Utils.println("% Size of hidden literals generated from hiddenPredNames: " + Utils.getSizeSafely(hiddenLiterals)); }
		if (numbQueries > maxNumberOfHiddenLiterals) { Utils.error("Too many hidden literals.  Note that the current code requires they all be explicitly grounded, even with lazy inference, since statistics need to be collected for each."); }
	}

	public void setPosEvidencePredNames(Set<PredNameArityPair> posEvidencePredNames) {
		if (this.posEvidencePredNames == null) { this.posEvidencePredNames = posEvidencePredNames; }
		else { Utils.error("Already have some positive-evidence predicateNames/arities: " + Utils.limitLengthOfPrintedList(this.posEvidencePredNames, 25)); }
	}
	private boolean calledCreateAllPositiveEvidence = false;
	public void createAllPositiveEvidence() {
		if (calledCreateAllPositiveEvidence) { return; }
		calledCreateAllPositiveEvidence = true;
		if (posEvidenceLiterals != null) { Utils.error("Already have some positive-evidence literals: " + Utils.limitLengthOfPrintedList(posEvidenceLiterals, 25)); }
		posEvidenceLiterals = new HashSet<GroundLiteral>(4);
		for (PredNameArityPair predNameArityPair : posEvidencePredNames) { 
			Set<GroundLiteral> groundings = groundThisLiteral(predNameArityPair);
			if (true) { Utils.println("% Have " + Utils.comma(groundings) + " groundings for positive evidence " + predNameArityPair+ "."); }
			if (groundings != null) { posEvidenceLiterals.addAll(groundings); }
			else { Utils.error("Have no groundings for positive evidence: " + predNameArityPair); }
		}
		if (debugLevel > 0) { Utils.println("% Size of positive-evidence literals generated from evidencePredNames: " + Utils.getSizeSafely(posEvidenceLiterals)); }
	}	
	
	public void setNegEvidencePredNames(Set<PredNameArityPair> negEvidencePredNames) {
		if (this.negEvidencePredNames == null) { this.negEvidencePredNames = negEvidencePredNames; }
		else { Utils.error("Already have some negative-evidence predicateNames/arities: " + Utils.limitLengthOfPrintedList(this.negEvidencePredNames, 25)); }
	}
	private boolean calledCreateAllNegativeEvidence = false;
	public void createAllNegativeEvidence() {
		if (calledCreateAllNegativeEvidence) { return; }
		calledCreateAllNegativeEvidence = true;
		if (negEvidenceLiterals != null) { Utils.error("Already have some negative-evidence literals: " + Utils.limitLengthOfPrintedList(negEvidenceLiterals, 25)); }
		negEvidenceLiterals = new HashSet<GroundLiteral>(4);
		for (PredNameArityPair predNameArityPair : negEvidencePredNames) { 
			Set<GroundLiteral> groundings = groundThisLiteral(predNameArityPair);
			if (true) { Utils.println("% Have " + Utils.comma(groundings) + " groundings for negative evidence " + predNameArityPair+ "."); }
			if (groundings != null) { negEvidenceLiterals.addAll(groundings); }
			else { Utils.error("Have no groundings for negative evidence: " + predNameArityPair); }
		}
		if (debugLevel > 0) { Utils.println("% Size of negative-evidence literals generated from evidencePredNames: " + Utils.getSizeSafely(negEvidenceLiterals)); }
	}			
	
	private boolean conflictingData = false;
	private void checkForConflictsInPredNames() {
		if (initialized) { Utils.error("Should not call after initialization."); }
		conflictingData = false;		
		checkForIntersectingPredNames("query literals",        queryPredNames,       "hidden literals",       hiddenPredNames); 
		checkForIntersectingPredNames("query literals",        queryPredNames,       "pos-evidence literals", posEvidencePredNames); 
		checkForIntersectingPredNames("query literals",        queryPredNames,       "neg-evidence literals", negEvidencePredNames); 
		checkForIntersectingPredNames("hidden literals",       hiddenPredNames,      "pos-evidence literals", posEvidencePredNames); 
		checkForIntersectingPredNames("hidden literals",       hiddenPredNames,      "neg-evidence literals", negEvidencePredNames); 
		checkForIntersectingPredNames("pos-evidence literals", posEvidencePredNames, "neg-evidence literals", negEvidencePredNames); 
		comparePredNamesAndLiterals(  "query literals",        queryPredNames);
		comparePredNamesAndLiterals(  "hidden literals",       hiddenPredNames);
		comparePredNamesAndLiterals(  "pos-evidence literals", posEvidencePredNames);
		comparePredNamesAndLiterals(  "neg-evidence literals", negEvidencePredNames);
		if (conflictingData) { Utils.error("Due to conflicting data, aborting."); }
	}
	// See if any of these pairs are in specific evidence.
	private void comparePredNamesAndLiterals(String name, Collection<PredNameArityPair> pairs) {
		comparePredNamesAndLiteralsThisMap(name, pairs, "query literals",        knownQueriesThisPnameArity);
		comparePredNamesAndLiteralsThisMap(name, pairs, "hidden literals",       knownHiddensThisPnameArity);
		comparePredNamesAndLiteralsThisMap(name, pairs, "pos-evidence literals", knownPosEvidenceThisPnameArity);
		comparePredNamesAndLiteralsThisMap(name, pairs, "neg-evidence literals", knownNegEvidenceThisPnameArity);
	}
	private void checkForIntersectingPredNames(String name1, Collection<PredNameArityPair> pairs1, String name2, Collection<PredNameArityPair> pairs2) {
		if (pairs1 == null || pairs2 == null) { return; }
		for (PredNameArityPair pair1 : pairs1) if (pairs2.contains(pair1)) {
			conflictingData = true;
			Utils.println("% Conflicting data!  PredName/arity specification for the " + name1 + " of '" + pair1 + "' is also in predName/arity specification for " + name2 + "."); 
		}
	}
	private void comparePredNamesAndLiteralsThisMap(String name, Collection<PredNameArityPair> pairs, String mapName, Map<PredicateName,Map<Integer,Map<Term,Collection<GroundLiteral>>>> map) {
		if (pairs == null || map == null) { return; }
		for (PredNameArityPair pair : pairs) {
			Map<Integer,Map<Term,Collection<GroundLiteral>>> lookup1 = map.get(pair.pName);
			if (lookup1 == null) { continue; }
			Map<Term,Collection<GroundLiteral>>              lookup2 = lookup1.get(pair.arity);
			if (lookup2 == null) { continue; }
			Collection<GroundLiteral>                        lookup3 = lookup2.get(null); // Get the 'all first arguments' list.
			if (Utils.getSizeSafely(lookup3) > 0) {
				conflictingData = true;
				Utils.println("% Conflicting data!  PredName/arity specification for the " + name + " of '" + pair + "' conflicts with the set of specific " + mapName + ", which contains: " + Utils.limitLengthOfPrintedList(lookup3, 25));
			}
		}
	}
	
	// This function checks and removes any evidence literals from the query literals. 
	private void removeAnyEvidenceFromQuery(){
		if (Utils.getSizeSafely(queryLiterals) < 1) { return; }
		Iterator<GroundLiteral> it = queryLiterals.iterator();
		while(it.hasNext()){
			GroundLiteral currLiteral = it.next();
			if (posEvidenceLiterals!=null && posEvidenceLiterals.contains(currLiteral)) {
				if (posEvidenceInQueryLiterals == null) { posEvidenceInQueryLiterals = new HashSet<GroundLiteral>(); }
				posEvidenceInQueryLiterals.add(currLiteral);
				it.remove();
			}
			else if (negEvidenceLiterals != null && negEvidenceLiterals.contains(currLiteral)) {
				if (negEvidenceInQueryLiterals == null) { negEvidenceInQueryLiterals = new HashSet<GroundLiteral>(); }
				negEvidenceInQueryLiterals.add(currLiteral);
				it.remove();			
			}
		}
	}
	
	
	/**
	 * Populate the predNameToClauseList data structure.
	 */
	private void populateLiteralToClauseList() {
		predNameToClauseList = new HashMap<PredicateName,Map<Integer,Set<Clause>>>(4);			
		
		if (allClauses == null) { Utils.error("Should not have allClauses = null."); }
		for (Clause currClause : allClauses) {	// Walk through the structure (i.e., the set of clauses).		
			for (int i = 0; i < 2; i++) {
				Iterator<Literal> iter = null;
				if (i == 0 && currClause.posLiterals != null) {
					iter = currClause.posLiterals.iterator();
				} else if (currClause.negLiterals != null) {
					iter = currClause.negLiterals.iterator();
				}
				if (iter == null) {	continue; }
				while (iter.hasNext()) {
					Literal       literal  = iter.next();
					PredicateName predName = literal.predicateName;
					int           arity    = literal.numberArgs();
					Map<Integer,Set<Clause>> lookup1 = predNameToClauseList.get(predName); // Get the clause list for this predicate name.
					Set<Clause>              lookup2 = null;
					
					if (lookup1 == null) {
						lookup1 = new HashMap<Integer,Set<Clause>>(4);
						predNameToClauseList.put(predName, lookup1);
						lookup2 = new HashSet<Clause>(4);
						lookup1.put(arity, lookup2);
					} else {
						lookup2 = lookup1.get(arity); // Get the clause list for this predicateName/arity pair.
						if (lookup2 == null) {
							lookup2 = new HashSet<Clause>(4);
							lookup1.put(arity, lookup2);
						}
					}
					lookup2.add(currClause);
				}
			}						
		}
	}	
	
	Set<Variable> varsInLiterals; // The next two methods use this to save some argument passing. 
	Map<FunctionName,Variable> skolemsInClauseMapToReplacement; // Ditto.
	int locationInSkolemMarkerArray = 0; // Ditto.

	private Collection<Clause> preprocessForSkolems(Collection<Clause> rawClauses) {
		if (rawClauses == null) { return null; }
		Collection<Clause> results = new ArrayList<Clause>(rawClauses.size());
		int numbOfSkolemMarkers = 5;
		skolemMarker1 = stringHandler.getExternalVariable("SkolemForMLNs");
		skolemMarker2 = stringHandler.getExternalVariable("SkolemForMLNs");
		skolemMarker3 = stringHandler.getExternalVariable("SkolemForMLNs");
		skolemMarker4 = stringHandler.getExternalVariable("SkolemForMLNs");
		skolemMarker5 = stringHandler.getExternalVariable("SkolemForMLNs");
		allSkolemMarkers[0] = skolemMarker1;
		allSkolemMarkers[1] = skolemMarker2;
		allSkolemMarkers[2] = skolemMarker3;
		allSkolemMarkers[3] = skolemMarker4;
		allSkolemMarkers[4] = skolemMarker5;
		setOfSkolemMarkers = new HashSet<Variable>(8);
		skolemsPerLiteral  = new HashMap<Literal,Set<Term>>(4);
		for (int i = 0; i < numbOfSkolemMarkers; i++) { setOfSkolemMarkers.add(allSkolemMarkers[i]); }
		skolemsInClauseMapToReplacement = new HashMap<FunctionName,Variable>(4);
		boolean warning = false;
		for (Clause clause : rawClauses) {
			varsInLiterals = new HashSet<Variable>(4);
			skolemsInClauseMapToReplacement.clear(); // In case clauses are ever used for resolution, consistently deal with Skolems across an entire clause.
			locationInSkolemMarkerArray = 0; // Reset count for each CLAUSE (NOT for each literal).
			List<Literal> newPos = processSkolemInLiterals(clause.posLiterals, true);
			Set<Variable> varsInLiteralsPOS = new HashSet<Variable>(4);
			varsInLiteralsPOS.addAll(varsInLiterals);
			varsInLiterals = new HashSet<Variable>(4);
			List<Literal> newNeg = processSkolemInLiterals(clause.negLiterals, false);
			if (Utils.getSizeSafely(clause.negLiterals) > 0) for (Variable var : varsInLiteralsPOS) if (!varsInLiterals.contains(var)) { // Don't report singletons since their use is recommended by Pedro for MLNs.  Actually, don't report unless any implication.
				Utils.println("\n%   WARNING: Should this be an existential variable '" + var + "'?\n%    " + clause.toString(Integer.MAX_VALUE) + "?");
				warning = true;
			}
			Clause newClause = stringHandler.getClause(newPos, newNeg);
			newClause.setWeightOnSentence(clause.getWeightOnSentence());
			newClause.setBodyContainsCut(clause.getBodyContainsCut());
			results.add(newClause);
		}
		if (skolemFunctions != null) {
			Utils.println("%   Skolems in use:              " + skolemFunctions);
			Utils.println("%   Literals with these Skolems: " + skolemsPresent);
		}
		if (debugLevel > 0 && warning) { Utils.waitHere(); }
		return results;
	}
	
	// If there are any Skolem functions in these literals, replace the Skolem argument with a skolemMarker.
	// If there are any other functions, look up their values (TODO - actually, these will need to be done at time of GROUNDING!).
	private List<Literal> processSkolemInLiterals(List<Literal> literals, boolean pos) {
		if (literals == null) { return null; }
		List<Literal> results = new ArrayList<Literal>(literals.size());
		Set<Term> skolemMarkersThisLiteral = new HashSet<Term>(4);
		for (Literal lit : literals) {
			if (lit.numberArgs() < 1) { results.add(lit); continue; }
			PredicateName pName = lit.predicateName;
			Literal      newLit = lit.copy(false); // This will insure all the properties of the literal are properly assigned, even of a small waste in copying the list holding the arguments.
			List<Term> arguments2 = new ArrayList<Term>(lit.numberArgs());
			skolemMarkersThisLiteral.clear();
			for (Term term : lit.getArguments()) if (term instanceof Function) {
				if (((Function) term).functionName.isaSkolem) {
					if (!pos) { Utils.println("Note: a Skolem in a NEGATED literal found: " + term + " in " + lit); Utils.waitHere("bug somewhere?"); }
					FunctionName fName = ((Function) term).functionName;
					if (skolemFunctions == null) { skolemFunctions = new HashSet<FunctionName>(4); }
					skolemFunctions.add(fName);

					Variable markerToUse = skolemsInClauseMapToReplacement.get(fName);
					if (debugLevel > 1) { Utils.println("%    Marker to use for Skolem '" + fName + "' is '" + markerToUse + "'."); }
					if (skolemsPresent == null) { skolemsPresent = new HashMap<PredicateName,Set<Integer>>(4); }
					Set<Integer> lookup = skolemsPresent.get(pName); // skolemsPresent not used currently, but seems worth keeping this information.
					if (lookup == null) {
						lookup = new HashSet<Integer>(4);
						skolemsPresent.put(pName, lookup);
					}
					lookup.add(lit.numberArgs()); // Since a Set, deals with duplicates.
					if (markerToUse == null) { // Not yet encountered in this clause.
						if (locationInSkolemMarkerArray >= 5) { Utils.error("Have too many Skolems (max = 5) in one clause.  Processing: " + lit); }
						markerToUse = allSkolemMarkers[locationInSkolemMarkerArray++]; // Get next free one.
						if (debugLevel > 1) { Utils.println("%       Need a NEW marker: " + markerToUse); }
						if (skolemsInClauseMapToReplacement == null) { skolemsInClauseMapToReplacement = new HashMap<FunctionName,Variable>(4); }
						skolemsInClauseMapToReplacement.put(fName, markerToUse);
					}
					skolemMarkersThisLiteral.add(markerToUse);  // A Set, so will handle duplicates properly.
					arguments2.add(markerToUse);					
				} else {
					Utils.error("Need to write code that looks up values of non-Skolem functions: " + term);
				}
			} else {
				if (term instanceof Variable) { varsInLiterals.add((Variable) term); }
				arguments2.add(term);
			}
			newLit.setArguments(arguments2);
			results.add(newLit);
			if (!skolemMarkersThisLiteral.isEmpty()) { skolemsPerLiteral.put(newLit, skolemMarkersThisLiteral); }
		}
		return results;
	}
	
	// Ground the network with respect to the clauses containing (i.e., unify with) query or hidden literals.
	public GroundedMarkovNetwork createReducedNetwork() {
		if (!initialized) { initialize(); }
		Collection<Clause> clausesContainingQueryOrHiddenLiterals;
		if (useAllClauses) { 
			clausesContainingQueryOrHiddenLiterals = allClauses;
		} else {
			if (debugLevel > 0) { Utils.println("\n% Creating a grounded network.  First indexing all clauses in which query or hidden literals appear."); }
			clausesContainingQueryOrHiddenLiterals = new HashSet<Clause>(4); // Use a set so duplicates removed.
			
			Utils.println("% queryPredNames=" + Utils.limitLengthOfPrintedList(queryPredNames));
			if (queryPredNames  != null) for (PredNameArityPair pair : queryPredNames) { 
				Collection<Clause> matchingClauses = getClausesContainingThisPredNameAndArity(pair.pName, pair.arity);
				if (debugLevel > 0) { Utils.println("%   For query '" + pair + "' have collected: " +  Utils.limitLengthOfPrintedList(matchingClauses, 25)); }
				if (matchingClauses != null) { clausesContainingQueryOrHiddenLiterals.addAll(matchingClauses); }
				else if (warningCount < maxWarnings) { Utils.println("% MLN WARNING #" + Utils.comma(++warningCount) + ": no clauses match " + pair + "."); }
			}
			if (debugLevel > 0 && queryPredNames != null) { Utils.println("%  Done with the " + Utils.comma(Utils.getSizeSafely(queryPredNames)) + " query predicate/arity names: " + Utils.limitLengthOfPrintedList(queryPredNames, 25)); }
			
			Utils.println("% hiddenPredNames=" + Utils.limitLengthOfPrintedList(hiddenPredNames));
			if (hiddenPredNames != null) for (PredNameArityPair pair : hiddenPredNames) { 
				Collection<Clause> matchingClauses = getClausesContainingThisPredNameAndArity(pair.pName, pair.arity);
				if (debugLevel > 0) { Utils.println("%   For hidden '" + pair + "' have collected: " +  Utils.limitLengthOfPrintedList(matchingClauses, 25)); }
				if (matchingClauses != null) { clausesContainingQueryOrHiddenLiterals.addAll(matchingClauses); }
				else if (warningCount < maxWarnings) { Utils.println("% MLN WARNING #" + Utils.comma(++warningCount) + ": no clauses match " + pair); }
			}
			if (debugLevel > 0 && hiddenPredNames != null) { Utils.println("%  Done with the " + Utils.comma(Utils.getSizeSafely(hiddenPredNames)) + " hidden predicate/arity names: " + Utils.limitLengthOfPrintedList(hiddenPredNames, 25)); }
			
			Utils.println("% queryLiterals=" + Utils.limitLengthOfPrintedList(queryLiterals));
			if (queryLiterals   != null) for (Literal lit : queryLiterals) { 
				Collection<Clause> unifyingClauses = getClausesThatUnifyWithThisLiteral(lit, false); 
				if (debugLevel > 0) { Utils.println("%   For query '" + lit + "' have collected: " +  Utils.limitLengthOfPrintedList(unifyingClauses, 25)); }
				if (unifyingClauses != null) { clausesContainingQueryOrHiddenLiterals.addAll(unifyingClauses); } // Do NOT apply bindings.
			}
			if (debugLevel > 0 && queryLiterals != null) { Utils.println("%  Done with the " + Utils.comma(queryLiterals) + " query literals: " + Utils.limitLengthOfPrintedList(queryLiterals, 25)); }
			
			Utils.println("% hiddenLiterals=" + Utils.limitLengthOfPrintedList(hiddenLiterals));
			if (hiddenLiterals != null) for (Literal lit : hiddenLiterals) { 
				Collection<Clause> unifyingClauses = getClausesThatUnifyWithThisLiteral(lit, false); 
				if (debugLevel > 0) { Utils.println("%   For hidden '" + lit + "' have collected: " +  Utils.limitLengthOfPrintedList(unifyingClauses, 25)); }
				if (unifyingClauses != null) { clausesContainingQueryOrHiddenLiterals.addAll(unifyingClauses); } // Do NOT apply bindings.
			}
			if (debugLevel > 0 && hiddenLiterals != null) { Utils.println("%  Done with the " + Utils.comma(hiddenLiterals) + " hidden literals: " + Utils.limitLengthOfPrintedList(hiddenLiterals, 25)); }
		}
		if (debugLevel > 0) {
			Utils.println("% Have collected " + Utils.comma(clausesContainingQueryOrHiddenLiterals) + " clauses: " + Utils.limitLengthOfPrintedList(clausesContainingQueryOrHiddenLiterals, 25));
		}
		GroundedMarkovNetwork grounder = new GroundedMarkovNetwork(this, clausesContainingQueryOrHiddenLiterals);
		grounder.analyzeClauses();
		return grounder;
	}
	@SuppressWarnings("unused")
	private GroundedMarkovNetwork createAllClausesGroundedNetwork() {
		GroundedMarkovNetwork grounder = new GroundedMarkovNetwork(this, allClauses);
		grounder.analyzeClauses();
		return grounder;		
	}
	
	// TODO - make this generic and put in some utilities class.
	// If this literal is not in this 'database' (db), add it and return true.  Otherwise return false.
	@SuppressWarnings("unused")
	private boolean addIfNotPresent(GroundLiteral gLit, Map<PredicateName,Map<Integer,List<GroundLiteral>>> db) {
		PredicateName pName = gLit.predicateName;
		int           arity = gLit.numberArgs();
		Map<Integer,List<GroundLiteral>> lookup1 = db.get(pName);
		if (lookup1 == null) {
			lookup1 = new HashMap<Integer,List<GroundLiteral>>(4);
			db.put(pName, lookup1); // Add to DB.
		}
		List<GroundLiteral> lookup2 = lookup1.get(arity);
		if (lookup2 == null) {
			lookup2 = new ArrayList<GroundLiteral>(1);
			lookup1.put(arity, lookup2); // A new arity, so add to DB.
			if (arity == 0) { // If got here with a zero-argument literal, then it is not yet present.
				return lookup2.add(gLit);
			}
		}
		if (arity == 0) { return false; } // This zero-argument literal is already present.  (Code below would still work, but leave this hear anyway.)
		List<Term> args = gLit.getArguments();
		boolean foundMatch = false;
		for (GroundLiteral inDB : lookup2) {
			boolean matches = true;
			for (int i = 0; i < arity; i++) if (!args.get(i).equals(inDB.getArgument(i))) {
				matches = false;
				break;
			}
			if (matches) {
				foundMatch = true;
				break;
			}
		}
		if (!foundMatch) { return lookup2.add(gLit); }
		return false;
	}
	
	/**
	 * Get all groundings of the literal whose predicate name and arity are passed as an argument.
	 * Postcondition: Be wary that at the end of this method, gndClauseList in the resulting ground literals in not initialized.
	 * 
	 * @param predName 
	 * 				We want to get all groundings of this predicate name and arity.
	 * @return Return all the groundings of predName/arity.
	 */
	private Set<GroundLiteral> groundThisLiteral(PredNameArityPair predNameArity) {
		if (predNameArity == null) { Utils.error("Should not have predNameArity=null."); }
		//Literal literal = convertPredNameArityPairToLiteral(predNameArity);
		Set<GroundLiteral> results = new HashSet<GroundLiteral>(4);	
		if (predNameArity.arity < 1) { // Handle case of a literal with NO arguments.
			Literal lit = stringHandler.getLiteral(predNameArity.pName);
			GroundLiteral gndLiteral = getCanonicalRepresentative(lit);
			results.add(gndLiteral);
			return results;
		}			
			
		// Collect all the types in the literal.
		Collection<TypeSpec> typeSpecs = collectLiteralArgumentTypes(predNameArity.pName, predNameArity.arity);
		if (debugLevel > -10) { Utils.println("% In groundThisLiteral(" + predNameArity + ") with typeSpecs = " + typeSpecs); }		
		List<Set<Term>> allArgPossibilities = new ArrayList<Set<Term>>(typeSpecs.size());
		for (TypeSpec typeSpec : typeSpecs) { // Need to convert from lists of constants to lists of terms at some point.  Might as well do it here (seems work the same regardless).
			Set<Term> constants = getReducedConstantsOfThisType(typeSpec.isaType);
			if (constants != null) {
				Set<Term> convertConstantsToTerms = new HashSet<Term>(4);
				convertConstantsToTerms.addAll(constants);
				allArgPossibilities.add(convertConstantsToTerms);
			} else {
				//allArgPossibilities.add(null);
				return null; // There are no groundings.
			}
		}
		if (debugLevel > -10) { 
			int size = 1;
			if (debugLevel > 3) { Utils.println(" allArgPossibilities = " + allArgPossibilities); }
			for (Set<Term> possibilities : allArgPossibilities) { size *= Utils.getSizeSafely(possibilities); }
			Utils.print("%   Will produce " + Utils.comma(size) + " groundings.  [1"); // TODO - filter if too many?
			for (Set<Term> possibilities : allArgPossibilities) { Utils.print(" x " + possibilities.size()); }
			Utils.println("]");
		}
		List<List<Term>> crossProduct = Utils.computeCrossProduct(allArgPossibilities, maxGroundingsOfLiteral);
		int counter = 0;
		for (List<Term> argList : crossProduct) {
			if (debugLevel > -10 && ++counter % 100000 == 0) { Utils.println("%       counter = " + Utils.comma(counter)); }
			Literal              lit = stringHandler.getLiteral(predNameArity.pName, argList);
			GroundLiteral gndLiteral = getCanonicalRepresentative(lit);
			results.add(gndLiteral);
		}
		if (debugLevel > 2) { Utils.println("%  Returning " + Utils.comma(Utils.getSizeSafely(results)) + " results\n"); }
		return results;
	}
	
	// Find the canonical (and grounded) representation of this literal, which should contain only constants as arguments.
	// Hash on predicate name, arity, and the first two arguments (after which, do a linear lookup).
	// Add this Literal to hashOfGroundLiterals if it isn't already there, unless requested not do so.
	// Return the entry in hashOfGroundLiterals for the (grounded version of this) literal (or null if not there and not requested to add it). 
	// NOTE: literal signs are IGNORED in this method, so users of these GroundLiteral's need to maintain sign elsewhere (other p(1) and ~p(1) will not match). 
	//       also, weights are ignored, so if they differ, a new design is needed here.
	private int countOfCanonicalGroundLiterals = 0;
	public  int getCountOfCanonicalGroundLiterals() { 
		int counter  = 0;
		int counter2 = 0;
		int max      = 0;
		Integer indexOfMax = 0;
		for (Integer index : hashOfGroundLiterals.keySet()) {
			int size = hashOfGroundLiterals.get(index).size();
			//Utils.println(" " + Utils.limitLengthOfPrintedList(hashOfGroundLiterals.get(index), 25)); 
			counter += size;
			if (size > max) { max = size; indexOfMax = index; }
			if (size > 1)   { counter2++; }
		}
		Utils.println("\n% There are " + Utils.comma(countOfCanonicalGroundLiterals) + " unique ground literals.");
		Utils.println("%  |canonical ground-literal hash codes| = " + Utils.comma(hashOfGroundLiterals.keySet().size()) + 
				        ", |hash of ground literals| = "            + Utils.comma(counter)  +
						", |with collisions| = "                    + Utils.comma(counter2) +
						", max # of collisions = "                  + Utils.comma(max));
		Utils.println("%    max collisions: " + Utils.limitLengthOfPrintedList(hashOfGroundLiterals.get(indexOfMax), 25));
		//Utils.waitHere();
		return countOfCanonicalGroundLiterals; 
	}
	private GroundLiteral newGlit_hold;
	private Integer       hashcode_hold;
	public void storeGroundLiteralBeingHeld() {
		if (hashcode_hold != null) {
			List<GroundLiteral> lookup = hashOfGroundLiterals.get(hashcode_hold);
			if (lookup == null) {
				lookup = new ArrayList<GroundLiteral>(1);
				hashOfGroundLiterals.put(hashcode_hold, lookup);
			}
			lookup.add(newGlit_hold);
			countOfCanonicalGroundLiterals++;
			if (checkForNewConstants) { collectTypedConstants(newGlit_hold.predicateName, newGlit_hold.getArguments()); }  // Check for new constants when first stored.
			if (debugLevel > 2) { Utils.println("%     new ground literal: " + newGlit_hold); }
		}
	}
	public GroundLiteral getCanonicalRepresentative(Literal lit) {
		return getCanonicalRepresentative(lit, true, false);
	}
	public GroundLiteral getCanonicalRepresentative(Literal lit, boolean storeIfNotThere, boolean postponeAddition) {	
		boolean hold = stringHandler.useFastHashCodeForLiterals;
		stringHandler.useFastHashCodeForLiterals = false; // Need this setting in order to get proper matching of equivalent literals.
		int hash = lit.hashCode(); 
		stringHandler.useFastHashCodeForLiterals = hold;
		List<GroundLiteral> lookup = hashOfGroundLiterals.get(hash);
		if (lookup == null) {
			if (!storeIfNotThere) { return null; } // Return an indicator that this literal is not in the hash table.
		} else { 
			for (GroundLiteral gLit : lookup) if (gLit.matchesThisGroundLiteral(lit)) { // Check the literals that hashed here.
				newGlit_hold  = null;
				hashcode_hold = null;
				return gLit; // Have found the canonical representative.  No need to store anything later.
			}
			if (!storeIfNotThere) { return null; } // Return an indicator that this literal is not in the hash table.
		}
		// This literal is new.  Convert to a GroundLiteral (if not already), add to hash table, and return it.
		GroundLiteral newGlit = (lit instanceof GroundLiteral ? (GroundLiteral) lit : new GroundLiteral(lit));
		newGlit_hold  = newGlit; /// If postponeAddition = true, then we'll add these later (e.g., after calling code decides if these should be stored).
		hashcode_hold = hash;
		if (!postponeAddition) { storeGroundLiteralBeingHeld();	}
		return newGlit;
	}
	/* TODO delete after 2/15/09
	public GroundLiteral getCanonicalRepresentative2(Literal lit, boolean storeIfNotThere, boolean postponeAddition) {
		PredicateName pName = lit.predicateName;
		int           arity = lit.numberArgs();
		
		Constant      arg0 = (arity == 0 ? null : (Constant) lit.getArgument(0)); // For 0-arity literals, use 'null' as the first argument.
		Constant      arg1 = (arity <= 1 ? null : (Constant) lit.getArgument(1)); // For 0- and 1-arity literals, use 'null' as the second argument.
		boolean       pavedNewGround = false; // Indicate if NEW memory created (if so, this literal has not been seen before).
		
		Map<Integer,Map<Constant,Map<Constant,List<GroundLiteral>>>> lookup1 = hashOfGroundLiterals2.get(pName);
		if (lookup1 == null) {
			if (!storeIfNotThere) { return null; }
			lookup1 = new HashMap<Integer,Map<Constant,Map<Constant,List<GroundLiteral>>>>(4);
			hashOfGroundLiterals2.put(pName, lookup1);
			pavedNewGround = true;
		}
		Map<Constant,Map<Constant,List<GroundLiteral>>> lookup2 = lookup1.get(arity);
		if (lookup2 == null) {
			if (!storeIfNotThere) { return null; }
			lookup2 = new HashMap<Constant,Map<Constant,List<GroundLiteral>>>(4);
			lookup1.put(arity, lookup2);
			pavedNewGround = true;
		}
		Map<Constant,List<GroundLiteral>> lookup3 = lookup2.get(arg0);
		if (lookup3 == null) {
			if (!storeIfNotThere) { return null; }
			lookup3 = new HashMap<Constant,List<GroundLiteral>>(4);
			lookup2.put(arg0, lookup3);
			pavedNewGround = true;
		}
		List<GroundLiteral> lookup4 = lookup3.get(arg1);
		if (lookup4 == null) {
			if (!storeIfNotThere) { return null; }
			lookup4 = new ArrayList<GroundLiteral>(1);
			lookup3.put(arg1, lookup4);
			pavedNewGround = true;
		}
		if (!pavedNewGround && lookup4.size() > 0) { //  Note that the lookup4 space might have been created yet nothing stored, due to postponeAddition=true.
			// Now need to walk through lookup4 to see if literal's representative is in there.
			if (arity <= 2) { return lookup4.get(0); } // Only one ground literal can reach these. 
			List<Term> litArgs = lit.getArguments();
			for (GroundLiteral gLit : lookup4) { // Still need to check the rest of the literals.
				boolean haveFoundIt = true;
				List<Term> gLitArgs = gLit.getArguments();
				for (int i = 2; i < arity; i++) if (gLitArgs.get(i) != litArgs) { haveFoundIt = false; continue; }
				if (haveFoundIt) { return gLit; } // Have found the canonical representative.
			}
		}
		if (!storeIfNotThere) { return null; } // Return an indicator that this literal is not in the hash table.
		// This literal is new.  Convert to a GroundLiteral (if not already), add to hash table, and return it.
		GroundLiteral newGlit = (lit instanceof GroundLiteral ? (GroundLiteral) lit : new GroundLiteral(lit));
		lookup4_hold = lookup4;
		newGlit_hold = newGlit;
		if (!postponeAddition) { storeGroundLiteralBeingHeld();	}
		return newGlit;
	}
	*/
	
	public Set<Clause> getClauseListFromPredNameAndArity(Literal lit) {
		return getClauseListFromPredNameAndArity(lit.predicateName, lit.numberArgs());
	}	
	public Set<Clause> getClauseListFromPredNameAndArity(PredicateName pName, int arity) {
		Map<Integer,Set<Clause>> lookup1 = predNameToClauseList.get(pName);
		if (lookup1 == null) { Utils.error("Cannot find " + pName + "/" + arity + " in " + Utils.limitLengthOfPrintedList(predNameToClauseList, 25)); }
		Set<Clause> lookup2 = lookup1.get(arity);
		if (lookup2 == null) { Utils.error("Cannot find " + pName + "/" + arity + " in " + lookup1); }
		return lookup2;
	}
	
	// Return a list of types for the arguments in this literal.
	public List<TypeSpec> collectLiteralArgumentTypes(Literal literal) {
		return collectLiteralArgumentTypes(literal.predicateName, literal.numberArgs());
	}
	public List<TypeSpec> collectLiteralArgumentTypes(PredicateName pName, int arity) {
		if (arity < 1) { return null; }
		List<PredicateSpec> typeList = pName.getTypeOnlyList(arity);
		// Currently ASSUME each literal has only one typeList.  TODO - relax assumption 
		if (Utils.getSizeSafely(typeList) < 1) { Utils.error("Could not find the argument types for: '" + pName + "/" + arity + "'."); }
		if (typeList.size() > 1) {
			if (warningCount < maxWarnings) { Utils.println("% MLN WARNING #" + Utils.comma(++warningCount) + ":  There is more than one mode for: '"  + pName + "/" + arity + "'. " + typeList + "  Will only use first one."); }
		}
		return typeList.get(0).getTypeSpecList();
	}
	
	public boolean isaQueryLiteral(Literal lit) {
		if (queryLiterals != null) { return queryLiterals.contains(lit); }
		return false;
	}
	
	public boolean isaPositiveEvidenceLiteral(GroundLiteral lit) {
		if (debugLevel > 2) { Utils.print("*** Is '" + lit + "' in positive evidence " + Utils.limitLengthOfPrintedList(posEvidenceLiterals, 25)); }
		boolean foundInPos = false;
		if (posEvidenceLiterals  != null) { foundInPos = posEvidenceLiterals.contains(lit); }
		if (posEvidencePredNames != null) { Utils.error("Need to look here as well - TODO."); }
		if (debugLevel > 2) { Utils.println((foundInPos ? " YES" : " NO")); }
		return foundInPos;
	}
	
	public boolean isaNegativeEvidenceLiteral(GroundLiteral lit) {
		if (debugLevel > 2) { Utils.print("*** Is '" + lit + "' in negative evidence " + Utils.limitLengthOfPrintedList(negEvidenceLiterals, 25)); }
		boolean foundInNeg = false;
		if (negEvidenceLiterals  != null) { foundInNeg = negEvidenceLiterals.contains(lit); }
		if (negEvidencePredNames != null) { Utils.error("Need to look here as well - TODO."); }
		if (debugLevel > 2) { Utils.println((foundInNeg ? " YES" : " NO")); }
		return foundInNeg;
	}
	
	public boolean isaEvidenceLiteral(GroundLiteral lit) {
		return (isaNegativeEvidenceLiteral(lit) || isaPositiveEvidenceLiteral(lit));
	}

	// Don't use this, since we really care about those clauses that were grounded, which can be a subset of this.
	//private Collection<Clause> getAllClauses() {
	//	return allClauses;
	//}

	public int getTotalNumberOfClauses() {
		return Utils.getSizeSafely(allClauses);
	}
	public void setAllClauses(Collection<Clause> allClauses) {
		if (allClauses == null) { Utils.error("Should not call with allClauses = null."); }
		this.allClauses = preprocessForSkolems(allClauses);
		populateLiteralToClauseList();
	}
	public void setAllClauses(Clause clause) {
		if (clause == null) { Utils.error("Should not call with clause = null."); }
		Collection<Clause> clauseList = new ArrayList<Clause>(1);
		clauseList.add(clause);
		setAllClauses(clauseList);
	}
	
	public void setNoCWApredNames(Collection<PredNameArityPair> noCWApredNames) {
		if (noCWApredNames == null) { return; }
		if (neverCWAonThisPredNameArity == null) { neverCWAonThisPredNameArity = new HashMap<PredicateName,Set<Integer>>(4); }
		for (PredNameArityPair pair : noCWApredNames) {
			addAlwaysCWAonThisPredNameArity(pair.pName, pair.arity);
		}
	}
	public void setYesCWApredNames(Collection<PredNameArityPair> yesCWApredNames) {
		if (yesCWApredNames == null) { return; }
		if (alwaysCWAonThisPredNameArity == null) { alwaysCWAonThisPredNameArity = new HashMap<PredicateName,Set<Integer>>(4); }
		for (PredNameArityPair pair : yesCWApredNames) {
			addAlwaysCWAonThisPredNameArity(pair.pName, pair.arity);
		}
	}
	public void addNeverCWAonThisPredNameArity(PredicateName pName, int arity) {
		if (neverCWAonThisPredNameArity == null) { neverCWAonThisPredNameArity = new HashMap<PredicateName,Set<Integer>>(4); }
		addToCWAoverrides(pName, arity, neverCWAonThisPredNameArity);
	}	
	public void addAlwaysCWAonThisPredNameArity(PredicateName pName, int arity) {
		if (alwaysCWAonThisPredNameArity == null) { alwaysCWAonThisPredNameArity = new HashMap<PredicateName,Set<Integer>>(4); }
		addToCWAoverrides(pName, arity, alwaysCWAonThisPredNameArity);
	}
	private void addToCWAoverrides(PredicateName pName, int arity, Map<PredicateName,Set<Integer>> map) {
		Set<Integer> lookup = map.get(pName);
		if (lookup == null) {
			lookup = new HashSet<Integer>(4);
			map.put(pName, lookup);
		}
		lookup.add(arity);
	}
	// If the first argument in a gLit is a VARIABLE, then can no longer index on the first variable.
	// In this case do not add more to the index based on constants.  TODO erase all old items if any, but only do so the FIRST time a variable encountered.
	private void addToKnowns(GroundLiteral gLit, boolean gLitHasVars, Map<PredicateName,Map<Integer,Map<Term,Collection<GroundLiteral>>>> map) {
		PredicateName pName = gLit.predicateName;
		int           arity = gLit.numberArgs();
		Term       firstArg = (arity < 1 ? null : gLit.getArgument(0));
		
		Map<Integer,Map<Term,Collection<GroundLiteral>>> lookup1 = map.get(pName);
		if (lookup1 == null) {
			lookup1 = new HashMap<Integer,Map<Term,Collection<GroundLiteral>>>(4);
			map.put(pName, lookup1);
		}
		Map<Term,Collection<GroundLiteral>> lookup2 = lookup1.get(arity);
		if (lookup2 == null) {
			lookup2 = new HashMap<Term,Collection<GroundLiteral>>(4);
			lookup1.put(arity, lookup2);
		}
		// Each gLit whose first argument is a constant is put in two lists.
		if (!gLitHasVars && firstArg != null && firstArg instanceof Constant) {
			Collection<GroundLiteral> lookup3a = lookup2.get(firstArg);
			if (lookup3a == null) {
				lookup3a = new ArrayList<GroundLiteral>(1);
				lookup2.put(firstArg, lookup3a);
			}
			lookup3a.add(gLit);
		}
		// All gLit's are in the entry.
		Collection<GroundLiteral> lookup3b = lookup2.get(null);
		if (lookup3b == null) {
			lookup3b = new ArrayList<GroundLiteral>(1);
			lookup2.put(null, lookup3b);
		}
		lookup3b.add(gLit);		
	}
	public boolean isaKnownLiteral(Literal gLit) {
		PredicateName pName = gLit.predicateName;
		int           arity = gLit.numberArgs();
		return isaKnownLiteral(pName, arity);
	}
	public boolean isaKnownLiteral(PredicateName pName, int arity) {
		return (Utils.getSizeSafely(getKnownsCollection(pName, arity, null, knownPosEvidenceThisPnameArity)) > 0 ||
				Utils.getSizeSafely(getKnownsCollection(pName, arity, null, knownQueriesThisPnameArity))     > 0 ||
				Utils.getSizeSafely(getKnownsCollection(pName, arity, null, knownHiddensThisPnameArity))     > 0 ||
				Utils.getSizeSafely(getKnownsCollection(pName, arity, null, knownNegEvidenceThisPnameArity)) > 0);
	}
	public boolean isInQueries(Literal gLit) {
		PredicateName pName = gLit.predicateName;
		int           arity = gLit.numberArgs();
		return isInQueries(pName, arity);
	}
	public boolean isInQueries(PredicateName pName, int arity) {
		return Utils.getSizeSafely(getKnownsCollection(pName, arity, null, knownQueriesThisPnameArity)) > 0;
	}
	public boolean isInHiddens(Literal gLit) {
		PredicateName pName = gLit.predicateName;
		int           arity = gLit.numberArgs();
		return isInHiddens(pName, arity);
	}
	public boolean isInHiddens(PredicateName pName, int arity) {
		return Utils.getSizeSafely(getKnownsCollection(pName, arity, null, knownHiddensThisPnameArity)) > 0;
	}
	public boolean isInEvidence(Literal gLit) {
		PredicateName pName = gLit.predicateName;
		int           arity = gLit.numberArgs();
		return isInEvidence(pName, arity);
	}
	public boolean isInEvidence(PredicateName pName, int arity) {
		return (Utils.getSizeSafely(getKnownsCollection(pName, arity, null, knownPosEvidenceThisPnameArity)) > 0  ||
				Utils.getSizeSafely(getKnownsCollection(pName, arity, null, knownNegEvidenceThisPnameArity)) > 0);
	}
	public Collection<GroundLiteral> getQueryKnowns(Literal lit) {
		return getKnownsCollection(lit, knownQueriesThisPnameArityHasVariables,     knownQueriesThisPnameArity);
	}
	public Collection<GroundLiteral> getHiddenKnowns(Literal lit) {
		return getKnownsCollection(lit, knownHiddensThisPnameArityHasVariables,     knownHiddensThisPnameArity);
	}
	public Collection<GroundLiteral> getPosEvidenceKnowns(Literal lit) {
		return getKnownsCollection(lit, knownPosEvidenceThisPnameArityHasVariables, knownPosEvidenceThisPnameArity);
	}
	public Collection<GroundLiteral> getNegEvidenceKnowns(Literal lit) {
		return getKnownsCollection(lit, knownNegEvidenceThisPnameArityHasVariables, knownNegEvidenceThisPnameArity);
	}
	private Collection<GroundLiteral> getKnownsCollection(Literal lit, boolean hasVariables, Map<PredicateName,Map<Integer,Map<Term,Collection<GroundLiteral>>>> map) {
		PredicateName pName = lit.predicateName;
		int           arity = lit.numberArgs();
		Term       firstArg = (hasVariables || arity < 1 ? null : lit.getArgument(0)); // If there are variables in this Map, then don't use constants index since if we did we would need to merge two lists (TODO - rethink this space-time tradeoff).
		return getKnownsCollection(pName, arity, firstArg, map);
	}
	private Collection<GroundLiteral> getKnownsCollection(PredicateName pName, int arity, Term firstArg, Map<PredicateName,Map<Integer,Map<Term,Collection<GroundLiteral>>>> map) {
		Map<Integer,Map<Term,Collection<GroundLiteral>>> lookup1 = map.get(pName);
		if (lookup1 == null) { return null; }
		Map<Term,Collection<GroundLiteral>> lookup2 = lookup1.get(arity);
		if (lookup2 == null) { return null; }
		if (firstArg != null && firstArg instanceof Constant) { return lookup2.get(firstArg); }
		return lookup2.get(null);
	}
	
	public Set<GroundLiteral> getQueryLiterals() {
		return queryLiterals;
	}
	public void setQueryLiterals(Collection<Literal> queryLiterals) {
		setQueryLiterals(queryLiterals, true);
	}
	public void setQueryLiterals(Collection<Literal> queryLiterals, boolean complainIfNonNull) {
		if (initialized) { Utils.error("Should not call after initialization."); }
		if (complainIfNonNull && this.queryLiterals != null) {
			Utils.error("Already have queryLiterals = " + Utils.limitLengthOfPrintedList(this.queryLiterals, 25));
		}
		if (queryLiterals == null) { Utils.error("Should not call with queryLiterals = null."); }
		this.queryLiterals = new HashSet<GroundLiteral>(4);
		int counter = 0;
		if (queryLiterals != null) for (Literal literal : queryLiterals) {
			GroundLiteral   gLit = null;
			boolean hasVariables = literal.containsVariables();
			if (hasVariables) { // Handle facts with variables specially - they are pulled out by GroundThisMarkovNetwork in factsWithVariables.
				collectTypedConstants(literal.predicateName, literal.getArguments()); // Check for new constants.
				gLit = new GroundLiteral(literal);
			} else {
				gLit = getCanonicalRepresentative(literal);
			}
			this.queryLiterals.add(gLit);
			knownQueriesThisPnameArityHasVariables = hasVariables || knownQueriesThisPnameArityHasVariables;
			addToKnowns(gLit, knownQueriesThisPnameArityHasVariables, knownQueriesThisPnameArity);
			gLit.setValue(Utils.random() > 0.5, null, timeStamp); // Give a random setting to query variables.
			counter++; if (counter % 10000 == 0) { Utils.println("%   Have hashed and collected constants from " + Utils.comma(counter) + " query literals."); }
		}
	}
	
	public Collection<GroundLiteral> getQueryLiteralsForTraining(boolean pos) {
		if (pos) { return posQueryLiteralsForTraining; } else { return negQueryLiteralsForTraining; }
	}
	public Set<GroundLiteral> setQueryLiteralsForTraining(Set<GroundLiteral> queryLiterals, boolean pos) {
		return setQueryLiteralsForTraining(queryLiterals, pos, true);
	}
	public Set<GroundLiteral> setQueryLiteralsForTraining(Set<GroundLiteral> queryLiterals, boolean pos, boolean complainIfNonNull) {
		if (initialized) { Utils.error("Should not call after initialization."); }
		if (complainIfNonNull &&  pos && posQueryLiteralsForTraining != null) {
			Utils.error("Already have posQueryLiteralsForTraining = " + Utils.limitLengthOfPrintedList(posQueryLiteralsForTraining, 25));
		}
		if (complainIfNonNull && !pos && this.negQueryLiteralsForTraining != null) {
			Utils.error("Already have negQueryLiteralsForTraining = " + Utils.limitLengthOfPrintedList(negQueryLiteralsForTraining, 25));
		}
		if (queryLiterals == null) { Utils.error("Should not call with queryLiterals = null."); }
		if (pos) {posQueryLiteralsForTraining = new HashSet<GroundLiteral>(4); } else { negQueryLiteralsForTraining = new HashSet<GroundLiteral>(4); }
		Collection<GroundLiteral> queryLiteralsToUse = (pos ? posQueryLiteralsForTraining : negQueryLiteralsForTraining);
		int counter = 0;
		if (queryLiterals != null) for (Literal literal : queryLiterals) { 
			queryLiteralsToUse.add(getCanonicalRepresentative(literal));
			counter++; if (counter % 10000 == 0) { Utils.println("%   Have hashed and collected constants from " + Utils.comma(counter) + (pos ? " positive" : " negative") + " query literals for training."); }
		}
		if (pos) { return posQueryLiteralsForTraining; }
		return negQueryLiteralsForTraining;
	}
	
	public void setAllQueryVariablesToTheirTrainingValues() {
		if (negQueryLiteralsForTraining != null) { // If the negatives are provided, assume that fraction of positives and negatives applies to the all the "unlabelled" examples as well.
			int    totalPos    = Utils.getSizeSafely(posQueryLiteralsForTraining);
			int    totalNeg    = Utils.getSizeSafely(negQueryLiteralsForTraining);
			int    total       = Utils.getSizeSafely(queryLiterals);
			double fractionNeg = (total - totalPos) / (double)total;
			if (totalPos + totalNeg < total) { Utils.println("% Assuming that " + Utils.truncate(100 * fractionNeg, 2) + " of the " + Utils.comma(total - (totalPos + totalNeg)) + " unlabeled training examples are negative."); }
			if (totalPos + totalNeg < total) { setAllQueryVariablesToFalseWithThisProbability(fractionNeg); }  // Ignores any block information.  TODO
		}
		Set<GroundClause> updateSatForClauses = new HashSet<GroundClause>();
		if (negQueryLiteralsForTraining != null) for (GroundLiteral gLit : negQueryLiteralsForTraining) {
			if (debugLevel > 2) { Utils.println("% Setting to FALSE this train-set query literal: '" + gLit + "'."); }
			gLit.setValueOnly(false, timeStamp); 
			if (gLit.getGndClauseSet() != null) updateSatForClauses.addAll(gLit.getGndClauseSet());
		} else { // If NO negatives are provided, assume ALL are negative, then override those said to be positive.
			if (debugLevel > 0) { Utils.println("% Setting to FALSE all the " + Utils.comma(Utils.getSizeSafely(queryLiterals)) + " query literals (some of which might be next changed to TRUE)."); }
			setAllQueryVariablesToFalseWithThisProbability(1.001); 
		}
		// Do the POSITIVES second so that it is correct to first set all query values to false.
		if (posQueryLiteralsForTraining != null) for (GroundLiteral gLit : posQueryLiteralsForTraining) {
			if (debugLevel > 2) { Utils.println("% Setting to TRUE this train-set query literal: '" + gLit + "'."); }
			gLit.setValueOnly(true, timeStamp);
			if (gLit.getGndClauseSet() != null) updateSatForClauses.addAll(gLit.getGndClauseSet());
		}
		// Update the isSatisfiedCached value for these clauses
		for (GroundClause gndClause : updateSatForClauses) {
			if (gndClause == null) Utils.error("% MLNTask: GndClause shouldn't be null");
			//boolean sat = 
				gndClause.checkIfSatisfied(timeStamp);
			// Utils.println("% MLNTASK Set " + sat + " to " + gndClause.toPrettyString());
		}
	}
	
	public void setAllQueryVariablesToFalseWithThisProbability(double probOfBeingFalse) {
		if (queryLiterals != null) for (GroundLiteral gLit : queryLiterals) { gLit.setValueOnly(Utils.random() > probOfBeingFalse, timeStamp); }
	}
	
	public Collection<GroundLiteral> getHiddenLiterals() {
		return hiddenLiterals;
	}
	public void setHiddenLiterals(Collection<Literal> hiddenLiterals) {
		if (initialized) { Utils.error("Should not call after initialization."); }
		if (hiddenLiterals == null) { Utils.error("Should not have called with hiddenLiterals = null."); }
		this.hiddenLiterals = new HashSet<GroundLiteral>(4);
		int counter = 0;
		if (hiddenLiterals != null) for (Literal literal : hiddenLiterals) { 
			GroundLiteral   gLit = null;
			boolean hasVariables = literal.containsVariables();
			if (hasVariables) { // Handle facts with variables specially - they are pulled out by GroundThisMarkovNetwork in factsWithVariables.
				collectTypedConstants(literal.predicateName, literal.getArguments()); // Check for new constants.
				gLit = new GroundLiteral(literal);
			} else {
				gLit = getCanonicalRepresentative(literal);
			}
			this.hiddenLiterals.add(gLit);
			knownHiddensThisPnameArityHasVariables =  hasVariables || knownHiddensThisPnameArityHasVariables;
			addToKnowns(gLit, knownHiddensThisPnameArityHasVariables, knownHiddensThisPnameArity);
			gLit.setValueOnly(Utils.random() > 0.5, timeStamp); // Give a random initial setting to hidden variables.
			counter++; if (counter % 10000 == 0) { Utils.println("%   Have hashed and collected constants from " + Utils.comma(counter) + " hidden literals."); }
		}
	}

	public Collection<GroundLiteral> getPosEvidenceLiterals() {
		return posEvidenceLiterals;
	}
	public void setPosEvidenceLiterals(Collection<Literal> posEvidenceLiterals) {
		if (initialized) { Utils.error("Should not call after initialization."); }
		if (posEvidenceLiterals == null) { Utils.error("Should not have called with posEvidenceLiterals = null."); }
		this.posEvidenceLiterals = new HashSet<GroundLiteral>(4);
		int counter = 0;
		if (posEvidenceLiterals != null) for (Literal literal : posEvidenceLiterals) { 
			GroundLiteral   gLit = null;
			Utils.println(literal.toString());
			boolean hasVariables = literal.containsVariables();
			if (hasVariables) { // Handle facts with variables specially - they are pulled out by GroundThisMarkovNetwork in factsWithVariables.
				collectTypedConstants(literal.predicateName, literal.getArguments()); // Check for new constants.
				gLit = new GroundLiteral(literal);
			} else {
				gLit = getCanonicalRepresentative(literal);
			}
			this.posEvidenceLiterals.add(gLit);
			knownPosEvidenceThisPnameArityHasVariables = hasVariables || knownPosEvidenceThisPnameArityHasVariables;
			addToKnowns(gLit, knownPosEvidenceThisPnameArityHasVariables, knownPosEvidenceThisPnameArity) ;
			gLit.setValue(true, null, timeStamp);
			counter++; if (counter % 10000 == 0) { Utils.println("%   Have hashed and collected constants from " + Utils.comma(counter) + " positive-evidence literals."); }
		}
	}

	public Collection<GroundLiteral> getNegEvidenceLiterals() {
		return negEvidenceLiterals;
	}
	public void setNegEvidenceLiterals(Collection<Literal> negEvidenceLiterals) {
		if (initialized) { Utils.error("Should not call after initialization."); }
		if (negEvidenceLiterals == null) { Utils.error("Should not have called with negEvidenceLiterals = null."); }
		this.negEvidenceLiterals = new HashSet<GroundLiteral>(4);
		int counter = 0;
		if (negEvidenceLiterals != null) for (Literal literal : negEvidenceLiterals) { 
			GroundLiteral gLit = null;
			boolean hasVariables = literal.containsVariables();
			if (hasVariables) { // Handle facts with variables specially - they are pulled out by GroundThisMarkovNetwork in factsWithVariables.
				collectTypedConstants(literal.predicateName, literal.getArguments()); // Check for new constants.
				gLit = new GroundLiteral(literal);
			} else {
				gLit = getCanonicalRepresentative(literal);
			}
			this.negEvidenceLiterals.add(gLit); 
			knownNegEvidenceThisPnameArityHasVariables = hasVariables || knownNegEvidenceThisPnameArityHasVariables;
			addToKnowns(gLit, knownNegEvidenceThisPnameArityHasVariables, knownNegEvidenceThisPnameArity);
			gLit.setValue(false, null, timeStamp);
			counter++; if (counter % 10000 == 0) { Utils.println("%   Have hashed and collected constants from " + Utils.comma(counter) + " negative-evidence literals."); }
		}
	}

	public Collection<PredNameArityPair> getQueryPredNames()       { return queryPredNames;       }
	public Collection<PredNameArityPair> getPosEvidencePredNames() { return posEvidencePredNames; }
	public Collection<PredNameArityPair> getNegEvidencePredNames() { return negEvidencePredNames; }
	public Collection<PredNameArityPair> getHiddenPredNames()      { return hiddenPredNames;      }
	
	
	// See if this literal contains any Skolems; if so, return them.
	public Collection<Term> getSkolemsInThisNewLiteral(Literal lit) {
		Collection<Term> results = null;
		if (lit.numberArgs() < 1) { return null; }
		for (Term term : lit.getArguments()) if (setOfSkolemMarkers.contains(term)) {
			if (results == null) { results = new HashSet<Term>(4); }
			results.add(term);
		}
		return results;
	}

	private boolean initialized = false;

	private void initialize() {
		if (initialized) { return; }
		checkForNewConstants = false;
		constantTypePairsHandled.clear(); // Return this memory.  No harm if later used again (other than some wasted cycles).

		List<PredicateName>   queryPredNamesReadIn  = stringHandler.getQueryPredicates();
		List<Integer>       queryPredAritiesReadIn  = stringHandler.getQueryPredArities();
		if (queryPredNamesReadIn != null) for (int i = 0; i < queryPredNamesReadIn.size(); i++) {
			PredicateName    pName = queryPredNamesReadIn.get(i); // See if this is already known, say from reading examples.
			int              arity = queryPredAritiesReadIn.get(i);
			boolean           done = false;
			PredNameArityPair pair = new PredNameArityPair(pName, arity);
			
			if (queryPredNames != null && queryPredNames.contains(pair)) { break; }
			if (queryLiterals != null) for (Literal qLit : queryLiterals) {
				if (qLit.predicateName == pName && qLit.numberArgs() == arity) { done = true; break; }
			}
			if (done) { break; }
			if (queryPredNames == null) { queryPredNames = new HashSet<PredNameArityPair>(4); }
			queryPredNames.add(new PredNameArityPair(pName, arity));
		}
		List<PredicateName>   hiddenPredNamesReadIn = stringHandler.getHiddenPredicates();
		List<Integer>       hiddenPredAritiesReadIn = stringHandler.getHiddenPredArities();
		if (hiddenPredNamesReadIn != null) for (int i = 0; i < hiddenPredNamesReadIn.size(); i++) {
			PredicateName pName = hiddenPredNamesReadIn.get(i); // See if this is already known, say from reading examples.
			int           arity = hiddenPredAritiesReadIn.get(i);
			boolean        done = false;
			PredNameArityPair pair = new PredNameArityPair(pName, arity);
			
			if (queryPredNames != null && queryPredNames.contains(pair)) { break; }
			
			if (hiddenLiterals != null) for (Literal hLit : hiddenLiterals) {
				if (hLit.predicateName == pName && hLit.numberArgs() == arity) { done = true; break; }
			}
			if (done) { break; }
			if (hiddenPredNames == null) { hiddenPredNames = new HashSet<PredNameArityPair>(4); }
			hiddenPredNames.add(new PredNameArityPair(pName, arity));
		}
		
		createTrueLiteralAndClause();
		indexLiteralsAndClauses();	
		checkForConflictsInPredNames();
		removeAnyEvidenceFromQuery();
		timeStamp = new TimeStamp("initializing an MLN task");
		initialized = true;
	}

	// Expand the information provided as predicate-name/arity pairs.  BUT DO NOT DO THIS UNLESS (AND UNTIL) NECESSARY,
	// SINCE THESE EXPANSIONS CAN BE LARGE (and can also greatly slow down the network-reduction process).
	public void expandAllPnameArityPairs() {
		createAllQueryLiterals();
		createAllHiddenLiterals();
		createAllPositiveEvidence();
		createAllNegativeEvidence();
	}
	
	private void indexLiteralsAndClauses() {
		pNameArityToLiteralMap = new HashMap<PredicateName,Map<Integer,Set<Literal>>>(4);
		literalToClauseMap     = new HashMap<Literal,Clause>(4);
		
		if (debugLevel > 0) { Utils.println("\n% Indexing all the literals in the " + Utils.comma(Utils.getSizeSafely(allClauses))+ " clauses."); }
		if (allClauses != null) for (Clause c : allClauses) {
			if (c.posLiterals != null) for (Literal pLit : c.posLiterals) { indexLiterals(c, pLit); }
			if (c.negLiterals != null) for (Literal nLit : c.negLiterals) { indexLiterals(c, nLit); }
		}
		if (debugLevel > 0) { // Note: here 'arity' is the NUMBER OF ARGUMENTS (rather than the # of distinct variables).
			Utils.println("\n% The mapping from predicateNames/arities to the clauses containing such literals.");
			for (PredicateName pName : pNameArityToLiteralMap.keySet()) {
				Utils.println(        "%   '" + pName + "'");
				Set<Integer> arities = pNameArityToLiteralMap.get(pName).keySet();
				for (Integer arity : arities) {
					if (arities.size() > 1) { Utils.println(    "%     arity = " + arity); }
					for (Literal lit : pNameArityToLiteralMap.get(pName).get(arity)) {
						Clause clause = literalToClauseMap.get(lit);
						Utils.println("%       " + (clause.getSign(lit) ? " '" : "'~") + lit + "' in '" + clause.toString(Integer.MAX_VALUE) + "'.");
					}
				}
			}
		}
	}
	
	public Collection<Clause> getClausesContainingThisPredNameAndArity(PredicateName pName, int arity) {
		Collection<Literal> literals = getLiteralsContainingThisPredNameAndArity(pName, arity);
		if (literals == null) { return null; }
		Collection<Clause> results = new HashSet<Clause>(4);
		for (Literal lit : literals) {
			results.add(literalToClauseMap.get(lit));
		}
		return results;
	}	
	// Use a LIST here since a literal might appear in one clause multiple times.  TODO - return the binding as well????
	public List<Clause> getClausesThatUnifyWithThisLiteral(Literal lit, boolean applyBindingsToResults) {
		return getClausesThatUnifyWithThisLiteral(lit, applyBindingsToResults, null);
	}
	public List<Clause> getClausesThatUnifyWithThisLiteral(Literal lit, boolean applyBindingsToResults, BindingList bindingList) {
		Collection<Literal> literals = getLiteralsContainingThisPredNameAndArity(lit.predicateName, lit.numberArgs());
		if (literals == null) { return null; }
		List<Clause> results = new ArrayList<Clause>(literals.size());
		boolean origBLisEmpty = (bindingList == null || Utils.getSizeSafely(bindingList.theta) < 1);
		for (Literal litInTheory : literals) {
			if (origBLisEmpty) {
				BindingList bl = unifier.unify(lit, litInTheory);
				if (bl != null) {
					if (applyBindingsToResults) { results.add(literalToClauseMap.get(litInTheory).applyTheta(bl.theta)); }
					else { results.add(literalToClauseMap.get(litInTheory)); } 
				}
			} else { // Need to copy because we want a fresh start for each literal (rather than a 'global' unification).
				BindingList bl = unifier.unify(lit, litInTheory, bindingList.copy());
				if (bl != null) { 
					if (applyBindingsToResults) { results.add(literalToClauseMap.get(litInTheory).applyTheta(bl.theta)); }
					else { results.add(literalToClauseMap.get(litInTheory)); }
				}	
			}
		}
		return results;
	}
	
	public Collection<Literal> getLiteralsContainingThisPredNameAndArity(PredicateName pName, int arity) {
		Map<Integer,Set<Literal>> pNameResults = pNameArityToLiteralMap.get(pName);
		if (pNameResults == null) { return null; }
		return pNameResults.get(arity);
	}
	public Collection<Literal> getLiteralsThatUnifyWithThisLiteral(Literal lit, BindingList bindingList) {
		Map<Integer,Set<Literal>> pNameResults = pNameArityToLiteralMap.get(lit.predicateName);
		if (pNameResults == null) { return null; }
		Collection<Literal> literals = pNameResults.get(lit.numberArgs());
		if (literals     == null) { return null; }
		Collection<Literal> results = new HashSet<Literal>(literals.size());
		boolean origBLisEmpty = (bindingList == null || Utils.getSizeSafely(bindingList.theta) < 1);
		for (Literal litInTheory : literals) {
			if (origBLisEmpty) {
				if (unifier.unify(lit, litInTheory)                     != null) { results.add(litInTheory); }
			} else { // Need to copy because we want a fresh start for each literal (rather than a 'global' unification).
				if (unifier.unify(lit, litInTheory, bindingList.copy()) != null) { results.add(litInTheory); }
			}
		}
		return results;
	}
	
	private void indexLiterals(Clause clause, Literal lit) {
		// Record 'reverse' pointers from literals to the clauses in which they appear.
		Map<Integer,Set<Literal>> lookup1 = pNameArityToLiteralMap.get(lit.predicateName);
		if (lookup1 == null) {
			lookup1 = new HashMap<Integer,Set<Literal>>(4);
			pNameArityToLiteralMap.put(lit.predicateName, lookup1);
		}
		Set<Literal> lookup2 = lookup1.get(lit.numberArgs());
		if (lookup2 == null) {
			lookup2 = new HashSet<Literal>(4);
			lookup1.put(lit.numberArgs(), lookup2);
		}
		lookup2.add(lit);
		literalToClauseMap.put(lit, clause);	
	}
	
	private void collectTypedConstants(PredicateName pName, List<Term> args) {
		// These might already have been collected, but play it safe.
		if (debugLevel > 2) { Utils.println("%     collectTypedConstants: " + pName + "/" + args); }
		if (!checkForNewConstants) { Utils.error("Checking for new constants, but should not happen at this stage."); }
		int numberOfArgs = Utils.getSizeSafely(args);
		if (numberOfArgs < 1) { return; }
		List<TypeSpec> typeSpecs = collectLiteralArgumentTypes(pName, numberOfArgs);
		if (debugLevel > 2) { Utils.println("%          typeSpecs(" + pName + "/" + numberOfArgs + ") = " + typeSpecs); }
		for (int i = 0; i < numberOfArgs; i++) if (args.get(i) instanceof Constant) {
			Constant c = (Constant) args.get(i);
			// See if already dealt with this constant/type pair.
			Set<Constant> lookup1 = constantTypePairsHandled.get(typeSpecs.get(i).isaType);
            if (lookup1 == null) { // Never saw this type before.
            	stringHandler.addNewConstantOfThisType(c, typeSpecs.get(i).isaType);
                lookup1 = new HashSet<Constant>(4);
                constantTypePairsHandled.put(typeSpecs.get(i).isaType, lookup1);
            }
            if (!lookup1.contains(c)) { // Save a call to the stringHandler if this constant has already been processed.
            	if (debugLevel > 1) { Utils.println("% Add constant '" + c + "' of type '" + typeSpecs.get(i).isaType + "'."); }
                stringHandler.addNewConstantOfThisType(c, typeSpecs.get(i).isaType);
                lookup1.add(c);
            }
		}
	}

	public boolean isClosedWorldAssumption(Literal lit) { // Require NULL so calling code explicitly makes sure this is a generic query.
		if (lit == null) { return closedWorldAssumption; }
		if (closedWorldAssumption) {
			return !neverCWAonThisLiteral(lit); 
		} else {
			return alwaysCWAonThisLiteral(lit); 
		}
	}
	private boolean neverCWAonThisLiteral( Literal lit) {
		if (neverCWAonThisPredNameArity != null) {
			Collection<Integer> arities = neverCWAonThisPredNameArity.get(lit.predicateName);
			if (arities == null) { return false; }
			return arities.contains(lit.numberArgs());
		}
		return false;
	}
	private boolean alwaysCWAonThisLiteral(Literal lit) {
		if (alwaysCWAonThisPredNameArity != null) {
			Collection<Integer> arities = alwaysCWAonThisPredNameArity.get(lit.predicateName);
			if (arities == null) { return false; }
			return arities.contains(lit.numberArgs());
		}
		return false;
	}
	public void setClosedWorldAssumption(boolean evidenceClosedWorldAssumption) {
		this.closedWorldAssumption = evidenceClosedWorldAssumption;
	}
	// Check for literals that need not have modes specified.  NO LONGER USED, but keep since might be needed later.
	public boolean isaBuiltInLiteral(Literal lit) { // TODO Add more here? prover.getProcedurallyDefinedPredicates()
		if (lit.predicateName == stringHandler.trueLiteral.predicateName)  { return true; }
		if (lit.predicateName == stringHandler.falseLiteral.predicateName) { return true; }
		return false;
	}
	
	public void setWorkingDirectory(String workingDirectory) {
		this.workingDirectory = workingDirectory;		
	}
	public Map<GroundLiteral,String> makeQueryLabelsCanonical(Map<GroundLiteral,String> queryLabels) {
		if (queryLabels == null) { return null; }
		Map<GroundLiteral,String> results = new HashMap<GroundLiteral,String>(queryLabels.size());
		for (GroundLiteral gLit : queryLabels.keySet()) { // TODO - can this be done in place?
			results.put(getCanonicalRepresentative(gLit), queryLabels.get(gLit));
		}
		return results;
	}

}
