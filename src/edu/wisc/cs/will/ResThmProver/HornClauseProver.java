/**
 * 
 */
package edu.wisc.cs.will.ResThmProver;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.ConsCell;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateNameAndArityFilter;
import edu.wisc.cs.will.FOPC.ProcedurallyDefinedPredicateHandler;
import edu.wisc.cs.will.FOPC.SLDQuery;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Theory;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.FOPC.UniversalSentence;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.ClosedList;
import edu.wisc.cs.will.stdAIsearch.DepthFirstSearch;
import edu.wisc.cs.will.stdAIsearch.ScoringFunction;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchMonitor;
import edu.wisc.cs.will.stdAIsearch.SearchResult;
import edu.wisc.cs.will.stdAIsearch.SearchStrategy;
import edu.wisc.cs.will.stdAIsearch.StateBasedSearchTask;

/**
 * @author shavlik
 *
 * A SLD theorem prover.  "SLD" stands for "SL resolution with Definite clauses."
 * 
 * See http://en.wikipedia.org/wiki/SLD_resolution and http://en.wikipedia.org/wiki/Horn_clause or an AI textbook.
 */
public class HornClauseProver extends StateBasedSearchTask<HornSearchNode> {
	protected static final int debugLevel = 0;  // Used to control output from this project (0 = no output, 1=some, 2=much, 3=all).
	
	protected Unifier           unifier = new Unifier();
    private   HornClauseContext context;

	protected Set<PredicateName>                predefinedPredicateNamesUsedByChildCollector; // Those in those list are handled by collectChildrenActual.
	protected HornClauseProverChildrenGenerator hornClauseProverChildrenGenerator;

    /** Indicates level of output during proof.
     *
     * The traceLevel controls the amount of output generated
     * at each step in the proof.  This is similar to the
     * debugLevel but instead prints out step by step information.
     *
     * Currently, the following levels exist:
     * 0 - silent.
     * 1 - Literal being expanded and abbreviated expansions.
     * 2 - Literal being expanded and full expansions.
     * 3 - Literal being expanded, full expansions, and all bindings (this is slow...).
     */
    private int                       traceLevel = 0;

    private PredicateNameAndArityFilter  spyEntries;
	
	/**
	 * 
     *
     * @param stringHandler
     */
	public HornClauseProver(HandleFOPCstrings stringHandler) {		
		this(stringHandler, null, null);
	}
	public HornClauseProver(HandleFOPCstrings stringHandler, Theory rules, Collection<? extends Sentence> facts) {
        this(stringHandler, new DefaultHornClausebase(stringHandler, (rules == null ? null : rules.getClauses()), facts), new DepthFirstSearch(), null);
	}
	public HornClauseProver(HandleFOPCstrings stringHandler, Theory rules, Collection<? extends Sentence> facts, SearchStrategy searchStrategy) {
		this(stringHandler, new DefaultHornClausebase(stringHandler, (rules == null ? null : rules.getClauses()), facts), searchStrategy, null);
	}
	public HornClauseProver(HandleFOPCstrings stringHandler, Theory rules, Collection<? extends Sentence> facts, SearchStrategy searchStrategy, ScoringFunction scorer) {
		this(stringHandler, new DefaultHornClausebase(stringHandler, (rules == null ? null : rules.getClauses()), facts), searchStrategy, scorer);
	}
	public HornClauseProver(HandleFOPCstrings stringHandler, Theory rules, Collection<? extends Sentence> facts, ProcedurallyDefinedPredicateHandler userProcedurallyDefinedPredicateHandler) {
		this(stringHandler, new DefaultHornClausebase(stringHandler, (rules == null ? null : rules.getClauses()), facts, userProcedurallyDefinedPredicateHandler), new DepthFirstSearch(), null);
	}
    public HornClauseProver(HandleFOPCstrings stringHandler, HornClausebase factbase) {
        this(stringHandler, factbase, new DepthFirstSearch(), null);
	}
	public HornClauseProver(HandleFOPCstrings stringHandler, HornClausebase factbase, boolean redoable) {        
        this(new DefaultHornClauseContext(factbase), new DepthFirstSearch(), null,redoable);
	}
	public HornClauseProver(HandleFOPCstrings stringHandler, HornClausebase factbase, SearchStrategy searchStrategy, ScoringFunction scorer) {
        this(new DefaultHornClauseContext(factbase), searchStrategy, scorer, false);
    }
    public HornClauseProver(HornClauseContext context) {
        this(context, false);
    }
    public HornClauseProver(HornClauseContext context, boolean redoable) {        
        this(context, new DepthFirstSearch(), null, redoable);
    }
    public HornClauseProver(HornClauseContext context, SearchStrategy searchStrategy, ScoringFunction scorer, boolean redoable) {
        this.context = context;
        taskName = "HornClauseProver";
        this.redoable = redoable;
        
        HandleFOPCstrings stringHandler = context.getStringHandler();

        spyEntries = stringHandler.getSpyEntries();
        
        predefinedPredicateNamesUsedByChildCollector = stringHandler.standardPredicateNames.buildinPredicates;
		
//		if (rules != null && !rules.isaDefiniteClauseTheory(true)) {
//			Utils.error("The Horn-Clause Theorem Prover requires all background knowledge to be definite clauses (i.e., of the form p and q => r):\n" + rules);
//		}
		InitHornProofSpace     myInitializer = new InitHornProofSpace(this);
		ProofDone              endTest       = new ProofDone(this);
		SearchMonitor          monitor       = new SearchMonitor(this); // new ProofMonitor(this); // Use this for more info.
		hornClauseProverChildrenGenerator                        = new HornClauseProverChildrenGenerator(this, context);
		ClosedList             myClosed      = null;

        maxSearchDepth     =   100000;
        setMaxNodesToConsider(1000000);
        setMaxNodesToCreate( 10000000);
        
        verbosity = 0; // Change if debugging odd behavior.
							
		initalizeStateBasedSearchTask(myInitializer, endTest, monitor, searchStrategy, scorer, hornClauseProverChildrenGenerator, myClosed);
	}

	public Clause getTheOnlyMatchingClause(Literal lit, boolean complainIfMoreThanOne) { // If complainIfMoreThanOne=false, return first match.
		if (lit == null) { return null; }
		PredicateName predName = lit.predicateName;
		int           arity    = lit.numberArgs();
		if (debugLevel > 1) { Utils.println("getMatchingClause: " + predName + "/" + arity); }
		Iterable<Clause> matchers = getClausebase().getPossibleMatchingBackgroundKnowledge(lit, null);

        Clause result = null;
		if (matchers != null) {
            int counter = 0;

            for (Clause clause : matchers) if (clause.posLiterals != null && clause.posLiterals.get(0).numberArgs() == arity) {
                if (!complainIfMoreThanOne) { return clause;   }
                if (counter < 1)            { result = clause; }
                if (counter < 2)            { counter++; }
                else { Utils.waitHere("Have at least two clauses matching: " + predName + "/" + arity + ".  Will use first match.\n  old = " + result + "\n  new = " + clause); }
            }
        } else {
        	Utils.waitHere("getTheOnlyMatchingClause: no matchers found for '" + lit + "'.");
        }
		return result;
	}

	/**
	 * Adds the given fact to this prover's knowledge base.
	 * 
	 * @param fact
	 *            The fact to add.
	 */
	public void addFact(Literal fact) {
//        if ( facts == null ) facts = new ArrayList<Sentence>();
//	    facts.add(fact); // Want a complete list here as well.  TODO - could pull out of childrenGenerator's hash table if space becomes an issue.
//	    ((HornClauseProverChildrenGenerator) childrenGenerator).addFact(fact);
        getClausebase().assertBackgroundKnowledge(fact);
	}
	
	public void addFacts(Collection<? extends Sentence> moreFacts) {
//        if ( facts == null ) facts = new ArrayList<Sentence>();
//		facts.addAll(moreFacts); // Want a complete list here as well.
//		((HornClauseProverChildrenGenerator) this.childrenGenerator).addFacts(moreFacts);
        getClausebase().assertBackgroundKnowledge(moreFacts);
	}	
	
	/**
	 * Adds the given clause to this prover's knowledge base.
	 * 
     * @param newClause
	 */
	public void addClause(Clause newClause) {
//	    if (rules == null) {
//	        List<Clause> listOfClauses = new ArrayList<Clause>(1);
//	        listOfClauses.add(newClause);
//	        rules = new Theory(listOfClauses);
//	    } else { rules.clauses.add(newClause); } // Want a complete list here as well.  TODO - could pull out of childrenGenerator's hash table if space becomes an issue.
//	    ((HornClauseProverChildrenGenerator) childrenGenerator).addClause(newClause);
        getClausebase().assertBackgroundKnowledge(newClause);
	}
	
	private PredicateName getPredicateNameFromFirstNegatedLiteral(HornSearchNode node) {
		List<Literal> queryLiterals  = node.clause.negLiterals;
		Literal       negatedLiteral = queryLiterals.get(0);
		return negatedLiteral.predicateName;
	}
	
    @Override
	public void cleanOpen() { // This is used to remove cutMarkers from the front of open.  This is only called from the read-eval-print loop, since some cutMarkers can be in an OPEN that should be empty.  Be careful calling this from elsewhere.
		if (open.isEmpty()) { return; }
		HornSearchNode node = open.popOpenList();
		while (getPredicateNameFromFirstNegatedLiteral(node) == getStringHandler().standardPredicateNames.cutMarker) {
			if (HornClauseProver.debugLevel > -2) { Utils.println("  discard this no-longer-needed cut marker: " + node); }
			if (open.isEmpty()) { return; } // The last item in open was a cutMarkerPred, so don't do another POP.
			node = open.popOpenList();
		}
		open.addToFrontOfOpenList(node); // Need to return the last item popped.
	}

    protected void initialize(List<Literal> negatedConjunctiveQuery ) {
        ((InitHornProofSpace) initializer).loadNegatedConjunctiveQuery(negatedConjunctiveQuery, open);
    }

    protected void initialize(SLDQuery query) throws IllegalArgumentException {
        initialize(query.getNegatedQueryClause().negLiterals);
    }

    public BindingList prove(SLDQuery query) throws IllegalArgumentException, SearchInterrupted {
        BindingList result = null;

        initialize(query);
        SearchResult sr = performSearch();

        if ( sr.goalFound() ) {
            result = new BindingList(((ProofDone) terminator).collectQueryBindings());
        }

        return result;
    }
    

    // Note: the string can only be a CONJUNCTION of literals (or just one literal).
	public int countProofs(FileParser parser, String string) {
		if (string == null) { return 0; }
		int count = 0;
		Variable       var       = parser.stringHandler.getExternalVariable("countProofsCounter");
		List<Sentence> sentences = parser.parse("countProofs((" + string + "), " + var + ").");
		for (Sentence s : sentences) {
			//Utils.println("countProofs: s = " + s);
			List<Clause> clauses = s.convertToClausalForm();
			for (Clause c : clauses) {
			//	Utils.println("countProofs:    c = " + c);
				try {
					BindingList bl = proveSimpleQueryAndReturnBindings(c.getPosLiteral(0)); // Should only be the countProofs literal.
					Variable  var2 = (Variable) (c.getPosLiteral(0).getArgument(1));  // A bit hacked up that exploits what we know we provided.
			//		Utils.println("bl = " + bl);
					Term lookup = bl.lookup(var2);
			//		Utils.println("lookup = " + lookup);
					if (lookup instanceof NumericConstant) {
						NumericConstant nc = (NumericConstant) lookup;
						
						count += nc.value.intValue();
					}
				} catch (SearchInterrupted e) {
					Utils.reportStackTrace(e);
					Utils.error();
				}
			}
		}
		if (debugLevel > -1) { Utils.println("% There are " + Utils.comma(count) + " proofs of: " + string + ".\n"); }
		return count;
	}
	
	// TODO Clean up the names of these functions.
	public boolean proveSimpleQuery(Literal negatedFact) throws SearchInterrupted {
		((InitHornProofSpace) initializer).loadNegatedSimpleQuery(negatedFact, open);
		return performSearch().goalFound();
	}

	public BindingList proveSimpleQueryAndReturnBindings(Literal negatedFact) throws SearchInterrupted {

		if (proveSimpleQuery(negatedFact)) {
		//	Utils.waitHere("proveSimpleQuery=true  " + ((ProofDone) terminator).collectQueryBindings());
			return new BindingList(((ProofDone) terminator).collectQueryBindings());
		}
	//	Utils.waitHere("proveSimpleQuery=false");
		return null;
	}
	
	private int maxWarningsForMaxNodes     = 100;
	private int countOfWarningsForMaxNodes =   0;
	public boolean proveConjunctiveQuery(List<Literal> negatedConjunctiveQuery) throws SearchInterrupted {
		if (negatedConjunctiveQuery == null) { return false; } // No way to make the empty query true.
		if (Utils.getSizeSafely(negatedConjunctiveQuery) == 1) { return proveSimpleQuery(negatedConjunctiveQuery.get(0)); }
		((InitHornProofSpace) initializer).loadNegatedConjunctiveQuery(negatedConjunctiveQuery, open);

        SearchResult result = performSearch();
        if ( result  == SearchMonitor.maxNodesConsideredReached && countOfWarningsForMaxNodes++ < maxWarningsForMaxNodes ) {
            Utils.warning( "#" + Utils.comma(countOfWarningsForMaxNodes) + " MaxNodesConsidered reached while proving:\n  " + negatedConjunctiveQuery + ".");
        }

		return result.goalFound();
	}

	public BindingList proveConjunctiveQueryAndReturnBindings(List<Literal> negatedConjunctiveQuery) throws SearchInterrupted {
		if (proveConjunctiveQuery(negatedConjunctiveQuery)) {
			return new BindingList(((ProofDone) terminator).collectQueryBindings());
		}
		return null;
	}
	
	public BindingList query(FileParser parser, String sentencesAsString) throws SearchInterrupted {
		char lastChar = sentencesAsString.charAt(sentencesAsString.length() - 1);
		
		// Add a terminating period if one isn't there.  Should be safe even if no final period is needed - though add the extra space in case the final item is an integer (alternatively, could use ';'). 
		if (lastChar != '.' && lastChar != ';') { sentencesAsString += " ."; }
		List<Sentence> sentences = parser.readFOPCstream(sentencesAsString);
		if (sentences.size() == 1) { return query(sentences.get(0)); }
		Utils.error("Queries must be conjunctive.  You provided: " + sentencesAsString); return null;
	}
	public BindingList query(Sentence sentence) throws SearchInterrupted {
		List<Literal> negLiterals = convertSentenceToConjunctiveQuery(sentence, getStringHandler(), null);
		
		if (negLiterals.size() == 1) { return proveSimpleQueryAndReturnBindings((negLiterals.get(0))); }
		return proveConjunctiveQueryAndReturnBindings(negLiterals);
	}
	
	public List<Term> getAllUniqueGroundings(Literal query, FileParser parser) throws SearchInterrupted {
		Function   queryAsFunction = query.convertToFunction(getStringHandler());
		Variable   var             = getStringHandler().getNewUnamedVariable();
		List<Term> findAllArgList  = new ArrayList<Term>(3);
		findAllArgList.add(queryAsFunction);
		Clause clause = getStringHandler().getClause(query, false);
		findAllArgList.add(getStringHandler().getSentenceAsTerm(clause, "getAllUniqueGroundings"));
		findAllArgList.add(var);
		Literal allRaw = getStringHandler().getLiteral(getStringHandler().standardPredicateNames.all, findAllArgList);
	//	List<Sentence> sentences = parser.readFOPCstream(allRaw.toString() + ".");  JWS: CANT DO THIS SINCE THIS WILL RENAME var AND THEN THE LOOKUP WILL FAIL.
	//	if (debugLevel > -1) { Utils.println("\n% allRaw = " + allRaw + "\n% sentences = " + sentences); }
	//	if (Utils.getSizeSafely(sentences) != 1) { Utils.error("Should only have ONE sentence here: " + sentences); }
		BindingList  bl = proveSimpleQueryAndReturnBindings(allRaw); // query(sentences.get(0));
		if (bl == null) { return null; }
		ConsCell allResults = (ConsCell) bl.lookup(var);
		if (debugLevel > 1) { Utils.println("% Have found " + Utils.comma(allResults == null ? 0 : allResults.length()) + " unique groundings of '" + query + "'.\n"); } // % var = " + var + " bl=" + bl); }
		if (allResults == null) { return null; }
		return allResults.convertConsCellToList();
	}
		
	private List<Literal> convertSentenceToConjunctiveQuery(Sentence sentence, HandleFOPCstrings stringHandler, BufferedReader br) {
		// Need to negate the query since we're doing proofs by negation.
		List<Clause> clauses = sentence.convertForProofByNegation();
	
		if (clauses == null)     { Utils.error("Cannot convert '" + sentence + "' to a negated conjuntive query for use in resolution theorem proving."); }
		if (clauses.size() != 1) { Utils.error("Should only get ONE clause from '" + sentence + "' but got: " + clauses); }
		List<Literal> negLiterals = convertSentenceToListOfNegativeLiterals(sentence);
		if (br != null) { // If a buffered reader is provided, we need a collector of the answers to show to the user.
			Literal collector;
			Collection<Variable> queryVariables   = clauses.get(0).collectFreeVariables(null);
			List<Term>           queryVarsAsTerms = (queryVariables == null ? null : new ArrayList<Term>(queryVariables.size()));
			if (queryVariables != null) for (Variable v : queryVariables) { queryVarsAsTerms.add(v); }
			PredicateName  pName          = getStringHandler().getPredicateName("readEvalPrintCollector");
			List<Term> args = new ArrayList<Term>(4);
			args.add(getStringHandler().getListAsTerm(queryVarsAsTerms)); // Keep two copies of the arguments, one will remain untouched and the other will be modified as variables are bound.
			args.add(getStringHandler().getListAsTerm(queryVarsAsTerms, false)); // Don't bind these variables.
			args.add(getStringHandler().getObjectAsTerm(br));
			args.add(getStringHandler().getObjectAsTerm(this));
			collector = getStringHandler().getLiteral(  pName, args);
		
			negLiterals.add(collector);
		}
		return negLiterals;
	}
	
	public void theoremProverReadEvalPrintLoop(FileParser parser) {
		theoremProverReadEvalPrintLoop(parser, null);
	}
	public void theoremProverReadEvalPrintLoop(FileParser parser, String queryFile) {		
		BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
		String         line = "readingFromQueryFile"; 
		List<Sentence> sentencesToProcess = null;
		if (queryFile != null) {
			sentencesToProcess = parser.readFOPCfile(queryFile);
			if (sentencesToProcess != null) { Utils.println("Read " + sentencesToProcess.size() + " queries from " + queryFile + ".  Will process them one-by-one."); }
		}
		try {
			Utils.print("\nEntering the read-eval-print-loop for the resolution theorem prover.\n ?- ");
			Utils.flush();
			while ((sentencesToProcess != null && sentencesToProcess.size() > 0) || (line = br.readLine()) != null) {
				if (line.equalsIgnoreCase("done") || line.equalsIgnoreCase("done;") || line.equalsIgnoreCase("done.") ||
					line.equalsIgnoreCase("quit") || line.equalsIgnoreCase("quit;") || line.equalsIgnoreCase("quit.") ||
					line.equalsIgnoreCase("exit") || line.equalsIgnoreCase("exit;") || line.equalsIgnoreCase("exit.") ||
					line.equalsIgnoreCase("halt") || line.equalsIgnoreCase("halt;") || line.equalsIgnoreCase("halt.")) {
					Utils.println("\nDone with the read-eval-print-loop.");
					return;
				}
				Sentence nextSentence  = null;
				if (sentencesToProcess != null && sentencesToProcess.size() > 0) {
					nextSentence = sentencesToProcess.remove(0); // This also returns the element removed.
					if (nextSentence instanceof UniversalSentence) { nextSentence = ((UniversalSentence) nextSentence).body; } // If a ForAll was added, drop it.
					Utils.println(nextSentence + " [read from " + queryFile + "]");
				}
				if (nextSentence == null) { 
					sentencesToProcess = parser.readFOPCreader(new StringReader(line), null); // Fine no directory here since processing a string.
					if (sentencesToProcess != null && sentencesToProcess.size() > 0) {
						nextSentence  = sentencesToProcess.remove(0);
					}
				}
				
				if (nextSentence == null) {  } // Allow the user to simply hit <return>.
				else
				{   List<Literal> negLiterals = convertSentenceToConjunctiveQuery(nextSentence, getStringHandler(), br);
					try {
						proveConjunctiveQuery(negLiterals);
						Utils.println("    No answers found.");
					}
					catch (SearchInterrupted e) {
						// User did not want any more answers, which is fine.  Simply catch and continue.
					}
				}
				Utils.print(" ?- ");
				Utils.flush();
			}
		} 
		catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Something apparently went wrong trying to read input from the user.  Error message: " + e.getMessage());
		}
	}
	
	private List<Literal> convertSentenceToListOfNegativeLiterals(Sentence sentence) {
		// Need to negate the query since we're doing proofs by negation.
		List<Clause> clauses = sentence.convertForProofByNegation();

		if (clauses == null)     { Utils.error("Cannot convert '" + sentence + "' to a negated conjuntive query for use in resolution theorem proving."); }
		if (clauses.size() != 1) { Utils.error("Should only get ONE clause from '" + sentence + "' but got: " + clauses); }
		Clause clause = clauses.get(0);
		List<Literal> posLiterals = clause.posLiterals;
		List<Literal> negLiterals = clause.negLiterals;
	
		if (posLiterals != null && posLiterals.size() > 0) {
			Utils.println(" Can only handle conjunctive queries where all the literals are unnegated. Please try again.");
		}
		return negLiterals;
	}

	// Allow direct use of the procedurally defined stuff.
	public boolean isProcedurallyDefined(PredicateName pName, int arity) {
        if ( getClausebase().getBuiltinProcedurallyDefinedPredicateHandler() != null && getClausebase().getBuiltinProcedurallyDefinedPredicateHandler().canHandle(pName,arity) ) return true;
        if ( getClausebase().getUserProcedurallyDefinedPredicateHandler() != null && getClausebase().getUserProcedurallyDefinedPredicateHandler().canHandle(pName,arity)) return true;
        return false;


    }
	public BindingList evaluateProcedurallyDefined(Literal lit) {
		if (lit == null) { return null; }
		return evaluateProcedurallyDefined(lit, new BindingList());
	}

	public BindingList evaluateProcedurallyDefined(Literal lit, BindingList bl) {
		if (lit == null) { return null; }
		BindingList result = null;
		try {
            ProcedurallyDefinedPredicateHandler handler = null;
            if ( (handler = getClausebase().getBuiltinProcedurallyDefinedPredicateHandler()) != null && handler.canHandle(lit.predicateName, lit.numberArgs()) ) {
                result = handler.handle(context,lit, unifier, bl);
            }
            else if ( (handler = getClausebase().getUserProcedurallyDefinedPredicateHandler()) != null && handler.canHandle(lit.predicateName, lit.numberArgs()) ) {
                result = handler.handle(context,lit, unifier, bl);
            }
		} catch (SearchInterrupted e) {
			Utils.reportStackTrace(e);
			Utils.error("Something when wrong with evaluateProcedurallyDefined(" + lit + ").");
		}
		return result;
	}
	
	/**
	 * @param args
	 * 
	 * This main shows how to use the Horn-clause theorem prover.  It also supports debugging.
	 * @throws SearchInterrupted 
	 * 
	 */
	public static void main(String[] args) throws SearchInterrupted {
		args = Utils.chopCommentFromArgs(args);
		
		if (args.length < 2) { Utils.error("Need at least two arguments to this test (e.g., background queries)."); }	

		Utils.createDribbleFile();
		HandleFOPCstrings stringHandler = new HandleFOPCstrings();
		FileParser        parser        = new FileParser(stringHandler);
		List<Sentence>    sentences     = parser.readFOPCfile(args[0]);
		List<Sentence>    rawRules      = new ArrayList<Sentence>(1);
		List<Sentence>    facts         = new ArrayList<Sentence>(1);
		
		for (Sentence s : sentences) {
			if (s instanceof Literal) { facts.add(s); } else { rawRules.add(s); }
		}
		Theory rules = new Theory(stringHandler, rawRules);

		if (HornClauseProver.debugLevel > 0) { Utils.println("\n" + rules); }	
				
		// Create the search space.
		HornClauseProver task = new HornClauseProver(stringHandler, rules, facts);
		//task.verbosity = 1;
		Utils.println("\nHave successfully read in the background knowledge.\n\n" + rules + "\n\nFacts:");
		if (Utils.getSizeSafely(facts) > 0) for (Sentence fact : facts) { Utils.println(" " + fact + "."); }
		
		//BindingList bl = task.query(parser, "countProofs(Q(X) and W(X, Y), Count)");
		//Utils.println("\n Binding list = " + bl);
		
		task.theoremProverReadEvalPrintLoop(parser, args[1]); // Allow the first query to be in a file (for easier debugging).
		Utils.println("\nDone with main in HornClauseProver.\n");
		
	}

    /**
     * @return the factbase
     */
    public HornClausebase getClausebase() {
        return context.getClausebase();
    }

    public HandleFOPCstrings getStringHandler() {
        return context.getStringHandler();
    }

    public PredicateNameAndArityFilter getSpyEntries() {
        return spyEntries;
    }

    public int getTraceLevel() {
        return traceLevel;
    }

    public void setSpyEntries(PredicateNameAndArityFilter spyEntries) {
        this.spyEntries = spyEntries;
    }

    public void setTraceLevel(int traceLevel) {
        this.traceLevel = traceLevel;
    }


}
