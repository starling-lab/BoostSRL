package edu.wisc.cs.will.FOPC;

import java.io.IOException;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.ILP.ChildrenClausesGenerator;
import edu.wisc.cs.will.ILP.InlineManager;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.Utils.MapOfLists;
import edu.wisc.cs.will.Utils.Utils;
import java.io.File;
/**
 * @author shavlik
 *
 * A 'theory' is a collection of first-order predicate calculus sentences, represented (for us) in clausal form.
 * 
 */
@SuppressWarnings("serial")
public class Theory extends AllOfFOPC implements Serializable, Iterable<Sentence> {
	private static final int debugLevel = 0;

	public  boolean reportUnsimplifiedClauses = true;
	
	private InlineManager              inlineHandler       = null;
	public InlineManager getInlineHandler() {
		return inlineHandler;
	}
	public void setInlineHandler(InlineManager inlineHandler) {
		this.inlineHandler = inlineHandler;
	}

	private boolean                    negated             = false; // Is this really the 'negated' version of what we want?  (Might happen because we flip-flopped the positive and negative training examples.)
	private boolean                    cannotNegateEasily  = false;
	private List<Clause>               clauses;
	private List<Clause>               supportClauses;  // These clauses are needed to support evaluation of the theory.  Let's keep these in a list, in case the order matters.
	private Collection<Sentence>       sentences;       // The original sentences.  Note: one sentence can become many clauses, so not a one-to-one match (could do so if needed).
	private List<Clause>               originalClauses; // Before dealing with IN-LINES.
	private List<Clause>               unsimplifiedClauses        = null; // Before simplification is called.
	private List<Clause>               unsimplifiedSupportClauses = null;
	private boolean                    somethingSimplified        = false; // See if the simplified version is different.	
	
	transient public HandleFOPCstrings stringHandler;

	private PredicateName sameAsPname;
	private PredicateName sameAsPnameIL;
	private PredicateName differentPname;
	private PredicateName differentPnameIL;
	private PredicateName numberPname;
	private PredicateName interNumbPname;
	private PredicateName interSymPname;
	private PredicateName interListPname;
	private PredicateName interCompoPname;
	private PredicateName diff_interNumbPname;
	private PredicateName diff_interSymPname;
	private PredicateName diff_interListPname;
	private PredicateName diff_interCompoPname;
	private PredicateName notPname;
	private FunctionName  notFname;

    private PrettyPrinterOptions prettyPrinterOptions = null;
	
	public Theory(HandleFOPCstrings stringHandler) {
		this.clauses              = null;
		this.stringHandler        = stringHandler;
		collectNeededNames();
	}
	public Theory(HandleFOPCstrings stringHandler, boolean negated) {
		this(stringHandler);
		this.negated = negated;
	}
	public Theory(HandleFOPCstrings stringHandler, Collection<? extends Sentence> standardSentences) {
		this(stringHandler, standardSentences, null);
	}
	public Theory(HandleFOPCstrings stringHandler, Collection<? extends Sentence> standardSentences, InlineManager inlineHandler) {
		this(stringHandler);
		this.inlineHandler = inlineHandler;
		if (standardSentences == null) { sentences = null;  clauses = null; }
		else { addTheseSentences(standardSentences, inlineHandler);	}
		
		originalClauses = clauses;
	}
    public Theory(HandleFOPCstrings stringHandler, List<Clause> clauses, boolean negated) { // This boolean mainly added so this constructor is different than the one below.
		this.stringHandler = stringHandler;
        sentences    = null;
	//	this.clauses = clauses;
		addAllMainClauses(clauses, null);
		this.negated = negated;
		collectNeededNames();
	}
    public Theory(HornClauseContext context) {
        this(context.getStringHandler());
    }
    
    public Theory(HandleFOPCstrings stringHandler, List<Theory> theories) { // TODO - need to merge stringHandlers ...
        this.stringHandler = stringHandler;
    	if (theories == null) { Utils.waitHere("Should not call with an empty list."); return; }
//        for (Theory theory : theories) {
//            if ( theory.stringHandler != this.stringHandler) throw new IllegalArgumentException("All theories combined into a single theory must use the same string handler.");
//        }
		collectNeededNames();
    	sentences                  = new ArrayList<Sentence>(4);
    	clauses                    = new ArrayList<Clause>(4);
    	supportClauses             = new ArrayList<Clause>(4);
    	originalClauses            = new ArrayList<Clause>(4);
    	unsimplifiedClauses        = new ArrayList<Clause>(4);
    	unsimplifiedSupportClauses = new ArrayList<Clause>(4); 	
    	stringHandler              = theories.get(0).stringHandler;
    	negated                    = false; // Don't allow combined theories to be negated (what if ALL are negated?  Still ok unless some cannot be negated ...).
    	reportUnsimplifiedClauses  = theories.get(0).reportUnsimplifiedClauses;
    	somethingSimplified        = theories.get(0).isSomethingSimplified();
    	theoryFlipFlopped          = false;
    	if (theories.get(0).isNegated() && !theories.get(0).theoryFlipFlopped) {
    		rewriteFlipFloppedTheory();
    		if (cannotNegateEasily) { Utils.waitHere("Have a negated theory but cannot flip-flop it."); }
    	}
    	cannotNegateEasily         = theories.get(0).cannotNegateEasily();
    	
    	for (Theory t : theories) {
    		if (t.sentences                  != null) { sentences.addAll(                 reparseSentences(t.sentences)); }
    		if (t.clauses                    != null) { clauses.addAll(                   reparseClauses(  t.clauses));   }
    		if (t.supportClauses             != null) { supportClauses.addAll(            reparseClauses(  t.supportClauses));  }
    		if (t.originalClauses            != null) { originalClauses.addAll(           reparseClauses(  t.originalClauses)); }
    		if (t.unsimplifiedClauses        != null) { unsimplifiedClauses.addAll(       reparseClauses(  t.unsimplifiedClauses));        }
    		if (t.unsimplifiedSupportClauses != null) { unsimplifiedSupportClauses.addAll(reparseClauses(  t.unsimplifiedSupportClauses)); }
    	//	if (stringHandler             != t.stringHandler) {
    	//		Utils.waitHere("merge theories: mismatching string handlers.");
    	//	} // NOTE: if it matters, reparse each theory with the original or a completely new stringHandler.
    		if (t.negated && !t.theoryFlipFlopped) {
        		t.rewriteFlipFloppedTheory();
        		if (t.cannotNegateEasily) { Utils.waitHere("Have a negated theory but cannot flip-flop it."); }
        	}
    		reportUnsimplifiedClauses = (reportUnsimplifiedClauses || t.reportUnsimplifiedClauses);
    		somethingSimplified       = (somethingSimplified       || t.somethingSimplified);
    	}
	}
    
    private void collectNeededNames() {
    	sameAsPname      = stringHandler.getPredicateName("sameAs");
    	sameAsPnameIL    = stringHandler.getPredicateName("sameAsIL"); // NOTE: this is some leakage of the BL project into WILL.
    	differentPname   = stringHandler.getPredicateName("different");
    	differentPnameIL = stringHandler.getPredicateName("differentIL"); // NOTE: this is some leakage of the BL project into WILL.
    	numberPname      = stringHandler.standardPredicateNames.number;
    	interNumbPname   = stringHandler.getPredicateName("isaInterestingNumber");
    	interSymPname    = stringHandler.getPredicateName("isaInterestingSymbol");
    	interListPname   = stringHandler.getPredicateName("isaInterestingList");
    	interCompoPname  = stringHandler.getPredicateName("isaInterestingComposite"); // NOTE: this is some leakage of the BL project into WILL.
    	diff_interNumbPname  = stringHandler.getPredicateName("isaDifferentInterestingNumber");
    	diff_interSymPname   = stringHandler.getPredicateName("isaDifferentInterestingSymbol");
    	diff_interListPname  = stringHandler.getPredicateName("isaDifferentInterestingList");
    	diff_interCompoPname = stringHandler.getPredicateName("isaDifferentInterestingComposite"); // NOTE: this is some leakage of the BL project into WILL.
    	notPname             = stringHandler.standardPredicateNames.negationByFailure;
    	notFname             = stringHandler.standardPredicateNames.negationByFailureAsFunction;
    }

    // Fix this code if/when needed ...  TODO
    private Collection<Sentence> reparseSentences(Collection<Sentence> sentences) {
    	if (sentences == null) { return null; }
    	return sentences;
    	/*
    	FileParser parser = stringHandler.get();
    	List<Sentence> results = new ArrayList<Sentence>(sentences.size());
    	for (Sentence s : clsentencesauses) {
    		results.addAll(parser.xxx(s.toString()));
    	}
    	return results;
    	*/
    }    
    // Does the parser work for Clauses?
    private List<Clause> reparseClauses(List<Clause> clauses) {
    	if (clauses == null) { return null; }
    	return clauses;
    	/*
    	FileParser parser = stringHandler.get();
    	List<Clause> results = new ArrayList<Clause>(clauses.size());
    	for (Clause c : clauses) {
    		results.addAll(parser.xxx(c.toString())
    	}
    	return results;
    	*/
    }    
    private Set<Clause> reparseClauses(Set<Clause> clauses) {
    	if (clauses == null) { return null; }
    	return clauses;
    	/*
    	FileParser parser = stringHandler.get();
    	Set<Clause> results = new HashSet<Clause>(clauses.size());
    	for (Clause c : clauses) {
    		results.addAll(parser..xxx(c.toString())
    	}
    	return results;
    	*/
    }
    
    public boolean isEmpty() {
    	return Utils.getSizeSafely(clauses) < 1;
    }
    
    // This assumes any desired inlining etc. has already been done.
	public Theory simplify() {
		collectAnyRemainingInliners();  // if (Utils.getSizeSafely(clauses) > 0) Utils.waitHere("check collectAnyRemainingInliners printouts above, if any");
    	if (unsimplifiedClauses != null) { Utils.warning("Have already simplified the clauses.");  return this; }
    	unsimplifiedClauses        = clauses;
    	unsimplifiedSupportClauses = supportClauses;
    	clauses        = simplify(unsimplifiedClauses);
    	supportClauses = simplify(unsimplifiedSupportClauses);
    	return this;
    }
    
	private List<Variable> newNegListVars = null;
    private List<Clause> simplify(List<Clause> theseClauses) {
    	if (theseClauses == null) { return null; }
    	List<Clause> results = new ArrayList<Clause>(4);
    	somethingSimplified  = false;
    	newNegListVars       = null; // I am not sure why this is outside the clause FOR loop, but that is the way it was when simplifyListOfLiterals's code was pulled out (to allow recursion), and so I left it that way (7/30/10).
    	for (Clause cRaw : theseClauses) {
    		Clause c = useDeterminateLiteralsToUnifyVariables(cRaw);

			if (debugLevel > 1) { Utils.println("\n% SIMPLIFY\n% " + c.toPrettyString("%  ", Integer.MAX_VALUE)); }
    		List<Literal> newNegLits = simplifyListOfLiterals(c.negLiterals);

			Clause newC = stringHandler.getClause(c.posLiterals, newNegLits, c.getExtraLabel());
    		results.add(newC);
    	}
    //	Utils.waitHere();
    	return results;
    }
    
    // It is possible some in-liners are still in a theory (eg, due to some bug).
    // So if a theory is to 'stand alone' in a new task, we need to keep the definitions of these in-liners.
    private boolean haveCollectedRemainingInLiners = false;
    private Set<Clause> collectedSupporters = new HashSet<Clause>(4);
    public void collectAnyRemainingInliners() {
    	if (haveCollectedRemainingInLiners) { return; }
    	collectedSupporters.clear();
    	help_collectAnyRemainingInliners(clauses,        1);
    	help_collectAnyRemainingInliners(supportClauses, 1);
    	if (!collectedSupporters.isEmpty()) {
    		supportClauses.addAll(collectedSupporters);
    	   	collectedSupporters.clear();
    	}
    	haveCollectedRemainingInLiners = true;    	
    }
    
    private void help_collectAnyRemainingInliners(List<Clause> theseClauses, int depth) {
    	if (theseClauses == null) { return; }
    	if (depth > 20) { for (Clause cRaw : theseClauses) { Utils.println("help_collectAnyRemainingInliners: " + cRaw); } Utils.error("depth = " + depth); }
    	for (Clause cRaw : theseClauses) {
    	//	Utils.println("%  help_collectAnyRemainingInliners(clause): " + cRaw);
    		if (cRaw.negLiterals != null) for (Literal lit : cRaw.negLiterals) { help_collectAnyRemainingInliners(lit, depth + 1); }
    	}
    }
    
    private void help_collectAnyRemainingInliners(Clause cRaw, int depth) {
    	if (cRaw == null) { return; }
    	if (depth > 20) { Utils.error("cRaw = " + cRaw + " depth = " + depth); }
    	if (cRaw.negLiterals != null) for (Literal lit : cRaw.negLiterals) { help_collectAnyRemainingInliners(lit, depth + 1); }
    }
    	
    private void help_collectAnyRemainingInliners(Literal lit, int depth) {
		PredicateName pName = lit.predicateName;
		if (depth > 20) {  Utils.error("help_collectAnyRemainingInliners: lit = '" + lit + "' depth = " + depth); }

	//	Utils.println("%  help_collectAnyRemainingInliners(lit): " + lit);    	

		if (pName.isaInlined(lit.getArity()) && inlineHandler == null)  { 
			Utils.warning("An in-line handler should have been associated with this theory ...  Needed for: " + lit);
		}  
		
		if (pName.isaInlined(lit.getArity()) && inlineHandler != null) {
			  				
			Iterable<Clause> definingClauses = inlineHandler.getHornClauseKnowledgeBase().getPossibleMatchingBackgroundKnowledge(lit, new BindingList());
			
			// ACTUALLY I THINK IT IS OK TO HAVE ANY NUMBER, SINCE WE'RE KEEPING THEM ALL:	if (Utils.getSizeSafely(definingClauses) != 1) { Utils.error("Expected ONE definition of: " + lit + ",\nbut got " + Utils.getSizeSafely(definingClauses) + "\n  " + definingClauses); }
			if (definingClauses != null) for (Clause inlinedDefn : definingClauses) { 
			
				List<Clause> inlinedDefnInList = new ArrayList<Clause>(1);
				inlinedDefnInList.add(inlinedDefn);
				// TODO this recursive step needs to be cleaned up.  Eg, here might not need to make a support clause but could inline the body.
				help_collectAnyRemainingInliners(inlinedDefnInList, depth + 1); // Need to make sure the inliner's body contains nothing that needs to be in-lined.
				Utils.println("%  Theory.help_collectAnyRemainingInliners(lit): add this clause" + inlinedDefn); 
				collectedSupporters.add(inlinedDefn);
			}
		}
		if (lit.getArity() > 0) for (Term term : lit.getArguments()) { help_collectAnyRemainingInliners(term, depth + 1); }
    }
    
    private void help_collectAnyRemainingInliners(Term term, int depth) {
		if (depth > 20) {  Utils.error("help_collectAnyRemainingInliners: term = '" + term + "' depth = " + depth); }
		
	//	Utils.println("%  help_collectAnyRemainingInliners(term): " + term);
    	if (term instanceof LiteralAsTerm) {
    		LiteralAsTerm lat = (LiteralAsTerm) term;
    		help_collectAnyRemainingInliners(lat.itemBeingWrapped, depth + 1);    		
    	} else if (term instanceof SentenceAsTerm) {
    		SentenceAsTerm sat = (SentenceAsTerm) term;
    		help_collectAnyRemainingInliners(sat.asClause(), depth);    		
    	} else if (term instanceof ListAsTerm) {
    		ListAsTerm lat = (ListAsTerm) term;
    		List<Term> terms = lat.objects;
    		for (Term latTerm : terms) { help_collectAnyRemainingInliners(latTerm, depth + 1); }    		
    	} else if (term instanceof ObjectAsTerm) {
    		ObjectAsTerm oat = (ObjectAsTerm) term;
    		Utils.waitHere("ObjectAsTerm? " + oat);    	// Probably OK to simply NOT recur into this.	
    	} else if (term instanceof Function) {
    		Function f = (Function) term;
    		help_collectAnyRemainingInliners(f.convertToLiteral(stringHandler), depth + 1);
    	
    		if (f.getArity() > 0) for (Term termInner : f.getArguments()) { help_collectAnyRemainingInliners(termInner, depth + 1); }
    	}
    }
    
    private List<Literal> simplifyListOfLiterals(List<Literal> inputList) {
    	if (inputList == null) { return null; }
		List<Literal> newNegLits     = new ArrayList<Literal>(inputList.size());
    	List<Literal> newNegLitsHold = null;
		for (Literal nLit : inputList) {
			boolean saveIt = true;

			//if (debugLevel > 1) { Utils.println("\n% CONSIDER: " + nLit); }			
			//Utils.println("    nLit.predicateName=" + nLit.predicateName + " notPname=" + notPname + "  nLit.numberArgs()=" + nLit.numberArgs());
			
			if (nLit.predicateName == notPname && nLit.numberArgs() == 1) { // See if we have not(not(something)) and convert to 'something'.
				Term arg = nLit.getArgument(0);
				
			//	Utils.waitHere("  have an arg to a negation-by-failure: " + arg);				
				if (arg instanceof Function) {
					Function f = (Function) arg;
			//		Utils.waitHere("  have a function in a negation-by-failure: " + f);
					if (f.functionName == notFname) {
						if (f.numberArgs() != 1) { Utils.writeMe("Have a double negation: '" + f + "'  but with more than one argument.");  }
						Term argNotNot = f.getArgument(0);
						if (argNotNot instanceof SentenceAsTerm) {
							SentenceAsTerm satNotNot = (SentenceAsTerm) argNotNot;
							List<Clause> clausesNotNot    = satNotNot.sentence.convertToClausalForm();
							List<Clause> simplifiedNotNot = simplify(clausesNotNot);
							if (simplifiedNotNot != null) for (Clause cNotNot : simplifiedNotNot) {
								if (Utils.getSizeSafely(cNotNot.posLiterals) == 0 && cNotNot.negLiterals != null) {
									newNegLits.addAll(cNotNot.negLiterals);
									saveIt = false; continue;
								}
								Utils.waitHere("Have a double negation: '" + f + "'  that needs to be handled.");
								// Could just let it go?
							}
						} else if (argNotNot instanceof Function) {
							Literal lit =  ((Function) argNotNot).convertToLiteral(stringHandler);
							newNegLits.add(lit);
							continue;
						} else {
							Utils.waitHere("Have a double negation: '" + f + "'  that needs to be handled."); // Do we need to handle other types of XYZasTerm?
							// Could just let it go?
						}
					}
				}
			}
			
			if (canPrune(nLit, newNegLits)) {
				if (debugLevel > 1) { Utils.println("% CAN PRUNE: " + nLit); }
				saveIt = false; continue; // Don't really need to set saveIt, but do so in case we later drop the 'break'.
			}
			
			if (nLit.predicateName == numberPname && nLit.numberArgs() == 1 && nLit.getArgument(0) instanceof NumericConstant) {
				if (debugLevel > 1) { Utils.println("% DISCARD number(#): " + nLit); }
				saveIt = false; continue; // Don't really need to set saveIt, but do so in case we later drop the 'break'.
			}
			
			// These are only used at learning time to introduce some constants into the hypothesis space.
			if (nLit.numberArgs() == 1 && (nLit.predicateName == interNumbPname || nLit.predicateName == interSymPname || nLit.predicateName == interListPname || nLit.predicateName == interCompoPname)) {
				if (debugLevel > 1) { Utils.println("% DISCARD isaInteresting(#): " + nLit); }
				saveIt = false; continue; // Don't really need to set saveIt, but do so in case we later drop the 'break'.
			}
			
			// For the binary case, we need to use a sameAs/2.  We don't want to replace, at least for numbers, since we want to support partial matches.
			if (nLit.numberArgs() == 2 && (nLit.predicateName == interNumbPname || nLit.predicateName == interSymPname || nLit.predicateName == interListPname || nLit.predicateName == interCompoPname)) {
				if (debugLevel > 1) { Utils.println("% Rename this isaInteresting/2 to use sameAs: " + nLit); }
				saveIt = false;
				Literal nLitSameAs = nLit.copy(false);
				nLitSameAs.predicateName = (nLit.predicateName == interCompoPname ? sameAsPnameIL : sameAsPname);
				newNegLits.add(nLitSameAs);
				continue;
			}
			
			// Different's need to be treated in a more complicated manner, since we cannot bind a variable with them (whereas in sameAs/2 we can).
			if (nLit.numberArgs() == 2 && (nLit.predicateName == diff_interNumbPname || nLit.predicateName == diff_interSymPname || nLit.predicateName == diff_interListPname || nLit.predicateName == diff_interCompoPname)) {
				if (debugLevel > 1) { Utils.println("% Rename this isaDifferentInteresting/2 to use different: " + nLit); }
				saveIt = false;
				Literal nLitDifferent = nLit.copy(false);
				nLitDifferent.predicateName = (nLit.predicateName == diff_interCompoPname ? differentPnameIL : differentPname);
				Term arg2 = nLit.getArgument(1); // NOTE: this code assumes the creators of these put the variable in the second argument.  TODO make more robust.
				if (arg2 instanceof Variable) {
					if (newNegLitsHold == null) {
						newNegLitsHold = new ArrayList<Literal>( 1); 
						newNegListVars = new ArrayList<Variable>(1);
					}
					newNegLitsHold.add(nLitDifferent);
					newNegListVars.add((Variable) arg2); // The clause has to FIRST bind this variable before different/2 can be called.
				}
				continue;
			}
			
			if (saveIt) for (Literal savedLit : newNegLits) {
				if (savedLit.equals(nLit, false)) {
					if (debugLevel > 1) { Utils.println("% DUPLICATES: '" + nLit + "' and '" + savedLit + "'."); }
					saveIt = false; break;
				}
			}
			
			if (saveIt) { newNegLits.add(nLit); } else { somethingSimplified = true; }
		}

		if (newNegLitsHold != null) {
			newNegLits.addAll(newNegLitsHold); // Could put these in the 'right' spot, but for now just stick on at the end.  TODO 
		}
		if (newNegLits.size() < 1) { newNegLits.add(stringHandler.trueLiteral); } // Could propagate this 'true' but it is an unlikely case and so don't bother.
		return newNegLits;
    }
    
    private Clause useDeterminateLiteralsToUnifyVariables(Clause c) {
    	if (c == null || Utils.getSizeSafely(c.negLiterals) < 1) { return c; }
    	Map<PredicateName,List<Literal>> samePredicates = new HashMap<PredicateName,List<Literal>>(4);
    	// First group literals by predicateName
    	for (Literal nLit : c.negLiterals) {
    		PredicateName pName = nLit.predicateName;
    		if (!pName.isFunctionAsPredicate(null, nLit.getArguments())) { continue; }
    		List<Literal> lookup = samePredicates.get(pName);
    		if (lookup == null) {
    			lookup = new ArrayList<Literal>(1);
    			samePredicates.put(pName, lookup);
    		}
    		if (!nLit.member(lookup, false)) { lookup.add(nLit); } // Set's weren't working (even when using setUseStrictEqualsForLiterals(false)), so handle explicitly.
    	}
    	if (samePredicates.size() < 1) { return c; }
    	BindingList bl = new BindingList();
    	for (PredicateName pNameInUse : samePredicates.keySet()) {
    		List<Literal> candidates = samePredicates.get(pNameInUse);
    		if (candidates.size() < 2) { continue; }
    		Utils.println("% determinatesToMatch for '" + pNameInUse + "' = " + candidates);
    		processThisSetOfCandidatesMatchingDeterminates(candidates, bl);
    	}
    	if (bl.theta.size() < 1) { return c; }
    //	Utils.waitHere("567, bl = " + bl);
    	List<Literal> newPlits = new ArrayList<Literal>(c.posLiterals.size());
    	List<Literal> newNlits = new ArrayList<Literal>(c.negLiterals.size());
    	for (Literal pLit : c.posLiterals) { newPlits.add(pLit.applyTheta(bl.theta)); }
    	for (Literal nLit : c.negLiterals) { newNlits.add(nLit.applyTheta(bl.theta)); }
    	return stringHandler.getClause(newPlits, newNlits, c.getExtraLabel());
    }
    
    private void processThisSetOfCandidatesMatchingDeterminates(List<Literal> candidates, BindingList bl) {
    	if (Utils.getSizeSafely(candidates) < 2) { return; }
    	List<Literal> copyOfSet = new ArrayList<Literal>(candidates.size());
    	copyOfSet.addAll(candidates);
    	// There might be some order-dependent aspects of this calculation, but we'll live with order we get.  TODO - think this out more.
    	while (!copyOfSet.isEmpty()) {
        	Literal litToConsider = copyOfSet.remove(0).applyTheta(bl.theta);
        	int numbArgs = litToConsider.numberArgs();
        	int arg      = litToConsider.predicateName.returnFunctionAsPredPosition(null, numbArgs);
        	Utils.println("\n%  litToConsider = " + litToConsider + ", arg #" + arg);
        	if (copyOfSet.size() > 0) for (Literal otherLit : copyOfSet) if (numbArgs == otherLit.numberArgs()) {
            	int otherArg = litToConsider.predicateName.returnFunctionAsPredPosition(null, otherLit.numberArgs());
            	if (otherArg != arg) { continue; }
            	Literal otherLit2 = otherLit.applyTheta(bl.theta); // This might be necessary, but do it anyway.
            	Utils.println("%  otherLitToConsider = " + otherLit2 + ", arg #" + otherArg);
            	boolean mismatched = false;
            	for (int i = 0; i < numbArgs; i++) if (i != arg - 1) { // Remember that external counting is from 1.
            		if (litToConsider.getArgument(i) != otherLit2.getArgument(i)) { 
            			mismatched = true; 
            			Utils.println("%    mismatch: '" + litToConsider.getArgument(i) + "' and '" + otherLit2.getArgument(i) + "'.");
            			break; 
            		}
            	}
            	if (!mismatched) { 
            		Term term1 = litToConsider.getArgument(arg - 1);
            		Term term2 = otherLit2.getArgument(    arg - 1);
            		if (term1 != term2) {
                		Utils.println("%    need to match: '" + term1 + "' and '" + term2 + "'.");
                		if      (term1 instanceof Variable) { bl.addBindingFailSoftly((Variable) term1, term2); } // At least one needs to be a variable.
            			else if (term2 instanceof Variable) { bl.addBindingFailSoftly((Variable) term2, term1); }
            		}
            	}
        	}
    	}
    }
    
    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    private Unifier          unifier        = new Unifier();
    private StringConstant[] constantsToUse = null; // These are used to replace variables when matching for pruning.
    private BindingList      cachedBindingListForPruning; // Used if any pruning is being considered.
    private Clause           numberedBodyForPruning;      // Also used when pruning.
    
    private boolean canPrune(Literal lit, List<Literal> body) {
    	
    	PredicateName pName = lit.predicateName;
    	if (pName == stringHandler.standardPredicateNames.lt || pName == stringHandler.standardPredicateNames.lte) {
    		Term arg0 = lit.getArgument(0);
    		Term arg1 = lit.getArgument(1);
    		
    		if (arg0 instanceof NumericConstant) {
				NumericConstant nc = (NumericConstant) arg0;
				if (nc.value.doubleValue() == Double.NEGATIVE_INFINITY) { return true; }
    		}
    		if (arg1 instanceof NumericConstant) {
				NumericConstant nc = (NumericConstant) arg1;
				if (nc.value.doubleValue() == Double.POSITIVE_INFINITY) { return true; }
    		}
    	}
    	if (pName == stringHandler.standardPredicateNames.gt || pName == stringHandler.standardPredicateNames.gte) {
    		Term arg0 = lit.getArgument(0);
    		Term arg1 = lit.getArgument(1);
    		
    		if (arg0 instanceof NumericConstant) {
				NumericConstant nc = (NumericConstant) arg0;
				if (nc.value.doubleValue() == Double.POSITIVE_INFINITY) { return true; }
    		}
    		if (arg1 instanceof NumericConstant) {
				NumericConstant nc = (NumericConstant) arg1;
				if (nc.value.doubleValue() == Double.NEGATIVE_INFINITY) { return true; }
    		}
    	}
    	
    	if (constantsToUse == null) {
    		constantsToUse = new StringConstant[ChildrenClausesGenerator.numberofConstantsToCreate];
    		for (int i = 0; i < ChildrenClausesGenerator.numberofConstantsToCreate; i++) { // Task is not yet assigned when instance created, so need an extra call.  Plus good to all a resetting of all instance variables.
    			constantsToUse[i] = stringHandler.getStringConstant("WillConst" + (i + 1));  // Need something that is unlikely to also appear in a clause "of its own right."  Also, recall that these count from ONE.
    		}
    		
    	}
    	if (lit == null) { return false; }
    	MapOfLists<PredicateNameAndArity,Pruner> allPruners = lit.predicateName.getPruners(lit.getArity());
    	if (allPruners == null) { return false; }
    	
    	putPartialBodyInFormForPruning(lit, body);
    	if (debugLevel > 0) {
    		Utils.println(" lit:                         " + lit);
    		Utils.println(" body:                        " + body);
    		Utils.println(" cachedBindingListForPruning: " + cachedBindingListForPruning);
    		Utils.println(" numberedBodyForPruning:      " + numberedBodyForPruning);
    	}
    	Literal     initNumberedLit = (cachedBindingListForPruning == null ? lit             : lit.applyTheta(cachedBindingListForPruning.theta));
		BindingList newBL           = bindVarsToUniqueConstants(initNumberedLit);
		Literal     fixedLit        = (newBL                       == null ? initNumberedLit : initNumberedLit.applyTheta(newBL.theta));

		// See if NULL is one of the pruners (NULL means nothing in the body needs to match).
		List<Pruner>  prunersMatchingNULL = allPruners.getValues(null);
		if (prunersMatchingNULL != null) for (Pruner p : prunersMatchingNULL) {
			if (p.truthValue != 0 && p.isaMatch(fixedLit, null)) {
				if (p.truthValue < 0) { 
					Utils.warning("% Have a literal that is said to evaluate to FALSE!\n lit = " + lit + "'\n% pruner: " + p); 
					return false; // Don't prune these since then they'd be treated as TRUE.  Could add 'false' but seems good to see the offending literal.
				}
				Utils.println("% CAN PRUNE '" + lit + "' [" + fixedLit + "] because of pruner: " + p);
				return true; 
			}
		}

		if (body == null) { return false; }

		List<Literal> numberedClauseBody = numberedBodyForPruning.negLiterals;	
		int parentBodyLength = numberedClauseBody.size();
		for (int bodyCounter = 0; bodyCounter < parentBodyLength; bodyCounter++) {
			Literal       numberedBodyLit = numberedClauseBody.get(bodyCounter);
			PredicateName parent_pName    = numberedBodyLit.predicateName;
		    List<Pruner>  matchingPruners = allPruners.getValues(numberedBodyLit.getPredicateNameAndArity());
			if (matchingPruners != null) for (Pruner p : matchingPruners) {
				if (p.truthValue != 0 && p.isaMatch(fixedLit, numberedBodyLit)) { 
					if (p.truthValue < 0) { Utils.warning("% Have a literal in clause that is said to evaluate to FALSE!\n lit = " + lit + "\n%   pruner: " + p + "\n%   clause body: " + body); continue; }
					Utils.println("% Can prune '" + lit + "' because of exiting literal '" + body.get(bodyCounter) + "' [" + numberedBodyLit + "] and pruner: " + p);
					return true; 
				}
    		}
    	}
    	return false;
    }

    private void putPartialBodyInFormForPruning(Literal lit, List<Literal> body) {
		List<Literal>  pos = new ArrayList<Literal>(1); pos.add(lit);
		Clause      clause = stringHandler.getClause(pos, body);
		//Collection<Variable> collectedFreeVariables = 
			clause.collectFreeVariables(null);  // Utils.println("%  collectedFreeVariables = " + collectedFreeVariables);
		BindingList     bl = clause.copyAndReplaceVariablesWithNumbers(constantsToUse);
		cachedBindingListForPruning = bl;
		numberedBodyForPruning      = (bl == null ? clause : clause.applyTheta(bl.theta));
	}

	private BindingList bindVarsToUniqueConstants(Literal lit) {
		BindingList          result      = new BindingList();
		Collection<Variable> newVars     = lit.collectFreeVariables(null);		
		if (newVars != null) {
			int currentPositionInConstants = (cachedBindingListForPruning == null ? 0 : cachedBindingListForPruning.theta.size());
			for (Variable newVar : newVars) { 
				result.addBinding(newVar, constantsToUse[currentPositionInConstants++]); // If we get an error here, look at Clause.copyAndReplaceVariablesWithNumbers (seems unlikely we'll ever have more than 100 unique variables in a clause ...).
			}
		}
		return result;
	}
	///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    
//	private final String cannotNegateString = "\n// This theory should be negated by code that uses it. \n";
	public boolean cannotNegateEasily() {
		return cannotNegateEasily;
	}
	
	private Clause getMainClauseForNegatedExamples() {
		// First check that the main clauses are all definite clauses and have the same predicate name.
		if (clauses == null || stringHandler == null) { return null; }
		
		PredicateName  pName = null;
		int            arity = -1;
		List<Term>     body  = null;
		for (Clause c : clauses) {
			if (!c.isDefiniteClause()) {
				Utils.warning("Cannot negate a theory that is not made up of DEFINITE clauses.");
				cannotNegateEasily = true;
				return null; 
			}
			Literal pLit = c.posLiterals.get(0);
			// If there is more than one clause, they may have different argument types, so for simplicity, use new arguments in all positions and let the constraining happen at unification time.
			if (pName == null) { 
				pName = pLit.predicateName; 
				arity = pLit.numberArgs(); 
				if (clauses.size() < 2) {
					body = pLit.getArguments();
				} else {
					body = new ArrayList<Term>(arity);
					body.addAll(stringHandler.getThisManyVars(arity, true));
				}
			} else if (pName != pLit.predicateName) { 
				Utils.warning("Cannot negate a theory with different head clauses: " + pName + " vs. " + pLit.predicateName); 
				cannotNegateEasily = true;
				return null; 
			} else if (arity != pLit.numberArgs())  { 
				Utils.warning("Cannot negate a theory with different arities of its head clauses: " + pName + "/" + arity + " vs. " + pLit.predicateName + "/" + pLit.numberArgs());
				cannotNegateEasily = true;
				return null; 
			}
		}
		cannotNegateEasily = false;
		List<Literal> pLits = new ArrayList<Literal>(4);
		List<Literal> nLits = new ArrayList<Literal>(4);
		Literal       head  = stringHandler.getLiteral(pName, body);
		pLits.add(head);
		Function   not_head  = stringHandler.getFunction(stringHandler.getFunctionName(FileParser.will_notPred_prefix + pName.name), body, null);
		nLits.add(stringHandler.wrapInNot(not_head));
		return stringHandler.getClause(pLits, nLits);
	}
	public void addTheseSentences(Collection<? extends Sentence> standardSentences) {
		addTheseSentences(standardSentences, inlineHandler);
	}
	public final void addTheseSentences(Collection<? extends Sentence> standardSentences, InlineManager checkForInlinersAndSupportingClauses) {
		if (standardSentences == null) { return; }
		if (clauses   == null) { clauses   = new ArrayList<Clause>(standardSentences.size()); }
		if (sentences == null) { sentences = new ArrayList<Sentence>(standardSentences);      }
		else                   { sentences.addAll(standardSentences); }
		for (Sentence s : standardSentences) {
			Boolean hold = stringHandler.prettyPrintClauses;
			stringHandler.prettyPrintClauses = false;
			if (debugLevel > 0) { 
				Utils.println(    "%  From: '" + s.toString(Integer.MAX_VALUE) + "'");
			}
			List<Clause> theseClauses = s.convertToClausalForm();
			if (debugLevel > 0) { 
				for (Clause c : theseClauses) {
					Utils.println("%         Clause: '" + c.toString(Integer.MAX_VALUE) + "'  containsCut=" + c.getBodyContainsCut());
				}
			}
			stringHandler.prettyPrintClauses = hold;
			addAllMainClauses(theseClauses, checkForInlinersAndSupportingClauses);
		}
	}

	// Order matters in Prolog, so don't allow arbitrary Collections.
	public void addAllMainClauses(List<? extends Clause> clausesToAdd) {
		addAllMainClauses(clausesToAdd, inlineHandler);
	}
	public final void addAllMainClauses(List<? extends Clause> clausesToAdd, InlineManager checkForInlinersAndSupportingClauses) {
	//	if (checkForInlinersAndSupportingClauses == null) { Utils.waitHere("Are you sure you don't have an checkForInlinersAndSupportingClauses?"); }
		for (Clause c : clausesToAdd) {
			addMainClause(c, checkForInlinersAndSupportingClauses);
		}	
	}
    public void addMainClause(Clause clause) {
        addMainClause(clause, inlineHandler);
    }
	public void addMainClause(Clause clause, InlineManager checkForInlinersAndSupportingClauses) {
	//	if (checkForInlinersAndSupportingClauses == null) { Utils.waitHere("Are you sure you dont have an checkForInlinersAndSupportingClauses?"); }
		if (clause == null) { return; }
		if (clauses         == null) { clauses         = new ArrayList<Clause>(4); }
		if (originalClauses == null) { originalClauses = new ArrayList<Clause>(4); }
		originalClauses.add(clause);
		
		if (debugLevel > 2) { 
			Utils.println("% AddMainClause: " + clause.toPrettyString("%    ", Integer.MAX_VALUE)); // Utils.waitHere();
		}
		if (checkForInlinersAndSupportingClauses != null) {
			List<Clause> doubleResults = checkForInlinersAndSupportingClauses.handleInlinerAndSupportingClauses(clause);
		//	Utils.println("doubleResults=" + doubleResults);			
			if (doubleResults == null) { Utils.error("Should not get a NULL here using: " + clause); }			
			clauses.add(doubleResults.remove(0));
			for (Clause sc : doubleResults) { addSupportingClause(sc, null); }
		} else {
			clauses.add(clause);
		}
		if (debugLevel > 2) { 
			Utils.println("\nCurrent Theory: " + this.toString());
			Utils.waitHere();		
		}
		
	}

    public void addSupportingClause(Clause clause) {
        addSupportingClause(clause, inlineHandler);
    }
	public void addSupportingClause(Clause clause, InlineManager checkForInlinersAndSupportingClauses) { 
		if (clause == null) { return; }
		if (supportClauses == null) { supportClauses = new ArrayList<Clause>(4); }
		
        boolean found = false;
        
        for (Clause aSupportClause : supportClauses) {
            if ( clause.isEquivalentUptoVariableRenaming(aSupportClause) ){
                found = true;
                break;
            }
        }

        if ( found == false ) supportClauses.add(clause);
	}
	
	public boolean isaDefiniteClauseTheory(boolean throwErrorIfNot) {	
		if (clauses == null) { return false; }
		for (Clause clause : clauses) {			
			if (!clause.isDefiniteClause()) { // A bit sloppy to mention 'The Horn-Clause Theorem Prover' here, but not that mortal of a sin.
				if (throwErrorIfNot) { Utils.error("The Horn-Clause Theorem Prover requires all background knowledge to be definite clauses (i.e., of the form 'p and q => r'):\nThis one isn't: " + clause); }
				return false;
			}
		}
		return true;
	}
	public String getTargetPredicateNameString(boolean throwErrorIfNotDefinite) {
		PredicateName result = getTargetPredicateName(throwErrorIfNotDefinite);
		if (result == null) { Utils.error("Could not find the name of the target predicate."); return null; }
		return result.name;
	}
	public PredicateName getTargetPredicateName(boolean throwErrorIfNotDefinite) {
		PredicateName pName = null;
		
		if (!isaDefiniteClauseTheory(throwErrorIfNotDefinite)) { return null; }
		
		for (Clause clause : clauses) {
			PredicateName headPname = clause.posLiterals.get(0).predicateName;
			
			if (pName == null) { pName = headPname; }
			else if (pName != headPname) { // Keep looking to see if there are more clauses with different names.  Shouldn't happen.
				if (throwErrorIfNotDefinite) { Utils.error("Have more than one target predicate: '" + pName + "' and '" + headPname + "' (might be more)."); }
				return pName;
			}
		}		
		return pName;		
	}
	
	/**
         * Count the number of definite clauses in this theory whose head
         * matches the provided literal.
         * 
         * @param head
         * @param unifier
         * @return The count of matching clauses.
         */
	public int countMatchingDefiniteClauses(Literal head, Unifier unifier) {
		return countMatchingDefiniteClauses(head, unifier, false);
	}
	public int countMatchingDefiniteClauses(Literal head, Unifier unifier, boolean reportMatches) {
		if (clauses == null) { return 0; }
		int counter = 0;
		for (Clause clause : clauses) if (clause.isDefiniteClause()) {
			if (unifier.unify(clause.posLiterals.get(0), head) != null) {
				if (reportMatches) { Utils.println("% matcher:\n% " + clause.toPrettyString("%  ")); } 
				counter++; }
		}
		return counter;
		
	}

    /**
     * @return the clauses
     */
    public List<Clause> getClauses() {
        return clauses;
    }
	public boolean isNegated() {
		return negated;
	}
	public void setNegated(boolean negated) {
		this.negated = negated;
	}
	
	private boolean theoryFlipFlopped = false; // Only want to flip-flop once.	
	public final void rewriteFlipFloppedTheory() {
		rewriteFlipFloppedTheory(true);
	}
		public void rewriteFlipFloppedTheory(boolean complainIfAlreadyFlipper) {
		if (!negated)          { return; }
		if (theoryFlipFlopped) { if (complainIfAlreadyFlipper) { Utils.waitHere("Have already flipped this theory!\n " + toString()); } return; }
		theoryFlipFlopped = true;
		if (clauses == null) { return; } // No clauses were learned.
		Clause newMainClause = getMainClauseForNegatedExamples();
		if (newMainClause == null) { Utils.waitHere("Why does newMainClause = null?"); return; }
		for (Clause clause : clauses) {
			Clause    newClause    = clause.copy(false);
			Literal        head    = newClause.posLiterals.get(0);
			PredicateName pName    = head.predicateName;
			PredicateName pNameNew = stringHandler.getPredicateName(FileParser.will_notPred_prefix + pName);
			pNameNew.addTemporary(head.numberArgs()); // We might need to later further rename this.
			head.predicateName = pNameNew;
			if (supportClauses == null) { supportClauses = new ArrayList<Clause>(4); }
			supportClauses.add(newClause);
		}
		clauses.clear();
		clauses.add(newMainClause);
	}
	
	public List<Clause> getSupportClauses() {
		return supportClauses;
	}
	public void setSupportClauses(List<Clause> supportClauses) {
		this.supportClauses = supportClauses;
	}
	public Collection<Sentence> getSentences() {
		return sentences;
	}
	public void setSentences(Collection<Sentence> sentences) {
		this.sentences = sentences;
	}
	public void setClauses(List<Clause> clauses) {
		this.clauses= null;  
		addAllMainClauses(clauses, inlineHandler);
	}
	
	public boolean haveTheory() {
		return Utils.getSizeSafely(clauses) > 0;
	}
	
	public String toPrettyString() {
        BindingList bl = null;
        if ( renameVariablesWhenPrinting ) {
            bl = new BindingList();
        }
		return toPrettyString("", Integer.MIN_VALUE, bl);
	}
	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		String str = newLineStarter; // No weights on theories - instead they are on sentences.
		if (Utils.getSizeSafely(clauses) < 1) {
			if (Utils.getSizeSafely(supportClauses) > 0) { Utils.error("There are SUPPORTING clauses, but no regular clauses!  Supporters: " + supportClauses); }
			return "% There are no clauses in this theory.";
		}
        BindingList bl = null; // Binding list to tie all variable together when printing.
		boolean firstTime = true;
		int counter = 1;
		for (Clause clause : clauses) {	
			if (firstTime) { firstTime = false; str += "\n% " + newLineStarter + "Clauses:\n\n"; }
			str += newLineStarter + printClause(clause, newLineStarter, bl) + " // Clause #" + counter++ + ".\n\n";
		}
		firstTime = true;
		counter   = 1;
		if (Utils.getSizeSafely(supportClauses) > 0) for (Clause clause : supportClauses) {	
			if (firstTime) { firstTime = false; str += "\n% " + newLineStarter + "Supporting Clauses:\n\n"; }
			str += newLineStarter + printClause(clause, newLineStarter, bl) + " // Supporting Clause #" + counter++ + ".\n\n";
		}
		if (!reportUnsimplifiedClauses) { return str; }
		firstTime = true;
		counter   = 1;
		boolean haveSimplified = somethingSimplified && (Utils.getSizeSafely(unsimplifiedClauses) +  Utils.getSizeSafely(unsimplifiedSupportClauses) > 0);
		if (haveSimplified) { str += "\n/* Before Simplification:\n"; }
		else { return str; }
		if (Utils.getSizeSafely(unsimplifiedClauses) > 0) for (Clause clause : unsimplifiedClauses) {
			if (firstTime) { firstTime = false; str += "\n% " + newLineStarter + "Unsimplified Clauses:\n\n"; }
			str += newLineStarter + printClause(clause, newLineStarter, bl) + " // Clause #" + counter++ + ".\n\n";
		}	
		firstTime = true;
		counter   = 1;	
		if (Utils.getSizeSafely(unsimplifiedSupportClauses) > 0) for (Clause clause : unsimplifiedSupportClauses) {	
			if (firstTime) { firstTime = false; str += "\n% " + newLineStarter + "Unsimplified Supporting Clauses:\n\n"; }	
			str += newLineStarter + printClause(clause, newLineStarter, bl) + " // Supporting Clause #" + counter++ + ".\n\n";
		}
		str += "\n*/";
		return str;
	}
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return toPrettyString("", precedenceOfCaller, bindingList);
	}


    private String printClause(Clause clause, String newLineStarter, BindingList bl) {
        //return clause.toPrettyString(newLineStarter + "   ", Integer.MAX_VALUE) +".";

        return PrettyPrinter.print(clause, "", newLineStarter, getPrettyPrinterOptions(), bl);

    }

    private PrettyPrinterOptions getPrettyPrinterOptions() {
        if ( prettyPrinterOptions == null ) {
            prettyPrinterOptions = new PrettyPrinterOptions();
            prettyPrinterOptions.setMaximumLiteralsPerLine(1);
            prettyPrinterOptions.setAlignParathesis(false);
            prettyPrinterOptions.setRenameVariables(true);
            prettyPrinterOptions.setNewLineAfterOpenParathesis(true);
            prettyPrinterOptions.setMaximumIndentationAfterImplication(5);
            prettyPrinterOptions.setNewLineAfterImplication(true);
        }

        return prettyPrinterOptions;
    }


	// Print a theory w/o any comments, for ease of processing elsewhere.
	public String toPlainString() {
		String str = ""; // No weights on theories - instead they are on sentences.
		
		if (Utils.getSizeSafely(clauses)        > 0) for (Clause clause : clauses) {
			str += clause.toString(Integer.MAX_VALUE) + ".\n";
		}		
		if (Utils.getSizeSafely(supportClauses) > 0) for (Clause clause : supportClauses) {		
			str += clause.toString(Integer.MAX_VALUE) + ".\n";
		}
		if (!reportUnsimplifiedClauses) { return str; }
		boolean haveSimplified = somethingSimplified && (Utils.getSizeSafely(unsimplifiedClauses) +  Utils.getSizeSafely(unsimplifiedSupportClauses) > 0);
		if (!haveSimplified) { return str; }
		str += "\n/*\n";
		if (Utils.getSizeSafely(unsimplifiedClauses) > 0) for (Clause clause : unsimplifiedClauses) {
			str += clause.toString(Integer.MAX_VALUE) + ".\n";
		}		
		if (Utils.getSizeSafely(unsimplifiedSupportClauses) > 0) for (Clause clause : unsimplifiedSupportClauses) {		
			str += clause.toString(Integer.MAX_VALUE) + ".\n";
		}
		str += "\n*/";
		return str;
	}
	
	public String printOriginalTheory() {
		String result = "\n/*\n";
		
		if (sentences != null) {
			result += "\nThe original sentences:\n";
			for (Sentence s : sentences) { result += "   " + s + "\n"; }
		}
		
		if (originalClauses != null) {
			result += "\nThe original clauses:\n";
			if (originalClauses != null) for (Clause c : originalClauses) {	result += "   " + c.toPrettyString("      ", Integer.MAX_VALUE) + "\n"; }
		}		
		return result + "\n*/\n";
	}
	
	public void addPreAndPostfixToTemporaryNames(String prefixForSupportClause, String postfixForSupportClause) {		
		if (clauses != null) for (Clause c : clauses) { // These are the main clauses.  Don't rename them (shouldn't happen since should not be in renameTheseSupportingPredicates), but check their bodies.
			for (int i = 0; i < c.getLength(); i++) {
				Literal lit = c.getIthLiteral(i);
				if (lit.predicateName == stringHandler.standardPredicateNames.negationByFailure) {
					renameNegationByFailure(lit, prefixForSupportClause, postfixForSupportClause);
				} else { 
					renameLiteralIfTemporary(lit, prefixForSupportClause, postfixForSupportClause);
				}
			}
		}
		if (supportClauses != null) for (Clause c : supportClauses) { // These are the supporting clauses.  Rename them, plus check their bodies.
			for (int i = 0; i < c.getLength(); i++) {
				Literal lit = c.getIthLiteral(i);
				if (lit.predicateName == stringHandler.standardPredicateNames.negationByFailure) {
					renameNegationByFailure(lit, prefixForSupportClause, postfixForSupportClause);
				} else {
					renameLiteralIfTemporary(lit, prefixForSupportClause, postfixForSupportClause);
				} //else { Utils.println("% THIS IS NOT A TEMPORARY NAME AND SO NO PRE/POST-FIX ADDED: " + lit.predicateName); }
			}
		}		
	}
	
	private void renameNegationByFailure(Literal negationByFailure, String prefixForSupportClause, String postfixForSupportClause) {

        Clause contents = negationByFailure.getStringHandler().getNegationByFailureContents(negationByFailure);

        for (Literal contentsLiteral : contents.getPositiveLiterals()) {
            renameLiteralIfTemporary(contentsLiteral, prefixForSupportClause, postfixForSupportClause);
        }

//		Term arg = lit.getArgument(0);
//		if (!(arg instanceof SentenceAsTerm)) { Utils.error("Should a negation-by-failure's argument not be a SentenceAsTerm? " + arg); }
//		Sentence sentence = ((SentenceAsTerm) arg).sentence;
//		if (sentence instanceof Literal) {
//			Literal lit2 = (Literal) sentence;
//			Utils.error("Should a literal be inside here? " + lit2 + " in " + lit);  // If so, wrap into a clause and use the code below ...
//		} else if (sentence instanceof Clause) {
//			Clause c = (Clause) sentence;
//			if (Utils.getSizeSafely(c.posLiterals) > 0) { Utils.error("Should not have positive literals inside a negation-by-failure.");         }
//			if (Utils.getSizeSafely(c.negLiterals) < 1) { Utils.error("Should have at least one negative literal inside a negation-by-failure."); }
//
//			for (Literal nLit : c.negLiterals) {
//				renameLiteralIfTemporary(nLit, prefixForSupportClause, postfixForSupportClause);
//			}
//		}
	}
		
	// This should all be done IN-PLACE.
	private void renameLiteralIfTemporary(Literal lit, String prefixForSupportClause, String postfixForSupportClause) {
		if (lit.predicateName.isaTemporaryName(lit.numberArgs())) {
			lit.predicateName = stringHandler.getPredicateName(prefixForSupportClause + lit.predicateName + postfixForSupportClause);
		}
		renameFunctionsIfTemporary(lit.getArguments(), prefixForSupportClause, postfixForSupportClause);
	}
	private void renameFunctionsIfTemporary(List<Term> arguments, String prefixForSupportClause, String postfixForSupportClause) {
		if (arguments != null) for (Term t : arguments) if (t instanceof Function) {
			Function      f            = (Function) t;
			PredicateName pNameVersion = stringHandler.getPredicateName(f.functionName.name);
			
			// Need to recur inside functions.
			renameFunctionsIfTemporary(f.getArguments(), prefixForSupportClause, postfixForSupportClause);
			// And need to change the function name as well, IF it is a temporary name.
			if (pNameVersion.isaTemporaryName(f.numberArgs())) {
				f.functionName = stringHandler.getFunctionName(prefixForSupportClause + f.functionName + postfixForSupportClause);
			}
		}
	}
	
	public boolean isEmptyTheory() {
		return (clauses == null);
	}
	
	public boolean isBodylessTheory() {
		if (clauses == null) { return true; }
		
		for (Clause c : clauses) {
			if (Utils.getSizeSafely(c.negLiterals) < 1) { continue; }
			if (c.negLiterals.size() > 1) { return false; }
			if (!c.negLiterals.get(0).predicateName.name.equalsIgnoreCase("true")) { return false; }
		}
		return true;
	}
	public void addToBodylessTheory(Literal litToAdd) {
		addToBodylessTheory(litToAdd, inlineHandler);
	}
	public void addToBodylessTheory(Literal litToAdd, InlineManager checkForInlinersAndSupportingClauses) {
		if (clauses == null) { 
			Clause newClause = stringHandler.getClause(litToAdd, true);
			Utils.println("% Added the literal '" + litToAdd + "' to produce this clause: " + newClause);
			addMainClause(newClause, checkForInlinersAndSupportingClauses);
		} else for (Clause c : clauses) {
			if (c.negLiterals == null) { c.negLiterals = new ArrayList<Literal>(1); }
			if (c.negLiterals.size() < 1) { 
				c.negLiterals.add(litToAdd);
				Utils.writeMe("Need to unify the clause head and the literal added to the body.\n " + c); // Figure this out if ever needed ...
			}
		}
	}
	
	public boolean isSomethingSimplified() {
		return somethingSimplified;
	}
	public void setSomethingSimplified(boolean somethingSimplified) {
		this.somethingSimplified = somethingSimplified;
	}

    public static Theory readTheory(String file, HornClauseContext context) {

        List<Sentence> sentences = context.getFileParser().readFOPCfile(file);
        PredicateNameAndArity predicate = null;

        Theory theory = new Theory(context);

        for (Sentence sentence : sentences) {
            List<Clause> clauses = sentence.convertToClausalForm();
            for (Clause clause : clauses) {
                if ( predicate == null ) {
                    predicate = clause.getDefiniteClauseHead().getPredicateNameAndArity();
                }

                if ( clause.getDefiniteClauseHead().getPredicateNameAndArity().equals(predicate) ) {
                    theory.addMainClause(clause);
                }
                else {
                    theory.addSupportingClause(clause);
                }
            }
        }

        return theory;
    }

    @Override
    public Theory applyTheta(Map<Variable, Term> bindings) {
    	// TODO Auto-generated method stub
    	Utils.writeMe("Theory applyTheta");
    	return this;
    }

    @Override
    public Iterator<Sentence> iterator() {
        return sentences.iterator();
    }


    @Override
    public String toString() {
        BindingList bl = null;
        if ( renameVariablesWhenPrinting ) {
            bl = new BindingList();
        }

        return toPrettyString("", 0, bl);
    }

   /** Methods for reading a Object cached to disk.
    *
    * @param in
    * @throws java.io.IOException
    * @throws java.lang.ClassNotFoundException
    */
    private void readObject(java.io.ObjectInputStream in) throws IOException, ClassNotFoundException {
        if ( in instanceof FOPCInputStream == false ) {
            throw new IllegalArgumentException(getClass().getCanonicalName() + ".readObject input stream must support FOPCObjectInputStream interface");
        }
        in.defaultReadObject();

        FOPCInputStream fOPCInputStream = (FOPCInputStream) in;

        this.stringHandler = fOPCInputStream.getStringHandler();
    }

    @Override
    public int countVarOccurrencesInFOPC(Variable v) {
    	return 2; // TODO - might want to do a real count, but for now we don't want to make any of these variable anonymous anyway.
    }

}
