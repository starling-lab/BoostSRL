package edu.wisc.cs.will.ILP;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.ResThmProver.HornClausebase;
import edu.wisc.cs.will.Utils.Utils;

public class InlineManager {
	protected final static int debugLevel = 0; // Used to control output from this project (0 = no output, 1=some, 2=much, 3=all).

	private HandleFOPCstrings  stringHandler;
	private HornClausebase     hornClauseKnowledgeBase;
	
	private PredicateName      notPname;
	
	public InlineManager(HandleFOPCstrings stringHandler, HornClausebase hornClauseKnowledgeBase) {
        this.stringHandler = stringHandler;
        this.hornClauseKnowledgeBase = hornClauseKnowledgeBase;

        this.notPname = stringHandler.standardPredicateNames.negationByFailure;
    }

    public InlineManager(HornClauseContext context) {
		this(context.getStringHandler(), context.getClausebase());
	}

	public void addInventedClause(Literal head, Clause c) {
		if (literalIsInlined(head)) { Utils.error("Already have inlined '" + head + "'."); }
		head.predicateName.addInliner(head.numberArgs());
	}
	
	private boolean literalIsInlined(Literal lit) { // TODO - put in Literals class if these seem to be more generally useful.
		if (lit == null) { return false; }
		PredicateName pName = lit.predicateName;
		return pName.isaInlined(lit.numberArgs());
	}
	
	private boolean literalIsaSupportingPredicate(Literal lit) {
		if (lit == null) { return false; }
		PredicateName pName = lit.predicateName;
		return pName.isaSupportingPredicate(lit.numberArgs());
	}
	
	private BindingList literalMatchesDeterminateClause(Literal lit, Clause c, BindingList bindings) {
		if (!c.isDefiniteClause()) { Utils.error("This code only handle definite clauses.  It was given: " + c); }
		Literal head = c.getDefiniteClauseHead();
		return Unifier.UNIFIER.unify(lit, head, bindings);
	}
	
	private Clause getLiteralDefinition(Literal lit) {
        if (lit == null) {
            return null;
        }
        if (literalIsInlined(lit)) {
            List<DefiniteClause> clauses = hornClauseKnowledgeBase.getAssertions(lit.predicateName, lit.getArity());
            if (clauses == null || clauses.size() != 1) {
                return null;
            }
            return clauses.get(0).getDefiniteClauseAsClause();
        }
        Utils.waitHere("getLiteralDefinition: this literal is not inlined: " + lit);
        return null;
    }
	
	public void addToFilterTheseOut(PredicateName pName) {
		pName.addFilter();
	}
	
	private Clause getUnifiedLiteralDefinition(int depth, Literal lit, BindingList overallBindings) {
		if (lit == null)                 { Utils.error("Literal should be NULL here."); }
		//Utils.println("   OLD: " + getLiteralDefinition(lit));
		getStringHandler().resetAllVariables(); // Need fresh variables for the following copy.
		Clause definer = getLiteralDefinition(lit);
		//Utils.println("   NEW: " + definer);
		if ( definer == null)            { Utils.error("Expected a definition of this literal: " + lit); }
		else {
			definer = definer.copy(true);  // We need a fresh copy in case the same head appears more than once in a clause.
		}
		if (!definer.isDefiniteClause()) { Utils.error("This code only handle definitions that are definite clauses.  It was given: " + definer); }
		Literal     head = definer.posLiterals.get(0);
		if (debugLevel > 3) { 
			indentAndPrintln(depth, "");
			indentAndPrintln(depth, "  raw rule  = " + definer);
			indentAndPrintln(depth, "  head      = " + head);
			indentAndPrintln(depth, "  lit       = " + lit);
			indentAndPrintln(depth, "  overall   = " + bindingsToDetailedString(overallBindings));
		}
		BindingList bl   = Unifier.UNIFIER.unify(head, lit, overallBindings); // Doing this order will make it more likely that lit's variables remain.
		if (debugLevel > 3) {
			indentAndPrintln(depth, "  bl        = " + bindingsToDetailedString(bl));
		}
		if (bl == null) {
			Utils.waitHere("Inliner could not be inserted; could not unify\n  " + lit + " and\n  " + head + "\n given overall bindings = " + overallBindings);
			return null;
		}
		// Will this next line mess up in recursion?  Hopefully not.
		overallBindings.addBindings(bl); // Delay this to here in case we figure out how to recover from that error.
		if (debugLevel > 3) { indentAndPrintln(depth, " combined = " + bindingsToDetailedString(overallBindings)); }
		List<Literal> litsToKeep = new ArrayList<Literal>(Utils.getSizeSafely(definer.negLiterals));
		if (definer.negLiterals != null) for (Literal innerLit : definer.negLiterals) if (!innerLit.predicateName.filter()) {
			litsToKeep.add(innerLit);
		}
		List<Literal> posLits = new ArrayList<Literal>(1);
		posLits.add(head);
		return getStringHandler().getClause(posLits, litsToKeep).applyTheta(overallBindings.theta);
	}

	// Handle any 'inliners' in this clause.  Return a LIST of clauses,
	// where the FIRST clause is the new version of the provided clause,
	// and the REST of the Clauses (if any) are the SUPPORTING literals in
	// this clause.  (Recall that supporting literals are ones that need to accompany theories.)
	public List<Clause> handleInlinerAndSupportingClauses(Clause c) {
		if (c == null) { return null; }
		boolean hold = getStringHandler().printVariableCounters;

		if (debugLevel > 3) { stringHandler.printVariableCounters = true; }
		if (!c.isDefiniteClause()) { Utils.error("This code only handle definite clauses.  It was given: " + c); }

		Literal head = c.posLiterals.get(0);

		if (literalIsInlined(             head)) { Utils.error("This code assumes the HEAD is not an in-liner: "          + head + "."); } // TODO generalize
		if (literalIsaSupportingPredicate(head)) { Utils.error("This code assumes the HEAD is not a supporting literal: " + head + "."); }

        if (debugLevel > 1) {
			getStringHandler().reportVarsInFOPC(c);
			Utils.println("\n% handleInlinerAndSupportingClauses:\n% IN  " +  c.toString(Integer.MAX_VALUE));
		}

		List<Clause> results = help_handleInlinerAndSupportingClauses(c, 0);
		if (results == null) { Utils.waitHere("Got no results from in-lining: " + c); return null; }
		VisitedClauses clausesVisited = new VisitedClauses(100000);  // Watch for duplicates in the Supporting Clauses.
		List<Clause>   newResults     = new ArrayList<Clause>(results.size());
		for (Clause c2 : results) {  //Utils.waitHere("C2: " + c2);
			if (debugLevel > 3) { Utils.println("\n% Refactored clause: "); getStringHandler().reportVarsInFOPC(c2); }
			Clause newClause = (Clause) getStringHandler().renameAllVariables(c2);
			if (clausesVisited.alreadyInClosedList(getStringHandler(),newClause) != null) {
				 // Utils.waitHere("% Duplicate supporting clause: " + newClause); // Can turn this off later - but watch now for debugging purposes.
			} else {
				newResults.add(newClause);
				clausesVisited.addClauseToClosed(getStringHandler(),newClause); // OK to add the 'main clause' here, since it would be odd to have the same clause as a main and supporting clause.
			}
			if (debugLevel > 1) { 
				Utils.println("\n% OUT " + c2.toString(Integer.MAX_VALUE));
				getStringHandler().reportVarsInFOPC(c);
			}
		}
		if (debugLevel > 3) { stringHandler.printVariableCounters = hold; }
		return newResults;
	}
	private BindingList blToUse =  new BindingList();
	private List<Clause> help_handleInlinerAndSupportingClauses(Clause c, int depth) {

		if (c == null) { return null; }

		if (depth >  50) { Utils.severeWarning("Are some in-liners calling each other, producing an infinite loop?\n " + c); }
		if (depth > 100) { Utils.error("Seems to be an infinite loop.\n " + c); } // If this passed the severeWarning, and still a problem, simply give up.

        if (!c.isDefiniteClause()) { Utils.error("This code only handle definite clauses.  It was given: " + c); }
		
		List<Literal> newBodyLiterals = new ArrayList<Literal>(c.getLength());
		Set<Clause>   supporters      = null; // Remove duplicates when possible, but might not too look for variants via VisitedClauses instance.
		BindingList   overallBindings = new BindingList(); // Need to keep track of all the bindings necessary to make the in-lines match up.
		
		if (debugLevel > 3) { indentAndPrintln(depth, "Handle: " + c.toString(Integer.MAX_VALUE)); }
		if (c.negLiterals != null) for (Literal lit : c.negLiterals) {
			boolean isaInliner   = literalIsInlined(             lit);
			boolean isaSupporter = literalIsaSupportingPredicate(lit);
			
			// Here we assume any functions can/will be converted to a literal, e.g., they are inside a FOR-LOOP of some sort.
			// TODO - maybe we need to check the predicateName of lit and treat like we do for NOT (should also handle ONCE, CALL, etc ...), but risky to require names be in a list ...
			if (lit.predicateName != notPname && lit.numberArgs() > 0) for (Term t : lit.getArguments()) if (t instanceof Function) {
				Literal functAtLit = ((Function) t).convertToLiteral(getStringHandler());
				Iterable<Clause> definingClauses = getHornClauseKnowledgeBase().getPossibleMatchingBackgroundKnowledge(functAtLit, blToUse);
				if (definingClauses != null) for (Clause c2 : definingClauses) { // TODO clean up the duplicated code.
					blToUse.theta.clear();
					BindingList bl = literalMatchesDeterminateClause(functAtLit, c2, blToUse);
					if (bl == null) { continue; }
					List<Clause> recurResults = help_handleInlinerAndSupportingClauses(c2.applyTheta(bl.theta), depth + 1);
					if (supporters == null) { supporters = new HashSet<Clause>(1); }
					//	Utils.println("%   supporters = " + recurResults);
					if (Utils.getSizeSafely(recurResults) > 0) { supporters.addAll(recurResults); }
				}
			}
			
			if (isaInliner && isaSupporter) { 
				Utils.error("This code assumes a literal is not BOTH an in-liner and a 'supporting' literal: " + lit + "."); // TODO generalize
			} else if (lit.predicateName == notPname) { // We want to leave these as is, but need to collecting any 'supporters' they need.
				if (debugLevel > 3) { indentAndPrintln(depth, " NEGATION: " + lit); } 
				//Utils.println(  "%   current supporters = " + supporters);
				if (isaInliner || isaSupporter) { Utils.error("This code assumes the negation-by-failure predicate is not an in-liner nor a 'supporting' literal: " + lit + "."); } // TODO generalize
//				if (lit.numberArgs() != 1)      { Utils.error("Should a negation-by-failure have more than one argument? " + lit); }
//				Term arg = lit.getArgument(0);
//				if (!(arg instanceof SentenceAsTerm)) {
//                    Utils.error("Should a negation-by-failure's argument not be a SentenceAsTerm? " + arg);
//                }

                Clause clause = getStringHandler().getNegationByFailureContents(lit);
                if ( clause == null ) {
                    Utils.error("Expected term of negation to be Function or SentenceAsTerm.");
                }
                
                if ( clause.getNegLiteralCount() > 0 && clause.getPosLiteralCount() > 0 ) {
                    Utils.error("Negated clause should be composed of either positive literal or negative literal, but not both.");
                }

                if ( clause.getPosLiteralCount() == 0) {
                    // Make sure the negated clauses literals are positive
                    clause = clause.getStringHandler().getClause(clause.getNegativeLiterals(), clause.getPositiveLiterals());
                }

                if (Utils.getSizeSafely(clause.negLiterals) > 0) { Utils.error("Should not have negative literals inside a negation-by-failure.");         }
                if (Utils.getSizeSafely(clause.posLiterals) < 1) { Utils.error("Should have at least one positive literal inside a negation-by-failure."); }

                for (Literal pLit : clause.getPositiveLiterals()) {
                    if (literalIsaSupportingPredicate(pLit) || literalIsInlined(pLit)) { // If in-lined inside a NOT, need to convert to a SUPPORTER (could check if the body only has one literal ...).
                        // Next see if the body of the negation-by-failure has any-liners.  (I hate to duplicate this code, but seems easiest to do so.)
                        Iterable<Clause> definingClauses = getHornClauseKnowledgeBase().getPossibleMatchingBackgroundKnowledge(pLit, blToUse);
                        if (definingClauses != null) for (Clause c2 : definingClauses) {
                            blToUse.theta.clear();
                            BindingList bl = literalMatchesDeterminateClause(pLit, c2, blToUse);
                            if (bl == null) { continue; }

                            List<Clause> recurResults = help_handleInlinerAndSupportingClauses(c2.applyTheta(bl.theta), depth + 1);
                            if (supporters == null) { supporters = new HashSet<Clause>(1); }
                            //Utils.println("%   supporters = " + recurResults);
                            if (Utils.getSizeSafely(recurResults) > 0) { supporters.addAll(recurResults); }
                        }
                    }
                    else {
                       Clause litAsDefiniteClause = stringHandler.getClause(stringHandler.getLiteral(stringHandler.standardPredicateNames.trueName), pLit);
                        List<Clause> moreClauses = help_handleInlinerAndSupportingClauses(litAsDefiniteClause, depth+1);
                        if ( moreClauses != null && moreClauses.size() > 1 ) {
                            for (int i = 1; i < moreClauses.size(); i++) {
                                if (supporters == null) { supporters = new HashSet<Clause>(1); }
                                supporters.add(moreClauses.get(i));
                            }
                        }
                    }
				}
				//Utils.waitHere("How does the negation-by-failure look?");
				if (debugLevel > 3) { indentAndPrintln(depth, " NEGATION, add this to body: " + lit); }
				newBodyLiterals.add(lit);
			} else if (isaSupporter) {
				if (debugLevel > 3) { indentAndPrintln(depth, " SUPPORTER (add to body): " + lit); } 
				newBodyLiterals.add(lit);
				// Next see if the body of the supporter has any-liners.
				Iterable<Clause> definingClauses = getHornClauseKnowledgeBase().getPossibleMatchingBackgroundKnowledge(lit, null);
				if (definingClauses != null) for (Clause c2 : definingClauses)  {
					blToUse.theta.clear();
					BindingList bl = literalMatchesDeterminateClause(lit, c2, blToUse);
					if (bl == null) { continue; }
					//stringHandler.reportVarsInFOPC(c2);
					if (supporters == null) { supporters = new HashSet<Clause>(1); }
					List<Clause> recurResults = help_handleInlinerAndSupportingClauses(c2.applyTheta(bl.theta), depth + 1);
					
					if (Utils.getSizeSafely(recurResults) > 0) { supporters.addAll(recurResults); }
				}
			} else if (isaInliner) { // Need to replace this literal.
				if (debugLevel > 3) { indentAndPrintln(depth, " INLINE this lit: " + lit); } 
				if (overallBindings == null) { Utils.error("How did overallBindings = null"); }
				Clause newDefn = getUnifiedLiteralDefinition(depth, lit, overallBindings); // This will change overallBindings.
				if (debugLevel > 3) { indentAndPrintln(depth, " INLINE defn:   " + newDefn); }
				// Utils.println("\nInlining newDefn: ");  stringHandler.reportVarsInFOPC(newDefn); Utils.println("");
				
				List<Clause> recurResults = help_handleInlinerAndSupportingClauses(newDefn, depth + 1);
				if (Utils.getSizeSafely(recurResults) < 1) { Utils.error("recurResults = " + recurResults + " for newliner = " + lit + "\n newDefn = " + newDefn + "\n overall bindings =" + overallBindings); }
				
				if (supporters == null) { supporters = new HashSet<Clause>(1); }
				Clause        result       = recurResults.remove(0);
				if (debugLevel > 3) { indentAndPrintln(depth, " INLINE result: " + result.toString(Integer.MAX_VALUE)); }
				if (debugLevel > 3) { indentAndPrintln(depth, " Overall binds: " + bindingsToDetailedString(overallBindings)); }
				List<Literal> litsToInsert = result.negLiterals;
				// Utils.println("\n%"); for (int i = 0; i < depth; i++) { Utils.print("  "); } Utils.println("Inlining result: ");  stringHandler.reportVarsInFOPC(result);
				if (litsToInsert != null) for (Literal litToInsert : litsToInsert) { 
					if (debugLevel > 3) { indentAndPrintln(depth, " INLINE (add to body): " + litToInsert); }
					if (debugLevel > 3) { indentAndPrintln(depth, " INLINE (theta'ed):    " + litToInsert.applyTheta(overallBindings.theta)); } 
					newBodyLiterals.add(litToInsert);  // Would be an odd 'inliner' to have no body ...
				}
				else { Utils.waitHere("Have an inliner with no body! " + newDefn); }
				if (Utils.getSizeSafely(recurResults) > 0) { supporters.addAll(recurResults); }				
			} else { // Simply save.
				newBodyLiterals.add(lit);
			}			
		}
		Clause newClause = getStringHandler().getClause(c.posLiterals, newBodyLiterals, c.getExtraLabel());  // Note we are REUSING THE OLD HEAD.
		List<Clause> newListOfClauses = new ArrayList<Clause>();
		Clause newClauseBound = newClause.applyTheta(overallBindings.theta);
		if (debugLevel > 3) {
			indentAndPrintln(depth, "Final processing of clause:    " + c.toString(             Integer.MAX_VALUE));
			indentAndPrintln(depth, "As collected (plus orig head): " + newClause.toString(     Integer.MAX_VALUE));
			indentAndPrintln(depth, "                Overall binds: " + bindingsToDetailedString(overallBindings)); 
			indentAndPrintln(depth, "         After applying theta: " + newClauseBound.toString(Integer.MAX_VALUE));
		}
		//stringHandler.reportVarsInFOPC(newClauseBound);
		newListOfClauses.add(newClauseBound);
		if (Utils.getSizeSafely(supporters) < 1) { return newListOfClauses; }
		newListOfClauses.addAll(supporters); // These do not need to be unified since they are stand-alone.
		return newListOfClauses;		
	}
	
	private String bindingsToDetailedString(BindingList bl) {
		String result = "";
		if (bl == null || bl.theta == null) {
			result = "| ";
		}
		else for (Variable var : bl.theta.keySet()) {
			result += "| " + var + (getStringHandler().printVariableCounters ? "" : ":" + var.counter) + " -> ";
			 			 
			Term term = bl.theta.get(var);
			if (getStringHandler().printVariableCounters) { result += term; }
			else if (term instanceof Variable)       { result += term + ":" + ((Variable) term).counter; }
			else                                     { result += term; }
			result += " ";
		}
		return result + "|";
	}
	
	@SuppressWarnings("unused")
	private void indentAndPrint(int depth, String str) {
		Utils.print("% "); for (int i = 0; i < depth; i++) { Utils.print("  "); }
		Utils.print(str);		
	}
	
	private void indentAndPrintln(int depth, String str) {
		Utils.print("% "); for (int i = 0; i < depth; i++) { Utils.print("  "); }
		Utils.println(str);		
	}

    /**
     * @return the stringHandler
     */
    public HandleFOPCstrings getStringHandler() {
        return stringHandler;
    }

    /**
     * @param stringHandler the stringHandler to set
     */
    public void setStringHandler(HandleFOPCstrings stringHandler) {
        this.stringHandler = stringHandler;
    }

    /**
     * @return the hornClauseKnowledgeBase
     */
    public HornClausebase getHornClauseKnowledgeBase() {
        return hornClauseKnowledgeBase;
    }

    /**
     * @param hornClauseKnowledgeBase the hornClauseKnowledgeBase to set
     */
    public void setHornClauseKnowledgeBase(HornClausebase hornClauseKnowledgeBase) {
        this.hornClauseKnowledgeBase = hornClauseKnowledgeBase;
    }
	
}
