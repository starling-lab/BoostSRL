/**
 * 
 */
package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.ConsCell;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.LiteralAsTerm;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.FOPC.Variable;
import java.io.File;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import java.io.FileNotFoundException;
import edu.wisc.cs.will.Utils.condor.CondorFileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import edu.wisc.cs.will.ResThmProver.HornClauseProver;
import edu.wisc.cs.will.ResThmProver.HornClausebase;
import edu.wisc.cs.will.Utils.MapOfLists;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

/**
 * @author shavlik
 * 
 *  THIS PROBABLY BELONGS IN FOPC
 *
 *	In ILP, "background" Horn clauses can be used to deduce/derive additional features from the 'raw' (i.e., given) features.
 */
public class Precompute {

    public static boolean operateAsSilentlyAsPossible = false;

    public static boolean stopIfNoPrecomputesFound = true;

    //protected LearnOneClause                  innerLoop;
    //protected HandleFOPCstrings stringHandler;
    public boolean reportPrunes = true; // Sometimes we want ONLY the precomputed facts and not the pruning rules.  If so, set this to false.

    public boolean complainIfFileExists = false; // The caller should take care of this (and this check can be turned off at the caller).

    public static boolean alwaysRecreatePrecomputeFiles = false;

    private int counter;

    private int duplicates;

    //private Set<List<Term>> checked;
    private Set<String> checked; // I (JWS) changed this (1/5/11) since FUNCTIONS are not unique.
    //private   List<PredicateName>             predicatesToPrecompute;
    //private   Map<PredicateName,List<Clause>> precomputeClauses;

    //private MapOfLists<PredicateNameAndArity, Clause> clausesToPrecompute;
    public Precompute(/*LearnOneClause innerLoop, HandleFOPCstrings stringHandler*/) {
        //this.innerLoop     = innerLoop;
        //this.stringHandler = stringHandler;
    }
    
    private boolean precomputeFileAlreadyExists(String fileName) {
    	return (new CondorFile(fileName)).exists() || (new CondorFile(fileName + ".gz")).exists();
    }

    public List<Literal> processPrecomputeSpecifications(boolean overwritePrecomputeFileIfExists, HornClausebase clausebase, List<Sentence> sentencesToPrecompute, String fileName) throws SearchInterrupted {
        List<Literal> results = null;

        if (sentencesToPrecompute != null) {

            File file = new CondorFile(fileName);
            if (!alwaysRecreatePrecomputeFiles && !overwritePrecomputeFileIfExists && precomputeFileAlreadyExists(fileName)) {
                if (complainIfFileExists) {
                    Utils.waitHere("\n% Precomputing of' " + fileName + "' has previously occurred.\n% If this is incorrect, delete:\n%   '" + file.getPath() + "' (or its *.gz version).");
                }

            }
            else {
                MapOfLists<PredicateNameAndArity, Clause> clausesToPrecompute = convertPrecomputeSpecificationToDefiniteClauseMap(sentencesToPrecompute);

                results = createPrecomputedFile(clausesToPrecompute, clausebase, fileName);
            }
        }
        return results;
    }

    /** Converts a sentence to precompute into a definite clauses.
     * 
     * @param sentence
     * @param clausesToPrecompute MapOfLists that is populated
     */
    public MapOfLists<PredicateNameAndArity, Clause> convertPrecomputeSpecificationToDefiniteClauseMap(List<Sentence> sentencesToPrecompute) {

        MapOfLists<PredicateNameAndArity, Clause> clausesToPrecompute = new MapOfLists<PredicateNameAndArity, Clause>();

        for (Sentence sentence : sentencesToPrecompute) {
            List<Clause> clauses = sentence.convertToClausalForm();

            if (clauses != null) {
                for (Clause clause : clauses) {
                    if (!clause.isDefiniteClause()) {
                        Utils.error("Can only precompute Horn ('definite' actually) clauses.  You provided: '" + sentence + "'.");
                    }

                    PredicateNameAndArity pName = clause.getDefiniteClauseHead().getPredicateNameAndArity();
//			if (predicatesToPrecompute == null) {
//				predicatesToPrecompute = new ArrayList<PredicateName>(4);
//			}
//			if (!predicatesToPrecompute.contains(pName)) { predicatesToPrecompute.add(pName); }
//			if (precomputeClauses == null) {
//				precomputeClauses = new HashMap<PredicateName,List<Clause>>(4);
//			}
//			List<Clause> existingClauses = precomputeClauses.get(pName);
//			if (existingClauses == null) {
//				existingClauses = new ArrayList<Clause>(4);
//				precomputeClauses.put(pName, existingClauses);
//			}
//			existingClauses.add(clause);  // Might want to check for duplicates, but can't do a simple equal test.  So deal with this by checking for duplicates at the time grounded facts precomputed.
                    clausesToPrecompute.add(pName, clause);
                }
            }
        }

        return clausesToPrecompute;
    }

    /**
     * For each predicate to be precomputed:
     * 		a) collect all constants that match the types of its arguments
     * 		b) try to prove each possible grounded list of arguments
     * 		c) write these out to a precomputedFacts file
     * 		d) if literalsInBodyCanAppearInRules=true then create some guidance for prune()
     * 				e.g., if p(x) :- q(x), r(x) IS THE ONLY CLAUSE FOR p(x) then if p(x) is in a clause, no need to consider adding q(x) and r(x).
     * 		e) remove the clause(s) used to precompute from background knowledge (so they aren't again used)
     * @throws SearchInterrupted
     */
    public List<Literal> createPrecomputedFile(MapOfLists<PredicateNameAndArity, Clause> clausesToPrecompute, HornClausebase clausebase, String fileName) throws SearchInterrupted {

        List<Literal> precomputedLiterals = new ArrayList<Literal>();

        HornClauseProver prover = new HornClauseProver(clausebase.getStringHandler(), clausebase);
        prover.maxSearchDepth = java.lang.Integer.MAX_VALUE;
        prover.setMaxNodesToConsider(java.lang.Integer.MAX_VALUE); // Should we limit these?
        prover.setMaxNodesToCreate(java.lang.Integer.MAX_VALUE);
        Utils.println("\n% Precomputing '" + fileName + "'.");
        counter = 0;
        duplicates = 0;
        checked = null;

        if (clausesToPrecompute.isEmpty() == false) {

            counter = 0;
            duplicates = 0;
         // checked = new HashSet<List<Term>>(128);
            checked = new HashSet<String>(128);

            //HornClauseProverChildrenGenerator rulesAndFactsHolder = null;
            HandleFOPCstrings stringHandler = prover.getStringHandler();

            Utils.println("\n%%% Precomputing " + clausesToPrecompute.size() + " predicates.");
            PrintStream printStream = null;
            try {


                if (fileName != null) {

                    CondorFileOutputStream outStream = new CondorFileOutputStream(fileName);
                    printStream = new PrintStream(outStream, false); // (Don't) Request auto-flush (can slow down code).
                }

                if (printStream != null) {
                    printStream.println("%%%%%%%%%%%  DO NOT EDIT THIS FILE.  IT'LL BE RE-LOADED AS IS.  %%%%%%%%%%%");
                }
                if (printStream != null) {
                    printStream.println("%%%%%%%%%%%    Precomputing " + clausesToPrecompute.size() + " predicates at " + Utils.getDateTime() + ".");
                }

                if (printStream != null) {
                    printStream.print("\n" + stringHandler.getStringToIndicateCurrentVariableNotation()); // Record settings at time file created.
                }
                if (printStream != null) {
                    printStream.println(stringHandler.getStringToIndicateStringCaseSensitivity());
                }

                for (PredicateNameAndArity predicateNameAndArity : clausesToPrecompute.keySet()) {
                    PredicateName pName = predicateNameAndArity.getPredicateName();

                    Utils.println("\n% Saving all provable instances of '" + pName + "'");
                    if (printStream != null) {
                        printStream.println("\n// All provable instances of '" + pName + "'");
                    }

                    List<Clause> clauses = clausesToPrecompute.getValues(predicateNameAndArity);
                    checked.clear();

                    if (clauses == null) {
                        Utils.error("Have no clauses for this to-be-precomputed predicate: " + pName);
                    }

                    for (Clause c : clauses) {
                        int currentCounter    = counter;
                        int currentDuplicates = duplicates;
                        if (!c.isDefiniteClause()) {
                            Utils.error("Can only precompute DEFINITE clauses, but you provided: " + c);
                        } // Check again even if checked above.
                        String utilsC       =         c.toPrettyString("    ",   Integer.MAX_VALUE, 999, null);
                        String printStreamC = "/* " + c.toStringOneLine(         Integer.MAX_VALUE,      null) + " */"; // TODO - fix bug that leads to an inserted linefeed (max line length of some sort?). 
                        if (!operateAsSilentlyAsPossible) {
                            Utils.println("% using clause:   " + utilsC + "\n");
                            if (printStream != null) {
                                printStream.println("// using clause:\n   " + printStreamC + "\n");
                            }
                        }
                        Literal head = c.getDefiniteClauseHead();            //Utils.warning("head = " + head);
                        Collection<Variable> boundVariables = head.collectFreeVariables(null); //Utils.warning("boundVariables = " + boundVariables);
                        Literal negatedQuery = stringHandler.getLiteral(stringHandler.standardPredicateNames.findAll); // Use 'findAll' since we may want to remove duplicates our own way.
                        Variable resultList = stringHandler.getNewUnamedVariable();  //Utils.warning("resultList = " + resultList);

                        List<Term> arguments2 = new ArrayList<Term>(3);
                        arguments2.add(stringHandler.getLiteralAsTerm(head)); // Need to create all(head, body, result) - use all instead of findAll since we don't care about duplicates.
                        arguments2.add(stringHandler.getSentenceAsTerm(stringHandler.getClause(c.negLiterals, false), "precompute"));
                        arguments2.add(resultList);
                        negatedQuery.setArguments(arguments2);
                        // Utils.println("%    negatedQuery: '" + negatedQuery + "'.");

                        /* Try to prove each possible grounded list of arguments */
                        BindingList bindings = prover.prove(negatedQuery);
                        if (bindings == null) {
                            Utils.warning("%  Found no proofs of '" + head + "'.");
                            continue;
                        }
                        Term lookup = bindings.lookup(resultList);
                        if (lookup == null) {
                            Utils.warning("%  Found no proofs of '" + head + "'.");
                            continue;
                        }
                        Utils.println("%  Found " + Utils.comma(((ConsCell) lookup).length()) + " proofs of '" + head + "'.");
                        writeResultsToStream((ConsCell) lookup, printStream, precomputedLiterals);
                        boolean canPrune = (reportPrunes
                                && matchingFactExists(clausebase, head) == null
                                && matchingClauseHeadExists(clausebase, head, null) == null
                                && matchingClauseHeadExists(clausebase, head, c, clauses) == null);
                        // Can only prune predicates that are DETERMINED by the arguments in the clauseHead.  Also see lookForPruneOpportunities.
                        // Note: this code is 'safe' but it misses some opportunities.  E.g., if one has 'p(x) :- q(x,y)' AND THERE IS ONLY ONE POSSIBLE y FOR EACH x, then pruning is valid.  (Called "determinate literals" in ILP - TODO handle such cases.)
                        if (canPrune && reportPrunes) {
                            for (Literal lit : c.negLiterals) {
                                if (lit.collectFreeVariables(boundVariables) == null) {
                                    if (printStream != null) {
                                        printStream.println("prune: " + lit + ", " + head + ", warnIf(1). % precomputed from\n   " + printStreamC + "\n");
                                    }
                                }
                            }
                        }
                        if (!operateAsSilentlyAsPossible) {
                            Utils.println("\n// Precomputed a total of " + Utils.comma(counter - currentCounter) + " facts (and found " + Utils.comma(duplicates - currentDuplicates) + " duplications) from: '" + utilsC + ".'\n");
                            if (printStream != null) {
                                printStream.println("\n% Precomputed a total of " + Utils.comma(counter - currentCounter) + " facts (and found " + Utils.comma(duplicates - currentDuplicates) + " duplications) from:\n   " + printStreamC + "\n");
                            }
                        }
                        if (counter - currentCounter < 1) {
                            boolean okNotFound = head.predicateName.canBeAbsent(head.getArity());

                            if (!okNotFound || !operateAsSilentlyAsPossible) {
                                Utils.println("/* *** NOTE THAT NOTHING WAS FOUND FOR '" + head.toStringOneLine() + "'. *** */");
                                if (printStream != null) {
                                    printStream.println("/* ***** NOTE THAT NOTHING WAS FOUND FOR '" + head.toStringOneLine() + "'. ***** */");
                                }
                                if (!okNotFound) { // NOTE: this is a little buggy in that there might be some 'regular' facts as well as the precomputed ones, but a okIfUnknown can be added safely.
                                    Utils.println("// Possibly a typo?  If not, add to a BK file:   okIfUnknown: " + head.predicateName + "/" + head.getArity() + ".\n// NOTE: if the head of this rule appears in other rules, this error report might be incorrect."); // TODO fix this
                                    if (printStream != null) {
                                        printStream.println("// Possibly a typo?  If not, add to a BK file:   okIfUnknown: " + head.predicateName + "/" + head.getArity() + ".\n// NOTE: if the head of this rule appears in other rules, this error report might be incorrect.");
                                    }
                                    if (stopIfNoPrecomputesFound) {
                                        Utils.waitHere("Fix the above?");
                                    }
                                }
                                else {
                                    Utils.println("// That is OK since 'okIfUnknown' has been specified for it.\n");
                                    printStream.println("// That is OK since 'okIfUnknown' has been specified for it.\n");
                                }
                            }
                        }
                    }
                }
                if (!operateAsSilentlyAsPossible) {
                    Utils.println("\n\n%%% Precomputed a total of " + Utils.comma(counter) + " facts (and found " + Utils.comma(duplicates) + " duplications).  Done at " + Utils.getDateTime() + "\n");
                    if ( printStream != null ) printStream.println("\n\n%%% Precomputed a total of " + Utils.comma(counter) + " facts (and found " + Utils.comma(duplicates) + " duplications).  Done at " + Utils.getDateTime() + "\n");
                }
            } catch (FileNotFoundException e) {
                Utils.reportStackTrace(e);
                Utils.error("Unable to successfully open this file for writing:\n   " + fileName + ".\nError message:\n   " + e.getMessage());
            } catch (IOException e) {
            	 Utils.reportStackTrace(e);
                Utils.error("I/O exception with: " + fileName + ".\nError message:\n   " + e.getMessage());
            } finally {
                if (printStream != null) {
                    printStream.close();
                    Utils.compressFile(fileName);
                }
            }
        }

        return precomputedLiterals;
    }

    // This is written iteratively instead of recursively to prevent stack overflows (which have happened).
    private void writeResultsToStream(ConsCell list, PrintStream printStream, List<Literal> precomputedLiterals) {
        if (list == null || list.numberArgs() == 0) {
            return;
        }
        HandleFOPCstrings stringHandler = list.getStringHandler();
        Term    first = list.getArgument(0);
        ConsCell rest = (ConsCell) list.getArgument(1); // ConsCells should never have one argument.  This will crash on 'dotted pairs' (since 'rest' isn't a ConsCell) but we're not allowing them.

        int counterAtStart    = counter;
        int duplicatesAtStart = duplicates;
        while (true) {
            if (!first.isGrounded()) {
                Utils.error("This code assumes all precomputed items are grounded (" + stringHandler.getShortStringToIndicateCurrentVariableNotation() + "),\n so need to rethink what to do here:\n '" + first + "'.");
            } // TODO
            Literal inner = ((LiteralAsTerm) first).itemBeingWrapped;
       //   List<Term> checkItem = inner.getArguments();
            String checkItem = inner.toString(); // See if the print the same (and hence will be re-parsed the same).
            if (!checked.contains(checkItem)) {
                counter++;
                checked.add(checkItem); // TRUE here means "has been checked," and does NOT mean "is true."
                if ((counter - counterAtStart) % 10000 == 0) {
                    Utils.println("%     Have precomputed a total of " + Utils.comma(counter - counterAtStart) + " unique facts (about " + inner.predicateName + "/" + inner.numberArgs() + ") so far and found " + Utils.comma(duplicates - duplicatesAtStart) + " duplications.");
                }
                if (printStream != null) {
                    printStream.println(inner + ".");
                }
                precomputedLiterals.add(inner);
            }
            else {
                duplicates++;
            }
            if (rest.numberArgs() == 0) {
                return;
            }
            first = rest.getArgument(0);
            rest = (ConsCell) rest.getArgument(1);
        }
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

        BindingList bindings = new BindingList(); // Note: the unifier can change this.  But save on creating a new one for each fact.
        Iterable<Literal> factsToUse = clausebase.getPossibleMatchingFacts(query, null);

        if (factsToUse != null) {
            for (Literal fact : factsToUse) {
                bindings.theta.clear(); // Revert to the empty binding list.
                if (Unifier.UNIFIER.unify(fact, query, bindings) != null) {
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

        BindingList bindings = new BindingList(); // Note: the unifier can change this.
        for (Clause clause : listOfClauses) {
            if (!clause.isDefiniteClause()) {
                Utils.error("Call clauses passed to the method must be Horn.  You provided: '" + clause + "'.");
            }
            if (clause != ignoreThisClause) {
                if (clause == null) {
                    Utils.error("Cannot have clause=null here.");
                } // Should be checked elsewhere, but play it safe.
                bindings.theta.clear();
                if (Unifier.UNIFIER.unify(clause.posLiterals.get(0), query, bindings) != null) {
                    return clause;
                }
            }
        }
        return null;
    }
}
