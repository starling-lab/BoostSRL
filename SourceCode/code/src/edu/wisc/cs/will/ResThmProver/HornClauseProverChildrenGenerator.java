/**
 * 
 */
package edu.wisc.cs.will.ResThmProver;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import edu.wisc.cs.will.FOPC.Binding;
import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.ObjectAsTerm;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.PrettyPrinter;
import edu.wisc.cs.will.FOPC.PrettyPrinterOptions;
import edu.wisc.cs.will.FOPC.ProcedurallyDefinedPredicateHandler;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.SentenceAsTerm;
import edu.wisc.cs.will.FOPC.StringConstant;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.ChildrenNodeGenerator;
import edu.wisc.cs.will.stdAIsearch.OpenList;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

/**
 * @author shavlik
 *
 */
public class HornClauseProverChildrenGenerator extends ChildrenNodeGenerator<HornSearchNode> {

    public static final int debugLevel = 0;

    public static boolean stopIfNothingMatches = true;

    protected HornClauseContext context;

    protected BindingList bindingList; // Use this repeatedly to save some "new'ing."

    private long usedPredNameHash = 0;

    private long usedFirstArgHash = 0;

    private long usedAllArgsHash = 0;

    private long counter = 0;

    private long factResolutions = 0;
    
    private long maxOpen = 0;

    private boolean singleFactAndBackgroundLookup = false; // Use a newer style of background/fact lookup that is hopefully faster.

    private final Unifier unifier;

    /** Literal that tracks where we need to cut to when encountered.
     *
     * The cutLiteral is created the first time a cut is encountered
     * for a given Literal expansion.  It holds a copy of the
     * appropriate CutMarkerNode.
     * <p>
     * As clauses are added to the list of negated literals, their
     * actual cut Literals (if any) are replaced by this special Literal.
     * <p>
     * During SLD resolution, if this CutLiteral is expanded,
     * the nodes of the task's openList will popped until the
     * appropriate CutMarkerNode is encountered.  The CutMarkerNode is
     * not removed during this process since multiple cut in the same clause
     * could result in multiple clearing of the open list.
     * <p>
     * The cutLiteral is reset to null at the beginning of each literal
     * expansion via the resetCutMarkerAndCounters() method.
     */
    private CutLiteral cutLiteral = null;
    //private   Literal             cutMarkerLiteral = null;
    //private   LiteralAsTerm cutMarkerLiteralAsTerm = null;

    /** Search Node holding the place to be cut to when a cut is encountered.
     *
     * The cutMarkerNode is created the first time a cut is encountered
     * for a given Literal expansion.  It is held by the corresponding
     * CutLiteral.
     * <p>
     * When a cut literal is expanded, all nodes between the head of the
     * task's open list and the CutMarkerNode are removed.  The CutMarkerNode
     * is not removed during this process.
     * <P>
     * When expanded during SLD resolution, the cutMarkerNode is simply
     * discarded.
     * <p>
     * The cutMarkerNode is reset to null at the beginning of each literal
     * expansion via the resetCutMarkerAndCounters() method.
     *
     */
    private CutMarkerNode cutMarkerNode = null;

    /** Tracks whether the cutMarker has already been added during the expansion of the current literal.
     *
     * Only want to add CutMarkerNode per expansion of a single literal.
     * <p>
     * The cutMarkerAdded is reset to false at the beginning of each literal
     * expansion via the resetCutMarkerAndCounters() method.
     */
    private boolean cutMarkerAdded;

    /** Tracks the expansion we are on.
     *
     * Use getNextExpansion() to get the next expansion.
     * <P>
     * The nextExpansion is reset to 0 by resetCutMarkerAndCounters() at
     * the beginning of each collectChildren call.
     */
    private int nextExpansion;

    /** Caches a failLiteral locally.
     *
     */
    private final Literal failLiteral;

    /** Tracks the current proof step counter.
     *
     * Each time a literal is evaluated (it's expanded to include it's children),
     * this counter is increased by 1.
     * <P>
     * Since the children generator can remain around over the course of many proofs,
     * this number can get quite large.  The HornClauseProver could probably reset
     * this number occasionally if this become a problem.
     */
    protected static long proofCounter = 0;

    protected static long cutMarkerCounter = 0;

    private PrettyPrinterOptions prettyPrintOptions;

    /** Indicates the default spy level that should be set when a spy point is hit.
     *
     * 1: Tracing enabled.  Minimum to get anything.
     * 2: Tracing of subliterals.
     * 3: Detail tracing of subliterals including bindings.
     * 4: Everything plus a printout of the openlist (don't do this).
     */
    public static int defaultSpyLevel = 1;

    private int traceDepth = 0;

    /**
     *
     *
     * @param task
     * @param context
     */
    public HornClauseProverChildrenGenerator(HornClauseProver task, HornClauseContext context) {
        super(task);

        this.context = context;

        // Reuse this since for many cases the result will be the empty binding list or null.
        bindingList = new BindingList();
        unifier = Unifier.UNIFIER;

        HandleFOPCstrings stringHandler = context.getStringHandler();

        failLiteral = stringHandler.getLiteral(stringHandler.standardPredicateNames.fail);

        prettyPrintOptions = new PrettyPrinterOptions();
        prettyPrintOptions.setMaximumConsCells(5);
        prettyPrintOptions.setMultilineOutputEnabled(false);
        prettyPrintOptions.setSentenceTerminator("");
        prettyPrintOptions.setRenameVariables(false);

    }

    @Override
    public List<HornSearchNode> collectChildren(HornSearchNode hornSearchNode) throws SearchInterrupted {

        // <editor-fold defaultstate="collapsed" desc="Debugging Code...">
        List<HornSearchNode> result = null;


        if (hornSearchNode instanceof FailedTraceNode) {
            FailedTraceNode failedTraceNode = (FailedTraceNode) hornSearchNode;

            BindingList localVarBindings = getLocalBindings(failedTraceNode.failedLiteral, failedTraceNode);

            String litString = PrettyPrinter.print(failedTraceNode.failedLiteral, "", "", prettyPrintOptions, localVarBindings);

            Utils.println(String.format("          [%d.%d] failed: %s", failedTraceNode.parentProofCounter, failedTraceNode.parentExpansionIndex, litString));
            Utils.println("\n--------------------------------------------------------------------------------\n");
        }
//        else if (hornSearchNode instanceof CutMarkerNode) {
//            CutMarkerNode cutNode = (CutMarkerNode) hornSearchNode;
//
//                HornSearchNode nextOpenNode = task.open.peekFirst();
//                if (nextOpenNode == null) {
//                    Utils.println("          [" + cutNode.parentProofCounter + "." + cutNode.parentExpansionIndex + "] failed: " + cutNode + ".  No remaining open.  Failing proof.");
//                }
//                else {
//                    Utils.println("          [" + cutNode.parentProofCounter + "." + cutNode.parentExpansionIndex + "] failed: " + cutNode + ".  Backtracking to expansion [" + nextOpenNode.parentProofCounter + "." + nextOpenNode.parentExpansionIndex + "].");
//                }
//
//
//            Utils.println(String.format("[%6d] Encounter cut marker [%d.%d]: ", proofCounter++, cutNode.parentProofCounter, hornSearchNode.parentExpansionIndex));
//            Utils.println("\n--------------------------------------------------------------------------------\n");
//        }
        else {

            // This is some debugging code.  Please do not delete me.
            boolean oldPrintVars = getStringHandler().printVariableCounters;

            List<Literal> queryLiterals = hornSearchNode.clause.negLiterals;

            Literal literalBeingExpanded = queryLiterals.get(0);

            // <editor-fold defaultstate="collapsed" desc="Pop Stack Return Literals">
            while (literalBeingExpanded instanceof StackTraceLiteral) {
                StackTraceLiteral trace = (StackTraceLiteral) literalBeingExpanded;

                Literal traceLiteral = trace.getTraceLiteral();
                if (getTask().getTraceLevel() >= 2 || isSpyLiteral(traceLiteral)) {
                    
                    BindingList localVarBindings = null;

                    if (getTask().getTraceLevel() >= 3 || isSpyLiteral(traceLiteral)) {
                        localVarBindings = getLocalBindings(traceLiteral, hornSearchNode);
                    }

                    String litString = PrettyPrinter.print(traceLiteral, "", "", prettyPrintOptions, localVarBindings);

                    Utils.println(String.format("          [%d.%d] returned: %s", trace.getProofCounter(), trace.getExpansion(), litString));

                    Utils.println("\n--------------------------------------------------------------------------------\n");
                    
                }

                queryLiterals.remove(0);

                // If we got rid of the last literal, then this was a successful proof.
                // Return an empty child.
                if (queryLiterals.isEmpty()) {
                    //                if ( traceLevel >= 1 ) {
                    //                    System.out.println("true (proof successful).");
                    //                }
                    return Collections.singletonList(createChildWithNoNewLiterals(hornSearchNode, queryLiterals, null));
                }
                else {
                    literalBeingExpanded = queryLiterals.get(0);
                }
            }// </editor-fold>

            // <editor-fold defaultstate="collapsed" desc="Spy Enable">
            // Enable spy points...
            if (getTask().getTraceLevel() == 0 && getTask().getSpyEntries().includeElement(literalBeingExpanded.predicateName, literalBeingExpanded.numberArgs())) {
                if (getTask().getTraceLevel() < defaultSpyLevel) {
                    Utils.println("Spy point encountered on " + literalBeingExpanded.predicateName + "/" + literalBeingExpanded.numberArgs() + ".  Enabling tracing.");
                    getTask().setTraceLevel(defaultSpyLevel);
                }
            }// </editor-fold>

            BindingList printBindings = tracePrefix(hornSearchNode, literalBeingExpanded, prettyPrintOptions);

            // Do the actual work right here...
            result = collectChildrenActual(hornSearchNode);

            if (result != null && (getTask().getTraceLevel() >= 2 || isSpyLiteral(literalBeingExpanded))) {
                result.add(new FailedTraceNode(getTask(), literalBeingExpanded, null, hornSearchNode.parentProofCounter, hornSearchNode.parentExpansionIndex));
            }
            
            maxOpen = Math.max(getTask().open.size(), maxOpen);

            traceSuffix(hornSearchNode, result, queryLiterals, literalBeingExpanded, printBindings, prettyPrintOptions);

            getStringHandler().printVariableCounters = oldPrintVars;

            proofCounter++;
        }
        return result;
    }

    private BindingList getLocalBindings(Literal traceLiteral, HornSearchNode hornSearchNode) {
        BindingList localVarBindings = new BindingList();
        Collection<Variable> freeVars = traceLiteral.collectFreeVariables(null);
        for (Variable freeVar : freeVars) {
            Term freeBinding = hornSearchNode.getBinding(freeVar);
            if (freeBinding != null) {
                localVarBindings.addBinding(freeVar, freeBinding);
            }
        }
        return localVarBindings;
    }

    private BindingList tracePrefix(HornSearchNode hornSearchNode, Literal firstQueryLiteral, PrettyPrinterOptions ppo) {
        try {
            if (getTask().getTraceLevel() >= 2 || (getTask().getTraceLevel() >= 1 && isSpyLiteral(firstQueryLiteral))) {

                getStringHandler().printVariableCounters = true;

                BindingList printBindings = getLocalBindings(firstQueryLiteral, hornSearchNode);


                String headerString = String.format("[%6d] Collecting expansions of [%d.%d]: ", proofCounter, hornSearchNode.parentProofCounter, hornSearchNode.parentExpansionIndex);
                String litString = PrettyPrinter.print(firstQueryLiteral, "", PrettyPrinter.spaces(headerString.length() + 2), ppo, printBindings);

                Utils.println(headerString + litString);

                if (getTask().getTraceLevel() >= 3) {
                    List<Binding> bindings = hornSearchNode.collectBindingsToRoot();
                    if (bindings != null) {
                        Collections.sort(bindings, new Comparator<Binding>() {

                            public int compare(Binding o1, Binding o2) {
                                if (o1.var.counter > o2.var.counter) {
                                    return 1;
                                } // These are longs and we need an int, so cannot simply subtract.
                                if (o1.var.counter < o2.var.counter) {
                                    return -1;
                                }
                                else {
                                    return 0;
                                }
                            }
                        });
                    }

                    Utils.println("  Initial bindings: " + bindings);
                }

                if (getTask().getTraceLevel() >= 4) {
                    Utils.println("  OpenList: ");
                    for (int i = 0; i < getTask().open.size(); i++) {
                        Utils.println("    " + getTask().open.get(i));
                    }
                }

                return printBindings;
            }
        } catch (Throwable e) {
            Utils.println("Error occurred while tracing: " + e.toString() + ".");
        }

        return null;
    }

    private void traceSuffix(HornSearchNode lastExpandedNode, List<HornSearchNode> list, List<Literal> queryLiterals, Literal negatedLiteral, BindingList printBindings, PrettyPrinterOptions ppo) {
        try {

            if (getTask().getTraceLevel() >= 2 || (getTask().getTraceLevel() >= 1 && isSpyLiteral(negatedLiteral))) {
                if (list == null) {
                    HornSearchNode nextOpenNode = task.open.peekFirst();
                    String literalString = PrettyPrinter.print(negatedLiteral, "", "", ppo, printBindings);
                    if (nextOpenNode == null) {
                        Utils.println("          [" + lastExpandedNode.parentProofCounter + "." + lastExpandedNode.parentExpansionIndex + "] failed: " + literalString + ".  No remaining open.  Failing proof.");
                    }
                    else {
                        Utils.println("          [" + lastExpandedNode.parentProofCounter + "." + lastExpandedNode.parentExpansionIndex + "] failed: " + literalString + ".  Backtracking to expansion [" + nextOpenNode.parentProofCounter + "." + nextOpenNode.parentExpansionIndex + "].");
                    }
                }
                else {
                    Literal nextLiteral = queryLiterals.size() > 1 ? queryLiterals.get(1) : null;

                    int expansionCount = list.size();
                    if (list.get(expansionCount - 1) instanceof FailedTraceNode) {
                        expansionCount--;
                    }

                    String headerString = "           Found " + expansionCount + " expansions:";
                    Utils.println(headerString);                //for (HornSearchNode searchNode : list) {
                    for (int expansion = 0; expansion < expansionCount; expansion++) {
                        HornSearchNode searchNode = list.get(expansion);

                        HornSearchNode nextHornSearchNode = searchNode;
                        StringBuilder sb = new StringBuilder();
                        Clause c = nextHornSearchNode.clause;

                        if (searchNode.bindings != null) {
                            Set<Variable> printVars = new HashSet<Variable>(printBindings.getVariables());
                            for (Variable variable : printVars) {
                                Term reverseBinding = searchNode.bindings.lookup(variable);
                                if (reverseBinding instanceof Variable && reverseBinding != null) {
                                    printBindings.addBinding((Variable) reverseBinding, variable);
                                }
                            }
                        }

//                    if (getTask().getTraceLevel() >= 2) {
//                        String clauseString = PrettyPrinter.print(c, "", "", ppo, printBindings);
//                        sb.append(clauseString);
//                    }
//                    else {
                        if (negatedLiteral.predicateName == getStringHandler().standardPredicateNames.negationByFailure && nextHornSearchNode.parentExpansionIndex == 0) {
                            String clauseString = PrettyPrinter.print(c, "", "", ppo, printBindings);
                            sb.append(clauseString);
                        }
                        else if (nextHornSearchNode.parentExpansionIndex == -1) {
                            sb.append("cutMarker");
                        }
                        else {
                            int maxNewCount = c.getNegLiteralCount() - (queryLiterals.size() - 1);

                            int realLiteralCount = 0;  // count ignoring StackTraceLiterals
                            for (int i = 0; i < c.getNegLiteralCount(); i++) {
                                Literal lit = c.getNegLiteral(i);
                                if (lit instanceof StackTraceLiteral == false) {

                                    if (realLiteralCount > 0) {
                                        sb.append(" ^ ");
                                    }
                                    if (realLiteralCount < maxNewCount && c.negLiterals.get(i) != nextLiteral) {

                                        String clauseString = PrettyPrinter.print(c.negLiterals.get(i), "", "", ppo, printBindings);
                                        sb.append(clauseString);
                                    }
                                    else {
                                        if (realLiteralCount == 0) {
                                            sb.append("true ^ ");
                                        }
                                        sb.append("REST");
                                        realLiteralCount++;
                                        break;
                                    }

                                    realLiteralCount++;
                                }
                            }

                            if (realLiteralCount == 0) {
                                sb.append("true (proof successful)");
                            }
                        }
//                    }
                        Utils.println(String.format("             [%d.%d] %s", nextHornSearchNode.parentProofCounter, nextHornSearchNode.parentExpansionIndex, sb.toString()));

                        if (getTask().getTraceLevel() >= 2 || isSpyLiteral(negatedLiteral)) {

                            int bindingCount = 0;

                            StringBuilder stringBuilder = new StringBuilder();

                            stringBuilder.append("{");

                            Collection<Variable> freeVars = lastExpandedNode.clause.collectFreeVariables(null);
                            boolean first = true;
                            for (Variable freeVar : freeVars) {



                                Term to = searchNode.getBinding(freeVar);

                                if (to != null && to instanceof Variable == false) {
                                    String from = PrettyPrinter.print(freeVar, "", "", ppo, null);
                                    Term printBinding = printBindings.getMapping(freeVar);
                                    if (printBinding != null) {
                                        from = ((StringConstant) printBinding).getBareName();
                                    }

                                    if (first == false) {
                                        stringBuilder.append(", ");
                                    }

                                    stringBuilder.append(from).append(" => ").append(PrettyPrinter.print(to, "", "", ppo, printBindings));
                                    first = false;
                                    bindingCount++;
                                }
                            }

                            stringBuilder.append("}");
                            if (bindingCount > 0) {
                                Utils.println(String.format("                     with: %s.", stringBuilder.toString()));
                            }
                        }

                    }
                }

                
                Utils.println("           OpenList size =  "+ getTask().open.size() + ".  Max Open = " + maxOpen + ".");
                
                Utils.println("\n--------------------------------------------------------------------------------\n");
            }
        } catch (Throwable e) {
            Utils.println("Error occurred while tracing: " + e.toString() + ".");
        }
    }

    private boolean isSpyLiteral(Literal traceLiteral) {
        return getStringHandler().spyEntries.includeElement(traceLiteral.predicateName, traceLiteral.getArity());
    }

    private List<HornSearchNode> collectChildrenActual(HornSearchNode hornSearchNode) throws SearchInterrupted {
// </editor-fold>


        // Grab the first negated literal in this node, and find all "rules" in the theory that unify with it.
        // Each "resolvent" is a new node.  E.g., if node = (!P v !A v ... v !H) and the theory contains (P v !R v ... !Z)
        // then resolving P and !P produces (!A v ... v !H v !R v ... !Z) where theta=unify(P, P') is applied to the result.

        resetCutMarkerAndCounters();

        HandleFOPCstrings stringHandler = context.getStringHandler();

        if (HornClauseProver.debugLevel > 2) {
            Utils.println("\nNode being expanded: " + hornSearchNode);
        } //  + "\n open = " + ((HornClauseProver) task).open); }

        List<Literal> queryLiterals = hornSearchNode.clause.negLiterals;
        Literal negatedLiteral = queryLiterals.get(0);
        HornClauseProver thisTask = (HornClauseProver) this.task;
        PredicateName negatedLiteralPredName = negatedLiteral.predicateName;
        int numberOfQueryLiterals = queryLiterals.size();

        List<HornSearchNode> children = null;  // Collect the children nodes.

        if (HornClauseProver.debugLevel > 3) {
            Utils.println("% negatedLiteralPredName = '" + negatedLiteralPredName + "/" + negatedLiteral.numberArgs()
                    + "', |open| = " + Utils.getSizeSafely(((HornClauseProver) task).open)
                    + ", |query| = " + Utils.comma(numberOfQueryLiterals));
            if (queryLiterals != null) {
                Utils.print("%     query lit names: ");
                for (Literal lit : queryLiterals) {
                    Utils.print(" " + lit.predicateName);
                }
                Utils.println("");
            }
//												if (queryRemainder != null) {
//													Utils.print("%     remaining names: ");
//													for (Literal lit : queryRemainder) { Utils.print(" " + lit.predicateName); }
//													Utils.println("");
//												}
        }

        boolean noPredArgMatchFound = false;

        // <editor-fold defaultstate="collapsed" desc="Predefined Predicate Handling">
        if (thisTask.predefinedPredicateNamesUsedByChildCollector.contains(negatedLiteralPredName)) {

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.falseName || negatedLiteralPredName == stringHandler.standardPredicateNames.fail) {
                if (negatedLiteral.numberArgs() != 0) {
                    Utils.error("Cannot have arguments to the 'false' predicate.  You have: '" + negatedLiteral + "'");
                }
                return null;
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.trueName) { // Could have this be procedurally defined, but duplicate code here for simplicity.
                if (negatedLiteral.numberArgs() != 0) {
                    Utils.error("Cannot have arguments to the 'true' predicate.  You have: '" + negatedLiteral + "'");
                }
                if (children == null) {
                    children = new ArrayList<HornSearchNode>(1);
                } // For safety (e.g., in case this code gets moved) check if this exists.
                children.add(createChildWithNoNewLiterals(hornSearchNode, queryLiterals, null));
                return children;
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.repeat) {
                if (negatedLiteral.numberArgs() != 0) {
                    Utils.error("Cannot have arguments to the 'repeat' predicate.  You have: '" + negatedLiteral + "'");
                }
                if (children == null) {
                    children = new ArrayList<HornSearchNode>(1);
                } // For safety (e.g., in case this code gets moved) check if this exists.
                children.add(createChildWithNoNewLiterals(hornSearchNode, queryLiterals, null));
                children.add(hornSearchNode); // In a repeat, we backtrack to this same node.  'Repeat' can be viewed as: 'repeat. repeat :- repeat.'
                return children;
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.cutMarker) {
                if (HornClauseProver.debugLevel > 2) {
                    Utils.println("Discarding a cut marker.");
                }
                return null; // Don't want this to succeed.
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.cut) {
                if (HornClauseProver.debugLevel > 2) {
                    Utils.println("At a cut pred: " + negatedLiteral);
                }

                popOpenUptoThisCutMarker(negatedLiteral); // Discard everything up this cut's marker.
                // Add the remainder of this query following the cut.
                if (children == null) {
                    children = new ArrayList<HornSearchNode>(1);
                } // For safety (e.g., in case this code gets moved) check if this exists.
                children.add(createChildWithNoNewLiterals(hornSearchNode, queryLiterals, null));
                return children;
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.negationByFailure) {
                // Convert '\+ P' to
                //    dummy :- P, !, false.
                //    dummy :- true.

                Clause negationContents = stringHandler.getNegationByFailureContents(negatedLiteral);

                if (negationContents == null) {
                    Utils.error("Expected term of negation to be Function or SentenceAsTerm.");
                }

                if (negationContents.getNegLiteralCount() == 0) {
                    negationContents = stringHandler.getClause(negationContents.getNegativeLiterals(), negationContents.getPositiveLiterals());
                }

                createCutMarkerNode(hornSearchNode, negatedLiteral);

                List<Literal> expandedNotLiterals = new LinkedList<Literal>();
                if (negationContents.getNegativeLiterals() != null) {
                    expandedNotLiterals.addAll(negationContents.getNegativeLiterals());
                }
                if (cutLiteral == null) { Utils.waitHere(); }
                expandedNotLiterals.add(cutLiteral);
                expandedNotLiterals.add(failLiteral);

                HornSearchNode negationSucessNode = createChildWithMultipleNewLiterals(hornSearchNode, expandedNotLiterals, queryLiterals, null);
                HornSearchNode negationFailedNode = createChildWithMultipleNewLiterals(hornSearchNode, null, queryLiterals, null);

                if (children == null) {
                    children = new ArrayList<HornSearchNode>(3);
                }

                children.add(negationSucessNode);
                children.add(negationFailedNode);
                children.add(cutMarkerNode);

                return children;
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.then) {
                // Convert 'if P then Q else R' - note there is no backtracking across P due to the cut.
                //    if(P,Q,R) :- P, !, Q.
                //    if(P,Q,R) :- R. [note that R is optional]
                throw new UnsupportedOperationException();
//				if (HornClauseProver.debugLevel > 2) { Utils.println("At a THEN pred: " + negatedLiteral); }
//				if (negatedLiteral.getArguments() == null || negatedLiteral.numberArgs() < 1 || negatedLiteral.numberArgs() > 2) { Utils.error("This THEN is not properly structured: '" + negatedLiteral + "'"); }
//				if (children == null) { children = new ArrayList<HornSearchNode>(3); } // For safety (e.g., in case this code gets moved) check if this exists.
//
//                Clause clausePcutQ = (Clause) ((SentenceAsTerm) negatedLiteral.getArgument(0)).sentence;
//				if (cutMarkerLiteral != null) { Utils.error("cutMarkerLiteral should be null here!"); }
//				createCutMarkerNode(hornSearchNode);
//
//				// Need to replace the cut in clausePcutQ with cutMarkerLiteral so it knows its cutMarker.
//				if (clausePcutQ.negLiterals == null) { Utils.error("Should not have clausePcutQ=null here."); }
//
//				// Need to replace the cut in clausePcutQ with cutMarkerLiteral so it knows its cutMarker.
//				List<Literal> newNegLiterals = markCutLiterals(clausePcutQ.negLiterals);
//				newNegLiterals.addAll(queryRemainder);
//				Clause newClause1 = getStringHandler().getClause(newNegLiterals, false);
//				children.add(new HornSearchNode((HornSearchNode) nodeBeingExpanded, newClause1, null, proofCounter, expansion++));
//				if (negatedLiteral.numberArgs() == 2) {
//					Clause clauseR    = (Clause) ((SentenceAsTerm) negatedLiteral.getArgument(1)).sentence;
//					Clause newClause2 = clauseR.copyThenAppendToNegativeLiterals(queryRemainder);
//					if (newClause2.negLiterals == null) { Utils.error("Should not have negLiterals=null here."); }
//					children.add(new HornSearchNode((HornSearchNode) nodeBeingExpanded, newClause2, null, proofCounter, expansion++));
//				}
//                cutMarkerNode.parentProofCounter = 2;
//				children.add(cutMarkerNode); // Want the cut marker to be the OLDEST item in OPEN among these children.
//				return children;
            }

            // Handle "call(X)" by pulling out X and adding it back in.
            if (negatedLiteralPredName == stringHandler.standardPredicateNames.call || negatedLiteralPredName == stringHandler.standardPredicateNames.implicit_call) { //Utils.println("% CALL!");
                if (negatedLiteral.numberArgs() != 1) {
                    Utils.error("Must have ONE argument to the 'call' predicate.  You have: '" + negatedLiteral + "'");
                }
                Clause callBody = negatedLiteral.getArgument(0).asClause();

//                Literal callBodyAsLit = null;
//                if (callBody instanceof Function) {
//                    callBodyAsLit = ((Function) callBody).convertToLiteral(getStringHandler());
//                }
//                else if (callBody instanceof StringConstant) {
//                    StringConstant stringConstant = (StringConstant) callBody;
//                    PredicateName pn = stringHandler.getPredicateName(stringConstant.name);
//                    pn.setCanBeAbsent(0);
//                    callBodyAsLit = stringHandler.getLiteral(pn);
//                }
//                else {
//                    Utils.error("Call/1: Illegal Call Argument 1.  Must be Function or StringConstant.  Found: " + callBody + ".");
//                }
//				List<Literal> queryRemainderPlusCall = new ArrayList<Literal>(queryRemainder.size() + 1); // I think we could simply add callBodyAsLit to the FRONT and could skip the list copying, but play it safe, especially since this is likely to be rarely called.
//				queryRemainderPlusCall.add(   callBodyAsLit);
//				queryRemainderPlusCall.addAll(queryRemainder);
                HornSearchNode newNode = createChildWithMultipleNewLiterals(hornSearchNode, callBody.getPositiveLiterals(), queryLiterals, null);
                if (children == null) {
                    children = new ArrayList<HornSearchNode>(1);
                }
                //if (HornClauseProver.debugLevel > 2) { Utils.println("% CALL body = " + callBodyAsLit + ", |query remainder| = " + Utils.getSizeSafely(queryRemainder)); }
                children.add(newNode);
                return children;
            }

            // Here is the definition for once: once(G) :- call(G), !.
            if (negatedLiteralPredName == stringHandler.standardPredicateNames.once) {
                if (negatedLiteral.numberArgs() != 1) {
                    Utils.error("Must have ONE argument to the 'once' predicate.  You have: '" + negatedLiteral + "'");
                }
                // Need to convert the body of the once() to clause form (this is now done at parse time) and add a cut at the end.  BE SURE THE CLAUSE IS MARKED AS CONTAINING A CUT!
                // Then need to add this internal clause to
                SentenceAsTerm onceBody = (SentenceAsTerm) negatedLiteral.getArgument(0); // Count on these being the proper type, so that casting works.
                Clause clauseBody = (Clause) onceBody.sentence;

                if (cutMarkerNode != null) {
                    Utils.error("cutMarkerLiteral should be null here!");
                }
                createCutMarkerNode(hornSearchNode, negatedLiteral);

                List<Literal> expandedOnceLiterals = new LinkedList<Literal>();
                if (clauseBody.negLiterals != null) {
                    expandedOnceLiterals.addAll(clauseBody.negLiterals);
                }
                Utils.println("once: Adding a cut marker.");  if (cutLiteral == null) { Utils.waitHere(); }
                expandedOnceLiterals.add(cutLiteral);

                HornSearchNode expandedOnceNode = createChildWithMultipleNewLiterals(hornSearchNode, expandedOnceLiterals, queryLiterals, null);
                if (children == null) {
                    children = new ArrayList<HornSearchNode>(2);
                }
                children.add(expandedOnceNode);
                children.add(cutMarkerNode); // Want the cut to be the OLDEST item in OPEN among these children.
                return children;
            }

            // Handle a findAll (and all, setOf, bagOf, etc)
            if (negatedLiteralPredName == stringHandler.standardPredicateNames.findAll || negatedLiteralPredName == stringHandler.standardPredicateNames.all
                    || negatedLiteralPredName == stringHandler.standardPredicateNames.setOf || negatedLiteralPredName == stringHandler.standardPredicateNames.bagOf
                    || negatedLiteralPredName == stringHandler.standardPredicateNames.countProofs || negatedLiteralPredName == stringHandler.standardPredicateNames.countUniqueBindings) {
                Term term, list;
                Clause goal;
                if (negatedLiteralPredName == stringHandler.standardPredicateNames.countProofs || negatedLiteralPredName == stringHandler.standardPredicateNames.countUniqueBindings) {
                    if (negatedLiteral.numberArgs() != 2) {
                        Utils.error("Must have TWO arguments to the '" + negatedLiteralPredName + "' predicate.  You have: '" + negatedLiteral + "'");
                    }
                    term = negatedLiteral.getArgument(0); // Only needed for countUniqueBindings(), but stick in here anyway so internal rep's consistent across these variants.
                    goal = (Clause) ((SentenceAsTerm) term).sentence;
                    list = negatedLiteral.getArgument(1);
                }
                else {
                    if (negatedLiteral.numberArgs() != 3) {
                        Utils.error("Must have THREE arguments to the '" + negatedLiteralPredName + "' predicate.  You have: '" + negatedLiteral + "'");
                    }
                    term = negatedLiteral.getArgument(0);
                    goal = (Clause) ((SentenceAsTerm) negatedLiteral.getArgument(1)).sentence;
                    list = negatedLiteral.getArgument(2);
                }
                PredicateName collectorPred = getStringHandler().getPredicateName(negatedLiteralPredName + "Collector");
                // Collect ALL proofs of goal, which must be a literal or a conjunct - actually, a clause with only negative literals.
                // And for each proof, save 'term' (which presumably shares variables with 'goal') in a list.
                // Unify this list with 'list' as the final step.  EXCEPTION: the count* variants return the LENGTH of this list.
                ObjectAsTerm answersList = getStringHandler().getObjectAsTerm(getStringHandler().getNil(), false); // Need to WRAP this since we'll be "cons'ing" to the front and we need something to hold the resulting consCell.
                List<Term> collectorArgs = new ArrayList<Term>(2); // This will collect all the answers.
                collectorArgs.add(term);
                collectorArgs.add(answersList);
                List<Term> resultArgs = new ArrayList<Term>(3); // This will return once all the answers have been collected. The 3rd argument is simply there so that we can easily differentiate the two.
                resultArgs.add(list);
                resultArgs.add(answersList);
                resultArgs.add(term); // Might as well put something useful here ..
                Literal collector = getStringHandler().getLiteral(collectorPred, collectorArgs);

                List<Literal> collectorLiterals = new LinkedList<Literal>();
                if (goal.negLiterals != null) {
                    collectorLiterals.addAll(goal.negLiterals);
                }
                collectorLiterals.add(collector);

                if (HornClauseProver.debugLevel > 2) {
                    Utils.println("\n*** goal:             " + goal);
                }
                if (HornClauseProver.debugLevel > 2) {
                    Utils.println("*** term:             " + term);
                }
                if (HornClauseProver.debugLevel > 2) {
                    Utils.println("*** collectorArgs:    " + collectorArgs);
                }
                if (HornClauseProver.debugLevel > 2) {
                    Utils.println("*** negatedLiteral:   " + negatedLiteral);
                }
                if (HornClauseProver.debugLevel > 2) {
                    Utils.println("\n*** Collector literals: " + collectorLiterals);
                }

                Literal answerLiteral = getStringHandler().getLiteral(collectorPred, resultArgs);

                HornSearchNode collectNode = createChildWithMultipleNewLiterals(hornSearchNode, collectorLiterals, queryLiterals, null);
                HornSearchNode answerNode = createChildWithSingleNewLiteral(hornSearchNode, answerLiteral, queryLiterals, null);

                if (children == null) {
                    children = new ArrayList<HornSearchNode>(1);
                }
                children.add(collectNode);
                children.add(answerNode);
                if (HornClauseProver.debugLevel > 2) {
                    Utils.println("  FINDALL returning " + Utils.comma(children) + " children.");
                }
                return children;
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.spy) {

                for (int i = 0; i < negatedLiteral.numberArgs(); i++) {

                    Term arg = negatedLiteral.getArgument(i);
                    PredicateNameAndArity predicateNameArity = getPredicateNameAndArity(arg);

                    if (predicateNameArity != null) {
                        getTask().getSpyEntries().addLiteral(predicateNameArity);
                    }
                }

                if (children == null) {
                    children = new ArrayList<HornSearchNode>(1);
                }
                children.add(createChildWithMultipleNewLiterals(hornSearchNode, null, queryLiterals, null));
                return children;
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.nospy) {

                for (int i = 0; i < negatedLiteral.numberArgs(); i++) {

                    Term arg = negatedLiteral.getArgument(i);
                    PredicateNameAndArity predicateNameArity = getPredicateNameAndArity(arg);

                    if (predicateNameArity != null) {
                        getTask().getSpyEntries().removeLiteral(predicateNameArity);
                    }
                }

                if (children == null) {
                    children = new ArrayList<HornSearchNode>(1);
                }
                children.add(createChildWithMultipleNewLiterals(hornSearchNode, null, queryLiterals, null));
                return children;
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.nospyall) {

                getTask().getSpyEntries().clear();

                if (children == null) {
                    children = new ArrayList<HornSearchNode>(1);
                }
                children.add(createChildWithNoNewLiterals(hornSearchNode, queryLiterals, null));
                return children;
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.trace) {

                if (negatedLiteral.numberArgs() != 1) {
                    Utils.error("trace must have 1 argument.  You have: '" + negatedLiteral + "'");
                }

                Term arg1 = negatedLiteral.getArgument(0);
                if (arg1 instanceof NumericConstant == false) {
                    Utils.error("trace/1 argument must be a number.");
                }

                NumericConstant numericConstant = (NumericConstant) arg1;
                int traceLevel = numericConstant.value.intValue();

                getTask().setTraceLevel(traceLevel);

                if (children == null) {
                    children = new ArrayList<HornSearchNode>(1);
                }
                children.add(createChildWithMultipleNewLiterals(hornSearchNode, null, queryLiterals, null));
                return children;
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.notrace) {

                if (negatedLiteral.numberArgs() != 0) {
                    Utils.error("notrace must have 0 arguments.  You have: '" + negatedLiteral + "'");
                }

                getTask().setTraceLevel(0);

                if (children == null) {
                    children = new ArrayList<HornSearchNode>(1);
                }
                children.add(createChildWithNoNewLiterals(hornSearchNode, queryLiterals, null));
                return children;
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.retract) {

                if (negatedLiteral.numberArgs() != 1) {
                    Utils.error("retract must have 1 arguments.  You have: '" + negatedLiteral + "'");
                }

                boolean successful = false;

                Sentence termAsSentence = negatedLiteral.getArgument(0).asSentence();
                if (termAsSentence instanceof DefiniteClause) {
                    DefiniteClause definiteClause = (DefiniteClause) termAsSentence;

                    bindingList = new BindingList();

                    // Do the first 'asserted(A), removeFromClausebase(A)' via calling retract.
                    successful = getTask().getClausebase().retract(definiteClause, bindingList);
                }

                if (successful) {
                    if (children == null) {
                        children = new ArrayList<HornSearchNode>(2);
                    }

                    // retract is essentially defined as:
                    //   retract(A) :- asserted(A), removeFromClausebase(A).
                    //
                    // The first child is successful proof corresponding to a sucessful asserted(A), removeFromClausebase(A).
                    // The asserted(A), removeFromClausebase(A) was done above.
                    children.add(createChildWithNoNewLiterals(hornSearchNode, queryLiterals, bindingList));

                    // The second child allows for the backtracking over the retract to remove multiple clauses from the clausebase.
                    children.add(createChildWithSingleNewLiteral(hornSearchNode, negatedLiteral, queryLiterals, null));
                    return children;
                }
                else {
                    return null;
                }
            }

            if (negatedLiteralPredName == stringHandler.standardPredicateNames.retractall) {

                if (negatedLiteral.numberArgs() != 1) {
                    Utils.error("retractall must have 1 arguments.  You have: '" + negatedLiteral + "'");
                }

                boolean successful = false;

                Sentence termAsSentence = negatedLiteral.getArgument(0).asSentence();
                if (termAsSentence instanceof Literal) {
                    DefiniteClause definiteClause = (DefiniteClause) termAsSentence;

                    successful = getTask().getClausebase().retractAllClauseWithHead(definiteClause);
                }

                if (successful) {
                    if (children == null) {
                        children = new ArrayList<HornSearchNode>(1);
                    }
                    children.add(createChildWithNoNewLiterals(hornSearchNode, queryLiterals, bindingList));
                    return children;
                }
                else {
                    return null;
                }
            }
        }// </editor-fold>

        // <editor-fold defaultstate="collapsed" desc="procedurally defined predicate handling">

        // See if there is a special procedurally defined predicate, and if so, call its handler.
        int arity = negatedLiteral.numberArgs();
        ProcedurallyDefinedPredicateHandler userProcedurallyDefinedPredicateHandlerInstance = getClausebase().getUserProcedurallyDefinedPredicateHandler();
        if (userProcedurallyDefinedPredicateHandlerInstance != null && userProcedurallyDefinedPredicateHandlerInstance.canHandle(negatedLiteralPredName, arity)) {
            if (HornClauseProver.debugLevel > 2) {
                Utils.println("%      Chosen resolvent is a USER procedurally defined predicate: " + negatedLiteral);
            }
            if (bindingList.theta.size() > 0) {
                bindingList.theta.clear();
            } // Revert to the empty binding list.
            BindingList theta = userProcedurallyDefinedPredicateHandlerInstance.handle(context, negatedLiteral, unifier, bindingList);
            if (theta != null) {
                HornSearchNode newNode = createChildWithNoNewLiterals(hornSearchNode, queryLiterals, theta.copy());

                if (children == null) {
                    children = new ArrayList<HornSearchNode>(1);
                } // Wait to create until needed.
                if (HornClauseProver.debugLevel > 3) {
                    newNode.reportNodePredicates();
                }
                children.add(newNode);
                return children;
            }
            if (HornClauseProver.debugLevel > 2) {
                Utils.println("%      USER procedurally defined literal failed.");
            }
            return null;  // If the procedurally defined predicate failed, then this search path has failed.
        }
        // See if this is a built-in (into the ResolutionTheoremProver) predicate that needs to be handled by special code.
        ProcedurallyDefinedPredicateHandler builtinProcedurallyDefinedPredicateHandlerInstance = getClausebase().getBuiltinProcedurallyDefinedPredicateHandler();
        if (builtinProcedurallyDefinedPredicateHandlerInstance.canHandle(negatedLiteralPredName, arity)) {
            if (HornClauseProver.debugLevel > 2) {
                Utils.println("%      Chosen resolvent is a built-in procedurally defined predicate: " + negatedLiteral);
            }
            if (bindingList.theta.size() > 0) {
                bindingList.theta.clear();
            } // Revert to the empty binding list.
            BindingList theta = builtinProcedurallyDefinedPredicateHandlerInstance.handle(context, negatedLiteral, unifier, bindingList);
            if (theta != null) {

                HornSearchNode newNode = createChildWithNoNewLiterals(hornSearchNode, queryLiterals, theta);

                if (children == null) {
                    children = new ArrayList<HornSearchNode>(1);
                } // Wait to create until needed.
                if (HornClauseProver.debugLevel > 3) {
                    newNode.reportNodePredicates();
                }
                children.add(newNode);
                return children;
            }
            if (HornClauseProver.debugLevel > 2) {
                Utils.println("      Built-in procedurally defined literal failed.");
            }
            return null;  // If the built-in procedurally defined predicate failed, then this search path has failed.
        }// </editor-fold>

        // If we get here, there is no special handling to do.  Just look the literal up in the clause base and
        // handle it appropriately.
        if (HornClauseProver.debugLevel > 2) {
            Utils.println(" Chosen resolvent: " + negatedLiteral);
        }

        if ( singleFactAndBackgroundLookup ) {
            boolean predIsInBackgroundKnowledge = getClausebase().checkForPossibleMatchingBackgroundKnowledge(negatedLiteralPredName, arity);
            if ( predIsInBackgroundKnowledge ) {
                noPredArgMatchFound = !predIsInBackgroundKnowledge;
                children = createChildrenForMixedBackgroundAndFacts(hornSearchNode, negatedLiteral, queryLiterals);
            }
        }
        else {
            boolean predIsInBackgroundKnowledge = getClausebase().checkForPossibleMatchingBackgroundKnowledge(negatedLiteralPredName, arity);
            boolean predIsInFacts = getClausebase().checkForPossibleMatchingFacts(negatedLiteralPredName, arity);

            noPredArgMatchFound = (predIsInBackgroundKnowledge == false && predIsInFacts == false);

            // Handle the cases where there are only facts, only background knowledge, and where
            // the two are mixed together...
            if (predIsInFacts == true && predIsInBackgroundKnowledge == false) {      //Utils.println("    predIsInFacts");
                children = createChildrenForFactsOnly(hornSearchNode, negatedLiteral, queryLiterals);
            }
            else if (predIsInFacts == true || predIsInBackgroundKnowledge == true) {  //Utils.println("    predIs BOTH");
                children = createChildrenForMixedBackgroundAndFacts(hornSearchNode, negatedLiteral, queryLiterals);
            }
        }

        if (noPredArgMatchFound && !negatedLiteralPredName.canBeAbsent(arity)) {
            if (stopIfNothingMatches) { Utils.waitHereErr("There is no fact nor clause nor built-in predicate matching: '" + negatedLiteralPredName + "/" + arity + "'.\n  Possibly a typo?  If not, add to the BK file:   okIfUnknown: " + negatedLiteralPredName + "/" + arity + "."); }

            negatedLiteralPredName.setCanBeAbsent(arity);
        }
        if (cutMarkerNode != null) {
            if (HornClauseProver.debugLevel > 2) {
                Utils.println("*** ADD THIS CUT MARKER: " + cutMarkerNode);
            }
            children.add(children.size(), cutMarkerNode);
        }
        if (HornClauseProver.debugLevel > 2) {
            Utils.println("  Children being added: " + Utils.limitLengthOfPrintedList(children, 10));
        }
        return children;
    }

    private List<HornSearchNode> createChildrenForFactsOnly(HornSearchNode hornSearchNode, Literal negatedLiteral, List<Literal> queryLiterals) {
        List<HornSearchNode> children = null;

        int arity = negatedLiteral.numberArgs();

        Iterable<Literal> matchingFacts = getClausebase().getPossibleMatchingFacts(negatedLiteral, null);
        if (HornClauseProver.debugLevel > 2 && ++counter % 10000000 == 0) {
            Utils.println("% usedPredNameHash=" + usedPredNameHash + " usedFirstArgHash=" + usedFirstArgHash + " usedAllArgsHash=" + usedAllArgsHash + " factResolutions=" + factResolutions);
        }

        if (matchingFacts != null) {
            for (Literal fact : matchingFacts) {
                factResolutions++;

//                if (bindingList.theta.size() > 0) {
//                    bindingList.theta = new HashMap<Variable, Term>();
//                } // Revert to the empty binding list.
                BindingList theta = unify(negatedLiteral, fact, new BindingList());

                if (theta != null && fact.containsFreeVariablesAfterSubstitution(theta)) { // If any variables in the fact are unbound, need to rename then rebind.
                    // TAW: I don't think that facts are supposed to have free variables.  However,
                    // TAW: we only print a warning and don't restrict it, so I guess we need to do this step.
                    Utils.println("Since variables in the fact remain after unification, need to rename '" + fact + "'.");
                    fact = (Literal) fact.copyAndRenameVariables();
                    bindingList.theta.clear();
                    theta = unify(negatedLiteral, fact, new BindingList());
                }

                if (theta != null) {
                    HornSearchNode newNode = createChildWithNoNewLiterals(hornSearchNode, queryLiterals, theta);

                    if (children == null) {
                        children = new ArrayList<HornSearchNode>();
                    }
                    children.add(newNode); // Do NOT return here.
                }
            }
        }

        if (HornClauseProver.debugLevel > 2) {
            Utils.println("  returning " + Utils.comma(children) + " children.");
        }
        return children;
    }

    private List<HornSearchNode> createChildrenForMixedBackgroundAndFacts(HornSearchNode hornSearchNode, Literal negatedLiteral, List<Literal> queryLiterals) {
        List<HornSearchNode> children = null;

        int arity = negatedLiteral.numberArgs();

        Collection<DefiniteClause> possibleMatchingAssertions = getClausebase().getPossibleMatchingAssertions(negatedLiteral, null);

        if (possibleMatchingAssertions != null) {

            for (DefiniteClause definiteClause : possibleMatchingAssertions) {  //Utils.println("Consider: " + clause);
                Literal ruleHead = definiteClause.getDefiniteClauseHead();

//                if (bindingList.theta.size() > 0) {
//                    bindingList.theta.clear();
//                } // Revert to the empty binding list.

                BindingList theta = unify(negatedLiteral, ruleHead, new BindingList());

                if (theta != null && definiteClause.isDefiniteClauseFact() == false && definiteClause.containsFreeVariablesAfterSubstitution(theta)) { // If any variables in the clause are unbound (even in the BODY!), need to rename then rebind.
                    definiteClause = (DefiniteClause) definiteClause.getDefiniteClauseAsClause().copyAndRenameVariables();
                    ruleHead = definiteClause.getDefiniteClauseHead();
                   // bindingList.theta.clear();

                    // We have to rebind theta since the clause is a copy...
                    theta = unify(negatedLiteral, ruleHead, new BindingList());
                    if (theta == null) {
                        Utils.println("Since variables in the new clause remain after unification, need to rename '" + definiteClause + "'.");
                        Utils.println("  renamed clause: " + definiteClause.getDefiniteClauseAsClause().toPrettyString("     ", Integer.MAX_VALUE, theta));
                        Utils.println("  negatedLiteral= " + negatedLiteral);
                        Utils.println("  ruleHead      = " + ruleHead);
                        Utils.println("  theta         = " + theta);
                        Utils.error("What happened to theta???");
                    }
                }

                if (theta != null) {
                    List<Literal> ruleBody = definiteClause.getDefiniteClauseBody();

                    if (definiteClause.isDefiniteClauseRule()) {
                        Clause clause = definiteClause.getDefiniteClauseAsClause();
                        if (!cutMarkerAdded && clause.getBodyContainsCut()) {
                            createCutMarkerNode(hornSearchNode, negatedLiteral);
                        }
                        if (clause.getBodyContainsCut()) {
                            ruleBody = markCutsInClauseWithCurrentCutMarker(ruleBody);
                        }
                    }

                    HornSearchNode newNode;
                    if (ruleBody == null) {
                        newNode = createChildWithNoNewLiterals(hornSearchNode, queryLiterals, theta);
                    }
                    else {
                        newNode = createChildWithMultipleNewLiterals(hornSearchNode, ruleBody, queryLiterals, theta);
                    }

                    if (children == null) {
                        children = new ArrayList<HornSearchNode>();
                    }
                    children.add(newNode);
                }
            }
        }

        return children;
    }

    private BindingList unify(Literal lit1, Literal lit2, BindingList bindingList) {
        Unifier.increaseUnificationCount();
        return unifier.unify(lit1, lit2, bindingList);
    }

    // Assume lit1 has FEWER variables (only impacts efficiency).
    protected boolean sharedVariables(Literal lit1, Literal lit2) {
        Collection<Variable> varsInList1 = lit1.collectFreeVariables(null);
        if (varsInList1 == null) {
            return false;
        }
        Collection<Variable> varsInList2 = lit2.collectFreeVariables(null);
        if (varsInList2 == null) {
            return false;
        }
        for (Variable v1 : varsInList1) {
            if (varsInList2.contains(v1)) {
                return true;
            }
        }
        return false;
    }

    private void resetCutMarkerAndCounters() {
        cutMarkerAdded = false;
        cutLiteral     = null;
        cutMarkerNode  = null; 

        nextExpansion = 0;
    }

    private void createCutMarkerNode(HornSearchNode hornSearchNode, Literal literalBeingCut) {
        if (cutMarkerAdded == false) { 
            cutMarkerAdded = true;
            cutMarkerNode = new CutMarkerNode(hornSearchNode, literalBeingCut, proofCounter);
            cutLiteral    = new CutLiteral(getStringHandler(), cutMarkerNode);
        }
    }

    /** Create a new list, where all the cuts are replaced by new cuts that have the argument cutMarkerLiteralAsTerm.
     *
     * @param ruleBody
     * @return
     */
    private List<Literal> markCutsInClauseWithCurrentCutMarker(List<Literal> ruleBody) {
        List<Literal> newRuleBody = new ArrayList<Literal>(ruleBody.size());
        for (Literal lit : ruleBody) {
            if (lit.predicateName == getStringHandler().standardPredicateNames.cut) {
            	if (cutLiteral == null) { Utils.waitHere(); }
                newRuleBody.add(cutLiteral);
            }
            else {
                newRuleBody.add(lit);
            }
        }
        if (HornClauseProver.debugLevel > 2) {
            Utils.println("markCutLiterals: " + newRuleBody);
        }
        return newRuleBody;
    }

    public void popOpenUptoThisCutMarker(Literal cutLiteral) {

        CutMarkerNode markerNode = ((CutLiteral) cutLiteral).cutMarkerNode;

        OpenList<HornSearchNode> openList = getTask().open;

        while (openList.isEmpty() == false && openList.peek() != markerNode) {
            openList.popOpenList();
        }

        if (openList.isEmpty()) {
            Utils.error("Pop'ed all of OPEN but did not find: '" + markerNode + "'");
        }

        if (HornClauseProver.debugLevel > 2) {
            Utils.println("Final OPEN = " + openList);
        }
    }

    public int getNextExpansion() {
        return nextExpansion++;
    }

    @Override
    public void clearAnySavedInformation(boolean insideIterativeDeepening) {
        return;  // We want the theory to persist across searches.
    }

    public HandleFOPCstrings getStringHandler() {
        return context.getStringHandler();
    }

    public HornClausebase getClausebase() {
        return context.getClausebase();
    }

    public HornClauseProver getTask() {
        return (HornClauseProver) task;
    }

    private PredicateNameAndArity getPredicateNameAndArity(Term arg) {

        HandleFOPCstrings stringHandler = getStringHandler();

        PredicateNameAndArity predicateNameArity = null;
        PredicateName name = null;
        int arity = -1;
        if (arg instanceof StringConstant) {
            StringConstant stringConstant = (StringConstant) arg;
            String contents = stringConstant.getName();
            int index = contents.indexOf("/");
            if (index == -1) {
                name = stringHandler.getPredicateName(contents);
            }
            else {
                String namePart = contents.substring(0, index);
                String arityPart = contents.substring(index + 1);
                try {
                    arity = Integer.parseInt(arityPart);
                    name = stringHandler.getPredicateName(namePart);
                } catch (NumberFormatException numberFormatException) {
                }
            }
        }
        else if (arg instanceof Function) {
            Function function = (Function) arg;
            if (function.functionName.name.equals("/") && function.numberArgs() == 2) {
                if (function.getArgument(0) instanceof StringConstant && function.getArgument(1) instanceof NumericConstant) {
                    name = stringHandler.getPredicateName(((StringConstant) function.getArgument(0)).getBareName());
                    arity = ((NumericConstant) function.getArgument(1)).value.intValue();
                }
            }
        }


        if (name != null) {
            predicateNameArity = new PredicateNameAndArity(name, arity);
        }

        return predicateNameArity;
    }

    private List<Literal> getQueryRemainder(List<Literal> queryLiterals, long proofCounter, int expansion, BindingList bindingList) {
        int querySize = queryLiterals.size();
        List<Literal> queryRemainder = new LinkedList<Literal>();

        if (querySize > 0) {
            if (getTask().getTraceLevel() >= 2 || (getTask().getTraceLevel() >= 1 && isSpyLiteral(queryLiterals.get(0)))) {
                queryRemainder.add(new StackTraceLiteral(queryLiterals.get(0), proofCounter, expansion));
            }

            for (int i = 1; i < querySize; i++) {
                Literal lit = queryLiterals.get(i);
                if (bindingList != null) {
                    lit = lit.applyTheta(bindingList.theta);
                }
                queryRemainder.add(lit);
            }
        }
        return queryRemainder;
    }

    private HornSearchNode createChildWithMultipleNewLiterals(HornSearchNode hornSearchNode, List<Literal> newLiterals, List<Literal> queryLiterals, BindingList bindingList) {

        int expansion = getNextExpansion();

        List<Literal> newQueryLiterals = getQueryRemainder(queryLiterals, proofCounter, expansion, bindingList);

        if (bindingList != null) {
            bindingList = bindingList.copy();
        }

        if (newLiterals != null) {
            for (int i = newLiterals.size() - 1; i >= 0; i--) {
                Literal newLit = newLiterals.get(i);
                if (bindingList != null) {
                    newLit = newLit.applyTheta(bindingList.theta);
                }
                newQueryLiterals.add(0, newLit);
            }
        }

        return new HornSearchNode(hornSearchNode, getStringHandler().getClause(newQueryLiterals, false), bindingList, proofCounter, expansion);
    }

    private HornSearchNode createChildWithSingleNewLiteral(HornSearchNode hornSearchNode, Literal newLiteral, List<Literal> queryLiterals, BindingList bindingList) {

        int expansion = getNextExpansion();

        if (bindingList != null) {
            bindingList = bindingList.copy();
        }

        List<Literal> newQueryLiterals = getQueryRemainder(queryLiterals, proofCounter, expansion, bindingList);

        if (newLiteral != null) {
            newQueryLiterals.add(0, newLiteral);
        }

        return new HornSearchNode(hornSearchNode, getStringHandler().getClause(newQueryLiterals, false), bindingList, proofCounter, expansion);
    }

    private HornSearchNode createChildWithNoNewLiterals(HornSearchNode hornSearchNode, List<Literal> queryLiterals, BindingList bindingList) {
        int expansion = getNextExpansion();

        if (bindingList != null) {
            bindingList = bindingList.copy();
        }

        List<Literal> newQueryLiterals = getQueryRemainder(queryLiterals, proofCounter, expansion, bindingList);

        return new HornSearchNode(hornSearchNode, getStringHandler().getClause(newQueryLiterals, false), bindingList, proofCounter, expansion);
    }

    
    

    private BindingList getLocalBindings(Literal literal, BindingList currentBindings) {
        Collection<Variable> vars = literal.collectAllVariables();
        BindingList localVarBindings = null;
        if (vars != null && vars.isEmpty() == false && currentBindings != null) {
            localVarBindings = new BindingList();
            for (Variable variable : vars) {
                Term binding = currentBindings.lookup(variable);
                if (binding != null && binding != variable) {
                    localVarBindings.addBinding(variable, binding);
                }
            }
        }
        return localVarBindings;
    }

    private class StackTraceLiteral extends Literal {

        private Literal traceLiteral;

        private long proofCounter;

        private int expansion;

        public StackTraceLiteral(Literal traceLiteral, long proofCount, int expansion) {
            this.traceLiteral = traceLiteral;
            this.proofCounter = proofCount;
            this.expansion = expansion;

            predicateName = traceLiteral.getStringHandler().getPredicateName("StackTrace");
        }

        public int getExpansion() {
            return expansion;
        }

        public Literal getTraceLiteral() {
            return traceLiteral;
        }

        public long getProofCounter() {
            return proofCounter;
        }

        @Override
        public String toString(int precedenceOfCaller) {
            return "StackTrace(Return of " + traceLiteral + " [" + getProofCounter() + "." + getExpansion() + "])";
        }

        @Override
        public String toPrettyString() {
            return toString();
        }

        @Override
        public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
            return toString();
        }

        @Override
        public String toString(int precedenceOfCaller, BindingList bindingList) {
            return toString();
        }
    }

    protected static class CutMarkerNode extends HornSearchNode {

        private CutMarkerLiteral cutMarkerLiteral;

        public CutMarkerNode(HornSearchNode parentNode, Literal literalBeingCut, long proofCounterOfCutClause) {
            super(parentNode, null, null, proofCounterOfCutClause, -1);

            this.cutMarkerLiteral = new CutMarkerLiteral(literalBeingCut.getStringHandler(), literalBeingCut, proofCounterOfCutClause);
            this.clause = literalBeingCut.getStringHandler().getClause(null, this.cutMarkerLiteral);
        }

        public CutMarkerNode(HornClauseProver task, Literal literalBeingCut, long proofCounterOfCutClause) {
            super(task, null, null, proofCounterOfCutClause, -1);

            this.cutMarkerLiteral = new CutMarkerLiteral(literalBeingCut.getStringHandler(), literalBeingCut, proofCounterOfCutClause);
            this.clause = literalBeingCut.getStringHandler().getClause(null, this.cutMarkerLiteral);
        }

        @Override
        public String toString() {
            return cutMarkerLiteral.toString();
        }

        public Literal getLiteralBeingCut() {
            return cutMarkerLiteral.getLiteralBeingCut();
        }

        public long getProofCounterOfCutClause() {
            return cutMarkerLiteral.getProofCounterOfCutClause();
        }
    }

    protected static class CutMarkerLiteral extends Literal {

        /** Head of the clause that contained the cut.
         *
         * This is just for debugging purpose, never used in the actual resolution.
         *
         */
        private Literal literalBeingCut;

        private long proofCounterOfCutClause;

        public CutMarkerLiteral(HandleFOPCstrings stringHandler, Literal literalBeingCut, long proofCounterOfCutClause) {
            super(stringHandler, stringHandler.standardPredicateNames.cutMarker);
            this.literalBeingCut = literalBeingCut;
            this.proofCounterOfCutClause = proofCounterOfCutClause;
        }

        @Override
        public String toString(int precedenceOfCaller) {
            return "CutMarker [Cut of [" + getProofCounterOfCutClause() + ".*] " + literalBeingCut + "]";
        }

        public Literal getLiteralBeingCut() {
            return literalBeingCut;
        }

        public long getProofCounterOfCutClause() {
            return proofCounterOfCutClause;
        }
    }

    protected static class CutLiteral extends Literal {

        /** Head of the clause that contained the cut.
         *
         */
        private CutMarkerNode cutMarkerNode;

        public CutLiteral(HandleFOPCstrings stringHandler, CutMarkerNode cutMarkerNode) {
            super(stringHandler, stringHandler.standardPredicateNames.cut);
            this.cutMarkerNode = cutMarkerNode;
        }

        @Override
        public String toString(int precedenceOfCaller) {
            return "! [Cut to marker [" + cutMarkerNode.getProofCounterOfCutClause() + ".*] " + cutMarkerNode.getLiteralBeingCut() + "]";
        }

        @Override
        public String toPrettyString() {
            return toString();
        }

        @Override
        public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
            return toString();
        }

        @Override
        public String toString(int precedenceOfCaller, BindingList bindingList) {
            return toString();
        }
    }

    private static class FailedTraceNode extends HornSearchNode {

        Literal failedLiteral;

        public FailedTraceNode(HornClauseProver task, Literal failedLiteral, BindingList bindings, long parentProofCounter, int parentExpansionIndex) {
            super(task, null, bindings, parentProofCounter, parentExpansionIndex);
            this.failedLiteral = failedLiteral;
        }

        @Override
        public String toString() {
            return "StackTrace(Fail of " + failedLiteral + " [" + parentProofCounter + "." + parentExpansionIndex + "])";
        }
    }
}
