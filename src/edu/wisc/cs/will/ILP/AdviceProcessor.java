/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.AllOfFOPC;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.visitors.ElementPositionVisitor;
import edu.wisc.cs.will.FOPC.visitors.ElementPath;
import edu.wisc.cs.will.FOPC.visitors.ElementPositionVisitor.ElementPositionData;
import edu.wisc.cs.will.FOPC.PrettyPrinter;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.PredicateSpec;
import edu.wisc.cs.will.FOPC.PrettyPrinterOptions;
import edu.wisc.cs.will.FOPC.PruneDuplicatesIfTrueRule;
import edu.wisc.cs.will.FOPC.PruneIfTrueRule;
import edu.wisc.cs.will.FOPC.PruningRule;
import edu.wisc.cs.will.FOPC.RelevanceStrength;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.SentenceAsTerm;
import edu.wisc.cs.will.FOPC.StringConstant;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.ILP.ActiveAdvice.ModeInfo;
import edu.wisc.cs.will.ResThmProver.AssertRetractListener;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.ResThmProver.HornClausebase;
import edu.wisc.cs.will.Utils.LinkedMapOfSets;
import edu.wisc.cs.will.Utils.MapOfSets;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.WILLjumpOutOfHere;

import java.io.File;
import java.io.FileNotFoundException;
import edu.wisc.cs.will.Utils.condor.CondorFileOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

/**
 *
 * @author twalker
 */
public class AdviceProcessor {

    public static int debugLevel = 0;

    // <editor-fold defaultstate="collapsed" desc="Advice Statement Data">
    /** Original Relevance statements, prior to generalization.
     *
     * This list contains the original relevance statements prior to generalization.
     * groundedRelevance is a bit of a misnomer, since the relevance may contain variables.
     */
    private List<RelevantClauseInformation> relevantClauses = new ArrayList<RelevantClauseInformation>();

    private List<RelevantFeatureInformation> relevantFeatures = new ArrayList<RelevantFeatureInformation>();

    private List<RelevantModeInformation> relevantModes = new ArrayList<RelevantModeInformation>();

    protected Set<Integer> unsplitableExamplePositions = new HashSet<Integer>();
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Noise Data Generation Variables">
    public static boolean createNoisyBKfile = false;

    public final static int numberOfRuns = 30;

    public final static double[] droppingProbs = {0.0, 0.05, 0.10, 0.15, 0.25, 0.37, 0.50, 0.62, 0.75, 0.87}; // Note: these will be multiplied by 100 and then truncated.  So be sure that is unique.// </editor-fold>

    private final HornClauseContext context;

    private final HandleFOPCstrings stringHandler;

    private final LearnOneClause learnOneClause;

    private int anonymousClauseIndex = 0;

    private RelevantClauseListener relevantClauseListener;

    private Set<PredicateNameAndArity> assertedRelevanceModes = new HashSet<PredicateNameAndArity>();

    private Set<PredicateNameAndArity> assertedRelevanceClauses = new HashSet<PredicateNameAndArity>();

    private Map<PredicateNameAndArity, RelevanceStrength> originalRelevantStrengths = new HashMap<PredicateNameAndArity, RelevanceStrength>();

    private MutuallyExclusiveModeConstraint constraint = null;

    private boolean verifyPositiveAdviceOnOriginalExampleEnabled = false;

    private boolean verifyNegativeAdviceOnOriginalExampleEnabled = false;

    private boolean verifyAllPredicateExist = true;

    private boolean outputArgumentsEnabled = false;

    private boolean inliningEnabled = true;

    private boolean removeDuplicateDeterminatesEnabled = true;

    private boolean removeDoubleNegationEnabled = true;

    private boolean verifyInputsToFunctionsAsPredAreBoundEnabled = true;

    private List<PruningRule> pruningRules = null;

    public AdviceProcessor(HornClauseContext context, LearnOneClause learnOneClause) {

        this.context = context;
        this.stringHandler = context.getStringHandler();
        this.learnOneClause = learnOneClause;

        setupRelevantClauseListener(this.context);

        context.getStringHandler().setStringsAreCaseSensitive(true);
        HandleFOPCstrings.VarIndicator oldVI = context.getStringHandler().getVariableIndicatorNoSideEffects();
        context.getStringHandler().setVariableIndicator(HandleFOPCstrings.VarIndicator.uppercase);

        Clause memberPruneCondition = context.getFileParser().parseDefiniteClause("prune(ExistingLiteral, AddedLiteral) :- member(Iter1,List1)=ExistingLiteral, member(Iter2,List2)=AddedLiteral, List1 == List2, Iter2 = Iter1.");
        PruneDuplicatesIfTrueRule memberPruneRule = new PruneDuplicatesIfTrueRule(context.getStringHandler().getPredicate("member", 2), memberPruneCondition);
        addPruningRule(memberPruneRule);

        Clause compositeNamePruneCondition = context.getFileParser().parseDefiniteClause("prune(ExistingLiteral, AddedLiteral) :- ilField_Composite_name(W,Name1,Symbol1,S)=ExistingLiteral, ilField_Composite_name(W,Name2,Symbol2,S)=AddedLiteral, Symbol1 == Symbol2, Name2 = Name1.");
        PruneDuplicatesIfTrueRule compositeNamePruneRule = new PruneDuplicatesIfTrueRule(context.getStringHandler().getPredicate("ilField_Composite_name", 4), compositeNamePruneCondition);
        addPruningRule(compositeNamePruneRule);

        Clause sameAsCondition1 = context.getFileParser().parseDefiniteClause("prune(AddedLiteral) :- sameAsIL(W,X,X,S)=AddedLiteral.");
        PruneIfTrueRule sameAsPrune1 = new PruneIfTrueRule(context.getStringHandler().getPredicate("sameAsIL", 4), sameAsCondition1);
        addPruningRule(sameAsPrune1);

        Clause forEachInChainPruneCondition = context.getFileParser().parseDefiniteClause("prune(Literal, Literal).");
        PruneDuplicatesIfTrueRule forEachInChainPruneRule = new PruneDuplicatesIfTrueRule(context.getStringHandler().getPredicate("forEachIn_chain", 7), forEachInChainPruneCondition);
        addPruningRule(forEachInChainPruneRule);

        context.getStringHandler().setVariableIndicator(oldVI);
    }

    // <editor-fold defaultstate="collapsed" desc="Stage 1/2 Advice Processing Methods">
    /** Returns the active advice for the given examples and relevanceStrength without asserting/retracting.
     *
     * @param relevanceStrength
     * @param positiveExamples
     * @param negativeExamples
     * @return
     */
    public ActiveAdvice getActiveAdvice(RelevanceStrength relevanceStrength, List<? extends Example> positiveExamples, List<? extends Example> negativeExamples) {
        ActiveAdvice activeAdvice = new ActiveAdvice(stringHandler, relevanceStrength, positiveExamples, negativeExamples);

        processRelevantClauses(activeAdvice, relevanceStrength, positiveExamples, negativeExamples);

        processRelevantFeatures(activeAdvice, relevanceStrength, positiveExamples, negativeExamples);

        processRelevantModes(activeAdvice, relevanceStrength, positiveExamples, negativeExamples);

        return activeAdvice;
    }

    /** Generalizes the relevance statements and asserts the clauses and relevance into the context.
     *
     * The positiveExamples and negativeExample collections are required to determine
     *
     * @param learnOneClause
     * @param relevanceStrength
     * @param positiveExamples
     * @param negativeExamples
     * @return
     */
    public ActiveAdvice processAdvice(RelevanceStrength relevanceStrength, List<? extends Example> positiveExamples, List<? extends Example> negativeExamples) {

        retractRelevanceAdvice();

        ActiveAdvice activeAdvice = getActiveAdvice(relevanceStrength, positiveExamples, negativeExamples);

        assertRelevanceAdvice(activeAdvice, relevanceStrength);
        
        return activeAdvice;
    }

    public void processRelevantClauses(ActiveAdvice activeAdvice, RelevanceStrength relevanceStrength, List<? extends Example> positiveExamples, List<? extends Example> negativeExamples) {

        List<Clause> allClauses = new ArrayList<Clause>();



        // First, make sure that the world/state variable positions are included
        // in the unsplitable set.
        if (stringHandler.locationOfWorldArg != -1) {
            unsplitableExamplePositions.add(stringHandler.locationOfWorldArg);
        }

        if (stringHandler.locationOfStateArg != -1) {
            unsplitableExamplePositions.add(stringHandler.locationOfStateArg);
        }

        // Filter out duplicate relevance statements that exist on multiple examples.
        MapOfSets<Example, RelevantClauseInformation> filteredGroundedPerPieceMap = createFilteredGroundedPerPieceMap(positiveExamples, negativeExamples);

        // Create the generalized, split, per piece map.
        MapOfSets<Example, RelevantClauseInformation> generalizedPerPieceMap = createPerPieceMap(filteredGroundedPerPieceMap, relevanceStrength);

        // Create the generalized, split, per example map.
        MapOfSets<Example, RelevantClauseInformation> generalizedPerExampleMap = createPerExampleMap(filteredGroundedPerPieceMap, relevanceStrength);

        // When we generate clauses, we always generate mega first, then per-single-example, then per-piece.
        // That way, if duplicates occur, the highest relevance levels will be kept.
        List<Clause> megaClauses = generateMegaCombinations(activeAdvice, generalizedPerExampleMap, relevanceStrength);
        allClauses.addAll(megaClauses);

        List<Clause> singleExampleClauses = generateActiveAdviceForRCIs(activeAdvice, generalizedPerExampleMap, "single_example_advice", relevanceStrength, RelevanceStrength.VERY_STRONGLY_RELEVANT, RelevanceStrength.VERY_STRONGLY_RELEVANT_NEG);
        allClauses.addAll(singleExampleClauses);

        List<Clause> singlePieceClauses = generateActiveAdviceForRCIs(activeAdvice, generalizedPerPieceMap, "single_piece_advice", relevanceStrength, RelevanceStrength.STRONGLY_RELEVANT, RelevanceStrength.STRONGLY_RELEVANT_NEG);
        allClauses.addAll(singlePieceClauses);

        // <editor-fold defaultstate="collapsed" desc="Debug Printing">
        if (debugLevel >= -1) {
            if (allClauses.isEmpty()) {
                Utils.print("% [AdviceProcessor]  Generated 0 clauses at relevance level " + relevanceStrength + ".");
                Utils.print("\n");
            }
            else {
                Utils.print("% [AdviceProcessor]  Generated " + allClauses.size() + " clause(s) at relevance level " + relevanceStrength + ":\n");

                boolean first = true;
                for (Clause clause : allClauses) {
                    if (first == false) {
                        Utils.print("\n");
                    }
                    first = false;

                    RelevanceStrength strongestStrength = RelevanceStrength.getWeakestRelevanceStrength();
                    for (ModeInfo modeInfo : activeAdvice.getModeInfo(clause.getDefiniteClauseHead().getPredicateNameAndArity())) {
                        RelevanceStrength rs = modeInfo.strength;
                        if (rs.isStronger(strongestStrength)) {
                            strongestStrength = rs;
                        }
                    }

                    PrettyPrinterOptions ppo = new PrettyPrinterOptions();
                    ppo.setMaximumLiteralsPerLine(1);
                    ppo.setSentenceTerminator("");
                    ppo.setMaximumIndentationAfterImplication(10);
                    ppo.setNewLineAfterImplication(true);

                    String s = PrettyPrinter.print(clause, "% [AdviceProcessor]   ", ppo);

                    Utils.print(s + "  " + strongestStrength);
                }

                Utils.print("\n\n");
            }
        }
        // </editor-fold>

//        // Form Conjunctive clauses
//        List<Clause> conjunctiveClauses = generateBackgroundForConjunctions(activeAdvice, exampleToSplitVariableMap, relevanceStrength);
//        generateNegationByFailureOfConjuncts(activeAdvice, conjunctiveClauses);
//
//        // <editor-fold defaultstate="collapsed" desc="Debug Printing">
//        if (debugLevel >= 1) {
//            Utils.print("% [AdviceProcessor]  Final Conjunctive Clauses:" + "\n");
//
//            boolean first = true;
//            for (Clause clause : conjunctiveClauses) {
//                if (first == false) {
//                    Utils.print(",\n");
//                }
//                first = false;
//                RelevanceStrength rs = clause.getPosLiteral(0).predicateName.getRelevance(clause.getPosLiteral(0).getArity());
//                Utils.print("% [AdviceProcessor]   " + clause.toString(Integer.MAX_VALUE) + ", " + rs);
//            }
//
//            Utils.print("\n\n");
//        }// </editor-fold>
//
//        List<Clause> disjunctiveClauses = generateBackgroundForDisjunctions(activeAdvice, exampleToSplitVariableMap, relevanceStrength);
//        generateNegationByFailureOfDisjuncts(activeAdvice, disjunctiveClauses);
//
//        // <editor-fold defaultstate="collapsed" desc="Debug Printing">
//        if (debugLevel >= 1) {
//            Utils.print("% [AdviceProcessor]  Final Disjunctive Clauses:" + "\n");
//
//            boolean first = true;
//            for (Clause clause : disjunctiveClauses) {
//                if (first == false) {
//                    Utils.print(",\n");
//                }
//                first = false;
//                RelevanceStrength rs = clause.getPosLiteral(0).predicateName.getRelevance(clause.getPosLiteral(0).getArity());
//                Utils.print("% [AdviceProcessor]   " + clause.toString(Integer.MAX_VALUE) + ", " + rs);
//            }
//
//            Utils.print("\n\n");
//        }// </editor-fold>

    }

    public MapOfSets<Example, RelevantClauseInformation> createFilteredGroundedPerPieceMap(List<? extends Example> positiveExamples, List<? extends Example> negativeExamples) {
        //   ex1 : adviceA
        //   ex1 : adviceB
        //   ex2 : adviceC
        //
        // We get the map:
        //   ex1 => { adviceA, adviceB }
        //   ex2 => { adviceC }
        MapOfSets<Example, RelevantClauseInformation> exampleToAdviceMap = createExampleToAdviceMap(relevantClauses);
        // <editor-fold defaultstate="collapsed" desc="Debug Printing">
        if (debugLevel >= 2) {
            Utils.print("% [AdviceProcessor] All Grounded-Clauses Advice Map:" + "\n");
            Utils.print(exampleToAdviceMap.toString("% [AdviceProcessor]   "));
            Utils.print("\n");
        } // </editor-fold>
        // This will also remove any relevance that is not associate with an current relevanceFromPositiveExample or negative example.
        MapOfSets<Example, RelevantClauseInformation> activeExampleToAdviceMap = createActiveExampleMap(context, exampleToAdviceMap, positiveExamples, negativeExamples, RelevanceStrength.getWeakestRelevanceStrength());

        // <editor-fold defaultstate="collapsed" desc="Debug Printing">
        if (debugLevel >= 2) {
            Utils.print("% [AdviceProcessor] All Active Clauses (with duplicates):" + "\n");
            Utils.print(activeExampleToAdviceMap.toString("% [AdviceProcessor]   "));
            Utils.print("\n");
        } // </editor-fold>
        MapOfSets<Example, RelevantClauseInformation> filteredGroundedPerPieceMap = filterDuplicateRelevance(activeExampleToAdviceMap);
        return filteredGroundedPerPieceMap;
    }

    public MapOfSets<Example, RelevantClauseInformation> createPerPieceMap(MapOfSets<Example, RelevantClauseInformation> filteredGroundedPerPieceMap, RelevanceStrength relevanceStrength) {

        // <editor-fold defaultstate="collapsed" desc="Debug Printing">
        if (debugLevel >= 2) {
            Utils.print("% [AdviceProcessor] Filtered Grounded Clauses:\n");
            Utils.print(filteredGroundedPerPieceMap.toString("% [AdviceProcessor]   "));
            Utils.print("\n");
        } // </editor-fold>
        MapOfSets<Example, RelevantClauseInformation> generalizedPerPieceMap = createExampleToGeneralizedMap(filteredGroundedPerPieceMap);
        //Tag the possible set of output variables on the PerPiece map
        collectOutputVariables(generalizedPerPieceMap);
        // <editor-fold defaultstate="collapsed" desc="Debug Printing">
        if (debugLevel >= 2) {
            Utils.print("% [AdviceProcessor]  Generalized Per Piece Map:\n");
            Utils.print(generalizedPerPieceMap.toString("% [AdviceProcessor]   "));
            Utils.print("\n");
        } // </editor-fold>
        MapOfSets<Example, RelevantClauseInformation> splitPerPieceMap = createExampleToSplitVariableMap(generalizedPerPieceMap, relevanceStrength);
        // <editor-fold defaultstate="collapsed" desc="Debug Printing">
        if (debugLevel >= 2) {
            Utils.print("% [AdviceProcessor]  Example Split Per Piece:" + "\n");
            Utils.print(splitPerPieceMap.toString("% [AdviceProcessor]   "));
            Utils.print("\n");
        } // </editor-fold>
        return splitPerPieceMap;
    }

    private MapOfSets<Example, RelevantClauseInformation> createPerExampleMap(MapOfSets<Example, RelevantClauseInformation> filteredGroundedPerPieceMap, RelevanceStrength relevanceStrength) {
        MapOfSets<Example, RelevantClauseInformation> grounedPerExampleAdviceMap = createExampleToPerExampleAdviceMap(filteredGroundedPerPieceMap, relevanceStrength);
        // <editor-fold defaultstate="collapsed" desc="Debug Printing">
        if (debugLevel >= 2) {
            Utils.print("% [AdviceProcessor] Duplicates-Removed Grounded-Clauses To Conjoined Advice Map:\n");
            Utils.print(grounedPerExampleAdviceMap.toString("% [AdviceProcessor]   "));
            Utils.print("\n");
        } // </editor-fold>
        MapOfSets<Example, RelevantClauseInformation> generalizedPerExampleConjunctiveMap = createExampleToGeneralizedMap(grounedPerExampleAdviceMap);
        //Tag the possible set of output variables on the PerExample map
        collectOutputVariables(generalizedPerExampleConjunctiveMap);
        // <editor-fold defaultstate="collapsed" desc="Debug Printing">
        if (debugLevel >= 2) {
            Utils.print("% [AdviceProcessor]  Generalized Clauses To Conjoined Advice Map:\n");
            Utils.print(generalizedPerExampleConjunctiveMap.toString("% [AdviceProcessor]   "));
            Utils.print("\n");
        } // </editor-fold>
        MapOfSets<Example, RelevantClauseInformation> splitPerExampleMap = createExampleToSplitVariableMap(generalizedPerExampleConjunctiveMap, relevanceStrength);
        // <editor-fold defaultstate="collapsed" desc="Debug Printing">
        if (debugLevel >= 2) {
            Utils.print("% [AdviceProcessor]  Example To Split-Clauses Advice Map:" + "\n");
            Utils.print(splitPerExampleMap.toString("% [AdviceProcessor]   "));
            Utils.print("\n");
        } // </editor-fold>
        //        MapOfSets<Example, RelevantClauseInformation> filteredSplitMap = filterDuplicateRelevance(exampleToSplitVariableMap);
        //
        //        if ( debugLevel >= 1 ) Utils.print("Filtered Example To Split Advice Map:");
        //        if ( debugLevel >= 1 ) Utils.print(filteredSplitMap.toString("  "));
        //        if ( debugLevel >= 1 ) Utils.print("");
        // That way, if duplicates occur, the highest relevance levels will be kept.
        return splitPerExampleMap;
    }

    public void processRelevantFeatures(ActiveAdvice activeAdvice, RelevanceStrength relevanceStrength, List<? extends Example> positiveExamples, List<? extends Example> negativeExamples) {

        // <editor-fold defaultstate="collapsed" desc="Non-working code">
        MapOfSets<Example, RelevantFeatureInformation> exampleToAdviceMap = createExampleToAdviceMap(relevantFeatures);

//        if (debugLevel >= 2) {
//            Utils.print("% [AdviceProcessor]  All Relevant Features Map:" + "\n");
//            Utils.print(exampleToAdviceMap.toString("% [AdviceProcessor]   "));
//            Utils.print("\n");
//        }

        // Update the ground examples relevanceFromPositiveExample/negative status according to the positiveExample/negativeExamples lists.
        // This will also remove any relevance that is not associate with an current relevanceFromPositiveExample or negative example.
        MapOfSets<Example, RelevantFeatureInformation> activeExampleToAdviceMap = createActiveExampleMap(context, exampleToAdviceMap, positiveExamples, negativeExamples, relevanceStrength);

//        if (debugLevel >= 2) {
//            Utils.print("% [AdviceProcessor]  All Active Relevant Features (with duplicates):" + "\n");
//            Utils.print(activeExampleToAdviceMap.toString("% [AdviceProcessor]   "));
//            Utils.print("\n");
//        }

        // Filter out duplicate relevance statements that exist on multiple examples.
        MapOfSets<Example, RelevantFeatureInformation> filteredGroundedRelevance = filterDuplicateRelevance(activeExampleToAdviceMap);

//        if (debugLevel >= 2) {
//            Utils.print("% [AdviceProcessor]  Filtered Relevant Features:\n");
//            Utils.print(filteredGroundedRelevance.toString("% [AdviceProcessor]   "));
//            Utils.print("\n");
//        }

        for (Set<RelevantFeatureInformation> set : filteredGroundedRelevance.values()) {
            for (RelevantFeatureInformation rfi : set) {
                activeAdvice.addFeatureRelevance(rfi.getPredicateNameAndArity(), rfi.getRelevanceStrength());

//                if (debugLevel >= 1) {
//                    Utils.println("% [AdviceProcessor] Relevant Feature: " + rfi.getPredicateNameAndArity() + ", " + rfi.getRelevanceStrength() + ".");
//                }
            }
        }// </editor-fold>

//        // While we are here, we should also see if any of the modes have relevance marked.
//        Set<PredicateNameAndArity> modes = learnOneClause.getBodyModes();
//
//        for (PredicateNameAndArity predicateNameAndArity : modes) {
//
//            PredicateName name = predicateNameAndArity.getPredicateName();
//            List<PredicateSpec> predicateSpecs = name.getTypeListForThisArity(predicateNameAndArity.getArity());
//            for (PredicateSpec predicateSpec : predicateSpecs) {
//                RelevanceStrength strength = name.getRelevance(predicateNameAndArity.getArity());
//                if ( relevanceStrength == strength || ( strength != null && relevanceStrength.isEqualOrWeaker(strength))) {
//                    if ( debugLevel >= 2 ) System.out.println("Adding Relevances: " + predicateNameAndArity + " @ " + strength + ".");
//                    activeAdvice.addModeAndRelevanceStrength(predicateNameAndArity, predicateSpec.getSignature(), predicateSpec.getTypeSpecList(), strength);
//                }
//            }
//        }
//
//
//        //commitFeatureRelevance(filteredGroundedRelevance);
//        if (debugLevel >= 2) {
//            Utils.println("% [AdviceProcessor]  Call to processRelevantFeatures() completed.\n");
//        }



    }

    public void processRelevantModes(ActiveAdvice activeAdvice, RelevanceStrength relevanceStrength, List<? extends Example> positiveExamples, List<? extends Example> negativeExamples) {

        MapOfSets<Example, RelevantModeInformation> exampleToAdviceMap = createExampleToAdviceMap(relevantModes);

        if (debugLevel >= 2) {
            Utils.print("% [AdviceProcessor]  All Relevant Mode Map:" + "\n");
            Utils.print(exampleToAdviceMap.toString("% [AdviceProcessor]   "));
            Utils.print("\n");
        }

        // Update the ground examples relevanceFromPositiveExample/negative status according to the positiveExample/negativeExamples lists.
        // This will also remove any relevance that is not associate with an current relevanceFromPositiveExample or negative example.
        MapOfSets<Example, RelevantModeInformation> activeExampleToAdviceMap = createActiveExampleMap(context, exampleToAdviceMap, positiveExamples, negativeExamples, relevanceStrength);

        if (debugLevel >= 2) {
            Utils.print("% [AdviceProcessor]  All Active Relevant Mode (with duplicates):" + "\n");
            Utils.print(activeExampleToAdviceMap.toString("% [AdviceProcessor]   "));
            Utils.print("\n");
        }

        // Filter out duplicate relevance statements that exist on multiple examples.
        MapOfSets<Example, RelevantModeInformation> filteredGroundedRelevance = filterDuplicateRelevance(activeExampleToAdviceMap);

        if (debugLevel >= 2) {
            Utils.print("% [AdviceProcessor]  Filtered Relevant Mode:\n");
            Utils.print(filteredGroundedRelevance.toString("% [AdviceProcessor]   "));
            Utils.print("\n");
        }

        for (Set<RelevantModeInformation> set : filteredGroundedRelevance.values()) {
            for (RelevantModeInformation rmi : set) {
                PredicateNameAndArity predicateNameAndArity = rmi.getPredicateNameAndArity();
                List<Term> signature = rmi.getSignature();
                List<TypeSpec> typeSpecList = rmi.getTypeSpecs();
                RelevanceStrength rs = rmi.getRelevanceStrength();

                if ( relevanceStrength == null || relevanceStrength.isEqualOrWeaker(rs) ) {

                    if (debugLevel >= 1) {
                        Utils.println("% [AdviceProcessor] Relevant Mode: " + predicateNameAndArity + "(" + typeSpecList + "), " + rs + ".");
                    }
                    activeAdvice.addAdviceMode(this, rmi);
                }
            }
        }

        //commitFeatureRelevance(filteredGroundedRelevance);
        if (debugLevel >= 2) {
            Utils.println("% [AdviceProcessor]  Call to processRelevantModes() completed.\n");
        }
    }// </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Example-to-advice mapping/filter methods methods">
    public <T extends RelevantInformation> MapOfSets<Example, T> filterDuplicateRelevance(MapOfSets<Example, T> activeExampleToAdviceMap) {

        Map<T, T> positiveGeneralizedRelevance = new HashMap<T, T>();
        Map<T, T> negativeGeneralizedRelevance = new HashMap<T, T>();


        boolean save = AllOfFOPC.renameVariablesWhenPrinting;
        AllOfFOPC.renameVariablesWhenPrinting = true;

        int uniqueCount = 0;
        int groundCount = 0;

        for (Map.Entry<Example, Set<T>> entry : activeExampleToAdviceMap.entrySet()) {
            for (T rci : entry.getValue()) {

                T generalizedRCI = (T) rci.getGeneralizeRelevantInformation();//.getSimplified(context, null);

                if (generalizedRCI.isValidAdvice(this) == false) {
                    if (debugLevel >= 2) {
                        Utils.println("% [AdviceProcessor] " + "   INVALID ADVICE #" + (groundCount) + ":");
                        Utils.println(rci.toString("% [AdviceProcessor]      "));
                    }
                }
                else {

                    Map<T, T> appropriateList = rci.isRelevanceFromPositiveExample() ? positiveGeneralizedRelevance : negativeGeneralizedRelevance;

                    if (debugLevel >= 2) {
                        Utils.println("% [AdviceProcessor] " + "   GROUND #" + (groundCount) + ":");
                        Utils.println(generalizedRCI.toString("% [AdviceProcessor]      "));
                    }

                    boolean addIt = false;
                    int index;
                    //if ((index = getIndexOfRelevanceClauseInformationUptoRenaming(appropriateList, generalizedRCI)) == -1) {
                    if ((index = getIndexOfSubsumedRelevanceClauseInformation(appropriateList.keySet(), generalizedRCI)) == -1) {

                        addIt = true;

                        if (debugLevel >= 2) {
                            Utils.println("% [AdviceProcessor] " + "   UNIQUE #" + (uniqueCount++) + ":");
                            Utils.println(rci.toString("% [AdviceProcessor]      "));
                        }
                    }
                    else {
                        if (debugLevel >= 2) {
                            Utils.println("% [AdviceProcessor] " + "   DUPLICATE of #" + (index) + ".  Original Advice:");
                            Utils.println(rci.toString("% [AdviceProcessor]      "));
                        }
                    }

                    if (addIt) {
                        // First remove any RCI that the new one subsums.
                        for (Iterator<Entry<T, T>> it = appropriateList.entrySet().iterator(); it.hasNext();) {
                            Entry<T, T> e = it.next();
                            RelevantInformation relevantInformation = e.getKey();
                            if (generalizedRCI.subsumes(relevantInformation)) {
                                if ( debugLevel >= 1 ) Utils.println("% [AdviceProcessor] SUBSUMPTION!  REMOVING: ");
                                if ( debugLevel >= 1 ) Utils.println(e.getValue().toString("% [AdviceProcessor]      "));
                                it.remove();
                            }
                        }

                        appropriateList.put(generalizedRCI, rci);
                    }
                }

                groundCount++;
            }
        }

        if (debugLevel >= 2) {
            Utils.println("\n% [AdviceProcessor] Final Unique Clauses:\n");
        }

        MapOfSets<Example, T> uniqueGroundRelevance = new LinkedMapOfSets<Example, T>();

        for (Entry<T, T> entry : positiveGeneralizedRelevance.entrySet()) {
            uniqueGroundRelevance.put(entry.getValue().getExample(), entry.getValue());
        }

        for (Entry<T, T> entry : negativeGeneralizedRelevance.entrySet()) {
            uniqueGroundRelevance.put(entry.getValue().getExample(), entry.getValue());
        }

        for (Set<T> set : uniqueGroundRelevance.values()) {
            for (RelevantInformation relevantInformation : set) {
                if (debugLevel >= 2) {
                    Utils.println(relevantInformation.toString("% [AdviceProcessor]      "));
                }
            }
        }
        if ( debugLevel >= 2 )Utils.println("% [AdviceProcessor] ");

        AllOfFOPC.renameVariablesWhenPrinting = save;


        return uniqueGroundRelevance;
    }

    public <T extends RelevantInformation> MapOfSets<Example, T> createExampleToAdviceMap(List<T> relevantInformationList) {
        MapOfSets<Example, T> exampleToAdviceSetMap = new LinkedMapOfSets<Example, T>();

        for (T rci : relevantInformationList) {
//            if ( rci instanceof RelevantClauseInformation) {
//                System.out.println(((RelevantClauseInformation)rci).getInlined(context, null));
//            }
            exampleToAdviceSetMap.put(rci.getExample(), rci);
        }

        return exampleToAdviceSetMap;
    }

    private HandleFOPCstrings getStringHandler() {
        return learnOneClause.getStringHandler();
    }

    private void collectOutputVariables(MapOfSets<Example, RelevantClauseInformation> rciMap) {

        for (Set<RelevantClauseInformation> set : rciMap.values()) {
            for (RelevantClauseInformation rci : set) {
                // We assume at this point that the rci only contains clauses

                Sentence s = SentenceCompressor.getCompressedSentence(rci.getSentence());

                if (s instanceof Clause) {
                    Clause clause = (Clause) s;
                    if (clause.getPosLiteralCount() > 0) {
                        Literal lastLiteral = clause.getPosLiteral(clause.getPosLiteralCount() - 1);

                        if (lastLiteral.getArity() > 2) {
                            Variable outputVariable = null;

                            // We are going to cheat here and assume that the last argument
                            // of the last literal is the "State" argument and therefore is
                            // not an output variable.  This should really be based upon the
                            // HandleFOPCstrings.locationOfStateArg...but that would require
                            // that I look up that argument location in the example head and
                            // then trace that argument to determine where it occurs in
                            // the last literal.
                            //
                            // We make the same assumption for the "World" argument too.
                            // Hence we iteration from argity-2 to 1
                            for (int i = lastLiteral.getArity() - 2; i > 0; i--) {
                                Term arg = lastLiteral.getArgument(i);
                                if (arg instanceof Variable) {
                                    outputVariable = (Variable) arg;
                                    break;
                                }
                            }

                            if (outputVariable != null) {
                                rci.addOutputVariable(outputVariable);
                            }
                        }
                    }
                }
                else {
                    Utils.warning("Error collecting advice output variables.  Expected a clause.  Got:\n" + rci.getSentence());
                }

            }
        }
    }

    public MapOfSets<Example, RelevantClauseInformation> createExampleToPerExampleAdviceMap(MapOfSets<Example, RelevantClauseInformation> exampleToAdviceMap, RelevanceStrength relevanceStrength) {
        MapOfSets<Example, RelevantClauseInformation> exampleToConjunctionMap = new LinkedMapOfSets<Example, RelevantClauseInformation>();

        for (Map.Entry<Example, Set<RelevantClauseInformation>> entry : exampleToAdviceMap.entrySet()) {
            RelevantClauseInformation conjunct = null;

            for (RelevantClauseInformation anRCI : entry.getValue()) {
                if (anRCI.isContainsAllAdvicePieces()) {
                    if (conjunct == null) {
                        conjunct = anRCI;
                    }
                    else {
                        conjunct = conjunct.getConjunction(anRCI);
                    }
                }
            }

            if (conjunct != null) {
                //conjunct.getCompressed();
                exampleToConjunctionMap.put(entry.getKey(), conjunct);
            }
            else {
                Utils.warning("No advice with all pieces exists for example " + entry.getKey() + ".");
            }
        }

        return exampleToConjunctionMap;
    }

    public MapOfSets<Example, RelevantClauseInformation> createExampleToGeneralizedMap(MapOfSets<Example, RelevantClauseInformation> exampleToGroundedConjunctiveMap) {
        MapOfSets<Example, RelevantClauseInformation> result = new LinkedMapOfSets<Example, RelevantClauseInformation>();

        for (Map.Entry<Example, Set<RelevantClauseInformation>> entry : exampleToGroundedConjunctiveMap.entrySet()) {
            Example example = entry.getKey();
            Set<RelevantClauseInformation> groundAdviceForExample = entry.getValue();

//            Set<RelevantClauseInformation> generalizedAdviceForExample = new HashSet<RelevantClauseInformation>();

            for (RelevantClauseInformation rci : groundAdviceForExample) {
                RelevantClauseInformation newRCI = rci.getGeneralizeRelevantInformation(); //.getSimplified(context, null);

                result.put(example, newRCI);
            }
        }

        return result;
    }

    public MapOfSets<Example, RelevantClauseInformation> createExampleToSplitVariableMap(MapOfSets<Example, RelevantClauseInformation> exampleToGeneralizedConjunctiveMap, RelevanceStrength relevanceStrength) {

        MapOfSets<Example, RelevantClauseInformation> result = new LinkedMapOfSets<Example, RelevantClauseInformation>();

        // Don't split for now...
        result = exampleToGeneralizedConjunctiveMap;

//        for (Map.Entry<Example, Set<RelevantClauseInformation>> entry : exampleToGeneralizedConjunctiveMap.entrySet()) {
//            Example example = entry.getKey();
//            Set<RelevantClauseInformation> generalizedAdviceForExample = entry.getValue();
//
////            Set<RelevantClauseInformation> splitAdviceForExample = new HashSet<RelevantClauseInformation>();
//
//            Set<RelevantClauseInformation> uniqueRCISet = new HashSet<RelevantClauseInformation>();
//
//            // Each example will have a set of generalized clauses representing the various
//            // pieces of conjoined advice for that particular example.  Although those clauses
//            // have been generalized, the variables have not been split.
//            //
//            // For instance:
//            //  ex(A,B) => p(A), q(A), r(B)
//            //  ex(A,B) => p(A)
//            //  ex(A,B) => q(A), r(B)
//            //
//            // To split the variables for any given clause, we record all the variables
//            // of that clause that were previously generalized.
//            //
//            // For instance, to split "ex(A,B) => p(A), q(A), r(B)", we would record:
//            //   S = {0:0, 1:0, 2:0}, where x:y represents the Example and term position respectively.
//            //
//            // We then get P = power set of S.
//            //
//            // Given P, to obtain all possible variable splits, generate a new clause
//            // for each subset X of P.  For each element E of X, we replace the term
//            // represented by E with a new anonymous variable
//
//            for (RelevantClauseInformation rci : generalizedAdviceForExample) {
//                Sentence originalSentence = rci.getSentence();
//                MapOfSets<Variable, TermPosition> setOfVariablePositions = new MapOfSets<Variable, TermPosition>();
//
//                Set<Term> unsplitableTerms = getUnsplitableTerms(rci);
//
//                CollectSplitableVariablePositionVisitor visitor = new CollectSplitableVariablePositionVisitor();
//                CollectSplitableVariableData collectSplitableVariableData = new CollectSplitableVariableData(rci);
//
//                originalSentence.accept(visitor, collectSplitableVariableData);
//
////                // record all the variables of originalClause that were generalized.
////                for (int i = 0; i < originalSentence.getPosLiteralCount(); i++) {
////                    Literal aLiteral = originalSentence.getPosLiteral(i);
////                    for (int j = 0; j < aLiteral.getArity(); j++) {
////                        Term aTerm = aLiteral.getArgument(j);
////
////                        if (unsplitableTerms.contains(aTerm) == false && aTerm instanceof Variable) {
////                            Variable varBeingSplit = (Variable) aTerm;
////                            Term backwardMapping = rci.getBackwardMappingForTerm(varBeingSplit);
////
////                            if (backwardMapping != null && shouldBeSplit(rci, varBeingSplit, backwardMapping)) {
////                                TermPosition tp = new TermPosition(i, j);
////                                setOfVariablePositions.put(varBeingSplit, tp);
////                            }
////                        }
////                    }
////                }
//
//                // get P = power set of setOfVariablePositions.
//                Set<Set<TermPosition>> crossSet = new HashSet<Set<TermPosition>>();
//
//                for (Set<TermPosition> positionsForSingleVariable : setOfVariablePositions.values()) {
//                    Set<Set<TermPosition>> P = Utils.getPowerSet(positionsForSingleVariable);
//                    crossSet = Utils.getCrossProduct(crossSet, P);
//                }
//
//                crossSet.add(Collections.EMPTY_SET);
//
//                // Split variables based on cross set.
//                //
//                // It is possible that duplicates are generated when
//                // a variable is split that didn't occur in the example
//                // itself.  Thus we check for duplicates.
//                for (Set<TermPosition> subset : crossSet) {
//                    RelevantClauseInformation newRCI = rci.copy();
//
//                    for (TermPosition termPosition : subset) {
//                        newRCI.replacePositiveTerm(termPosition, stringHandler.getNewUnamedVariable());
//                    }
//
//                    // If any of the variables were split, mark the RCI as split.
//                    if (subset.isEmpty() == false) {
//                        newRCI.setConstantsSplit(true);
//                    }
//
//                    if (newRCI.getFinalRelevanceStrength().isEqualOrStronger(relevanceStrength)) {
//
//                        if (debugLevel >= 2) {
//                            Utils.print("% [AdviceProcessor] Created New split: " + newRCI + "\n");
//                        }
//
//                        if (getIndexOfRelevanceClauseInformationUptoRenaming(uniqueRCISet, newRCI) == -1) {
//                            uniqueRCISet.add(newRCI);
//                            result.put(example, newRCI);
//                        }
//                    }
//                }
//            }
//        }

        return result;
    }

    public <T extends RelevantInformation> MapOfSets<Example, T> createActiveExampleMap(HornClauseContext context, MapOfSets<Example, T> exampleToAdviceMap, List<? extends Example> positiveExamples, List<? extends Example> negativeExamples, RelevanceStrength minimumRelevance) {

        MapOfSets<Example, T> result = new LinkedMapOfSets<Example, T>();

        for (Example example : positiveExamples) {
            Example newExample = example.copy(false);
            Set<T> set = exampleToAdviceMap.getValues(newExample);
            if (set != null) {
                for (T rci : set) {

                    if (rci.isValidAdvice(this)) {
                        rci = (T) rci.copy();
                        rci.setRelevanceFromPositiveExample(true);
                        if (rci.getRelevanceStrength().isEqualOrStronger(minimumRelevance)) {
                            if (verifyPositiveAdviceOnOriginalExampleEnabled) {
                                if (context != null && rci.prove(context) == false) {
                                    if (AdviceProcessor.debugLevel >= 1) {
                                        Utils.println("% [AdviceProcessor] " + "Flipping positive advice clause to negative: ");
                                    }
                                    if (AdviceProcessor.debugLevel >= 1) {
                                        Utils.println("% [AdviceProcessor] " + "  " + rci + ".");
                                    }
                                    rci.setRelevanceFromPositiveExample(false);
                                }
                                result.put(newExample, rci);
                            }
                            else {
                                result.put(newExample, rci);
                            }
                        }
                    }
                    else if (debugLevel >= 2) {
                        Utils.println("% [AdviceProcessor] " + "   INVALID ADVICE:");
                        Utils.println(rci.toString("% [AdviceProcessor]      "));
                    }
                }
            }
        }

        for (Example example : negativeExamples) {
            Example newExample = example.copy(false);
            Set<T> set = exampleToAdviceMap.getValues(newExample);
            if (set != null) {
                for (T rci : set) {
                    if (rci.isValidAdvice(this)) {
                        rci = (T) rci.copy();
                        rci.setRelevanceFromPositiveExample(false);
                        if (rci.getRelevanceStrength().isEqualOrStronger(minimumRelevance)) {

                            if (verifyNegativeAdviceOnOriginalExampleEnabled) {
                                if (context != null && rci.prove(context) == false) {
                                    if (AdviceProcessor.debugLevel >= 1) {
                                        Utils.println("% [AdviceProcessor] " + "Flipping negative advice clause to positive: ");
                                    }
                                    if (AdviceProcessor.debugLevel >= 1) {
                                        Utils.println("% [AdviceProcessor] " + "  " + rci + ".");
                                    }
                                    rci.setRelevanceFromPositiveExample(true);
                                }
                                result.put(newExample, rci);
                            }
                            else {
                                result.put(newExample, rci);
                            }
                        }
                    }
                }
            }
        }

        return result;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Support Methods (Mega & Conjunctive clauses)">
    private List<Clause> generateMegaCombinations(ActiveAdvice activeAdvice, MapOfSets<Example, RelevantClauseInformation> exampleToSplitVariableMap, RelevanceStrength relevanceStrength) {

        Map<Example, RelevantClauseInformation> singleExampleConjunctMap = new HashMap<Example, RelevantClauseInformation>();

        for (Map.Entry<Example, Set<RelevantClauseInformation>> entry : exampleToSplitVariableMap.entrySet()) {
            RelevantClauseInformation conjunct = null;
            for (RelevantClauseInformation anRCI : entry.getValue()) {
                if (anRCI.isContainsAllAdvicePieces()) {
                    if (conjunct == null) {
                        conjunct = anRCI;
                    }
                    else {
                        conjunct = conjunct.getConjunction(anRCI);
                    }
                }
            }

            if (conjunct != null) {
                conjunct = conjunct.getCompressed();
                singleExampleConjunctMap.put(entry.getKey(), conjunct);
            }
            else {
                Utils.warning("No advice with all pieces exists for example " + entry.getKey() + ".");
            }
        }

        RelevantClauseInformation comboPosAND = null;
        RelevantClauseInformation comboPosOR = null;
        RelevantClauseInformation comboNotPosOR = null;
        RelevantClauseInformation comboNegAND = null;
        RelevantClauseInformation comboNegOR = null;
        RelevantClauseInformation comboNotNegOR = null;

        for (RelevantClauseInformation rci : singleExampleConjunctMap.values()) {
            if (rci.isRelevanceFromPositiveExample()) {
                if (comboPosAND == null) {
                    comboPosAND = rci;
                }
                else {
                    comboPosAND = comboPosAND.getConjunction(rci);
                }

                if (comboPosOR == null) {
                    comboPosOR = rci;
                }
                else {
                    comboPosOR = comboPosOR.getDisjunction(rci);
                }

                if (comboNotPosOR == null) {
                    comboNotPosOR = rci.getNegationByFailure();
                }
                else {
                    comboNotPosOR = comboNotPosOR.getConjunction(rci.getNegationByFailure());
                }
            }
            else {
                if (comboNegAND == null) {
                    comboNegAND = rci;
                }
                else {
                    comboNegAND = comboNegAND.getConjunction(rci);
                }

                if (comboNegOR == null) {
                    comboNegOR = rci;
                }
                else {
                    comboNegOR = comboNegOR.getDisjunction(rci);
                }

                if (comboNotNegOR == null) {
                    comboNotNegOR = rci.getNegationByFailure();
                }
                else {
                    comboNotNegOR = comboNotNegOR.getConjunction(rci.getNegationByFailure());
                }
            }
        }

        if (comboPosAND != null) {
            comboPosAND = comboPosAND.getCompressed();
        }

        if (comboNegAND != null) {
            comboNegAND = comboNegAND.getCompressed();
        }

        List<Clause> assertedClauses = new ArrayList<Clause>();

        RelevantClauseInformation rule = null;
        RelevantClauseInformation that = null;

        String predSuffix = "";
        if (getStringHandler().getInventedPredicateNameSuffix().isEmpty() == false) {
            predSuffix = getStringHandler().getInventedPredicateNameSuffix();
            if (predSuffix.startsWith("_") == false) {
                predSuffix = "_" + predSuffix;
            }
        }

        // At this point, either comboPosAND or comboNegAND must be non-null (possibly both will be non-null).
        // Thus, our logic can reflect that. Also, if comboPosAND != null, then comboNegatedPosOR != null, and
        // if comboNegAND != null, then comboNegatedNegOR != null.

        if (comboPosAND != null) {
            // Below all 8 rules are generated.  However, if the Negative combos are null, only four 
            // will be unique.  I could adjust the logic here, but they
            rule = comboPosAND.getConjunction(comboNotNegOR);
            rule.setRelevanceStrength(RelevanceStrength.POSSIBLE_ANSWER);
            activeAdvice.addAdviceClause(this, "mega_posAnd_notNegOr" + (anonymousClauseIndex++) + predSuffix, rule, assertedClauses);

            rule = comboPosAND.getNegationByFailure().getConjunction(comboNegAND);
            rule.setRelevanceStrength(RelevanceStrength.POSSIBLE_ANSWER);
            activeAdvice.addAdviceClause(this, "mega_notPosAnd_negAnd" + (anonymousClauseIndex++) + predSuffix, rule, assertedClauses);

            rule = comboPosOR.getConjunction(comboNotNegOR);
            rule.setRelevanceStrength(RelevanceStrength.POSSIBLE_ANSWER);
            activeAdvice.addAdviceClause(this, "mega_posOr_notNegOr" + (anonymousClauseIndex++) + predSuffix, rule, assertedClauses);

            rule = comboNotPosOR.getConjunction(comboNegAND);
            rule.setRelevanceStrength(RelevanceStrength.POSSIBLE_ANSWER);
            activeAdvice.addAdviceClause(this, "mega_notPosOr_negAnd" + (anonymousClauseIndex++) + predSuffix, rule, assertedClauses);

            if (comboNegAND != null) {
                rule = comboPosAND.getConjunction(comboNegAND.getNegationByFailure());
                rule.setRelevanceStrength(RelevanceStrength.POSSIBLE_ANSWER);
                activeAdvice.addAdviceClause(this, "mega_posAnd_notNegAnd" + (anonymousClauseIndex++) + predSuffix, rule, assertedClauses);

                rule = comboPosAND.getNegationByFailure().getConjunction(comboNegOR);
                rule.setRelevanceStrength(RelevanceStrength.POSSIBLE_ANSWER);
                activeAdvice.addAdviceClause(this, "mega_negPosAnd_negOr" + (anonymousClauseIndex++) + predSuffix, rule, assertedClauses);

                that = comboNegAND == null ? null : comboNegAND.getNegationByFailure();
                rule = comboPosOR.getConjunction(that);
                rule.setRelevanceStrength(RelevanceStrength.POSSIBLE_ANSWER);
                activeAdvice.addAdviceClause(this, "mega_posOr_notNegAnd" + (anonymousClauseIndex++) + predSuffix, rule, assertedClauses);

                rule = comboNotPosOR.getConjunction(comboNegOR);
                rule.setRelevanceStrength(RelevanceStrength.POSSIBLE_ANSWER);
                activeAdvice.addAdviceClause(this, "mega_negPosOr_negOr" + (anonymousClauseIndex++) + predSuffix, rule, assertedClauses);
            }

        }
        else if (comboNegAND != null) {
            // At this point, the positive combos will null.  Thus, there are only four negative rules to generate.
            // corresponding directly to comboNegAND and comboNegatedNegOR, since the other four will be
            // redundant.
            rule = comboNegAND.getNegationByFailure();
            rule.setRelevanceStrength(RelevanceStrength.POSSIBLE_ANSWER);
            activeAdvice.addAdviceClause(this, "mega_posAnd_notNegAnd" + (anonymousClauseIndex++) + predSuffix, rule, assertedClauses);

            rule = comboNegAND;
            rule.setRelevanceStrength(RelevanceStrength.POSSIBLE_ANSWER);
            activeAdvice.addAdviceClause(this, "mega_notPosAnd_negAnd" + (anonymousClauseIndex++) + predSuffix, rule, assertedClauses);

            rule = comboNotNegOR;
            rule.setRelevanceStrength(RelevanceStrength.POSSIBLE_ANSWER);
            activeAdvice.addAdviceClause(this, "mega_posAnd_notNegOr" + (anonymousClauseIndex++) + predSuffix, rule, assertedClauses);

            rule = comboNegOR;
            rule.setRelevanceStrength(RelevanceStrength.POSSIBLE_ANSWER);
            activeAdvice.addAdviceClause(this, "mega_negPosAnd_negOr" + (anonymousClauseIndex++) + predSuffix, rule, assertedClauses);
        }

        return assertedClauses;
    }

    private int getIndexOfRelevanceClauseInformationUptoRenaming(Collection<? extends RelevantInformation> list, RelevantInformation info) {

        int index = -1;

        int count = 0;

        for (RelevantInformation rci : list) {
            if (rci.isEquivalentUptoVariableRenaming(info)) {

//                if ( debugLevel >= 1 ) Utils.print("  Equivalent:");
//                if ( debugLevel >= 1 ) Utils.print("    " + rci);
//                if ( debugLevel >= 1 ) Utils.print("    " + info);
//
//                rci.isEquivalentUptoVariableRenaming(info);

                index = count;
                break;
            }
            count++;
        }
        return index;
    }

    private int getIndexOfSubsumedRelevanceClauseInformation(Collection<? extends RelevantInformation> list, RelevantInformation info) {

        int index = -1;

        int count = 0;

        for (RelevantInformation rci : list) {
            if (rci.subsumes(info)) {

                index = count;
                break;
            }
            count++;
        }
        return index;
    }

    private boolean shouldBeSplit(RelevantClauseInformation rci, Variable variableBeingConsidered, Term backwardMapping) {
//        if ( rci.example.containsThisVariable(variableBeingConsidered)) {
//            return true;
//        }
//        else {
//            return false;
//        }

        return false;
    }

    private List<RelevantClauseInformation> createConjunctiveClauses(MapOfSets<Example, RelevantClauseInformation> exampleToSplitVariableMap) {
        List<List<RelevantClauseInformation>> pieceList = new ArrayList<List<RelevantClauseInformation>>();

        for (Set<RelevantClauseInformation> set : exampleToSplitVariableMap.values()) {
            List<RelevantClauseInformation> rcisForExampleList = new ArrayList<RelevantClauseInformation>(set);
            pieceList.add(rcisForExampleList);
        }

        int numberOfPieces = exampleToSplitVariableMap.size();

        List<List<RelevantClauseInformation>> clausesAsLists = Utils.getCombinations(pieceList);

        List<RelevantClauseInformation> result = new ArrayList<RelevantClauseInformation>();

        for (List<RelevantClauseInformation> combination : clausesAsLists) {
            RelevantClauseInformation newConjunctRCI = null;
            Set<RelevantClauseInformation> addedPieces = new HashSet<RelevantClauseInformation>();

            for (RelevantClauseInformation anRCIPiece : combination) {

                // Don't duplicate already added pieces ... this doesn't guarantee there
                // won't be some duplication (since this doesn't check a canonical form)
                // but it will reduce them.
                if (getIndexOfRelevanceClauseInformationUptoRenaming(addedPieces, anRCIPiece) == -1) {
                    addedPieces.add(anRCIPiece);

                    if (newConjunctRCI == null) {
                        newConjunctRCI = anRCIPiece;
                    }
                    else {
                        newConjunctRCI = newConjunctRCI.getConjunction(anRCIPiece);
                    }
                }
            }

            //newConjunctRCI.setContainsAllAdvicePieces(combination.size() == numberOfPieces || combination.size() == 1);
            newConjunctRCI.setContainsAllAdvicePieces(addedPieces.size() == numberOfPieces || addedPieces.size() == 1);

            result.add(newConjunctRCI);

        }

        return result;

    }

    private List<Clause> generateActiveAdviceForRCIs(ActiveAdvice activeAdvice, MapOfSets<Example, RelevantClauseInformation> rcis, String namePrefix, RelevanceStrength minimumRelevanceStrength, RelevanceStrength positiveClauseStrength, RelevanceStrength negativeClauseStrength) {

        List<Clause> clauses = new ArrayList<Clause>();
        String name;

        String predSuffix = "";
        if (getStringHandler().getInventedPredicateNameSuffix().isEmpty() == false) {
            predSuffix = getStringHandler().getInventedPredicateNameSuffix();
            if (predSuffix.startsWith("_") == false) {
                predSuffix = "_" + predSuffix;
            }
        }

        for (Set<RelevantClauseInformation> set : rcis.values()) {
            for (RelevantClauseInformation rci : set) {
                if (positiveClauseStrength.isEqualOrStronger(minimumRelevanceStrength)) {
                    name = namePrefix + (anonymousClauseIndex++) + predSuffix;
                    rci.setRelevanceStrength(positiveClauseStrength);
                    activeAdvice.addAdviceClause(this, name, rci, clauses);

                    if (negativeClauseStrength.isEqualOrStronger(minimumRelevanceStrength)) {
                        RelevantClauseInformation not = rci.getNegationByFailure();
                        not.setRelevanceStrength(negativeClauseStrength);
                        name = "not_" + name;
                        activeAdvice.addAdviceClause(this, name, not, clauses);
                    }
                }
            }
        }

        return clauses;
    }

    private Clause createdNegationByFailure(Literal head) {
        if (head == null) {
            return null;
        }

        PredicateName pName = head.predicateName;
        PredicateName pNameNOT = stringHandler.getPredicateName("not_" + pName);
        PredicateName negByFail = stringHandler.standardPredicateNames.negationByFailure;
        Literal lhs = stringHandler.getLiteral(pNameNOT, head.getArguments());
        Literal rhs = stringHandler.getLiteral(negByFail, stringHandler.getSentenceAsTerm(stringHandler.getClause(head, false), "not(" + head.toString(Integer.MAX_VALUE) + ")"));
        Clause result = stringHandler.getClause(lhs, rhs);

        //	Utils.waitHere("createdNegationByFailure: " + result);

//    	Example debugExample1 = stringHandler.getLiteral(stringHandler.standardPredicateNames.write, lhs.convertToFunction(stringHandler));
//    	result.negLiterals.add(0, debugExample1);
//    	Example debugExample0 = stringHandler.getLiteral(stringHandler.standardPredicateNames.write);
//    	result.negLiterals.add(0, debugExample0);
//    	Example debugExampleN = stringHandler.getLiteral(stringHandler.standardPredicateNames.write, stringHandler.getFunction(stringHandler.getFunctionName("reachedTheEnd"), lhs.convertToFunction(stringHandler), null));
//    	result.negLiterals.add(debugExampleN);

        return result;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Old/Unused Methods">
    private Set<Term> getUnsplitableTerms(RelevantClauseInformation rci) {
        Set<Term> set = new HashSet<Term>();
        for (Integer exampleArgumentIndex : unsplitableExamplePositions) {
            if (exampleArgumentIndex < 0 || exampleArgumentIndex >= rci.example.getArity()) {
                Utils.waitHere("Error: Example argument index " + exampleArgumentIndex + " specified as unsplitable, but example arity = " + rci.example.getArity() + ".");
            }
            else {
                set.add(rci.example.getArgument(exampleArgumentIndex));
            }
        }
        return set;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Noisy Advice Generation Methods">
    public void createNoisyBackgroundFiles(List<? extends Example> positiveExamples, List<? extends Example> negativeExamples) {
        // I moved the pre-processing into this method so we could deal with the negative
        // "did you mean X or not X" examples advice that was set to be positive.
        // As a side-effect, you can call this from the outside instead of calling
        // processRelevantClauses().
        verifyNegativeAdviceOnOriginalExampleEnabled = false;

        MapOfSets<Example, RelevantClauseInformation> exampleToAdviceMap = createExampleToAdviceMap(relevantClauses);

        // <editor-fold defaultstate="collapsed" desc="Debug Printing">
        if (debugLevel >= 2) {
            Utils.print("% [AdviceProcessor] All Grounded-Clauses Advice Map:" + "\n");
            Utils.print(exampleToAdviceMap.toString("% [AdviceProcessor]   "));
            Utils.print("\n");
        }// </editor-fold>

        // Update the ground examples relevanceFromPositiveExample/negative status according to the positiveExample/negativeExamples lists.
        // This will also remove any relevance that is not associate with an current relevanceFromPositiveExample or negative example.
        MapOfSets<Example, RelevantClauseInformation> activeExampleToAdviceMap = createActiveExampleMap(context, exampleToAdviceMap, positiveExamples, negativeExamples, RelevanceStrength.getWeakestRelevanceStrength());

        // <editor-fold defaultstate="collapsed" desc="Debug Printing">
        if (debugLevel >= 2) {
            Utils.print("% [AdviceProcessor] All Active Clauses (with duplicates):" + "\n");
            Utils.print(activeExampleToAdviceMap.toString("% [AdviceProcessor]   "));
            Utils.print("\n");
        }// </editor-fold>

        // Filter out duplicate relevance statements that exist on multiple examples.
        MapOfSets<Example, RelevantClauseInformation> filteredGroundedRelevance = filterDuplicateRelevance(activeExampleToAdviceMap);

        for (double probOfDropping : droppingProbs) {
            for (int runNumber = 1; runNumber <= (probOfDropping < 0.000001 ? 1 : numberOfRuns); runNumber++) {
                String marker = (probOfDropping < 0.000001 ? "_all" : "_prob" + Utils.truncate(100 * probOfDropping, 0) + "_run" + runNumber + "_");
                String fileName = learnOneClause.getDirectoryName() + "/clauseNoise/" + (learnOneClause.getPrefix() == null ? "unspecifiedPrefix" : learnOneClause.getPrefix()) + marker + "AdviceClauseRel" + Utils.defaultFileExtensionWithPeriod;
                createNoisyBackgroundfile(filteredGroundedRelevance, fileName, probOfDropping);
            }
        }
        Utils.println("% Done making noisy advice files.");
        throw new WILLjumpOutOfHere("Done making noisy advice files.");

    }

    private void createNoisyBackgroundfile(MapOfSets<Example, RelevantClauseInformation> filteredGroundedRelevance, String fileName, double provided_probOfDroppingExample) {


        File file = Utils.ensureDirExists(fileName);

        double probOfDroppingExample = provided_probOfDroppingExample; // We will adjust this as needed.

        int sizeOrigClauses = 0;
        List<RelevantClauseInformation> originalRelevances = new ArrayList<RelevantClauseInformation>(4);
        List<Example> keys = new ArrayList<Example>(4);
        for (Example key : filteredGroundedRelevance.keySet()) {
            Set<RelevantClauseInformation> info = filteredGroundedRelevance.getValues(key);

            for (Iterator<RelevantClauseInformation> rels = info.iterator(); rels.hasNext();) {
                RelevantClauseInformation rel = rels.next();

                originalRelevances.add(rel);
                keys.add(key); // We are keeping these lists in synch, so add key every time.
                Clause origClause = rel.getClauseWithConstantsMarker(); // NOTE: to parse in later, we need the parentheses around the clause.

                sizeOrigClauses += (origClause != null ? Utils.getSizeSafely(origClause.posLiterals) : 0);
            }
        }


        boolean reportInWHILE = true;
        boolean acceptable = false;
        int attempts = 0;
        int desiredSizeNewClauses = (int) Math.round((1 - probOfDroppingExample) * sizeOrigClauses);
        List<Clause> noisyClauses = new ArrayList<Clause>(originalRelevances.size());

        if (desiredSizeNewClauses == sizeOrigClauses) { // No need to add noise.
            acceptable = true;

            for (int i = 0; i < originalRelevances.size(); i++) {
                RelevantClauseInformation rel = originalRelevances.get(i);
                Example key = keys.get(i);
                Clause origClause = rel.getClauseWithConstantsMarker();
                noisyClauses.add(origClause);
            }
        }

        while (!acceptable && attempts < 10000) { // Defer printing to a file until an acceptable fraction of the literals have been dropped.
            int sizeNewClauses = 0;
            desiredSizeNewClauses = (int) Math.round((1 - probOfDroppingExample) * sizeOrigClauses);

            for (int i = 0; i < originalRelevances.size(); i++) {
                RelevantClauseInformation rel = originalRelevances.get(i);
                Example key = keys.get(i);
                Clause origClause = rel.getClauseWithConstantsMarker();
                String str = "\n% DRAFT #" + attempts + ": ORIGINAL\n% relevantClause: " + key + "\n% : " + origClause.toString(Integer.MAX_VALUE) + ", " + rel.getFinalRelevanceStrength() + ".";
                if (reportInWHILE) {
                    Utils.println(str);

                }
                Clause noisyClause = randomlyDropNegLiteralsFromEnd(origClause, probOfDroppingExample);
                noisyClauses.add(noisyClause); // OK TO ADD null HERE.
                int noiseClauseSize = (noisyClause != null ? Utils.getSizeSafely(noisyClause.posLiterals) : 0);
                sizeNewClauses += noiseClauseSize;
                if (noiseClauseSize > 0) {
                    String str2 = " DRAFT #" + attempts + ": relevantClause: " + key + "\n  : " + noisyClause.toString(Integer.MIN_VALUE) + ", " + rel.getFinalRelevanceStrength() + ".";
                    if (reportInWHILE) {
                        Utils.println(str2);

                    }
                }
                else {
                    if (reportInWHILE) {
                        Utils.println("% DRAFT #" + attempts + ": [AdviceProcessor]     All Examples in the body were deleted.");

                    }
                }
            }
            attempts++;
            acceptable = Math.abs(sizeNewClauses - desiredSizeNewClauses) < 1;
            if (!acceptable) { // Every now and then report.  Let these be wait
                if (attempts % 100 == 0) {
                    Utils.waitHere("\n% [AdviceProcessor] ATTEMPT #" + Utils.comma(attempts) + " Current prob = " + Utils.truncate(probOfDroppingExample, 3) + " orig prob = " + Utils.truncate(provided_probOfDroppingExample, 3)
                            + "\n% [AdviceProcessor]  Printed noisy BK file to : \n% [AdviceProcessor] " + fileName
                            + "\n% [AdviceProcessor]  |orig| = " + sizeOrigClauses + " |final| = " + sizeNewClauses + " desired = " + desiredSizeNewClauses);

                }
                if (sizeNewClauses > desiredSizeNewClauses) {
                    probOfDroppingExample *= 1.05;
                } // Too few dropped.
                if (sizeNewClauses < desiredSizeNewClauses) {
                    probOfDroppingExample *= 0.95;
                } // Too many dropped.

                if (probOfDroppingExample >= 0.9999) {
                    probOfDroppingExample = 0.9999;
                }
                if (probOfDroppingExample <= 0.0001) {
                    probOfDroppingExample = 0.0001;
                }
            }
        }

        CondorFileOutputStream outStream;
        try {
            outStream = new CondorFileOutputStream(file);
            PrintStream pStream = new PrintStream(outStream, false);

            pStream.println("import: \"../" + learnOneClause.getPrefix() + "_allSupplementalAdvice" + Utils.defaultFileExtensionWithPeriod + "\";\n");
            pStream.println("import: \"../" + learnOneClause.getPrefix() + "_allFeatureAdvice" + Utils.defaultFileExtensionWithPeriod + "\";\n");

            for (int i = 0; i < originalRelevances.size(); i++) {
                RelevantClauseInformation rel = originalRelevances.get(i);
                Example key = keys.get(i);
                Clause noisyClause = noisyClauses.get(i);
                Clause origClause = rel.getClauseWithConstantsMarker(); // NOTE: to parse in later, we need the parentheses around the clause.

                String str = "\n% ORIGINAL\n% relevantClause: " + key + "\n% : " + origClause.toString(Integer.MIN_VALUE) + ", " + rel.getFinalRelevanceStrength() + ".";
                pStream.println(str);
                Utils.println(str);
                int noiseClauseSize = (noisyClause != null ? Utils.getSizeSafely(noisyClause.posLiterals) : 0);
                if (noiseClauseSize > 0) {
                    String str2 = "  relevantClause: " + key + "\n  : " + noisyClause.toString(Integer.MIN_VALUE) + ", " + rel.getFinalRelevanceStrength() + ".";
                    pStream.println(str2);
                    Utils.println(str2);
                }
                else {
                    pStream.println("%    All Examples in the body were deleted.");
                    Utils.println("% [AdviceProcessor]     All Examples in the body were deleted.");
                }
            }
            pStream.close();
        } catch (FileNotFoundException e) {
            Utils.reportStackTrace(e);
            Utils.error("Unable to successfully open this file for writing: " + fileName + ".  Error message: " + e.getMessage());
        }
    }

    // NOTE: this method reaches clauses that only contain POS Literals (these will become the BODY of some unnamed clause).
    private Clause randomlyDropNegLiteralsFromEnd(Clause c, double probOfDroppingExample) {
        if (c == null || Utils.getSizeSafely(c.posLiterals) < 1) {
            return null;
        }
        int counter = Utils.getSizeSafely(c.posLiterals);
        List<Literal> newPosLits = new ArrayList<Literal>(counter);
        newPosLits.addAll(c.posLiterals);

        Utils.println("% [AdviceProcessor]  randonmlyDropNegLiteralsFromEnd: counter = " + counter + "  prob = " + probOfDroppingExample + " newPosLits = " + newPosLits);

        while (counter > 0) {
            double rand = Utils.random();
            if (rand <= probOfDroppingExample) {
                counter--;
                Utils.println("       drop " + newPosLits.get(counter) + "     counter = " + counter + "  prob = " + probOfDroppingExample + ">" + rand + " newPosLits = " + newPosLits);
                newPosLits.remove(counter); // Drop the last Example.
            }
            else {
                return stringHandler.getClause(newPosLits, c.negLiterals);
            }
        }

        return null; // All Examples were dropped.
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Assert/Retract Advice Methods">
    public void retractRelevanceAdvice() {
        int modeCount = 0;
        int clauseCount = 0;

        if (assertedRelevanceModes.size() > 0) {
            if (learnOneClause != null && constraint != null) {
                learnOneClause.removeModeConstraint(constraint);
                constraint = null;
            }



            for (PredicateNameAndArity predicateNameAndArity : assertedRelevanceModes) {

                modeCount++;

                if (debugLevel >= 3) {
                    Utils.println("% [AdviceProcessor] retractRelevanceAdvice: retracted mode for " + predicateNameAndArity + ".");
                }

                stringHandler.removePredicateWithKnownModes(predicateNameAndArity);

                if (learnOneClause != null) {
                    learnOneClause.removeBodyMode(predicateNameAndArity);
                }
            }
        }

        if (assertedRelevanceClauses.size() > 0) {

            for (PredicateNameAndArity predicateNameAndArity : assertedRelevanceClauses) {

                if (debugLevel >= 3) {
                    Utils.println("% [AdviceProcessor] retractRelevanceAdvice: retracted clause definition for " + predicateNameAndArity + ".");
                }

                //    Collection<Clause> clauses = context.getClausebase().getBackgroundKnowledge(predicateNameAndArity.getPredicateName(), predicateNameAndArity.getArity());

                clauseCount++;

                context.getClausebase().retractAllClausesForPredicate(predicateNameAndArity);

            }



            assertedRelevanceClauses = new HashSet<PredicateNameAndArity>();
        }

        if (debugLevel >= 1) {
            Utils.println("% [AdviceProcessor] Retracted " + clauseCount + " clauses and " + modeCount + " modes.");
        }
        else if (Utils.getSizeSafely(assertedRelevanceModes) > 0) {
            Utils.println("% [AdviceProcessor] retractRelevanceAdvice: there are " + Utils.comma(assertedRelevanceModes) + " assertedRelevanceModes to retract.");
        }

        assertedRelevanceModes = new HashSet<PredicateNameAndArity>();
        assertedRelevanceClauses = new HashSet<PredicateNameAndArity>();
    }

    public void assertRelevanceAdvice(ActiveAdvice activeAdvice, RelevanceStrength minimumStrength) {

        for (ActiveAdvice.RelevanceInfo relevanceInfo : activeAdvice.getFeatureRelevances()) {
            if (relevanceInfo.strength.isEqualOrStronger(minimumStrength)) {
                PredicateNameAndArity pnaa = relevanceInfo.predicate;
                RelevanceStrength oldStrength = pnaa.getPredicateName().getRelevance(pnaa.getArity());

                getStringHandler().setRelevance(pnaa.getPredicateName(), pnaa.getArity(), relevanceInfo.strength);

                if (debugLevel >= 3) {
                    Utils.println("% [AdviceProcessor] Setting Feature Relevance for " + pnaa + " to " + relevanceInfo.strength);
                }

                originalRelevantStrengths.put(pnaa, oldStrength);
            }

        }

        int modeCount = 0;
        int clauseCount = 0;

        for (ModeInfo modeInfo : activeAdvice.getModes()) {
            if (modeInfo.strength.isEqualOrStronger(minimumStrength)) {

                if (assertedRelevanceModes.contains(modeInfo.predicate)) {
                    System.out.println("Doh!");
                }

                modeCount++;

                stringHandler.recordModeWithTypes(modeInfo.predicate, modeInfo.signature, modeInfo.specs, 1, Integer.MAX_VALUE, false);

                if (Double.isNaN(modeInfo.cost) == false) {
                    modeInfo.predicate.setCost(modeInfo.cost);
                }

                if (learnOneClause != null) {
                    learnOneClause.addBodyMode(modeInfo.predicate);
                }

                stringHandler.setRelevance(modeInfo.predicate.getPredicateName(), modeInfo.predicate.getArity(), modeInfo.strength);

                assertedRelevanceModes.add(modeInfo.predicate);
                if (modeInfo.predicate.isInlined() == false) {
                    modeInfo.predicate.markAsSupportingPredicate(true);
                }

                if (debugLevel >= 3) {
                    Utils.println("% [AdviceProcessor] Set mode for " + modeInfo.predicate + " to " + modeInfo.specs + ".");
                }
            }
        }

        for (Map.Entry<PredicateNameAndArity, Set<ActiveAdvice.ClauseInfo>> entry : activeAdvice.getClauses().entrySet()) {
            if (context.getClausebase().checkForPossibleMatchingBackgroundKnowledge(entry.getKey().getPredicateName(), entry.getKey().getArity()) == false) {
                for (ActiveAdvice.ClauseInfo clauseInfo : entry.getValue()) {
                    if (clauseInfo.strength.isEqualOrStronger(minimumStrength)) {
                        clauseCount++;

                        context.assertDefiniteClause(clauseInfo.getClause());

                        assertedRelevanceClauses.add(clauseInfo.getClause().getDefiniteClauseHead().getPredicateNameAndArity());

                        if (debugLevel >= 3) {
                            Utils.println("% [AdviceProcessor] Asserted clause " + clauseInfo.getClause().toPrettyString("% [AdviceProcessor]                     ", Integer.MAX_VALUE, 1) + ".");
                        }
                    }
                }
            }
        }

        for (List<Clause> list : activeAdvice.getSupportClauses().values()) {
            for (Clause clause : list) {
                if (context.getClausebase().checkForPossibleMatchingBackgroundKnowledge(clause.getDefiniteClauseHead().predicateName, clause.getDefiniteClauseHead().getArity()) == false) {

                    context.assertDefiniteClause(clause);

                    assertedRelevanceClauses.add(clause.getDefiniteClauseHead().getPredicateNameAndArity());

                    if (debugLevel >= 3) {
                        Utils.println("% [AdviceProcessor] Asserted clause " + clause.toPrettyString("% [AdviceProcessor]                     ", Integer.MAX_VALUE, 1) + ".");
                    }
                }
            }
        }


        applyModeConstraint();

        if (debugLevel >= 1) {
            Utils.println("% [AdviceProcessor]  Asserted " + clauseCount + " clauses and " + modeCount + " modes.");
        }
    }

    private void applyModeConstraint() {

        if (learnOneClause != null) {
            if (constraint != null) {
                learnOneClause.removeModeConstraint(constraint);
            }
            constraint = new MutuallyExclusiveModeConstraint(assertedRelevanceModes, 1);
            learnOneClause.addModeConstraint(constraint);
        }
    }
    // </editor-fold>

    //  <editor-fold defaultstate="collapsed" desc="Accessors (addAdvice, hasAdvice, getAdvice, getUnique, etc.)">
    public void addGroundedAdvice(Example example, boolean positiveExample, Clause relevanceClause, RelevanceStrength relevanceStrength) {

        RelevantClauseInformation rci = new RelevantClauseInformation(example, relevanceClause);
        rci.setRelevanceFromPositiveExample(positiveExample);
        rci.setOriginalRelevanceStrength(relevanceStrength);

        relevantClauses.add(rci);
    }

    public void addGroundedAdvice(List<RelevantClauseInformation> relevantClauseList) {
        if (debugLevel >= 1) {
            Utils.print("% [AdviceProcessor] Added Grounded Advice: " + relevantClauseList + "\n");
        }
        relevantClauses.addAll(relevantClauseList);
    }

    public List<RelevantClauseInformation> getGroundedAdvice() {
        return relevantClauses;
    }

    public void addRelevantFeature(Example example, boolean positiveExample, PredicateNameAndArity predicateNameAndArity, RelevanceStrength relevanceStrength) {


        RelevantFeatureInformation rfi = new RelevantFeatureInformation(example, predicateNameAndArity, relevanceStrength);

        if (relevantFeatures.contains(rfi) == false) {
            relevantFeatures.add(rfi);

            if ( debugLevel >= 1 ) Utils.print("% [AdviceProcessor] Added Relevant Feature Advice: " + rfi + "\n");
        }
    }

    public void addRelevantMode(Example example, boolean positiveExample, Literal mode, RelevanceStrength relevanceStrength) {


        RelevantModeInformation rfi = new RelevantModeInformation(example, positiveExample, mode, relevanceStrength);

        if (relevantModes.contains(rfi) == false) {
            relevantModes.add(rfi);

            if ( debugLevel >= 1 ) Utils.print("% [AdviceProcessor] Added Relevant Mode Advice: " + rfi + "\n");
        }
    }

    public int getAnonymousClauseIndex() {
        return anonymousClauseIndex;
    }

    public void setAnonymousClauseIndex(int anonymousClauseIndex) {
        this.anonymousClauseIndex = anonymousClauseIndex;
    }

    public boolean hasRelevantClauses(Example example) {
        boolean result = false;

        if (relevantClauses != null) {
            for (RelevantClauseInformation RelevantClauseInformationCopy : relevantClauses) {
                if (RelevantClauseInformationCopy.example.equals(example)) {
                    result = true;
                    break;
                }
            }
        }

        return result;
    }

    public boolean hasRelevantFeatures(Example example) {
        boolean result = false;

        if (relevantFeatures != null) {
            for (RelevantFeatureInformation relevantFeatureInformation : relevantFeatures) {
                if (relevantFeatureInformation.example.equals(example)) {
                    result = true;
                    break;
                }
            }
        }

        return result;
    }

    public boolean hasRelevantInformation(Example example) {
        return hasRelevantClauses(example) || hasRelevantFeatures(example);
    }

    public List<RelevantClauseInformation> getRelevantClausesForExample(Example example) {
        List<RelevantClauseInformation> result = new ArrayList<RelevantClauseInformation>();

        if (relevantClauses != null) {
            for (RelevantClauseInformation RelevantClauseInformationCopy : relevantClauses) {
                if (RelevantClauseInformationCopy.example.equals(example)) {
                    result.add(RelevantClauseInformationCopy);
                }
            }
        }

        return result;
    }

    public List<RelevantFeatureInformation> getRelevantFeatureForExample(Example example) {
        List<RelevantFeatureInformation> result = new ArrayList<RelevantFeatureInformation>();

        if (relevantFeatures != null) {
            for (RelevantFeatureInformation relevantFeatureInformation : relevantFeatures) {
                if (relevantFeatureInformation.example.equals(example)) {
                    result.add(relevantFeatureInformation);
                }
            }
        }

        return result;
    }

    public List<RelevantInformation> getRelevantInformationForExample(Example example) {
        List<RelevantInformation> result = new ArrayList<RelevantInformation>();

        if (relevantFeatures != null) {
            for (RelevantFeatureInformation relevantFeatureInformation : relevantFeatures) {
                if (relevantFeatureInformation.example.equals(example)) {
                    result.add(relevantFeatureInformation);
                }
            }
        }

        if (relevantClauses != null) {
            for (RelevantClauseInformation info : relevantClauses) {
                if (info.example.equals(example)) {
                    result.add(info);
                }
            }
        }

        return result;
    }

    public boolean removeUnsplitableExamplePosition(int o) {
        return unsplitableExamplePositions.remove(o);
    }

    public void clearUnsplitableExamplePositions() {
        unsplitableExamplePositions.clear();
    }

    public boolean addUnsplitableExamplePosition(int e) {
        return unsplitableExamplePositions.add(e);
    }

    public List<Example> getExamplesWithUniqueAdvice(List<? extends Example> examplesToCheck) {

        List<RelevantInformation> riForExamples = new ArrayList<RelevantInformation>();
        for (Example Example : examplesToCheck) {
            riForExamples.addAll(getRelevantInformationForExample(Example));
        }
        MapOfSets<Example, RelevantInformation> exampleToAdviceMap = createExampleToAdviceMap(riForExamples);

        // Filter out duplicate relevance statements that exist on multiple examples.
        MapOfSets<Example, RelevantInformation> filteredGroundedRelevance = filterDuplicateRelevance(exampleToAdviceMap);

        List<Example> examplesWithAdvice = new ArrayList<Example>(filteredGroundedRelevance.keySet());

        return examplesWithAdvice;
    }

    public boolean isVerifyAdviceOnOriginalExampleEnabled() {
        return verifyNegativeAdviceOnOriginalExampleEnabled;
    }

    public void setVerifyAdviceOnOriginalExample(boolean verifyAdviceOnOriginalExample) {
        this.verifyNegativeAdviceOnOriginalExampleEnabled = verifyAdviceOnOriginalExample;
    }

    public boolean isOutputArgumentsEnabled() {
        return outputArgumentsEnabled;
    }

    public void setOutputArgumentsEnabled(boolean outputArgumentsEnabled) {
        this.outputArgumentsEnabled = outputArgumentsEnabled;
    }

    public HornClauseContext getContext() {
        return learnOneClause.getContext();
    }

    public boolean isInliningEnabled() {
        return inliningEnabled;
    }

    public void setInliningEnabled(boolean inliningEnabled) {
        this.inliningEnabled = inliningEnabled;
    }

    public boolean isRemoveDuplicateDeterminatesEnabled() {
        return removeDuplicateDeterminatesEnabled;
    }

    public void setRemoveDuplicateDeterminatesEnabled(boolean removeDuplicateDeterminatesEnabled) {
        this.removeDuplicateDeterminatesEnabled = removeDuplicateDeterminatesEnabled;
    }

    public boolean isVerifyAllPredicateExist() {
        return verifyAllPredicateExist;
    }

    public void setVerifyAllPredicateExist(boolean verifyAllPredicateExist) {
        this.verifyAllPredicateExist = verifyAllPredicateExist;
    }

    public boolean isVerifyInputsToFunctionsAsPredAreBoundEnabled() {
        return verifyInputsToFunctionsAsPredAreBoundEnabled;
    }

    public void setVerifyInputsToFunctionsAsPredAreBoundEnabled(boolean verifyInputsToFunctionsAsPredAreBoundEnabled) {
        this.verifyInputsToFunctionsAsPredAreBoundEnabled = verifyInputsToFunctionsAsPredAreBoundEnabled;
    }

    public boolean isVerifyNegativeAdviceOnOriginalExampleEnabled() {
        return verifyNegativeAdviceOnOriginalExampleEnabled;
    }

    public void setVerifyNegativeAdviceOnOriginalExampleEnabled(boolean verifyNegativeAdviceOnOriginalExampleEnabled) {
        this.verifyNegativeAdviceOnOriginalExampleEnabled = verifyNegativeAdviceOnOriginalExampleEnabled;
    }

    public boolean isVerifyPositiveAdviceOnOriginalExampleEnabled() {
        return verifyPositiveAdviceOnOriginalExampleEnabled;
    }

    public void setVerifyPositiveAdviceOnOriginalExampleEnabled(boolean verifyPositiveAdviceOnOriginalExampleEnabled) {
        this.verifyPositiveAdviceOnOriginalExampleEnabled = verifyPositiveAdviceOnOriginalExampleEnabled;
    }

    public boolean isRemoveDoubleNegationEnabled() {
        return removeDoubleNegationEnabled;
    }

    public void setRemoveDoubleNegationEnabled(boolean removeDoubleNegationEnabled) {
        this.removeDoubleNegationEnabled = removeDoubleNegationEnabled;
    }

    public List<PruningRule> getPruningRules() {
        return pruningRules;
    }

    public final void addPruningRule(PruningRule rule) {
        if (pruningRules == null) {
            pruningRules = new ArrayList<PruningRule>();
        }
        pruningRules.add(rule);
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Relevant Clause Listener Class">
    private void setupRelevantClauseListener(HornClauseContext context) {
        this.relevantClauseListener = new RelevantClauseListener();
        context.getClausebase().addAssertRetractListener(relevantClauseListener, stringHandler.getPredicate("relevant_clause", 3));

        context.getClausebase().addAssertRetractListener(relevantClauseListener, stringHandler.getPredicate("relevant_unsplitable_index", 1));

        context.getClausebase().addAssertRetractListener(relevantClauseListener, stringHandler.getPredicate("relevant_feature", 3));

        context.getClausebase().addAssertRetractListener(relevantClauseListener, stringHandler.getPredicate("relevant_mode", 3));
    }

    public class RelevantClauseListener implements AssertRetractListener {

        @Override
        public void clauseAsserted(HornClausebase context, DefiniteClause clause) {

            if (clause.isDefiniteClauseFact() == false) {
                Utils.waitHere("Illegal relevantClause specification '" + clause + "'.  Must be fact of form relevant_clause(Example, Clause, RelevantStrength.");
            }

            Literal lit = clause.getDefiniteClauseFactAsLiteral();

            if (lit.predicateName.name.equals("relevant_clause")) {

                try {
                    Literal relevantLiteral = ((Function) lit.getArgument(0)).convertToLiteral(stringHandler);
                    Sentence s = ((SentenceAsTerm) lit.getArgument(1)).sentence;
                    RelevanceStrength strength = RelevanceStrength.valueOf(((StringConstant) lit.getArgument(2)).getBareName().toUpperCase());

                    Clause relevantClause;
                    if (s instanceof Literal) {
                        Example Example = new Example((Literal) s);
                        relevantClause = stringHandler.getClause(Example, true);
                    }
                    else {
                        relevantClause = (Clause) s;
                    }

                    addGroundedAdvice(new Example(relevantLiteral), true, relevantClause, strength);
                } catch (ClassCastException castException) {
                    //	Utils.reportStackTrace(castException);
                    Utils.waitHere(castException + "\nIllegal relevantClause specification '" + clause + "'.\nMust be fact of form: relevant_clause(Example, Clause, RelevantStrength.");
                }
            }
            else if (lit.predicateName.name.equals("relevant_unsplitable_index")) {
                try {
                    NumericConstant indexConstant = (NumericConstant) lit.getArgument(0);
                    int index = indexConstant.value.intValue();

                    addUnsplitableExamplePosition(index);

                } catch (ClassCastException castException) {
                    //	Utils.reportStackTrace(castException);
                    Utils.waitHere(castException + "\nIllegal relevantClause specification '" + clause + "'.  Must be fact of form relevant_clause(Example, Clause, RelevantStrength.");
                }
            }
            else if (lit.predicateName.name.equals("relevant_feature")) {
                Example relevantLiteral = new Example((Function) lit.getArgument(0));

                String nameAndArityString = ((StringConstant) lit.getArgument(1)).getBareName();
                int index = nameAndArityString.indexOf("/");
                String name = nameAndArityString.substring(0, index);
                String arityString = nameAndArityString.substring(index + 1);
                int arity = Integer.parseInt(arityString);

                PredicateNameAndArity pnaa = stringHandler.getPredicate(name, arity);
                RelevanceStrength strength = RelevanceStrength.valueOf(((StringConstant) lit.getArgument(2)).getBareName().toUpperCase());

//                addRelevantFeature(relevantLiteral, true, pnaa, strength);
            }
            else if (lit.predicateName.name.equals("relevant_mode")) {
                Example relevantLiteral = new Example((Function) lit.getArgument(0));
                Literal mode = ((Function) lit.getArgument(1)).asLiteral();
                RelevanceStrength strength = RelevanceStrength.valueOf(((StringConstant) lit.getArgument(2)).getBareName().toUpperCase());

                addRelevantMode(relevantLiteral, true, mode, strength);
            }

        }

        @Override
        public void clauseRetracted(HornClausebase context, DefiniteClause clause) {
            throw new UnsupportedOperationException("Not supported yet.");
        }
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Split Variable Collector Visitor Classes">
    public class CollectSplitableVariablePositionVisitor extends ElementPositionVisitor<CollectSplitableVariableData> {

        @Override
        public Term visitVariable(Variable varBeingSplit, CollectSplitableVariableData data) {
            if (unsplitableExamplePositions.contains(data.getCurrentPosition().getIndex()) == false) {

                Term backwardMapping = data.relevantClauseInformation.getBackwardMappingForTerm(varBeingSplit);

                if (backwardMapping != null && shouldBeSplit(data.relevantClauseInformation, varBeingSplit, backwardMapping)) {
                    data.markSplittablePosition(varBeingSplit);
                }
            }

            return varBeingSplit;
        }
    }

    public static class CollectSplitableVariableData extends ElementPositionData {

        RelevantClauseInformation relevantClauseInformation;

        MapOfSets<Variable, ElementPath> splittablePositions = new MapOfSets<Variable, ElementPath>();

        public CollectSplitableVariableData(RelevantClauseInformation relevantClauseInformation) {
            this.relevantClauseInformation = relevantClauseInformation;
        }

        public void markSplittablePosition(Variable variable) {
            splittablePositions.put(variable, currentPosition);
        }
    }// </editor-fold>
}
