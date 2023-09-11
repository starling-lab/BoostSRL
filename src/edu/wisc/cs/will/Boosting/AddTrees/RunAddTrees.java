/**
 * Code to add decision lists obtained from boosted trees using Boosted RDN learning method.
 */
package edu.wisc.cs.will.Boosting.AddTrees;

import com.hp.hpl.jena.tdb.store.Hash;
import edu.wisc.cs.will.Boosting.MLN.RunBoostedMLN;
import edu.wisc.cs.will.Boosting.OneClass.RunOneClassModel;
import edu.wisc.cs.will.Boosting.RDN.*;
import edu.wisc.cs.will.Boosting.RDN.Models.RelationalDependencyNetwork;
import edu.wisc.cs.will.Boosting.Regression.RunBoostedRegressionTrees;
import edu.wisc.cs.will.Boosting.Trees.RegressionTree;
import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;
import edu.wisc.cs.will.Boosting.Utils.CommandLineArguments;
import edu.wisc.cs.will.Boosting.Utils.ThresholdSelector;
import edu.wisc.cs.will.DataSetUtils.ComputeAUC;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.ILP.CoverageScore;
import edu.wisc.cs.will.ILP.LearnOneClause;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.check_disc;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.Utils.condor.CondorFileWriter;
import edu.wisc.cs.will.Utils.disc;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;
import ilp.basic.Matching;

import java.io.*;
import java.math.BigInteger;
import java.util.*;


/**
 * @author siwen
 *   copied and modified from edu.wisc.cs.will.Boosting.Common.RunBoostedModels, edu.wisc.cs.will.Boosting.RDN.RunBoostedRDN
 */
public abstract class RunAddTrees {
    public static CommandLineArguments cmdGlob;
    protected CommandLineArguments cmdArgs;
    //protected static List<Example> allExamplesList;
    //protected static Map<Example, Integer> allExamplesMap;


    public CommandLineArguments getCmdArgs() {
        return cmdArgs;
    }


    public void setCmdArgs(CommandLineArguments cmdArgs) {
        CombinedTree.cmd = cmdArgs;
        this.cmdArgs = cmdArgs;
        cmdGlob = this.cmdArgs;
    }


    protected WILLSetup setup;


    public RunAddTrees() {
    }


    public static CommandLineArguments parseArgs(String[] args) {
        CommandLineArguments cmdArgs = new CommandLineArguments();
        if (cmdArgs.parseArgs(args)) {
            return cmdArgs;
        }
        return null;
    }


    public void runJob() {
        /* train, learn */
        if (cmdArgs.isLearnVal()) {
            long start = System.currentTimeMillis();
            learnModel();
            long end = System.currentTimeMillis();
            Utils.println("\n% Total learning time ("  + Utils.comma(cmdArgs.getMaxTreesVal()) + " trees): " + Utils.convertMillisecondsToTimeSpan(end - start, 3) + ".");
        }
        /* test, infer */
        if (cmdArgs.isInferVal()) {
            long start = System.currentTimeMillis();
            inferModel();
            long end = System.currentTimeMillis();
            Utils.println("\n% Total inference time (" + Utils.comma(cmdArgs.getMaxTreesVal()) + " trees): " + Utils.convertMillisecondsToTimeSpan(end - start, 3) + ".");
        }
    }


    public static int numbModelsToMake = 1; // Each 'tree' in the sequence of the trees is really a forest of this size. TODO - allow this to be settable.
    //	public static int    numbFullTheoriesToCombine = 10; // This is the number of separate complete predictions of TESTSET probabilities to combine.  TODO - allow this to be settable.
    public static String nameOfCurrentModel = null; // "Run1"; // NOTE: file names will look best if this starts with a capital letter.  If set (ie, non-null), will write testset results out.
    public static String resultsFileMarker = null; // Allow caller to put extra markers in results file names.


    public abstract void learn();


    public void learnModel() {
        setupWILLForTrain();
        beforeLearn();
        learn();
        afterLearn();
    }


    protected void setupWILLForTrain() {
        setup = new WILLSetup();
        try {
            Utils.println("\n% Calling SETUP.");
            setup.setup(cmdArgs, cmdArgs.getTrainDirVal(), true);
        } catch (SearchInterrupted e) {
            Utils.reportStackTrace(e);
            Utils.error("Problem in setupWILLForTrain.");
        }
    }


    /**
     * Override this method if you want to take some steps before calling learn.
     */
    protected void beforeLearn() {
        Utils.println(cmdArgs.getModelDirVal());
        File dir = new CondorFile(cmdArgs.getModelDirVal());
        Utils.ensureDirExists(dir);
        // Rename old model files to prevent accidental re-use.
        renameOldModelFiles();
    }


    /**
     * Override to call methods after learning.
     */
    protected void afterLearn() {
        Utils.println("cached groundings hit: " + setup.getInnerLooper().num_hits + "\nMisses: " +setup.getInnerLooper().num_misses);
    }


    protected void clearCheckPointFiles(String saveModelName) {
        if (Utils.fileExists(BoostingUtils.getCheckPointFile(saveModelName))) {
            Utils.delete(BoostingUtils.getCheckPointFile(saveModelName));
        }
        if (Utils.fileExists(BoostingUtils.getCheckPointExamplesFile(saveModelName))) {
            Utils.delete(BoostingUtils.getCheckPointExamplesFile(saveModelName));
        }
        if (Utils.fileExists(BoostingUtils.getCheckPointFlattenedLitFile(saveModelName))) {
            Utils.delete(BoostingUtils.getCheckPointFlattenedLitFile(saveModelName));
        }
    }


    private void renameOldModelFiles() {
        for (int i = 0; i < numbModelsToMake; i++) {
            // Rename model files.
            for (String pred : cmdArgs.getTargetPredVal()) {
                String filename = BoostingUtils.getModelFile(cmdArgs, pred, true);
                File f = new CondorFile(filename);
                if (f.exists()) {
                    renameAsOld(f);
                }
            }
        }
    }


    public static void renameAsOld(File f) {
        //	File   newF         = new CondorFile(f.getAbsoluteFile() + ".old");
        /*	THIS WAS MAKING THE OLD FILE BE A DIRECTORY RATHER THAN A FILE FOR SOME ODD REASON (JWS)  ...
         * */
        String justFileName = f.getName();
        File parent = f.getParentFile();
        File newF = new CondorFile(parent, "old_" + justFileName);
        //	Utils.waitHereRegardless("renameAsOld: " + f + "\n name = " + justFileName + "\n parent = " + parent + "\n newF = " + newF);
        if (newF.exists()) {
            if (!newF.delete()) {
                Utils.error("Couldn't delete the file: " + newF.getAbsolutePath());
            }
        }
        if (!f.renameTo(newF)) {
            Utils.error("Couldn't rename from " + f.getAbsolutePath() + " to " + newF.getAbsolutePath());
        }
    }


    public abstract void loadModel();


    public abstract void infer();


    public void inferModel() {
        if (!setupWILLForTest()) {
            return;
        }
        beforeInfer();
        infer();
        afterInfer();
    }


    protected void afterInfer() {
    }


    protected void beforeInfer() {
        loadModel();
        if (cmdArgs.outFileSuffix != null) {
            cmdArgs.setModelFileVal(cmdArgs.outFileSuffix);
        }
    }


    protected boolean setupWILLForTest() {
        if(cmdArgs.isDisabledBoosting()) {  // Added By Navdeep Kaur to make Disable Boosting (-noBoost) work
            cmdArgs.setMaxTreesVal(1);
        }
        setup = new WILLSetup();
        try {
            if(!setup.setup(cmdArgs, cmdArgs.getTestDirVal(), false)) {
                Utils.println("\nSetup failed (possibly because there are no examples), so will not infer anything.");
                return false;
            }
        } catch (SearchInterrupted e) {
            Utils.reportStackTrace(e);
            Utils.error("Problem in inferModel.");
        }
        return true;
    }

    // overall compress clause entry
    protected static Clause compressClause(Clause inputClause, int iteration, String method) {
        if (method.equalsIgnoreCase("naive")) {
            return compressClause(prepareClause(inputClause), iteration);
        } else if (method.equalsIgnoreCase("subsume")) {
            return compressClauseSubsume(prepareClause(inputClause), iteration);
        } else {
            return inputClause;
        }
    }

    // overall compress clauses entry
    protected static List<Clause> compressClauses(List<Clause> inputClauses, int iteration, String method) {
        if (method.equalsIgnoreCase("naive")) {
            return compressClauses(inputClauses, iteration);
        } else if (method.equalsIgnoreCase("subsume")) {
            return compressClausesSubsume(inputClauses, iteration);
        } else {
            return inputClauses;
        }
    }

    // merge postive literals and clean up negative literals
    protected static Clause prepareClause(Clause inputClause) {
        /* Change variables, may need to order predicates for later simplification */
        // create new variables
        int k = inputClause.getPosLiteral(0).numberArgs() - 1;
        List<Term> terms = new ArrayList<Term>();
        for (int j = 0; j < k; j++) {
            // .pushVariable is used to create new variable
            // .getVariableOrConstant can help get variable if created or create variable
            terms.add(inputClause.getStringHandler().pushVariable((TypeSpec) null, HandleFOPCstrings.alphabet2[j]));
        }
        // create binding for variables in posLiterals
        BindingList bl = new BindingList();
        for (Literal lit : inputClause.getPositiveLiterals()) {
            for (int j = 0; j < lit.numberArgs() - 1; j++) {
                if (lit.getArgument(j) instanceof Variable) {
                    bl.addBinding((Variable) lit.getArgument(j), terms.get(j));
                }
            }
        }
        // create binding for unbounded variables which appear once
        // and variables which appear multiple times only in negLiterals
        for (Literal lit : inputClause.getNegativeLiterals()) {
            for (int j = 0; j < lit.numberArgs(); j++) {
                if (lit.getArgument(j) instanceof Variable) {
                    Variable tmpVar = (Variable) lit.getArgument(j);
                    // actually, only `bl.getMapping(tmpVar) == null` is enough
                    if (tmpVar.name.equals("_") || bl.getMapping(tmpVar) == null) {
                        // the variable names in alphabet2 are limited, which may cause array index out bound error
                        // so make new variable name "$alphabet2[k % len(alphabet2)]" + (k / len(alphabet2) == 0 ? "" : "k / len(alphabet2)")
                        bl.addBinding(tmpVar, inputClause.getStringHandler().pushVariable((TypeSpec) null,
                                HandleFOPCstrings.alphabet2[k % HandleFOPCstrings.alphabet2Size]
                                        + (k / HandleFOPCstrings.alphabet2Size == 0 ? "" : k / HandleFOPCstrings.alphabet2Size)));
                        k++;
                    }
                }
            }
        }
        // apply bindings
        Clause outputClause = inputClause.applyTheta(bl.theta);
        //oneClause = decisionLists.get(i);
        // sort before creating binding for unbounded variable in negLiterals
        // for the ease of removing clause with duplicate negative literals part later
        //Collections.sort(oneClause.negLiterals, new Comparator<Literal>() {
        //    @Override
        //    public int compare(Literal o1, Literal o2) {
        //        return o1.toString().compareTo(o2.toString());
        //    }
        //});
        //BindingList bl2 = new BindingList();
        // apply bindings
        //decisionLists.set(i, oneClause.applyTheta(bl2.theta));

        /* Combine positive literals of each clause */
        double number = 0;
        for (Literal lit : outputClause.getPositiveLiterals()) {
            number += ((NumericConstant) lit.getArgument(lit.numberArgs() - 1)).value.doubleValue();
        }
        List<Term> termArgs = new ArrayList<Term>(outputClause.getPosLiteral(0).getArguments());
        termArgs.set(termArgs.size() - 1, outputClause.getStringHandler().getNumericConstant(number));
        List<Literal> lits = new ArrayList<Literal>(1);
        lits.add(outputClause.getStringHandler().getLiteral(outputClause.getPosLiteral(0).getPredicateName(), termArgs));
        return outputClause.getStringHandler().getClause(lits, outputClause.negLiterals);
    }

    // compress one clause with naive check
    protected static Clause compressClause(Clause inputClause, int iteration) {
        // use to check correctness
        //if (iteration == 5 || iteration == 13) {
        //    System.out.println(inputClause);
        //}

        /* Simplify negative literals of each clause */
        // remove duplicate predicates
        // and simplify the case siblingof(A,C) ^ siblingof(A,D) -> siblingof(A,C)
        // may also need to consider the case siblingof(A,C) ^ male(C) ^ siblingof(A,D) ^ male(D) -> siblingof(A,C) ^ male(C)
        // can be solved by just replacing any variable not in head by "_" and the predicates with the same string will be
        // replaced by the one with the highest number of appearance of the variable, not replace if there is a tie
        List<Literal> updatedLits = new ArrayList<Literal>();
        Set<String> hashSet = new HashSet<String>();
        for (Literal lit: inputClause.getNegativeLiterals()) {
            StringBuilder sb = new StringBuilder();
            sb.append(lit.getPredicateName().name).append("(");
            for (int j = 0; j < lit.numberArgs(); j++) {
                if (j > 0) {
                    sb.append(", ");
                }
                if (lit.getArgument(j) instanceof Variable && inputClause.countVarOccurrencesInFOPC((Variable) lit.getArgument(j)) == 1) {
                    sb.append("_");
                } else {
                    sb.append(lit.getArgument(j).toString());
                }
            }
            sb.append(")");
            if (hashSet.add(sb.toString())) {
                updatedLits.add(lit);
            }
        }
        // use to check correctness
        Clause clauseToPrint = inputClause.getStringHandler().getClause(inputClause.posLiterals, updatedLits);
        //if (iteration == 5 || iteration == 13) {
        //    System.out.println("compressed to");
        //    System.out.println(clauseToPrint);
        //    System.out.println();
        //}
        return clauseToPrint;
    }

    // compress multiple clauses with naive check
    protected static List<Clause> compressClauses(List<Clause> inputClauses, int iteration) {
        // Remove the negative literals part duplicate
        Set<String> hashSet = new HashSet<String>();
        List<Clause> updatedClauses = new ArrayList<Clause>();
        for (Clause oneClause : inputClauses) {
            List<Literal> negLits = oneClause.getNegativeLiterals();
            List<String> negLitsStrs = new ArrayList<String>(negLits.size());
            for (Literal negLit : negLits) {
                // remove some uncertainty caused by the appearance order
                // not useful for now
                //StringBuilder sb = new StringBuilder();
                //sb.append(negLit.getPredicateName().name).append("(");
                //for (int j = 0; j < negLit.numberArgs(); j++) {
                //    if (j > 0) {
                //        sb.append(", ");
                //    }
                //    if (oneClause.countVarOccurrencesInFOPC((Variable) negLit.getArgument(j)) == 1) {
                //        sb.append("_");
                //    } else {
                //        sb.append(negLit.getArgument(j).toString());
                //    }
                //}
                //sb.append(")");
                negLitsStrs.add(negLit.toString());
            }
            Collections.sort(negLitsStrs);
            if (hashSet.add(negLitsStrs.toString())) {
                updatedClauses.add(oneClause);
            }
            //else if (iteration == 5 || iteration == 13) { // use to check correctness
            //    System.out.println(oneClause);
            //    System.out.println("removed because same clause exists.");
            //    System.out.println();
            //}
        }
        // Remove the negative literals part of which the previous list is a sub, i.e. current entails the previous
        // this is hard since they may contain variables with different names
        // select matching number of each predicate name and do unification, time complexity may be high
        // a method might be adapted from the duplicate predicates removal

        // a naive check for entailment, need to update both for full check and efficiency
        List<String> listNoEntail = new ArrayList<String>();
        List<Clause> outputClauses = new ArrayList<Clause>();
        for (Clause oneClause : updatedClauses) {
            List<Literal> negLits = oneClause.getNegativeLiterals();
            StringBuilder sb = new StringBuilder();
            boolean first = true;
            for (Literal negLit : negLits) {
                if (first) {
                    first = false;
                } else {
                    sb.append(", ");
                }
                sb.append(negLit.toString());
            }
            // naive check of entailment
            boolean contained = false;
            String strNegLits = sb.toString();
            for (String s : listNoEntail) {
                if (strNegLits.contains(s)) {
                    contained = true;
                    // use to check correctness
                    //if (iteration == 5 || iteration == 13) {
                    //    System.out.println(oneClause);
                    //    System.out.println("removed because " + s + " is its substring.");
                    //    System.out.println();
                    //}
                    break;
                }
            }
            if (!contained) {
                listNoEntail.add(strNegLits);
                outputClauses.add(oneClause);
            }
        }
        return outputClauses;
    }

    /*protected static class LiteralWrapper {
        protected Literal lit;
        protected LiteralWrapper(Literal lit) {
            this.lit = lit;
        }
        protected Literal getLit() {
            return this.lit;
        }
    }*/

    protected static Literal getRoot(Literal lit, Map<Literal, Literal> map) {
        Literal parent = map.get(lit);
        List<Literal> list = new ArrayList<Literal>();
        while (parent != lit) { // search the root
            list.add(lit);
            lit = parent;
            parent = map.get(parent);
        }
        // compress the path
        for (Literal l : list) {
            map.put(l, parent);
        }
        return parent;
    }

    protected static List<List<Literal>> groupLiterals(List<Literal> literals) {
        // create a graph G(V,E) first
        // then do search to find all connected components
        //List<Literal> posLits = inputClause.getPositiveLiterals();
        //List<Literal> negLits = inputClause.getNegativeLiterals();
        // a map from variable to a list of literal, constant doesn't matter
        // arguments from head/positiveLiterals aren't considered as connection
        //Set<Term> excludedSet = new HashSet<Term>();
        //for (Literal posLit : posLits) {
        //    for (int i = 0; i < posLit.numberArgs() - 1; i++) {
        //        if (posLit.getArgument(i) instanceof Variable) {
        //            excludedSet.add(posLit.getArgument(i));
        //        }
        //    }
        //}

        // each list is a group, then combine groups with same literals
        // not only edge connects nodes, but also node connects edges
        // union-find: keep merging and compressing, always one step from root
        // needs Map<Literal, Literal> : parent of literal, and Map<Term, Literal> : root of argument
        Map<Literal, Literal> parentMap = new HashMap<Literal, Literal>(literals.size());
        for (Literal negLit : literals) {
            parentMap.put(negLit, negLit);
        }
        // use Term as key is fine, its equals check address
        Map<Term, Literal> rootMap = new HashMap<Term, Literal>();
        // to check getRoot outOfSpace bug
        //System.out.println("getRoot: group by variables.");
        for (Literal negLit : literals) {
            for (Term arg : negLit.getArguments()) {
                //if (arg instanceof Variable && !excludedSet.contains(arg)) {
                if (arg instanceof Variable) {
                    // this variable can be used as connection
                    if (rootMap.containsKey(arg)) {
                        // not first time
                        Literal root1 = getRoot(negLit, parentMap);
                        // there can be a bug if root1 is a root of another arg
                        // this can create a loop, lit1 -> lit2 and lit2 -> lit1
                        // always keep the rootMap updated
                        Literal root2 = rootMap.get(arg);
                        Literal root = getRoot(root2, parentMap);
                        if (root2 != root) {
                            rootMap.put(arg, root);
                            root2 = root;
                        }
                        if (root1 != root2) {
                            // do union
                            parentMap.put(root1, root2);
                        }
                        // if root1 == root2, already unioned, do nothing
                    } else {
                        // first time
                        Literal root = getRoot(negLit, parentMap);
                        rootMap.put(arg, root);
                    }
                }
            }
        }
        // to check getRoot outOfSpace bug
        //System.out.println("getRoot: shorten path.");
        // guarantee one-step to root
        for (Literal negLit : literals) {
            getRoot(negLit, parentMap);
        }
        // group literals
        Set<Literal> roots = new HashSet<Literal>(parentMap.values());
        Map<Literal, List<Literal>> groupMap = new HashMap<Literal, List<Literal>>();
        for (Literal root : roots) {
            groupMap.put(root, new ArrayList<Literal>());
        }
        for (Literal lit : parentMap.keySet()) {
            groupMap.get(parentMap.get(lit)).add(lit);
        }
        // sort by #literals in group from small to large
        // if tie, sort by #constant arguments from small to large
        List<List<Literal>> res = new ArrayList<List<Literal>>(groupMap.values());
        Collections.sort(res, new Comparator<List<Literal>>() {
            @Override
            public int compare(List<Literal> o1, List<Literal> o2) {
                if (o1.size() < o2.size()) {
                    return -1;
                } else if (o1.size() > o2.size()) {
                    return 1;
                } else {
                    int numConstants1 = 0;
                    int numConstants2 = 0;
                    for (Literal lit : o1) {
                        for (Term t : lit.getArguments()) {
                            if (!(t instanceof Variable)) { // may need to change StringConstant and NumericConstant
                                numConstants1++;
                            }
                        }
                    }
                    for (Literal lit : o2) {
                        for (Term t : lit.getArguments()) {
                            if (!(t instanceof Variable)) { // may need to change StringConstant and NumericConstant
                                numConstants2++;
                            }
                        }
                    }
                    if (numConstants1 < numConstants2) {
                        return -1;
                    } else if (numConstants1 > numConstants2) {
                        return 1;
                    } else {
                        return 0;
                    }
                }
            }
        });
        return res;
    }

    // can create a new subsume function to check multiple subsumptions at once
    // this may do multithreading to increase speed
    // Resumer2 does have multithreading
    protected static boolean subsume(String s1, String s2) {
        ilp.logic.Clause hypothesis = ilp.logic.Clause.parsePrologLikeClause(s1);
        ilp.logic.Clause example = ilp.logic.Clause.parsePrologLikeClause(s2);
        List<ilp.logic.Clause> positiveExamples = new ArrayList<ilp.logic.Clause>();
        positiveExamples.add(example);
        List<ilp.logic.Clause> negativeExamples = new ArrayList<ilp.logic.Clause>();

        ilp.basic.Matching m = new ilp.basic.Matching(positiveExamples, negativeExamples);

        boolean[] undecided = new boolean[]{true}; // used to denote which subsumption checks are of interest
        int[] result = m.evaluatePositiveExamples(hypothesis, undecided);
        if (result[0] == ilp.basic.Matching.YES) {
            return true;
        } else {
            return false;
        }
    }

    protected static boolean[] subsume(String s1, List<String> s2s) {
        ilp.logic.Clause hypothesis = ilp.logic.Clause.parsePrologLikeClause(s1);
        List<ilp.logic.Clause> positiveExamples = new ArrayList<ilp.logic.Clause>();
        for (String s2 : s2s) {
            positiveExamples.add(ilp.logic.Clause.parsePrologLikeClause(s2));
        }
        List<ilp.logic.Clause> negativeExamples = new ArrayList<ilp.logic.Clause>();

        ilp.basic.Matching m = new ilp.basic.Matching(positiveExamples, negativeExamples);

        boolean[] undecided = new boolean[s2s.size()];
        for (int i = 0; i < undecided.length; i++) {
            undecided[i] = true; // used to denote which subsumption checks are of interest
        }
        int[] result = m.evaluatePositiveExamples(hypothesis, undecided);
        boolean[] res = new boolean[result.length];
        for (int i = 0; i < result.length; i++) {
            if (result[i] == Matching.YES) {
                res[i] = true;
            } else {
                res[i] = false;
            }
        }
        return res;
    }

    protected static final String[] alphabet3 = {"a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "m", "n", "p",
        "q", "r", "s", "t", "u", "w", "x", "y", "z"}; // "l" like 1, "o" like 0, "v" means OR
    protected static final int alphabet3Size = alphabet3.length;
    // compress one clause with subsumption check
    protected static Clause compressClauseSubsume(Clause inputClause, int iteration) {
        // to check the bug
        //System.out.println(inputClause);

        // not handling functions for now
        // copy the inputClause
        //Clause inputClauseCopy = inputClause.copy(false);
        // forgot to merge positive literals and clean up negative literals first
        // need to set StringHanlder's useStrictEqualsForLiterals first
        boolean useStrictEqualsForLiterals = inputClause.getStringHandler().usingStrictEqualsForLiterals();
        inputClause.getStringHandler().setUseStrictEqualsForLiterals(true);

        // copy the negative literals / body
        // maintaining mapping of groups before and after arguments replacement and substitution
        // replace constants with lower characters for Resumer2 to recognize, this might not be necessary
        // substitute arguments from head by constants
        List<Literal> literals = new ArrayList<Literal>(inputClause.getNegLiteralCount());
        Map<Literal, Literal> litsMap = new HashMap<Literal, Literal>(literals.size());
        BindingList bl = new BindingList();
        int k = 0;
        for (Literal posLit : inputClause.getPositiveLiterals()) {
            for (int i = 0; i < posLit.numberArgs() - 1; i++) {
                if (posLit.getArgument(i) instanceof Variable) {
                    bl.addBinding((Variable) posLit.getArgument(i),
                            posLit.getStringHandler().getVariableOrConstant(alphabet3[k % alphabet3Size]
                                    + (k / alphabet3Size == 0 ? "" : k / alphabet3Size)));
                    k++;
                }
            }
        }
        for (Literal negLit : inputClause.getNegativeLiterals()) {
            //Literal newLit = negLit.getStringHandler().getLiteral(negLit.getPredicateName(), new ArrayList<Term>(negLit.getArguments()));
            Literal newLit = negLit.applyTheta(bl);
            literals.add(newLit);
            litsMap.put(newLit, negLit);
        }
        // group literals by their arguments connection except arguments from head
        // rank group by its number of literals
        // assume 1) each path is shortest; 2) larger group subsuming smaller group doesn't interest us
        // for group with same length, rank by the number of constant arguments from smaller to bigger
        List<List<Literal>> groups = groupLiterals(literals);
        // check subsumption from left to right, if subsume, remove; check whether to keep each group from left to right
        // 1st -> last, 2nd -> last, ...
        List<String> groupsString = new ArrayList<String>(groups.size());
        for (List<Literal> group : groups) {
            boolean first = true;
            StringBuilder sb = new StringBuilder();
            for (Literal lit : group) {
                if (first) {
                    sb.append(lit.toString());
                    first = false;
                } else {
                    sb.append(", ").append(lit.toString());
                }
            }
            groupsString.add(sb.toString());
        }
        boolean[] keep = new boolean[groups.size()];
        for (int i = 0; i < groupsString.size(); i++) { // the last group won't be checked neither removed
            // it's important to go over all elements: i \in [0, groupsString.size() - 1]
            keep[i] = true;
            for (int j = i + 1; j < groupsString.size(); j++) {
                if (subsume(groupsString.get(i), groupsString.get(j))) { // can be further optimized by putting all rest strings to examples
                    keep[i] = false;
                    break;
                }
            }
        }

        // compose outputClause with groups of literals left
        List<Literal> negLiterals = new ArrayList<Literal>();
        for (int i = 0; i < groups.size(); i++) {
            if (keep[i]) {
                // need to map each literal back to original
                for (Literal lit : groups.get(i)) {
                    negLiterals.add(litsMap.get(lit));
                }
                //negLiterals.addAll(groups.get(i));
            }
        }
        Clause outputClause = inputClause.getStringHandler().getClause(inputClause.getPositiveLiterals(), negLiterals);
        outputClause.getStringHandler().setUseStrictEqualsForLiterals(useStrictEqualsForLiterals);
        return outputClause;
    }

    // compress multiple clauses with subsumption check
    protected static List<Clause> compressClausesSubsume(List<Clause> inputClauses, int iteration) {
        // if the early clause subsumes the later clause, then the later clause should be removed
        // for each clause, check whether any of the early clause subsumes it, if subsumes, remove; otherwise, keep
        // may need to copy the clause and substitute arguments from head to constants
        List<String> clausesString = new ArrayList<String>(inputClauses.size());
        for (Clause oneClause : inputClauses) {
            BindingList bl = new BindingList();
            //List<Literal> literals = new ArrayList<Literal>();
            int k = 0; // arguments from head substitute to same constants
            for (Literal posLit : oneClause.getPositiveLiterals()) {
                for (int i = 0; i < posLit.numberArgs() - 1; i++) {
                    if (posLit.getArgument(i) instanceof Variable) {
                        // this guarantees arguments from head substitute to same constants
                        bl.addBinding((Variable) posLit.getArgument(i),
                                posLit.getStringHandler().getVariableOrConstant(alphabet3[k % alphabet3Size]
                                        + (k / alphabet3Size == 0 ? "" : k / alphabet3Size)));
                        k++;
                    }
                }
            }
            StringBuilder sb = new StringBuilder();
            boolean first = true;
            for (Literal negLit : oneClause.getNegativeLiterals()) {
                if (first) {
                    sb.append(negLit.applyTheta(bl).toString());
                    first = false;
                } else {
                    sb.append(", ").append(negLit.applyTheta(bl).toString());
                }
            }
            clausesString.add(sb.toString());
        }
        // no non-empty clause subsumes empty clause, so we skip check empty clause ("") subsumed.
        // but empty clause subsumes any non-empty clause in our case
        // but no worry because we will only have at most one empty clause at the end of decision list
        // we check reversely since removing later clause
        boolean[] keep = new boolean[inputClauses.size()];
        for (int i = clausesString.size() - 1; i >= 0; i--) { // important to go over all elements, i \in [0, clausesString.size() - 1]
            keep[i] = true;
            if (clausesString.get(i).equals("")) { // skip check empty clause ("") subsumed
                // since we will have at most one empty clause, so no case of empty subsumes empty
                continue;
            }
            // the first clause will be kept
            for (int j = i - 1; j >= 0; j--) { // empty string won't appear here
                if (subsume(clausesString.get(j), clausesString.get(i))) {
                    keep[i] = false;
                    break;
                }
            }
        }
        // compose outputClauses
        List<Clause> outputClauses = new ArrayList<Clause>();
        for (int i = 0; i < inputClauses.size(); i++) {
            if (keep[i]) {
                outputClauses.add(inputClauses.get(i));
            }
        }
        return outputClauses;
    }

    // extract the leaf id of the last inference
    protected static String extractLastLeafId(String s) {
        if (s == null || s.isEmpty()) {
            return "";
        }
        boolean firstUnderline = true;
        if (!"_".equals(Character.toString(s.charAt(s.length() - 1)))) {
            // the string doesn't end with an underline, this is not normal
            firstUnderline = false;
        }
        StringBuilder sb = new StringBuilder();
        for (int i = s.length() - 1; i >= 0; i--) {
            if ("_".equals(Character.toString(s.charAt(i)))) {
                if (firstUnderline) {
                    // gets to the first underline
                    firstUnderline = false;
                } else {
                    // gets to the second underline, stop
                    break;
                }
            } else {
                // copy the digit
                sb.append(s.charAt(i));
            }
        }
        return sb.reverse().toString();
    }

    protected static List<List<String>> getExamplesLeafId(List<Clause> inputClauses, int iteration, CommandLineArguments cmd, RunBoostedRDN runClass) {
        // the whole process of inference and checking whether clause-example correspondence changes
        // this is supposed to be more time consuming on the top of exact subsumption approach
        // create InferBoostedRDN for inference using of model-based pruning
        InferBoostedRDN infer = null;
        for (String pred : cmd.getTargetPredVal()) {
            infer = new InferBoostedRDN(runClass.getCmdArgs(), runClass.getFullModel().get(pred).getSetup());
        }

        JointRDNModel fullModel = new JointRDNModel();
        for (String pred : cmd.getTargetPredVal()) {
            ConditionalModelPerPredicate rdn = runClass.getFullModel().get(pred);
            ConditionalModelPerPredicate rdnDL = new ConditionalModelPerPredicate(rdn.getSetup());
            RegressionTree tree = new RegressionTree(rdn.getSetup());
            for (Clause oneClause : inputClauses) {
                tree.addClause(oneClause);
            }
            rdnDL.setTargetPredicate(rdn.getTargetPredicate());
            rdnDL.setTreePrefix(rdn.getTreePrefix());
            rdnDL.addTree(tree, rdn.getStepLength(0), 0);
            rdnDL.updateSetOfTrees();
            rdnDL.setNumTrees(1);

            fullModel.put(pred, rdnDL);
        }

        infer.runInference(fullModel, runClass.getCmdArgs().getThreshold());

        LearnOneClause innerLooper = null;
        for (String pred : cmd.getTargetPredVal()) {
            innerLooper = runClass.getFullModel().get(pred).getSetup().getInnerLooper();
        }
        List<Example> examples = new ArrayList<Example>(innerLooper.getNumberOfPosExamples() + innerLooper.getNumberOfNegExamples());
        examples.addAll(innerLooper.getPosExamples());
        examples.addAll(innerLooper.getNegExamples());

        //HandleFOPCstrings stringHandler = innerLooper.getStringHandler();
        //boolean useStrictEqualsForLiterals = stringHandler.usingStrictEqualsForLiterals();
        //stringHandler.setUseStrictEqualsForLiterals(true);
        // test whether the example address changes

        // test whether the leaf id changes


        // create a map of examples to leafId
        // duplicate examples have equal leafId
        List<List<String>> examplesLeafId = new ArrayList<List<String>>(examples.size());
        //Map<String, String> examplesLeafId = new HashMap<String, String>(examples.size());
        // may need to deal with duplicate examples and sort to make sure the order of examples doesn't change each time
        // remove duplicate examples
        Set<String> exampleSet = new HashSet<>();
        for (Example ex : examples) {
            if (exampleSet.add(ex.toString())) {
                examplesLeafId.add(new ArrayList<String>(Arrays.asList(ex.toString(), extractLastLeafId(((RegressionRDNExample) ex).leafId))));
            }
        }
        // sort to make sure the order of examples doesn't change each time
        Collections.sort(examplesLeafId, new Comparator<List<String>>() {
            @Override
            public int compare(List<String> o1, List<String> o2) {
                return o1.get(0).compareTo(o2.get(0));
            }
        });
        return examplesLeafId;
    }

    // prune both within-clause and between-clauses to make the size of decision list as small as possible
    protected static List<Clause> pruneClauses(List<Clause> inputClauses, int iteration, CommandLineArguments cmd, RunBoostedRDN runClass) {
        // may need to set maxNumberTrees to 1 in cmd and cmdArgs since we only infer using our decision list
        runClass.getCmdArgs().setMaxTreesVal(1);
        cmd.setMaxTreesVal(1);
        // first, prune between-clauses: just remove all clauses that are never true for training data
        // this reduces the number of clauses that we need to do within-clause pruning
        // this should be fair enough, since boosted RDN learns on training data only
        List<List<String>> examplesLeafId = getExamplesLeafId(inputClauses, iteration, cmd, runClass);
        Set<Integer> leafIdSet = new HashSet<Integer>();
        for (List<String> eLI : examplesLeafId) {
            leafIdSet.add(Integer.valueOf(eLI.get(1)));
        }
        List<Integer> leafIdList = new ArrayList<Integer>(leafIdSet);
        Collections.sort(leafIdList);
        List<Clause> outputClauses = new ArrayList<Clause>(leafIdList.size());
        for (Integer leafId : leafIdList) {
            // leaf id starts from 1, we need to minus 1 to select corresponding clause
            outputClauses.add(inputClauses.get(leafId - 1));
        }

        // Second, prune within-clause: keep the clause and example correspondence not change
        // Before and after pruning one clause, the examples true at this clause are still true;
        // false at this clause are still false
        // Remove a group of literals or one literal at a time, until go over all literals;
        // The order of removal may decide how many literals we can remove
        // Try going over each group of literals, starting from the longest one
        /*for (Clause inputClause : outputClauses) {
            // need to set StringHanlder's useStrictEqualsForLiterals first
            boolean useStrictEqualsForLiterals = inputClause.getStringHandler().usingStrictEqualsForLiterals();
            inputClause.getStringHandler().setUseStrictEqualsForLiterals(true);

            // copy the negative literals / body
            // maintaining mapping of groups before and after arguments replacement and substitution
            // replace constants with lower characters for Resumer2 to recognize, this might not be necessary
            // substitute arguments from head by constants
            List<Literal> literals = new ArrayList<Literal>(inputClause.getNegLiteralCount());
            Map<Literal, Literal> litsMap = new HashMap<Literal, Literal>(literals.size());
            BindingList bl = new BindingList();
            int k = 0;
            for (Literal posLit : inputClause.getPositiveLiterals()) {
                for (int i = 0; i < posLit.numberArgs() - 1; i++) {
                    if (posLit.getArgument(i) instanceof Variable) {
                        bl.addBinding((Variable) posLit.getArgument(i),
                                posLit.getStringHandler().getVariableOrConstant(alphabet3[k % alphabet3Size]
                                        + (k / alphabet3Size == 0 ? "" : k / alphabet3Size)));
                        k++;
                    }
                }
            }
            for (Literal negLit : inputClause.getNegativeLiterals()) {
                //Literal newLit = negLit.getStringHandler().getLiteral(negLit.getPredicateName(), new ArrayList<Term>(negLit.getArguments()));
                Literal newLit = negLit.applyTheta(bl);
                literals.add(newLit);
                litsMap.put(newLit, negLit);
            }
            // group literals by their arguments connection except arguments from head
            // rank group by its number of literals
            // assume 1) each path is shortest; 2) larger group subsuming smaller group doesn't interest us
            // for group with same length, rank by the number of constant arguments from smaller to bigger
            List<List<Literal>> groups = groupLiterals(literals);
            // check subsumption from left to right, if subsume, remove; check whether to keep each group from left to right
            // 1st -> last, 2nd -> last, ...
            List<String> groupsString = new ArrayList<String>(groups.size());
            for (List<Literal> group : groups) {
                boolean first = true;
                StringBuilder sb = new StringBuilder();
                for (Literal lit : group) {
                    if (first) {
                        sb.append(lit.toString());
                        first = false;
                    } else {
                        sb.append(", ").append(lit.toString());
                    }
                }
                groupsString.add(sb.toString());
            }
            boolean[] keep = new boolean[groups.size()];
            for (int i = 0; i < groupsString.size(); i++) { // the last group won't be checked neither removed
                // it's important to go over all elements: i \in [0, groupsString.size() - 1]
                keep[i] = true;
                for (int j = i + 1; j < groupsString.size(); j++) {
                    if (subsume(groupsString.get(i), groupsString.get(j))) { // can be further optimized by putting all rest strings to examples
                        keep[i] = false;
                        break;
                    }
                }
            }

            // compose outputClause with groups of literals left
            List<Literal> negLiterals = new ArrayList<Literal>();
            for (int i = 0; i < groups.size(); i++) {
                if (keep[i]) {
                    // need to map each literal back to original
                    for (Literal lit : groups.get(i)) {
                        negLiterals.add(litsMap.get(lit));
                    }
                    //negLiterals.addAll(groups.get(i));
                }
            }
            Clause outputClause = inputClause.getStringHandler().getClause(inputClause.getPositiveLiterals(), negLiterals);
            outputClause.getStringHandler().setUseStrictEqualsForLiterals(useStrictEqualsForLiterals);
            return outputClause;

        }*/


        return outputClauses;
    }

    protected static void printTreesInfo(List<List<Clause>> clauses) {
        System.out.println("Print out tree information:");
        int i = 0;
        for (List<Clause> oneTree : clauses) {
            System.out.format("Print the %d tree:\n", i++);
            System.out.format("The number of clauses: %d\n", oneTree.size());
            int totalLenOneTree = 0;
            int maxLenOneClause = 0;
            for (Clause oneClause : oneTree) {
                maxLenOneClause = Math.max(maxLenOneClause, oneClause.getNegLiteralCount());
                totalLenOneTree += oneClause.getNegLiteralCount();
            }
            System.out.format("Length of the longest clause: %d\n", maxLenOneClause);
            System.out.format("Average length of clauses: %.2f\n", (double) totalLenOneTree / oneTree.size());
            System.out.println();
        }
    }

    protected static String generateLiteralsString(List<Literal> literals, boolean[] keep) {
        if (literals.size() != keep.length) {
            System.out.println("The size of literals is not equal to the length of array keep");
            return "";
        }
        boolean first = true;
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < literals.size(); i++) {
            if (keep[i]) {
                if (first) {
                    sb.append(literals.get(i).toString());
                    first = false;
                } else {
                    sb.append(", ").append(literals.get(i).toString());
                }
            }
        }
        return sb.toString();
    }

    protected static Clause reduceClause(Clause inputClause) {
        inputClause = prepareClause(inputClause);
        // not handling functions for now
        // need to set StringHanlder's useStrictEqualsForLiterals first
        boolean useStrictEqualsForLiterals = inputClause.getStringHandler().usingStrictEqualsForLiterals();
        inputClause.getStringHandler().setUseStrictEqualsForLiterals(true);

        // copy the negative literals / body
        // maintaining mapping of groups before and after arguments replacement and substitution
        // replace constants with lower characters for Resumer2 to recognize, this might not be necessary
        // substitute arguments from head by constants
        List<Literal> literals = new ArrayList<Literal>(inputClause.getNegLiteralCount());
        Map<Literal, Literal> litsMap = new HashMap<Literal, Literal>(inputClause.getNegLiteralCount());
        BindingList bl = new BindingList();
        int k = 0;
        for (Literal posLit : inputClause.getPositiveLiterals()) {
            for (int i = 0; i < posLit.numberArgs() - 1; i++) {
                if (posLit.getArgument(i) instanceof Variable) {
                    bl.addBinding((Variable) posLit.getArgument(i),
                            posLit.getStringHandler().getVariableOrConstant(alphabet3[k % alphabet3Size]
                                    + (k / alphabet3Size == 0 ? "" : k / alphabet3Size)));
                    k++;
                }
            }
        }
        for (Literal negLit : inputClause.getNegativeLiterals()) {
            Literal newLit = negLit.applyTheta(bl);
            literals.add(newLit);
            litsMap.put(newLit, negLit);
        }
        // do clause reduction
        boolean[] keep = new boolean[literals.size()];
        for (int i = 0; i < keep.length; i++) {
            keep[i] = true;
        }
        String literalsString = generateLiteralsString(literals, keep);
        for (int i = 0; i < literals.size(); i++) {
            keep[i] = false;
            String tempLiteralsString = generateLiteralsString(literals, keep);
            if (subsume(literalsString, tempLiteralsString)) {
                literalsString = tempLiteralsString;
            } else {
                keep[i] = true;
            }
        }
        // compose outputClause with literals left
        List<Literal> negLiterals = new ArrayList<Literal>();
        for (int i = 0; i < literals.size(); i++) {
            if (keep[i]) {
                // need to map each literal back to original
                negLiterals.add(litsMap.get(literals.get(i)));
            }
        }
        Clause outputClause = inputClause.getStringHandler().getClause(inputClause.getPositiveLiterals(), negLiterals);
        outputClause.getStringHandler().setUseStrictEqualsForLiterals(useStrictEqualsForLiterals);
        return outputClause;
    }

    private static class ClausePair {
        List<Literal> head;
        List<Integer> body;
        List<Integer> bodySubsume;
        List<Integer> bodyPrune;
        List<Integer> exampleList;
        List<Integer> pathExpList; // example list of this path over all examples for CiteSeerAuthor
        List<List<Integer>> exampleLists; // for each literal group in a path
        // to store the clause added to this clause
        ClausePair clP2;
        //List<Literal> head2;
        //List<Integer> body2;
        //List<Integer> exampleList2;
        //List<List<Integer>> exampleLists2;
        ClausePair(List<Literal> h, List<Integer> b) {
            this.head = h;
            this.body = b;
            exampleList = new ArrayList<Integer>();
        }
        ClausePair(List<Literal> h, List<Integer> b, List<Integer> eList) {
            this.head = h;
            this.body = b;
            this.exampleList = eList;
        }
        ClausePair(List<Literal> h, List<Integer> b, List<Integer> eList, List<List<Integer>> eLists) {
            this.head = h;
            this.body = b;
            this.exampleList = eList;
            this.exampleLists = eLists;
        }
        void setExampleList(List<Integer> eL) {
            this.exampleList = eL;
        }
        void setExampleLists(List<List<Integer>> eLs) {
            this.exampleLists = eLs;
        }
        ClausePair copy() {
            List<Literal> newHead = new ArrayList<Literal>(this.head);
            List<Integer> newBody = new ArrayList<Integer>(this.body);
            List<Integer> newExampleList = new ArrayList<Integer>(this.exampleList);
            if (this.exampleLists == null) {
                return new ClausePair(newHead, newBody, newExampleList);
            } else {
                List<List<Integer>> newExampleLists = new ArrayList<List<Integer>>(this.exampleLists);
                return new ClausePair(newHead, newBody, newExampleList, newExampleLists);
            }
        }
    }

    // substitute arguments from head by constants
    protected static void unvarHeadArgs(Clause clause, List<Literal> literals, Map<Literal, Literal> litsMap) {
        BindingList bl = new BindingList();
        int k = 0;
        for (Literal posLit : clause.getPositiveLiterals()) {
            for (int i = 0; i < posLit.numberArgs() - 1; i++) {
                if (posLit.getArgument(i) instanceof Variable) {
                    bl.addBinding((Variable) posLit.getArgument(i),
                            posLit.getStringHandler().getVariableOrConstant(alphabet3[k % alphabet3Size]
                                    + (k / alphabet3Size == 0 ? "" : k / alphabet3Size)));
                    k++;
                }
            }
        }
        for (Literal negLit : clause.getNegativeLiterals()) {
            Literal newLit = negLit.applyTheta(bl);
            literals.add(newLit);
            litsMap.put(newLit, negLit);
        }
    }

    protected static void generateLiteralGroups(List<List<Clause>> inputClauses, List<List<Literal>> litGroups, List<String> litGroupsStrs, List<List<ClausePair>> outputClausePairs) {
        // not handling functions for now
        // need to set StringHanlder's useStrictEqualsForLiterals first
        HandleFOPCstrings stringHandler = inputClauses.get(0).get(0).getStringHandler();
        boolean useStrictEqualsForLiterals = stringHandler.usingStrictEqualsForLiterals();
        stringHandler.setUseStrictEqualsForLiterals(true);
        int id = 0;
        for (List<Clause> oneTree : inputClauses) {
            List<ClausePair> clausePairs = new ArrayList<ClausePair>();
            for (Clause oneClause : oneTree) {
                // substitute arguments from head by constants
                List<Literal> literals = new ArrayList<Literal>(oneClause.getNegLiteralCount());
                Map<Literal, Literal> litsMap = new HashMap<Literal, Literal>(oneClause.getNegLiteralCount());
                unvarHeadArgs(oneClause, literals, litsMap);
                // group literals by their arguments connection except arguments from head
                // rank group by its number of literals
                // for group with same length, rank by the number of constant arguments from smaller to bigger
                List<List<Literal>> groups = groupLiterals(literals);
                List<Integer> ids = new ArrayList<Integer>();
                for (List<Literal> group : groups) {
                    List<Literal> literalGroup = new ArrayList<Literal>(group.size());
                    boolean first = true;
                    StringBuilder sb = new StringBuilder();
                    for (Literal lit : group) {
                        literalGroup.add(litsMap.get(lit));
                        if (first) {
                            sb.append(lit.toString());
                            first = false;
                        } else {
                            sb.append(", ").append(lit.toString());
                        }
                    }
                    litGroups.add(literalGroup);
                    ids.add(Integer.valueOf(id++));
                    litGroupsStrs.add(sb.toString());
                }
                clausePairs.add(new ClausePair(oneClause.getPositiveLiterals(), ids));
            }
            outputClausePairs.add(clausePairs);
        }
        stringHandler.setUseStrictEqualsForLiterals(useStrictEqualsForLiterals);
    }

    protected static boolean[][] buildSubsumeMatrix(List<String> litGroupsStrs) {
        int numLitGroups = litGroupsStrs.size();
        boolean[][] subsumeMatrix = new boolean[numLitGroups][numLitGroups];
        for (int i = 0; i < numLitGroups; i++) {
            boolean[] result = subsume(litGroupsStrs.get(i), litGroupsStrs);
            for (int j = 0; j < numLitGroups; j++) {
                subsumeMatrix[i][j] = result[j];
            }
        }
        return subsumeMatrix;
    }

    /*private static class ClauseExpPair {
        List<Integer> body;
        List<Integer> exampleList;
        ClauseExpPair(List<Integer> b, List<Integer>) {
            this.head = h;
            this.body = b;
        }
    }*/

    protected static void buildExpSetCorr(List<Clause> cls, List<ClausePair> clPairs, List<Integer> expList, int idx, Map<String, Integer> exp2Id, CommandLineArguments cmd, RunBoostedRDN runClass) {
        // the whole process of inference and record clause-example correspondence for each tree
        // create InferBoostedRDN for inference
        InferBoostedRDN infer = null;
        for (String pred : cmd.getTargetPredVal()) {
            infer = new InferBoostedRDN(runClass.getCmdArgs(), runClass.getFullModel().get(pred).getSetup());
        }

        JointRDNModel fullModel = new JointRDNModel();
        for (String pred : cmd.getTargetPredVal()) {
            ConditionalModelPerPredicate rdn = runClass.getFullModel().get(pred);
            ConditionalModelPerPredicate rdnDL = new ConditionalModelPerPredicate(rdn.getSetup());
            RegressionTree tree = new RegressionTree(rdn.getSetup());
            for (Clause oneClause : cls) {
                tree.addClause(oneClause);
            }
            rdnDL.setTargetPredicate(rdn.getTargetPredicate());
            rdnDL.setTreePrefix(rdn.getTreePrefix());
            rdnDL.addTree(tree, rdn.getStepLength(0), 0);
            rdnDL.updateSetOfTrees();
            rdnDL.setNumTrees(1);

            fullModel.put(pred, rdnDL);
        }

        infer.runInference(fullModel, runClass.getCmdArgs().getThreshold());

        LearnOneClause innerLooper = null;
        for (String pred : cmd.getTargetPredVal()) {
            innerLooper = runClass.getFullModel().get(pred).getSetup().getInnerLooper();
        }
        List<Example> examples = new ArrayList<Example>(innerLooper.getNumberOfPosExamples() + innerLooper.getNumberOfNegExamples());
        examples.addAll(innerLooper.getPosExamples());
        examples.addAll(innerLooper.getNegExamples());

        // check whether need to create example to id map
        if (exp2Id.isEmpty()) {
            int id = 0;
            for (Example ex : examples) {
                if (!exp2Id.containsKey(ex.toString())) {
                    exp2Id.put(ex.toString(), Integer.valueOf(id++));
                } // duplicate examples, only map to one id
            }
        }

        boolean[] expDuplicate = new boolean[exp2Id.size()]; // prevent duplicate examples
        // initialize
        for (int i = 0; i < expDuplicate.length; i++) {
            expDuplicate[i] = false;
        }
        if (expList == null) {
            // create example lists for a tree
            for (Example ex : examples) {
                int expId = exp2Id.get(ex.toString());
                if (!expDuplicate[expId]) {
                    expDuplicate[expId] = true;
                    clPairs.get(Integer.parseInt(extractLastLeafId(((RegressionRDNExample) ex).leafId)) - 1).exampleList.add(Integer.valueOf(expId));
                }
            }
            // sort example list for later convenience
            for (ClausePair clP : clPairs) {
                Collections.sort(clP.exampleList);
            }

        } else {
            // create example list for a literal group at idx
            for (Example ex : examples) {
                int expId = exp2Id.get(ex.toString());
                if (!expDuplicate[expId]) {
                    expDuplicate[expId] = true;
                    if (idx == Integer.parseInt(extractLastLeafId(((RegressionRDNExample) ex).leafId)) - 1) {
                        expList.add(Integer.valueOf(expId));
                    }
                }
            }
            // sort example list for later convenience
            Collections.sort(expList);
        }
    }

    protected static void buildExpSetCorr(List<List<Clause>> clauses, List<List<Literal>> literalGroups, List<List<ClausePair>> clausePairs, List<List<Integer>> litGExpLists, Map<String, Integer> example2Id, CommandLineArguments cmd, RunBoostedRDN runClass) {
        // set maxNumberTrees to 1 in cmd and cmdArgs since we only infer using one list of clauses
        runClass.getCmdArgs().setMaxTreesVal(1);
        cmd.setMaxTreesVal(1);
        HandleFOPCstrings stringHandler = clauses.get(0).get(0).getStringHandler();
        for (int i = 0; i < clauses.size(); i++) {
            // example lists for the tree
            buildExpSetCorr(clauses.get(i), clausePairs.get(i), null, -1, example2Id, cmd, runClass);
            // example list for each literal group if there are more than one literal groups in a path
            for (int j = 0; j < clauses.get(i).size(); j++) {
                if (clausePairs.get(i).get(j).body.size() > 1) {
                    // contain more than one literal group
                    for (Integer litG : clausePairs.get(i).get(j).body) {
                        List<Clause> tempClauses = new ArrayList<Clause>(clauses.get(i).size());
                        for (int k = 0; k < clauses.get(i).size(); k++) {
                            if (k == j) {
                                tempClauses.add(stringHandler.getClause(clausePairs.get(i).get(j).head, literalGroups.get(litG)));
                            } else {
                                tempClauses.add(clauses.get(i).get(k));
                            }
                        }
                        List<Integer> tempExpList = new ArrayList<Integer>();
                        buildExpSetCorr(tempClauses, null, tempExpList, j, example2Id, cmd, runClass);
                        //if (clausePairs.get(i).get(j).exampleLists == null) {
                        //    clausePairs.get(i).get(j).exampleLists = new ArrayList<List<Integer>>();
                        //}
                        //clausePairs.get(i).get(j).exampleLists.add(tempExpList); // save example list for the literal group
                        litGExpLists.add(tempExpList); // save example list for the literal group
                    }
                } else {
                    if (clausePairs.get(i).get(j).body.size() > 0) {
                        // only save non-empty literal group
                        litGExpLists.add(new ArrayList<Integer>(clausePairs.get(i).get(j).exampleList));
                    }
                }
            }
        }
    }

    protected static void buildExpSetAll(List<Clause> cls, List<Integer> expList, Map<String, Integer> exp2Id, CommandLineArguments cmd, RunBoostedRDN runClass) {
        // the whole process of inference and record clause-example correspondence for each tree
        // create InferBoostedRDN for inference
        InferBoostedRDN infer = null;
        for (String pred : cmd.getTargetPredVal()) {
            infer = new InferBoostedRDN(runClass.getCmdArgs(), runClass.getFullModel().get(pred).getSetup());
        }

        JointRDNModel fullModel = new JointRDNModel();
        for (String pred : cmd.getTargetPredVal()) {
            ConditionalModelPerPredicate rdn = runClass.getFullModel().get(pred);
            ConditionalModelPerPredicate rdnDL = new ConditionalModelPerPredicate(rdn.getSetup());
            RegressionTree tree = new RegressionTree(rdn.getSetup());
            for (Clause oneClause : cls) {
                tree.addClause(oneClause);
            }
            rdnDL.setTargetPredicate(rdn.getTargetPredicate());
            rdnDL.setTreePrefix(rdn.getTreePrefix());
            rdnDL.addTree(tree, rdn.getStepLength(0), 0);
            rdnDL.updateSetOfTrees();
            rdnDL.setNumTrees(1);

            fullModel.put(pred, rdnDL);
        }

        infer.runInference(fullModel, runClass.getCmdArgs().getThreshold());

        LearnOneClause innerLooper = null;
        for (String pred : cmd.getTargetPredVal()) {
            innerLooper = runClass.getFullModel().get(pred).getSetup().getInnerLooper();
        }
        List<Example> examples = new ArrayList<Example>(innerLooper.getNumberOfPosExamples() + innerLooper.getNumberOfNegExamples());
        examples.addAll(innerLooper.getPosExamples());
        examples.addAll(innerLooper.getNegExamples());
        boolean[] expDuplicate = new boolean[exp2Id.size()]; // prevent duplicate examples
        // initialize
        for (int i = 0; i < expDuplicate.length; i++) {
            expDuplicate[i] = false;
        }
        // create example list for a literal group/path over all examples
        for (Example ex : examples) {
            int expId = exp2Id.get(ex.toString());
            if (!expDuplicate[expId]) {
                expDuplicate[expId] = true;
                if (0 == Integer.parseInt(extractLastLeafId(((RegressionRDNExample) ex).leafId)) - 1) {
                    expList.add(Integer.valueOf(expId));
                }
            }
        }
        // sort example list for later convenience
        Collections.sort(expList);
    }

    protected static void buildExpSetAll(List<List<Clause>> clauses, List<List<Literal>> literalGroups, List<List<ClausePair>> clausePairs, List<List<Integer>> litGExpLsAll, Map<String, Integer> example2Id, CommandLineArguments cmd, RunBoostedRDN runClass) {
        // set maxNumberTrees to 1 in cmd and cmdArgs since we only infer using one list of clauses
        runClass.getCmdArgs().setMaxTreesVal(1);
        cmd.setMaxTreesVal(1);
        HandleFOPCstrings stringHandler = clauses.get(0).get(0).getStringHandler();
        for (int i = 0; i < clauses.size(); i++) {
            // example list for each literal group in a path
            for (int j = 0; j < clauses.get(i).size(); j++) {
                if (clausePairs.get(i).get(j).body.size() > 0) {
                    // contain at least one literal group
                    for (Integer litG : clausePairs.get(i).get(j).body) {
                        List<Clause> tempClauses = new ArrayList<Clause>(2);
                        // we only need this literal group as the first clause and the empty clause
                        tempClauses.add(stringHandler.getClause(clausePairs.get(i).get(j).head, literalGroups.get(litG)));
                        tempClauses.add(clauses.get(i).get(clauses.get(i).size() - 1));
                        List<Integer> tempExpList = new ArrayList<Integer>();
                        buildExpSetAll(tempClauses, tempExpList, example2Id, cmd, runClass);
                        litGExpLsAll.add(tempExpList); // save example list for the literal group
                    }
                }
            }
        }
    }

    protected static void buildExpSetPathAll(List<List<Clause>> clauses, List<List<Integer>> litG2Path, List<List<ClausePair>> clausePairs, Map<String, Integer> example2Id, CommandLineArguments cmd, RunBoostedRDN runClass) {
        // set maxNumberTrees to 1 in cmd and cmdArgs since we only infer using one list of clauses
        runClass.getCmdArgs().setMaxTreesVal(1);
        cmd.setMaxTreesVal(1);
        HandleFOPCstrings stringHandler = clauses.get(0).get(0).getStringHandler();
        for (int i = 0; i < clauses.size(); i++) {
            // example list for each path over all examples
            for (int j = 0; j < clauses.get(i).size(); j++) {
                if (clausePairs.get(i).get(j).body.size() > 0) {
                    // not empty, for empty clause, we know that every example can satisfy it
                    List<Clause> tempClauses = new ArrayList<Clause>(2);
                    // we only need this path as the first clause and the empty clause
                    tempClauses.add(clauses.get(i).get(j));
                    tempClauses.add(clauses.get(i).get(clauses.get(i).size() - 1));
                    List<Integer> tempExpList = new ArrayList<Integer>();
                    buildExpSetAll(tempClauses, tempExpList, example2Id, cmd, runClass);
                    clausePairs.get(i).get(j).pathExpList = tempExpList;

                    // build the mapping from literal group to its path
                    for (Integer litG : clausePairs.get(i).get(j).body) {
                        litG2Path.add(new ArrayList<Integer>(Arrays.asList(i, j)));
                    }
                }
            }
        }
    }

    // combine positive literals of each clause
//    protected static void addNumbers(ClausePair clP) {
//        int valueIndex = clP.head.get(0).numberArgs() - 1;
//        double number = ((NumericConstant) clP.head.get(0).getArgument(valueIndex)).value.doubleValue() + ((NumericConstant) clP.clP2.head.get(0).getArgument(valueIndex)).value.doubleValue();
//        List<Term> termArgs = new ArrayList<Term>(clP.head.get(0).getArguments());
//        termArgs.set(termArgs.size() - 1, clP.head.get(0).getStringHandler().getNumericConstant(number));
//        clP.head.set(0, clP.head.get(0).getStringHandler().getLiteral(clP.head.get(0).getPredicateName(), termArgs));
//    }

    //protected static double calProb(double potential) {
    //    return
    //}

    protected static double probOfExample(double psi) {
        // calculate probability from potential
        return Math.exp(psi) / (1 + Math.exp(psi));
    }

    /*protected static void addNumbers(ClausePair clP, boolean isBagging, int iteration) {
        // boosting: sum of potentials
        // bagging: running average of probabilities
        int valueIndex = clP.head.get(0).numberArgs() - 1;
        double number = 0;
        if (isBagging) {
            if (iteration == 1) {
                number = (probOfExample(((NumericConstant) clP.head.get(0).getArgument(valueIndex)).value.doubleValue())
                        + probOfExample(((NumericConstant) clP.clP2.head.get(0).getArgument(valueIndex)).value.doubleValue())) / 2;
            } else {
                number = (iteration * ((NumericConstant) clP.head.get(0).getArgument(valueIndex)).value.doubleValue()
                        + probOfExample(((NumericConstant) clP.clP2.head.get(0).getArgument(valueIndex)).value.doubleValue())) / (iteration + 1);
            }
        } else {
            number = ((NumericConstant) clP.head.get(0).getArgument(valueIndex)).value.doubleValue() + ((NumericConstant) clP.clP2.head.get(0).getArgument(valueIndex)).value.doubleValue();
        }
        List<Term> termArgs = new ArrayList<Term>(clP.head.get(0).getArguments());
        termArgs.set(termArgs.size() - 1, clP.head.get(0).getStringHandler().getNumericConstant(number));
        clP.head.set(0, clP.head.get(0).getStringHandler().getLiteral(clP.head.get(0).getPredicateName(), termArgs));
    }*/

    protected static void addNumbers(ClausePair clP, boolean isBagging, int iteration) {
        // boosting: sum of potentials
        // bagging: sum of probabilities
        int valueIndex = clP.head.get(0).numberArgs() - 1;
        double number = 0;
        if (isBagging) {
            if (iteration == 1) {
                number = probOfExample(((NumericConstant) clP.head.get(0).getArgument(valueIndex)).value.doubleValue())
                        + probOfExample(((NumericConstant) clP.clP2.head.get(0).getArgument(valueIndex)).value.doubleValue());
            } else {
                number = ((NumericConstant) clP.head.get(0).getArgument(valueIndex)).value.doubleValue()
                        + probOfExample(((NumericConstant) clP.clP2.head.get(0).getArgument(valueIndex)).value.doubleValue());
            }
        } else {
            number = ((NumericConstant) clP.head.get(0).getArgument(valueIndex)).value.doubleValue() + ((NumericConstant) clP.clP2.head.get(0).getArgument(valueIndex)).value.doubleValue();
        }
        List<Term> termArgs = new ArrayList<Term>(clP.head.get(0).getArguments());
        termArgs.set(termArgs.size() - 1, clP.head.get(0).getStringHandler().getNumericConstant(number));
        clP.head.set(0, clP.head.get(0).getStringHandler().getLiteral(clP.head.get(0).getPredicateName(), termArgs));
    }

    protected static ClausePair compressClause(ClausePair newClause, boolean[][] subsumeMatrix, List<List<Literal>> literalGroups, int iteration) {
        newClause.bodySubsume = new ArrayList<Integer>();
        // check literal group in clP2 subsumes any literal group in clP
        List<List<Integer>> litGroups = new ArrayList<List<Integer>>();
        // sort by length of literal group and number of constants, and remove from largest one
        for (Integer litG : newClause.body) {
            litGroups.add(new ArrayList<Integer>(Arrays.asList(litG, literalGroups.get(litG).size(), countConstants(literalGroups.get(litG)))));
        }
        for (Integer litG : newClause.clP2.body) {
            litGroups.add(new ArrayList<Integer>(Arrays.asList(litG, literalGroups.get(litG).size(), countConstants(literalGroups.get(litG)))));
        }
        Collections.sort(litGroups, new Comparator<List<Integer>>() {
            @Override
            public int compare(List<Integer> o1, List<Integer> o2) {
                // try remove longer literal group first
                if (o1.get(1) < o2.get(1)) {
                    return -1;
                } else if(o1.get(1) > o2.get(1)) {
                    return 1;
                }
                // try remove literal group with more constants first
                if (o1.get(2) < o2.get(2)) {
                    return -1;
                } else if (o1.get(2) > o2.get(2)) {
                    return 1;
                }
                // try remove literal group with larger id first
                if (o1.get(0) < o2.get(0)) {
                    return -1;
                } else if (o1.get(0) > o2.get(0)) {
                    return 1;
                }
                return 0;
            }
        });
        boolean[] keepLitG = new boolean[litGroups.size()];
        // initialize
        for (int j = 0; j < keepLitG.length; j++) {
            keepLitG[j] = true;
        }
        for (int j = litGroups.size() - 1; j >= 0; j--) {
            for (int k = 0; k < litGroups.size(); k++) {
                if (k != j && keepLitG[k] && subsumeMatrix[litGroups.get(j).get(0)][litGroups.get(k).get(0)]) {
                    keepLitG[j] = false;
                    break;
                }
            }
        }
        //for (Integer litG2 : newClause.clP2.body) {
        //    boolean isSubsume = false;
        //    for (Integer litG : newClause.body) {
        //        if (subsumeMatrix[litG2][litG]) {
        //            isSubsume = true;
        //            break;
        //        }
        //    }
        //    if (!isSubsume) { // not subsume any literal group in clP
        //        litGroups.add(litG2);
        //    }
        //}
        // check literal group in clP subsumes any literal group in clP2
        //for (Integer litG : newClause.body) {
        //    boolean isSubsume = false;
        //    for (Integer litG2 : litGroups) {
        //        if (subsumeMatrix[litG][litG2]) {
        //            isSubsume = true;
        //            break;
        //        }
        //    }
        //    if (!isSubsume) {
        //        newClause.bodySubsume.add(litG);
        //    }
        //}
        //newClause.bodySubsume.addAll(litGroups);
        for (int j = 0; j < keepLitG.length; j++) {
            if (keepLitG[j]) {
                newClause.bodySubsume.add(litGroups.get(j).get(0));
            }
        }
        Collections.sort(newClause.bodySubsume);
        return newClause;
    }

    protected static ClausePair compressClauseForPrune(ClausePair newClause, boolean[][] subsumeMatrix, int iteration) {
        List<Integer> litGs = new ArrayList<Integer>();
        boolean[] keep = new boolean[newClause.bodyPrune.size()];
        // initialize
        for (int i = 0; i < keep.length; i++) {
            keep[i] = true;
        }
        // check subsumption reversely
        // because pruneClauses has sort literal groups by length and number of constants
        // so we don't need to sort again
        for (int i = newClause.bodyPrune.size() - 1; i >= 0; i--) {
            for (int j = i - 1; j >= 0; j--) {
                if (subsumeMatrix[newClause.bodyPrune.get(i)][newClause.bodyPrune.get(j)]) {
                    keep[i] = false;
                    break;
                }
            }
        }
        for (int i = 0; i < keep.length; i++) {
            if (keep[i]) {
                litGs.add(newClause.bodyPrune.get(i));
            }
        }
        newClause.bodyPrune = litGs;
        return newClause;
    }

    protected static boolean subsume(ClausePair clPEarlier, ClausePair clPLater, boolean[][] subsumeMatrix) {
        // one clause subsumes another clause: all literal groups in the first clause should subsume at least one
        // literal group in the second clause.
        if (clPEarlier.bodySubsume.isEmpty()) {
            // empty clause subsumes all
            return true;
        } else if (clPLater.bodySubsume.isEmpty()) {
            // non-empty clause cannot subsume empty clause
            return false;
        }
        for (Integer clPE : clPEarlier.bodySubsume) {
            boolean isSubsume = false;
            for (Integer clPL : clPLater.bodySubsume) {
                if (subsumeMatrix[clPE][clPL]) {
                    isSubsume = true;
                    break;
                }
            }
            if (!isSubsume) {
                // at least one literal group in the earlier clause doesn't subsume any literal group in the later clause
                return false;
            }
        }
        return true;
    }

    protected static List<ClausePair> compressClauses(List<ClausePair> inputClauses, boolean[][] subsumeMatrix, int iteration) {
        // if the early clause subsumes the later clause, then the later clause should be removed
        // for each clause, check whether any of the early clause subsumes it, if subsumes, remove; otherwise, keep
        // from later to earlier clause, if any earlier clause subsumes the later clause, remove the later clause
        // no non-empty clause subsumes empty clause, so we skip check empty clause ("") subsumed.
        // but empty clause subsumes any non-empty clause in our case
        // but no worry because we will only have at most one empty clause at the end of decision list
        // we check reversely since removing later clause
        boolean[] keep = new boolean[inputClauses.size()];
        for (int i = inputClauses.size() - 1; i >= 0; i--) { // important to go over all elements, i \in [0, inputClauses.size() - 1]
            keep[i] = true;
            if (inputClauses.get(i).bodySubsume.isEmpty()) { // skip check empty clause ("") subsumed
                // since we will have at most one empty clause, so no case of empty subsumes empty
                continue;
            }
            // the first clause will be kept
            for (int j = i - 1; j >= 0; j--) { // empty string won't appear here
                if (subsume(inputClauses.get(j), inputClauses.get(i), subsumeMatrix)) {
                    keep[i] = false;
                    break;
                }
            }
        }
        // compose outputClauses
        List<ClausePair> outputClauses = new ArrayList<ClausePair>();
        for (int i = 0; i < inputClauses.size(); i++) {
            if (keep[i]) {
                outputClauses.add(inputClauses.get(i));
            }
        }
        return outputClauses;
    }

    protected static int countConstants(List<Literal> lits) {
        int numConstants = 0;
        for (Literal lit : lits) {
            for (Term t : lit.getArguments()) {
                if (!(t instanceof Variable)) { // may need to change StringConstant and NumericConstant
                    numConstants++;
                }
            }
        }
        return numConstants;
    }

    protected static List<Integer> unionTwoLists(List<Integer> l1, List<Integer> l2, boolean[] occupied) {
        /* occupied may be modified in this function */
        List<Integer> result = new ArrayList<Integer>();
        // assume the two lists are sorted integer list
        int left = 0;
        int right = 0;
        while (left < l1.size() && right < l2.size()) {
            if (l1.get(left).equals(l2.get(right))) {
                if (occupied == null) {
                    result.add(l1.get(left));
                } else {
                    if (!occupied[l1.get(left)]) {
                        occupied[l1.get(left)] = true;
                        result.add(l1.get(left));
                    }
                }
                left++;
                right++;
            } else if (l1.get(left) < l2.get(right)) {
                left++;
            } else {
                right++;
            }
        }
        return result;
    }

    /*protected static boolean canRemove(List<List<Integer>> litGs, List<List<Integer>> litGExpLs, boolean[] keepLitG, boolean[] examplesEval) {
        List<Integer> expsLeft = new ArrayList<Integer>();
        boolean first = true;
        boolean anyLitG = false;
        for (int i = 0; i < keepLitG.length; i++) {
            if (keepLitG[i]) {
                anyLitG = true;
                if (first) {
                    first = false;
                    expsLeft.addAll(litGExpLs.get(litGs.get(i).get(0)));
                } else {
                    expsLeft = unionTwoLists(expsLeft, litGExpLs.get(litGs.get(i).get(0)), null);
                }
            }
        }
        // check whether more examples left
        if (expsLeft.isEmpty()) {
            // no example left, the only reason is that no literal group is considered after the only one is removed
            // since we skip those never satisfied clauses
            // check in case
            // not used because of the node expansion limit of proving example satisfaction, the example list may not
            // contain all satisfied examples
            //if (anyLitG) {
            //    System.out.println("Error in the function canRemove: expsLeft is empty while there is at least one literal group.");
            //    System.out.println("litGs: " + litGs.toString());
            //    System.out.println("keepLitG: ");
            //    for (int i = 0; i < keepLitG.length; i++) {
            //        System.out.println(String.valueOf(keepLitG[i]) + ", ");
            //    }
            //    System.exit(0);
            //}
            return false;
        }
        for (Integer expId : expsLeft) {
            if (!examplesEval[expId]) {
                return false;
            }
        }
        return true;
    }*/

    /*protected static boolean canRemove(List<List<Integer>> litGs, List<List<Integer>> litGExpLs, boolean[] keepLitG, List<Integer> expsL) {
        List<Integer> expsLeft = new ArrayList<Integer>();
        boolean first = true;
        boolean anyLitG = false;
        for (int i = 0; i < keepLitG.length; i++) {
            if (keepLitG[i]) {
                anyLitG = true;
                if (first) {
                    first = false;
                    expsLeft.addAll(litGExpLs.get(litGs.get(i).get(0)));
                } else {
                    expsLeft = unionTwoLists(expsLeft, litGExpLs.get(litGs.get(i).get(0)), null);
                }
            }
        }
        // check whether more examples left
        if (isSameList(expsLeft, expsL)) {
            return true;
        } else {
            return false;
        }
    }*/

    /*protected static boolean canRemove(List<List<Integer>> litGs, List<List<Integer>> litGExpLs, boolean[] keepLitG, List<Integer> expsBefore, List<Integer> expsAdded) {
        List<Integer> expsLeft = new ArrayList<Integer>(expsBefore);
        //boolean first = true;
        //boolean anyLitG = false;
        for (int i = 0; i < keepLitG.length; i++) {
            if (keepLitG[i]) {
                //anyLitG = true;
                //if (first) {
                //    first = false;
                //    expsLeft.addAll(litGExpLs.get(litGs.get(i).get(0)));
                //} else {
                //    expsLeft = unionTwoLists(expsLeft, litGExpLs.get(litGs.get(i).get(0)), null);
                //}
                expsLeft = unionTwoLists(expsLeft, litGExpLs.get(litGs.get(i).get(0)), null);
            }
        }
        // check whether more examples left
        // whether the example coverage doesn't change after removing literal groups from the next tree
        if (isSameList(expsLeft, expsAdded)) {
            return true;
        } else {
            return false;
        }
    }*/

    protected static boolean canRemovePath(List<List<Integer>> litGCs, List<List<ClausePair>> clPairs, boolean[] keepLGC, boolean[] occupied) {
        List<Integer> expsLeft = new ArrayList<Integer>();
        boolean first = true;
        for (int i = 0; i < keepLGC.length; i++) {
            if (keepLGC[i]) {
                List<Integer> litGC = litGCs.get(i);
                if (first) {
                    first = false;
                    expsLeft.addAll(clPairs.get(litGC.get(0)).get(litGC.get(1)).pathExpList);
                } else {
                    expsLeft = unionTwoLists(expsLeft, clPairs.get(litGC.get(0)).get(litGC.get(1)).pathExpList, null);
                }
            }
        }
        // check whether more examples left
        for (Integer exp : expsLeft) {
            if (!occupied[exp]) {
                return false;
            }
        }
        //if (first) { // no path left, there won't be a case we can remove all paths
        //    return false;
        //}
        // if all examples are covered, then this clause can be empty
        if (first) {
            for (int i = 0; i < occupied.length; i++) {
                if (!occupied[i]) {
                    return false;
                }
            }
            return true;
        }
        return true;
    }

    protected static boolean canRemoveLG(List<List<Integer>> litGs, List<List<Integer>> litGExpLsAll, boolean[] keepLitG, boolean[] occupied) {
        List<Integer> expsLeft = new ArrayList<Integer>();
        boolean first = true;
        //boolean anyLitG = false;
        for (int i = 0; i < keepLitG.length; i++) {
            if (keepLitG[i]) {
                if (first) {
                    first = false;
                    expsLeft.addAll(litGExpLsAll.get(litGs.get(i).get(0)));
                } else {
                    expsLeft = unionTwoLists(expsLeft, litGExpLsAll.get(litGs.get(i).get(0)), null);
                }
            }
        }
        // check whether more examples left
        // whether the example coverage doesn't change after removing literal groups from the next tree
        for (Integer exp : expsLeft) {
            if (!occupied[exp]) {
                return false;
            }
        }
        //if (first) { // no literal group left, there won't be a case we can remove all literal groups
        //    return false;
        //}
        // if all examples are covered, then this clause can be empty
        if (first) {
            for (int i = 0; i < occupied.length; i++) {
                if (!occupied[i]) {
                    return false;
                }
            }
            return true;
        }
        return true;
    }

    protected static boolean isSameLGC(List<Integer> lGC1, List<Integer> lGC2) {
        if (lGC1.get(0).equals(lGC2.get(0)) && lGC1.get(1).equals(lGC2.get(1))) {
            return true;
        }
        return false;
    }

    protected static List<List<Integer>> combineSameLGC(List<List<Integer>> lGCs, List<List<Literal>> litGroups) {
        List<List<Integer>> lGCsCopy = new ArrayList<List<Integer>>(lGCs);
        Collections.sort(lGCsCopy, new Comparator<List<Integer>>() {
            @Override
            public int compare(List<Integer> o1, List<Integer> o2) {
                if (o1.get(0) < o2.get(0)) {
                    return -1;
                } else if (o1.get(0) > o2.get(0)) {
                    return 1;
                } else if (o1.get(1) < o2.get(1)) {
                    return -1;
                } else if (o1.get(1) > o2.get(1)) {
                    return 1;
                } else if (o1.get(2) < o2.get(2)) {
                    return -1;
                } else if (o1.get(2) > o2.get(2)) {
                    return 1;
                }
                return 0;
            }
        });
        List<List<Integer>> result = new ArrayList<List<Integer>>();
        List<Integer> prevLGC = null;
        for (List<Integer> lGC : lGCsCopy) {
            if (prevLGC == null || !isSameLGC(prevLGC, lGC)) {
                // move the literal group id to the next next
                lGC.add(lGC.get(2));
                lGC.add(lGC.get(2));
                // record the length of the literal group after tree and clause id
                lGC.set(2, litGroups.get(lGC.get(4)).size());
                // record the number of constants after the length of the literal group
                lGC.set(3, countConstants(litGroups.get(lGC.get(4))));
                prevLGC = lGC;
                result.add(lGC);
            } else {
                // add length of literal groups in the same clause together
                prevLGC.set(2, prevLGC.get(2) + litGroups.get(lGC.get(2)).size());
                // add the number of constants in the same clause together
                prevLGC.set(3, prevLGC.get(3) + countConstants(litGroups.get(lGC.get(2))));
                // add the literal group id
                prevLGC.add(lGC.get(2));
            }
        }
        return result;
    }

    protected static List<ClausePair> pruneClauses(List<ClausePair> inputClauses, int numberOfExps, List<List<Literal>> literalGroups, List<List<Integer>> litGExpLsAll, List<List<Integer>> litG2Path, List<List<ClausePair>> clausePairs, boolean[] litGBased, int iteration) {
        // List<List<Integer>> lGELAllOrPath is overloaded, either for example list of each literal group over all examples, or for mapping back to path position
        // first, prune between-clauses: just remove all clauses that are never true for training data
        // this reduces the number of clauses that we need to do within-clause pruning
        // this should be fair enough, since boosted RDN learns on training data only
        boolean[] examplesEval = new boolean[numberOfExps];
        // initialize
        for (int i = 0; i < numberOfExps; i++) {
            examplesEval[i] = false;
        }
        // clauses in the previous decision list set the level of example set, while clauses in the tree constraint and spread examples
        boolean[] keep = new boolean[inputClauses.size()];
        for (int i = 0; i < inputClauses.size(); i++) {
            keep[i] = true;
            // we can record the first one of each combination from the previous decision list, or we just start from all examples
            // compute intersection of clP and clP2
            ClausePair clP = inputClauses.get(i);
            // there won't be duplicate in clP, clP2
            // update example list
            //clP.exampleList = unionTwoLists(clP.exampleList, clP.clP2.exampleList, examplesEval);
            // check whether we need to keep an overall examples covered array
            List<Integer> expList = unionTwoLists(clP.exampleList, clP.clP2.exampleList, examplesEval);
            if (expList.isEmpty()) {
                keep[i] = false;
            } else {
                // do within-clause pruning
                if (litGBased[0]) { // try to remove literal group
                    // literal group leads to more constraint, not brings more examples
                    // only need to check whether remove one literal group will increase examples, if increase, not remove;
                    // otherwise, remove
                    // if multiple literal groups can be removed at the same time, we can certainly remove one by one
                    List<List<Integer>> litGs = new ArrayList<List<Integer>>(clP.body.size() + clP.clP2.body.size());
                    // try to remove literal groups from the next tree and the decision list
                    for (Integer litGId : clP.body) {
                        litGs.add(new ArrayList<Integer>(Arrays.asList(litGId, literalGroups.get(litGId).size(), countConstants(literalGroups.get(litGId)))));
                    }
                    for (Integer litGId : clP.clP2.body) {
                        litGs.add(new ArrayList<Integer>(Arrays.asList(litGId, literalGroups.get(litGId).size(), countConstants(literalGroups.get(litGId)))));
                    }
                    Collections.sort(litGs, new Comparator<List<Integer>>() {
                        @Override
                        public int compare(List<Integer> o1, List<Integer> o2) {
                            // try remove longer literal group first
                            if (o1.get(1) < o2.get(1)) {
                                return -1;
                            } else if(o1.get(1) > o2.get(1)) {
                                return 1;
                            }
                            // try remove literal group with more constants first
                            if (o1.get(2) < o2.get(2)) {
                                return -1;
                            } else if (o1.get(2) > o2.get(2)) {
                                return 1;
                            }
                            // try remove literal group with larger id first
                            if (o1.get(0) < o2.get(0)) {
                                return -1;
                            } else if (o1.get(0) > o2.get(0)) {
                                return 1;
                            }
                            return 0;
                        }
                    });
                    boolean[] keepLitG = new boolean[litGs.size()];
                    // initialize
                    for (int j = 0; j < keepLitG.length; j++) {
                        keepLitG[j] = true;
                    }
                    /*List<Integer> exps = new ArrayList<Integer>();
                    boolean first = true;
                    for (List<Integer> litG : litGs) {
                        if (first) {
                            first = false;
                            exps.addAll(litGExpLs.get(litG.get(0)));
                        } else {
                            exps = unionTwoLists(exps, litGExpLs.get(litG.get(0)), null);
                        }
                    }
                    if (!isSameList(clP.exampleList, exps)) {
                        System.out.println("We have different lists");
                    }*/
                    // the bug is that we cannot remove literal groups from our decision list
                    // but only the literal groups from the added next tree
                    // due to
                    //    rule11 -> rule21
                    //           -> rule22
                    //    rule12 -> rule21 // if we remove rule12 here, the example coverage of rule21 will change
                    //                        we cannot use the pre-generated one
                    //           -> rule22
                    for (int j = litGs.size() - 1; j >= 0; j--) {
                        keepLitG[j] = false;
                        if (!canRemoveLG(litGs, litGExpLsAll, keepLitG, examplesEval)) {
                            keepLitG[j] = true;
                        }
                    }
                    //clP.bodyPrune = new ArrayList<Integer>(clP.body);
                    clP.bodyPrune = new ArrayList<Integer>();
                    for (int j = 0; j < keepLitG.length; j++) {
                        if (keepLitG[j]) {
                            clP.bodyPrune.add(litGs.get(j).get(0));
                        }
                    }
                } else { // try to remove each path in current combination
                    // if we don't have correct example list of literal groups, we try to remove each path
                    // collect all path in current combination
                    List<List<Integer>> litGC = new ArrayList<List<Integer>>(clP.body.size() + clP.clP2.body.size());
                    for (Integer lGId : clP.body) {
                        List<Integer> lGC = new ArrayList<Integer>(litG2Path.get(lGId));
                        lGC.add(lGId);
                        litGC.add(lGC);
                    }
                    for (Integer lGId : clP.clP2.body) {
                        List<Integer> lGC = new ArrayList<Integer>(litG2Path.get(lGId));
                        lGC.add(lGId);
                        litGC.add(lGC);
                    }
                    List<List<Integer>> litGCCombined = combineSameLGC(litGC, literalGroups);
                    // re-sort by the clause literal groups length, number of constants
                    // try to remove the longest clause first
                    Collections.sort(litGCCombined, new Comparator<List<Integer>>() {
                        @Override
                        public int compare(List<Integer> o1, List<Integer> o2) {
                            // compare the combined length of literal groups in the same clause
                            if (o1.get(2) < o2.get(2)) { // compare clause length
                                return -1;
                            } else if (o1.get(2) > o2.get(2)) {
                                return 1;
                            } else if (o1.get(3) < o2.get(3)) { // compare number of constants
                                return -1;
                            } else if (o1.get(3) > o2.get(3)) {
                                return 1;
                            } else if (o1.get(0) < o2.get(0)) { // compare tree id
                                return -1;
                            } else if (o1.get(0) > o2.get(0)) {
                                return 1;
                            } else if (o1.get(1) < o2.get(1)) { // compare clause id
                                return -1;
                            } else if (o1.get(1) > o2.get(1)) {
                                return 1;
                            }
                            return 0;
                        }
                    });
                    boolean[] keepLGC = new boolean[litGCCombined.size()];
                    // initialize
                    for (int j = 0; j < keepLGC.length; j++) {
                        keepLGC[j] = true;
                    }
                    // try to remove each path in current combination
                    for (int j = litGCCombined.size() - 1; j >= 0; j--) {
                        keepLGC[j] = false;
                        if (!canRemovePath(litGCCombined, clausePairs, keepLGC, examplesEval)) {
                            keepLGC[j] = true;
                        }
                    }
                    clP.bodyPrune = new ArrayList<Integer>();
                    for (int j = 0; j < keepLGC.length; j++) {
                        if (keepLGC[j]) {
                            for (int k = 4; k < litGCCombined.get(j).size(); k++) {
                                clP.bodyPrune.add(litGCCombined.get(j).get(k));
                            }
                        }
                    }
                }
                // update example coverage of the added rule
                clP.exampleList = expList;
            }
            // no within clause pruning
            //clP.bodyPrune = new ArrayList<Integer>(clP.bodySubsume);
        }
        List<ClausePair> outputClauses = new ArrayList<ClausePair>();
        for (int i = 0; i < inputClauses.size(); i++) {
            if (keep[i]) {
                outputClauses.add(inputClauses.get(i));
            }
        }

        // Second, prune within-clause: keep the clause and example correspondence not change
        // Before and after pruning one clause, the examples true at this clause are still true;
        // false at this clause are still false
        // Remove a group of literals or one literal at a time, until go over all literals;
        // The order of removal may decide how many literals we can remove

        // Try going over each group of literals, starting from the longest one to shortest, if tie, more constants first
        // for shorter clause and the ease of compression later

        return outputClauses;
    }

    protected static void finishUpdate(List<ClausePair> dL) {
        for (ClausePair cP : dL) {
            if (cP.bodyPrune == null) { // model-based pruning is not done
                cP.body = cP.bodySubsume;
            } else {
                cP.body = cP.bodyPrune;
            }
            // make it appear in the order of literal group ids
            Collections.sort(cP.body);

            cP.bodySubsume = null;
            cP.bodyPrune = null;
            cP.clP2 = null;
        }
    }

    protected static void convertCP2C(List<Clause> dCL, List<ClausePair> dCPL, List<List<Literal>> litGroups) {
        for (ClausePair cP : dCPL) {
            // create new variables
            int k = cP.head.get(0).numberArgs() - 1;
            HandleFOPCstrings stringHandler = cP.head.get(0).getStringHandler();
            List<Term> terms = new ArrayList<Term>();
            Map<String, Term> termsMap = new HashMap<String, Term>(); // to make it consistent for arguments from head in body
            for (int j = 0; j < k; j++) {
                // .pushVariable is used to create new variable
                // .getVariableOrConstant can help get variable if created or create variable
                Term t = stringHandler.pushVariable((TypeSpec) null, HandleFOPCstrings.alphabet2[j]);
                terms.add(t);
                termsMap.put(((Variable) t).getName(), t);
            }
            // create binding for variables in posLiterals
            BindingList bl = new BindingList();
            for (Literal lit : cP.head) {
                for (int j = 0; j < lit.numberArgs() - 1; j++) {
                    if (lit.getArgument(j) instanceof Variable) {
                        bl.addBinding((Variable) lit.getArgument(j), terms.get(j));
                    }
                }
            }
            List<Literal> negLits = new ArrayList<Literal>();
            for (Integer litId : cP.body) {
                negLits.addAll(litGroups.get(litId));
            }
            // create binding for arguments from head
            // unbounded variables which appear once
            // and variables which appear multiple times only in negLiterals
            for (Literal lit : negLits) {
                for (int j = 0; j < lit.numberArgs(); j++) {
                    if (lit.getArgument(j) instanceof Variable) {
                        Variable tmpVar = (Variable) lit.getArgument(j);
                        if (termsMap.containsKey(tmpVar.getName())) { // arguments from head in body
                            if (bl.getMapping(tmpVar) == null) { // don't need to repeat for the same argument
                                bl.addBinding(tmpVar, termsMap.get(tmpVar.getName()));
                            }
                        } else if (bl.getMapping(tmpVar) == null) { // not have bindings yet
                            // the variable names in alphabet2 are limited, which may cause array index out bound error
                            // so make new variable name "$alphabet2[k % len(alphabet2)]" + (k / len(alphabet2) == 0 ? "" : "k / len(alphabet2)")
                            bl.addBinding(tmpVar, stringHandler.pushVariable((TypeSpec) null,
                                    HandleFOPCstrings.alphabet2[k % HandleFOPCstrings.alphabet2Size]
                                            + (k / HandleFOPCstrings.alphabet2Size == 0 ? "" : k / HandleFOPCstrings.alphabet2Size)));
                            k++;
                        }
                    }
                }
            }
            // apply bindings
            dCL.add(stringHandler.getClause(cP.head, negLits).applyTheta(bl.theta));
        }
    }

    protected static void testIO() {
        List<Integer> list = new ArrayList<Integer>();
        list.add(1);
        list.add(1);
        list.add(1);
        List<Integer> list2 = new ArrayList<Integer>();
        list2.addAll(list);
        List<List<Integer>> lists = new ArrayList<List<Integer>>();
        lists.add(list);
        lists.add(list2);
        // serialize object
        try {
            FileOutputStream fileOut = new FileOutputStream("data/CiteSeerAuthor4/errorMessage/test.ser");
            ObjectOutputStream out = new ObjectOutputStream(fileOut);
            out.writeObject(lists);
            out.close();
            fileOut.close();
            System.out.printf("Serialized data is saved in data/CiteSeerAuthor4/errorMessage/test.ser");

        } catch (IOException i) {
            i.printStackTrace();
        }
        // deserialize object
        List<List<Integer>> lists2;
        try {
            FileInputStream fileIn = new FileInputStream("data/CiteSeerAuthor4/errorMessage/test.ser");
            ObjectInputStream in = new ObjectInputStream(fileIn);
            lists2 = (List<List<Integer>>) in.readObject();
            in.close();
            fileIn.close();
        } catch (IOException i) {
            i.printStackTrace();
        } catch (ClassNotFoundException c) {
            System.out.printf("List<List<Integer>> class not found");
            c.printStackTrace();
        }
    }

    protected static void saveLists(String path, List<List<Integer>> lists) {
        // serialize object
        try {
            FileOutputStream fileOut = new FileOutputStream(path);
            ObjectOutputStream out = new ObjectOutputStream(fileOut);
            out.writeObject(lists);
            out.close();
            fileOut.close();
            System.out.printf(path);
        } catch (IOException i) {
            i.printStackTrace();
        }
    }

    protected static void saveList(String path, List<Integer> list) {
        // serialize object
        try {
            FileOutputStream fileOut = new FileOutputStream(path);
            ObjectOutputStream out = new ObjectOutputStream(fileOut);
            out.writeObject(list);
            out.close();
            fileOut.close();
            System.out.printf(path);
        } catch (IOException i) {
            i.printStackTrace();
        }
    }

    protected static void loadLists(String path, List<List<Integer>> lists) {
        // deserialize object
        try {
            FileInputStream fileIn = new FileInputStream(path);
            ObjectInputStream in = new ObjectInputStream(fileIn);
            lists.addAll((List<List<Integer>>) in.readObject());
            in.close();
            fileIn.close();
        } catch (IOException i) {
            i.printStackTrace();
        } catch (ClassNotFoundException c) {
            System.out.printf("List<List<Integer>> class not found");
            c.printStackTrace();
        }
    }

    protected static void loadList(String path, List<Integer> list) {
        // deserialize object
        try {
            FileInputStream fileIn = new FileInputStream(path);
            ObjectInputStream in = new ObjectInputStream(fileIn);
            list.addAll((List<Integer>) in.readObject());
            in.close();
            fileIn.close();
        } catch (IOException i) {
            i.printStackTrace();
        } catch (ClassNotFoundException c) {
            System.out.printf("List<Integer> class not found");
            c.printStackTrace();
        }
    }

    protected static void attachLists(List<List<ClausePair>> clauses, List<List<Integer>> litGExpLists) {
        // this is wrong, because in test_pos.txt and test_neg.txt, there are 4 targets
        //int numExps = 116679;
        int numExps = 38893;
        for (List<ClausePair> oneTree : clauses) {
            boolean[] expsEval = new boolean[numExps];
            for (int i = 0; i < expsEval.length; i++) {
                expsEval[i] = false;
            }
            for (ClausePair oneClause : oneTree) {
                if (oneClause.body.size() > 1) {
                    boolean first = true;
                    List<Integer> exps = new ArrayList<Integer>();
                    for (Integer litGId : oneClause.body) {
                        if (first) {
                            first = false;
                            exps.addAll(litGExpLists.get(litGId));
                        } else {
                            exps = unionTwoLists(exps, litGExpLists.get(litGId), null);
                        }
                    }
                    oneClause.exampleList.addAll(exps);
                    for (Integer eId : oneClause.exampleList) {
                        expsEval[eId] = true;
                    }
                } else if (oneClause.body.size() > 0) {
                    oneClause.exampleList.addAll(litGExpLists.get(oneClause.body.get(0)));
                    for (Integer eId : oneClause.exampleList) {
                        expsEval[eId] = true;
                    }
                } else {
                    //List<Integer> expL = new ArrayList<Integer>();
                    for (int j = 0; j < expsEval.length; j++) {
                        if (!expsEval[j]) {
                            oneClause.exampleList.add(j);
                        }
                    }
                }
            }
        }
    }

    protected static boolean isSameList(List<Integer> l1, List<Integer> l2) {
        if (l1.size() != l2.size()) {
            return false;
        }
        for (int i = 0; i < l1.size(); i++) {
            if (!l1.get(i).equals(l2.get(i))) {
                return false;
            }
        }
        return true;
    }

    protected static void checkExpListConflicts(List<List<ClausePair>> clauses, List<List<Integer>> litGExpLists, boolean[] litGBased) {
        for (int i = 0; i < clauses.size(); i++) {
            List<ClausePair> oneTree = clauses.get(i);
            for (int j = 0; j < oneTree.size(); j++) {
                ClausePair oneClause = oneTree.get(j);
                if (oneClause.body.size() > 1) {
                    boolean first = true;
                    List<Integer> exps = new ArrayList<Integer>();
                    for (Integer litGId : oneClause.body) {
                        if (first) {
                            first = false;
                            exps.addAll(litGExpLists.get(litGId));
                        } else {
                            exps = unionTwoLists(exps, litGExpLists.get(litGId), null);
                        }
                    }
                    //oneClause.exampleList.addAll(exps);
                    if (!isSameList(oneClause.exampleList, exps)) {
                        System.out.printf("Tree %d, clause %d: %d vs. %d", i, j, oneClause.exampleList.size(), exps.size());
                        litGBased[0] = false;
                    }
                }
            }
        }
    }

    protected static void checkExpListConsistent(List<ClausePair> dList, List<List<Integer>> litGExpLists, int numExps, List<List<Literal>> literalGroups, CommandLineArguments cmd, RunBoostedRDN runClass) {
        // check whether any example list is empty
        System.out.println("Check whether any example list is empty");
        for (int i = 0; i < dList.size(); i++) {
            if (dList.get(i).exampleList.isEmpty()) {
                System.out.printf("The example list is empty: %d clause %n", i);
            }
        }

        // whether there is any overlapping between clauses in the decision list
        System.out.println("Check whether any overlapping between clauses in the decision list.");
        for (int i = 0; i < dList.size() - 1; i++) {
            for (int j = i + 1; j < dList.size(); j++) {
                List<Integer> expLI = unionTwoLists(dList.get(i).exampleList, dList.get(j).exampleList, null);
                if (!expLI.isEmpty()) {
                    System.out.printf("Clause example list overlapping: %d vs. %d %n", i, j);
                }
            }
        }

        // whether the intersection of example coverage of literal groups equal to the example list of the clause
        System.out.println("Check whether the intersection of example coverage of literal groups equal to the example list of the clause.");
        boolean[] examplesEval = new boolean[numExps];
        // initialize
        for (int i = 0; i < numExps; i++) {
            examplesEval[i] = false;
        }
        for (int i = 0; i < dList.size(); i++) {
            ClausePair oneClause = dList.get(i);
            for (int j = 0; j < oneClause.exampleList.size(); j++) {
                examplesEval[oneClause.exampleList.get(j)] = true;
            }
            boolean first = true;
            List<Integer> exps = new ArrayList<Integer>();
            for (Integer litGId : oneClause.body) {
                if (first) {
                    first = false;
                    exps.addAll(litGExpLists.get(litGId));
                } else {
                    exps = unionTwoLists(exps, litGExpLists.get(litGId), null);
                }
            }
            for (Integer ex : exps) {
                if (!examplesEval[ex]) {
                    System.out.printf("The intersection not equal to the list: %d clause %n", i);
                }
            }
            //oneClause.exampleList.addAll(exps);
            //if (!isSameList(oneClause.exampleList, exps)) {
            //    System.out.printf("Tree %d, clause %d: %d vs. %d", i, j, oneClause.exampleList.size(), exps.size());
            //}
        }

        // whether the example list is the same as actual inference
        System.out.println("Check whether the example list equal to the actual inference.");
        // covert the decision list of ClausePair to Clause first
        List<Clause> cls = new ArrayList<Clause>();
        convertCP2C(cls, dList, literalGroups);
        // the whole process of inference and record clause-example correspondence for each tree
        // create InferBoostedRDN for inference
        InferBoostedRDN infer = null;
        for (String pred : cmd.getTargetPredVal()) {
            infer = new InferBoostedRDN(runClass.getCmdArgs(), runClass.getFullModel().get(pred).getSetup());
        }

        JointRDNModel fullModel = new JointRDNModel();
        for (String pred : cmd.getTargetPredVal()) {
            ConditionalModelPerPredicate rdn = runClass.getFullModel().get(pred);
            ConditionalModelPerPredicate rdnDL = new ConditionalModelPerPredicate(rdn.getSetup());
            RegressionTree tree = new RegressionTree(rdn.getSetup());
            for (Clause oneClause : cls) {
                tree.addClause(oneClause);
            }
            rdnDL.setTargetPredicate(rdn.getTargetPredicate());
            rdnDL.setTreePrefix(rdn.getTreePrefix());
            rdnDL.addTree(tree, rdn.getStepLength(0), 0);
            rdnDL.updateSetOfTrees();
            rdnDL.setNumTrees(1);

            fullModel.put(pred, rdnDL);
        }

        infer.runInference(fullModel, runClass.getCmdArgs().getThreshold());

        LearnOneClause innerLooper = null;
        for (String pred : cmd.getTargetPredVal()) {
            innerLooper = runClass.getFullModel().get(pred).getSetup().getInnerLooper();
        }
        List<Example> examples = new ArrayList<Example>(innerLooper.getNumberOfPosExamples() + innerLooper.getNumberOfNegExamples());
        examples.addAll(innerLooper.getPosExamples());
        examples.addAll(innerLooper.getNegExamples());

        List<Set<String>> expSets = new ArrayList<Set<String>>(dList.size());
        // initialize
        for (int i = 0; i < dList.size(); i++) {
            expSets.add(new HashSet<String>());
        }
        for (Example ex : examples) {
            expSets.get(Integer.parseInt(extractLastLeafId(((RegressionRDNExample) ex).leafId)) - 1).add(ex.toString());
        }
        for (int i = 0; i < dList.size(); i++) {
            if (dList.get(i).exampleList.size() != expSets.get(i).size()) {
                System.out.printf("Example list not equal to actual inference: %d clause, %d vs. %d. %n",
                        i, dList.get(i).exampleList.size(), expSets.get(i).size());
            }
        }

    }

    protected static void saveTreePotentialsToFile(List<List<Clause>> clauses, CommandLineArguments cmd) {
        try {
            String targetPredVal = "";
            for (String pred : cmd.getTargetPredVal()) {
                targetPredVal = pred;
            }
            BufferedWriter writer = new BufferedWriter(new CondorFileWriter(cmd.getTestDirVal() + "tree_potentials_" + targetPredVal + ".txt"));
            for (List<Clause> oneTree : clauses) {
                for (int i = 0; i < oneTree.size(); i++) {
                    Clause oneClause = oneTree.get(i);
                    Literal lit = oneClause.getPosLiteral(0);
                    writer.write(i + "\t" + lit.getArgument(lit.getArguments().size() - 1));
                    writer.newLine();
                }
            }
            writer.close();
        } catch (IOException e) {
            Utils.reportStackTrace(e);
            Utils.error("saveTreePotentialsToFile`: IO exception");
        }
    }

    protected static void saveTreeToDotFile(List<List<Clause>> clauses, RunBoostedRDN runClass, CommandLineArguments cmd) {
        //WILLSetup setup = null;
        //JointRDNModel fullModel = null;
        Theory th = null;
        for (String pred : cmd.getTargetPredVal()) {
            th = runClass.getFullModel().get(pred).getSetup().getOuterLooper().getLearnedTheory();
            //fullModel = runClass.getFullModel();
        }
        String filename = cmd.getModelDirVal() + "bRDNs/dotFiles/decisionList" + BoostingUtils.getLabelForCurrentModel() + ".dot";
        TreeStructuredTheory thry = (TreeStructuredTheory) th;
        thry.writeDOTFile(filename);
        /*try {
            Utils.ensureDirExists(filename);
            BufferedWriter writer = new BufferedWriter(new CondorFileWriter(filename, false)); // create a new file
            //RelationalDependencyNetwork rdn = new RelationalDependencyNetwork(fullModel, setup);
            //rdn.printNetworkInDOT(writer);
            writer.close();
        } catch (IOException e) {
            Utils.reportStackTrace(e);
            Utils.error("Problem in saveTreeToDotFile.");
        }*/
        System.out.println("Decision List saved at " + filename);
    }

    protected static List<List<Double>> loadResult(String path) {
        List<Double> posProbs = new ArrayList<Double>();
        List<Double> negProbs = new ArrayList<Double>();

        BufferedReader reader;
        try {
            reader = new BufferedReader(new FileReader(path));
            String line = reader.readLine();
            while (line != null) {
                line = line.trim();
                if (!line.isEmpty()) {
                    String[] parts = line.split(" ");
                    //if (parts[parts.length - 1].length() > 18) {
                    //    parts[parts.length - 1] = parts[parts.length - 1].substring(0, 18);
                    //}
                    // results_arrest.db cannot be used because the double precision of the
                    // negative examples, use aucTemp.txt instead
                    /*if (line.startsWith("!")) { // negative example
                        negProbs.add(1 - Double.parseDouble(parts[parts.length - 1]));
                    } else { // positive example
                        posProbs.add(Double.parseDouble(parts[parts.length - 1]));
                    }*/
                    if (parts[1].trim().equals("1")) { // positive example
                        posProbs.add(Double.parseDouble(parts[0].trim()));
                    } else { // negative example
                        negProbs.add(Double.parseDouble(parts[0].trim()));
                    }
                }
                line = reader.readLine();
            }
            reader.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
        List<List<Double>> probs = new ArrayList<List<Double>>(2);
        probs.add(posProbs);
        probs.add(negProbs);
        return probs;
    }

    protected static void computeBaggingF1andAUC(CommandLineArguments cmd) {
        // load the path of the results
        List<String> paths_results = new ArrayList<String>();
        BufferedReader reader;
        try {
            reader = new BufferedReader(new FileReader("paths_results.txt"));
            String line = reader.readLine();
            while (line != null) {
                line = line.trim();
                if (!line.isEmpty()) {
                    paths_results.add(line);
                }
                line = reader.readLine();
            }
            reader.close();
        } catch (IOException e) {
            e.printStackTrace();
        }

        System.out.printf("paths_results.size: %d%n", paths_results.size());

        // load the results
        List<List<List<Double>>> results = new ArrayList<>(paths_results.size());
        for (String p : paths_results) {
            System.out.println("Each path: " + p);
            results.add(loadResult(p));
        }

        //System.out.printf("results.size: %d%n", results.size());

        // calculate average probabilities
        int num_pos = results.get(0).get(0).size();
        int num_neg = results.get(0).get(1).size();
        int num_model = results.size();

        System.out.printf("num_pos: %d%n", num_pos);
        System.out.printf("num_neg: %d%n", num_neg);
        System.out.printf("num_model: %d%n", num_model);

        List<Double> posProbs = new ArrayList<>(num_pos);
        List<Double> negProbs = new ArrayList<>(num_neg);
        for (int i = 0; i < num_pos; i++) {
            double val = 0.0;
            for (int j = 0; j < num_model; j++) {
                val += results.get(j).get(0).get(i);
            }
            posProbs.add(val / num_model);
        }
        for (int i = 0; i < num_neg; i++) {
            double val = 0.0;
            for (int j = 0; j < num_model; j++) {
                val += results.get(j).get(1).get(i);
            }
            negProbs.add(val / num_model);
        }

        // find the best threshold
        ThresholdSelector selector = new ThresholdSelector();
        for (Double posP : posProbs) {
            selector.addProbResult(posP, true);
        }
        for (Double negP : negProbs) {
            selector.addProbResult(negP, false);
        }
        double threshold = selector.selectBestThreshold();

        // calculate recall, precision and f1
        CoverageScore score = new CoverageScore();
        for (Double posP : posProbs) {
            double wtOnEx = 1.0;
            if (posP > threshold) {
                score.addToTruePositive(wtOnEx);
            } else {
                score.addToFalseNegative(wtOnEx);
            }
        }
        for (Double negP : negProbs) {
            double wtOnEx = 1.0;
            if (negP > threshold) {
                score.addToFalsePositive(wtOnEx);
            } else {
                score.addToTrueNegative(wtOnEx);
            }
        }

        // compute AUC
        String aucTempDirectory = cmd.getTestDirVal() + "AUC/";
        double minRecallForAUCPR = 0.0;
        String extraMarker = "";
        ComputeAUC.deleteAUCfilesAfterParsing = false;
        ComputeAUC auc = new ComputeAUC(posProbs, negProbs, aucTempDirectory, cmd.getAucPathVal(), extraMarker, minRecallForAUCPR, cmd.useLockFiles);;

        // print recall, precision, f1 and AUC
        Utils.println("\n%   AUC ROC   = " + Utils.truncate(auc.getROC(), 6));
        Utils.println(  "%   AUC PR    = " + Utils.truncate(auc.getPR(), 6));
        Utils.println(  "%   CLL       = " + Utils.truncate(auc.getCLL(), 6));
        Utils.println(  "%   Precision = " + Utils.truncate(score.getPrecision(), 6) + " at threshold = " + Utils.truncate(threshold, 3));
        Utils.println(  "%   Recall    = " + Utils.truncate(score.getRecall(), 6));
        Utils.println(  "%   F1        = " + Utils.truncate(score.getF1(), 6));
    }

    protected static void renameAsPrevious(File f, int iteration) {
        //	File   newF         = new CondorFile(f.getAbsoluteFile() + ".old");
        /*	THIS WAS MAKING THE OLD FILE BE A DIRECTORY RATHER THAN A FILE FOR SOME ODD REASON (JWS)  ...
         * */
        String justFileName = f.getName();
        File parent = f.getParentFile();
        File newF = new CondorFile(parent, (iteration-1) + "_" + justFileName);
        //	Utils.waitHereRegardless("renameAsOld: " + f + "\n name = " + justFileName + "\n parent = " + parent + "\n newF = " + newF);
        if (newF.exists()) {
            if (!newF.delete()) {
                Utils.error("Couldn't delete the file: " + newF.getAbsolutePath());
            }
        }
        if (!f.renameTo(newF)) {
            Utils.error("Couldn't rename from " + f.getAbsolutePath() + " to " + newF.getAbsolutePath());
        }
    }

    protected static String getModelFileName(CommandLineArguments cmdArgs, String target, boolean includeExtension, int iteration) {
        String filename = cmdArgs.getModelDirVal() + iteration + "bRDNs/" + target;
        if (cmdArgs.getModelFileVal() != null) {
            filename += "_" + cmdArgs.getModelFileVal();
        }
        filename += (includeExtension ? ".model" : "");
        Utils.ensureDirExists(filename);
        return filename;
    }

    protected static void saveDecisionList(List<ClausePair> decisionLists, List<List<Literal>> literalGroups, RunBoostedRDN runClass, CommandLineArguments cmd, int iteration, boolean isBagging) {
        /* Convert ClausePair back to Clause */
        List<Clause> decisionLs = new ArrayList<Clause>(decisionLists.size());
        convertCP2C(decisionLs, decisionLists, literalGroups);

        /* Print out the final result */
        /*System.out.println("Print out clauses from the final decision list:");
        i = 0;
        for (Clause oneClause : decisionLs) {
            System.out.format("Print the %d clause:\n", i++);
            System.out.println(oneClause);
            // give the probability with each clause
            System.out.println();
        }*/

        /* Write the final decision list into a file for inference */
        // add cut operation at the end of each clause
        List<Clause> temp = new ArrayList<Clause>();
        for (Clause oneClause : decisionLs) {
            List<Literal> tmpNegLits = new ArrayList<Literal>(oneClause.getNegativeLiterals());
            tmpNegLits.add(oneClause.getStringHandler().getLiteral("!", (List<Term>) null));
            // size is always > 0 now
            //tmpNegLits = (tmpNegLits.size() == 0) ? null : tmpNegLits;
            // if bagging, need to divide by iteration+1
            List<Literal> tmpPosLits = null;
            if (isBagging) {
                int valueIndex = oneClause.posLiterals.get(0).numberArgs() - 1;
                List<Term> termArgs = new ArrayList<Term>(oneClause.posLiterals.get(0).getArguments());
                double number = ((NumericConstant) oneClause.posLiterals.get(0).getArgument(valueIndex)).value.doubleValue() / (iteration + 1);
                termArgs.set(termArgs.size() - 1, oneClause.posLiterals.get(0).getStringHandler().getNumericConstant(number));
                tmpPosLits = new ArrayList<Literal>(oneClause.posLiterals);
                tmpPosLits.set(0, oneClause.posLiterals.get(0).getStringHandler().getLiteral(oneClause.posLiterals.get(0).getPredicateName(), termArgs));
            } else {
                tmpPosLits = oneClause.posLiterals;
            }
            temp.add(oneClause.getStringHandler().getClause(tmpPosLits, tmpNegLits));
        }
        decisionLs = temp;

        // rename the models folder to previous Models
        CommandLineArguments cmdArgs = runClass.getCmdArgs();
        //for (int i = 0; i < numbModelsToMake; i++) {
            // Rename model bRDNs folder.
        //    for (String pred : cmdArgs.getTargetPredVal()) {
        //        String filename = BoostingUtils.getModelFile(cmdArgs, pred, true);
        //        File f = new CondorFile(filename);
        //        if (f.exists()) {
        //            renameAsPrevious(f.getParentFile(), iteration);
        //        }
        //    }
        //}

        // initialize an empty copy from rdn with the decision list, pass in decision list
        // and call saveModel function
        for (String pred : cmd.getTargetPredVal()) {
            ConditionalModelPerPredicate rdn = runClass.getFullModel().get(pred);
            ConditionalModelPerPredicate rdnDL = new ConditionalModelPerPredicate(rdn.getSetup());
            //rdnDL.setNumTrees(1);
            //rdnDL.setStepLength(rdn.getStepLength(0), 0);
            //rdnDL.setLog_prior(rdn.getLo);
            //for (i = 1; i < cmdArgs.getMaxTreesVal(); i++) {
            //    rdn.setStepLength(null, i);
            //}
            RegressionTree tree = new RegressionTree(rdn.getSetup());
            for (Clause oneClause : decisionLs) {
                tree.addClause(oneClause);
            }
            rdnDL.setTargetPredicate(rdn.getTargetPredicate());
            rdnDL.setTreePrefix(rdn.getTreePrefix());
            rdnDL.addTree(tree, rdn.getStepLength(0), 0);
            rdnDL.updateSetOfTrees();
            rdnDL.setNumTrees(1);
            // save decision list model to file
            //String saveModelName = BoostingUtils.getModelFile(cmdArgs, pred, true);
            String saveModelName = getModelFileName(cmdArgs, pred, true, iteration);
            rdnDL.saveModel(saveModelName);
        }
    }

    /**
     * @param args
     * Instructions:
     *   java edu.wisc.cs.will.Boosting.AddTrees -i -model data/Father/train/models -test data/Father/test/ -target father -trees 10
     */
    public static void main(String[] args) {
        /* test */
        //testIO();

        /* Process arguments */
        args = Utils.chopCommentFromArgs(args);
        CommandLineArguments cmd = RunBoostedModels.parseArgs(args);
        if (cmd == null) {
            Utils.error(CommandLineArguments.getUsageString());
        }
        boolean disc_flag = false;
        disc discObj = new disc();

        /* Check for discretization */
        check_disc flagObj = new check_disc();
        if ((cmd.getTrainDirVal() != null)) {
            try {
                disc_flag = flagObj.checkflagvalues(cmd.getTrainDirVal());
            } catch (IOException e1) {
                // TODO Auto-generated catch block
                e1.printStackTrace();
            }
            /*Updates the names of the training and Test file based on discretization is needed or not*/
            cmd.update_file_name(disc_flag);
        } else if ((cmd.getTestDirVal() != null)) {
            try {
                System.out.println("cmd.getTestDirVal()" + cmd.getTestDirVal());
                disc_flag = flagObj.checkflagvalues(cmd.getTestDirVal());
                /*Updates the names of the training and Test file based on discretization is needed or not*/
                cmd.update_file_name(disc_flag);
			//System.out.println("Hellooooooooooooooooooooo"+cmd.get_filename());
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }
        /* Preprocess train or test data by discretization */
        if (cmd.getTrainDirVal() != null) {
            File  f = new File(cmd.getTrainDirVal() + "\\" + cmd.trainDir + "_facts_disc.txt");
            if(f.exists()) {
                f.delete();
            }
            try {
                if (disc_flag == true) {
                    discObj.Discretization(cmd.getTrainDirVal());
                }
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }
        if (cmd.getTestDirVal() != null) {
            File f = new File(cmd.getTestDirVal() + "\\" + cmd.testDir + "_facts_disc.txt");
            if(f.exists()) {
                f.delete();
            }
            /*This module does the actual discretization step*/
            try {
                if (disc_flag == true) {
                    discObj.Discretization(cmd.getTestDirVal());
                }
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }

        /* Compute AUC, recall, precision, f1 of bagging */
        //computeBaggingF1andAUC(cmd);
        //System.exit(0);

        /* Run boosted models */
        RunBoostedRDN runClass = new RunBoostedRDN();
        runClass.setCmdArgs(cmd);
        //runClass.runJob();
        /*------------------------ Load model -------------------------------*/
        // can be changed to loadModel, then don't need to modify RunBoostedRDN
        // this should be modified when model-based pruning is needed
        runClass.beforeInferModel();
        /* Get clauses */
        List<List<Clause> > clauses = new ArrayList<List<Clause>>(cmd.getMaxTreesVal());
        for (String pred : cmd.getTargetPredVal()) {
            ConditionalModelPerPredicate rdn = runClass.getFullModel().get(pred);
            for (int i = 0; i < cmd.getMaxTreesVal(); i++) {
                /* Retrieve clauses from each tree */
                List<Clause> oneTree = rdn.getTree(0, i).getRegressionClauses();
                // remove "!" at the end of body of each clause
                Clause firstClause = oneTree.get(0);
                if (firstClause.getNegLiteralCount() > 0
                        && firstClause.negLiterals.get(firstClause.negLiterals.size() - 1).getPredicateName().name.equals("!")) {
                    List<Clause> tmpTree = new ArrayList<Clause>(oneTree.size());
                    for (Clause oneClause : oneTree) {
                        List<Literal> tmpNegLits = new ArrayList<Literal>(oneClause.getNegativeLiterals());
                        tmpNegLits.remove(tmpNegLits.size() - 1);
                        tmpNegLits = (tmpNegLits.size() == 0) ? null : tmpNegLits;
                        tmpTree.add(oneClause.getStringHandler().getClause(oneClause.posLiterals, tmpNegLits));
                    }
                    clauses.add(tmpTree);
                } else {
                    clauses.add(oneTree);
                }
            }
        }
        /* Save potential and rule id to file, assume only one tree */
        //saveTreePotentialsToFile(clauses, cmd);
        /* Save clauses to dot file, assume only one tree */
        //saveTreeToDotFile(clauses, runClass, cmd);
        //System.exit(0);
        /*-------------------- Print clauses -------------------------------*/
        System.out.println("Print out clauses from each tree:");
        int i = 0;
        for (List<Clause> oneTree : clauses) {
            System.out.format("Print the %d tree:\n", i++);
            for (Clause oneClause: oneTree) {
                System.out.println(oneClause);
            }
            System.out.println();
        }
        /*--------- Print info of trees (before clause reduction):
           #clauses, length of the longest clause, average length of clauses in each tree -------*/
        printTreesInfo(clauses);
        //System.exit(0);
        /*----------------- Setting of boosting or bagging, ECoTE or SCoTE, literal group based or path based --------------------*/
        boolean isBagging = true; // whether it's for bagging or boosting
        boolean ecote = true; // whether it's ECoTE or SCoTE
        boolean[] literalGroupBased = new boolean[]{false}; // whether literal group based or path based

        /*----------------- Preprocess --------------------*/
        /* 1. Compress each path in each tree by clause reduction (subsumption) */
        System.out.println("Compress each path of each tree by clause reduction");
        long init_compress_start = System.currentTimeMillis();
        List<List<Clause>> newClauses = new ArrayList<List<Clause>>();
        for (List<Clause> oneTree : clauses) {
            List<Clause> newTree = new ArrayList<Clause>();
            for (Clause oneClause : oneTree) {
                newTree.add(reduceClause(oneClause));
            }
            newClauses.add(newTree);
        }
        long init_compress_end = System.currentTimeMillis();
        /* Print info of trees (after clause reduction):
           #clauses, length of the longest clause, average length of clauses in each tree */
        printTreesInfo(newClauses);
        //newClauses = tempClauses;
        long init_compress_time_usage = init_compress_end - init_compress_start;
        System.out.printf("## Preprocess: compress each path in each tree, time usage: %s%n",
                Utils.convertMillisecondsToTimeSpan(init_compress_time_usage, 3));
        System.out.printf("## init_compress_time_usage: %d%n", init_compress_time_usage);
        System.out.println();

        // going to not use pruning over subsumption reduction
        // either subsumption reduction, or model-based pruning
        /* 2. Build subsumption matrix between each pair of literal groups from different trees */
        // for now, we don't handle any possible same literal groups
        // trees/clauses are represented by literalGroups
        long gen_literal_group_start = System.currentTimeMillis();
        List<List<Literal>> literalGroups = new ArrayList<List<Literal>>();
        List<List<ClausePair>> clausePairs = new ArrayList<List<ClausePair>>();
        List<String> literalGroupsStrings = new ArrayList<String>();
        //List<List<Literal>> clauseHeads = new ArrayList<List<Literal>>();
        //List<List<Integer>> clauseBodies = new ArrayList<List<Integer>>();
        generateLiteralGroups(newClauses, literalGroups, literalGroupsStrings, clausePairs);
        long gen_literal_group_end = System.currentTimeMillis();
        long gen_literal_group_time_usage = gen_literal_group_end - gen_literal_group_start;
        System.out.printf("## Preprocess: generate literal groups, time usage: %s%n",
                Utils.convertMillisecondsToTimeSpan(gen_literal_group_time_usage, 3));
        System.out.printf("## gen_literal_group_time_usage: %d%n", gen_literal_group_time_usage);
        System.out.println();

        boolean[][] subsumeMatrix = null;
        long build_subsume_matrix_time_usage = 0;
        if (!ecote || !literalGroupBased[0]) {
            long build_subsume_matrix_start = System.currentTimeMillis();
            subsumeMatrix = buildSubsumeMatrix(literalGroupsStrings);
            long build_subsume_matrix_end = System.currentTimeMillis();
            build_subsume_matrix_time_usage = build_subsume_matrix_end - build_subsume_matrix_start;
            System.out.printf("## Preprocess: build subsume matrix, time usage: %s%n",
                    Utils.convertMillisecondsToTimeSpan(build_subsume_matrix_time_usage, 3));
            System.out.printf("## build_subsume_matrix_time_usage: %d%n", build_subsume_matrix_time_usage);
            System.out.println();

            System.out.printf("## Preprocess: SCoTE, generate literal groups and build subsume matrix, time usage: %s%n",
                    Utils.convertMillisecondsToTimeSpan(gen_literal_group_time_usage + build_subsume_matrix_time_usage, 3));
            System.out.println();
        }

        /* 3. Build the correspondance between, subset of examples, and, each path */
        // created for each tree since the order of path in the tree should be considered
        // example set for each path, not for each literal group
        // but example set for each literal group is also needed for model-based one clause pruning
        int numberOfExamples = 0;
        List<List<Integer>> litGExpLsAll = null;
        List<List<Integer>> litG2Path = null;
        long build_example_coverage_time_usage = 0;
        if (ecote) {
            long build_example_coverage_start = System.currentTimeMillis();
            //Map<String, Integer> example2Id = new HashMap<String, Integer>();
            List<List<Integer>> literalGExpLists = new ArrayList<List<Integer>>();
            // load from file
            //loadLists("data/CiteSeerAuthor4/errorMessage/literalGExpLists2.ser", literalGExpLists);
            //attachLists(clausePairs, literalGExpLists);
            // generate the example lists
            Map<String, Integer> exp2Id = new HashMap<String, Integer>();
            buildExpSetCorr(newClauses, literalGroups, clausePairs, literalGExpLists, exp2Id, cmd, runClass);
            for (ClausePair clauseP : clausePairs.get(0)) {
                numberOfExamples += clauseP.exampleList.size();
            }
            System.out.println("numberOfExamples: " + String.valueOf(numberOfExamples));
            // if example coverage of literal groups correct, remove redundancy by removing
            // literal group from newly added tree
            // literalGExpLists is only used to decide literal group based
            // this function is not reliable, sometimes can't find out whether max node reaches issue exists
            // maybe we need mannually set whether literal group based
            //checkExpListConflicts(clausePairs, literalGExpLists, literalGroupBased);

            /* preprocess to store an example list for each literal group/path(for CiteSeerAuthor) over all examples
            to fully remove unneeded literal groups */
            if (literalGroupBased[0]) { // exp list for each literal group over all exps
                litGExpLsAll = new ArrayList<List<Integer>>(literalGroups.size());
                // generate the example lists over all examples
                buildExpSetAll(newClauses, literalGroups, clausePairs, litGExpLsAll, exp2Id, cmd, runClass);
            } else { // exp list for each path over all exps
                litG2Path = new ArrayList<List<Integer>>(literalGroups.size());
                // the example list for each path over all examples will be stored with class ClausePair
                buildExpSetPathAll(newClauses, litG2Path, clausePairs, exp2Id, cmd, runClass);
            }
            long build_example_coverage_end = System.currentTimeMillis();
            build_example_coverage_time_usage = build_example_coverage_end - build_example_coverage_start;
            System.out.printf("## Preprocess: build example coverage, time usage: %s%n",
                    Utils.convertMillisecondsToTimeSpan(build_example_coverage_time_usage, 3));
            System.out.printf("## build_example_coverage_time_usage: %d%n", build_example_coverage_time_usage);
            System.out.println();

            System.out.printf("## Preprocess: ECoTE, generate literal groups and build example coverage, time usage: %s%n",
                    Utils.convertMillisecondsToTimeSpan(gen_literal_group_time_usage + build_example_coverage_time_usage, 3));
            System.out.println();
        }

        //saveLists("literalGExpLists2.ser", literalGExpLists);
        //saveList("clPairs-0-2.ser", clausePairs.get(0).get(2).exampleList);
        //saveList("clPairs-0-2-body.ser", clausePairs.get(0).get(2).body);
        //saveList("clPairs-1-3.ser", clausePairs.get(1).get(3).exampleList);
        //saveList("clPairs-1-3-body.ser", clausePairs.get(1).get(3).body);
        /*-------------------- Iterative compression ----------------------*/
        /* Add clauses to get the final decision lists */
        List<ClausePair> decisionLists = new ArrayList<ClausePair>();
        for (ClausePair oneClause : clausePairs.get(0)) {
            decisionLists.add(oneClause.copy());
        }

        // store the length of the longest clause without compression
        int lenLongestClause = 0;
        // store the total length of all clauses without compression
        BigInteger totalLenClause = new BigInteger("0");
        for (Clause antClause : clauses.get(0)) {
            lenLongestClause = Math.max(lenLongestClause, antClause.getNegativeLiterals().size());
            totalLenClause = totalLenClause.add(new BigInteger(String.valueOf(antClause.getNegativeLiterals().size())));
        }
        // store the total number of clauses without compression
        BigInteger totalNumberClauses = new BigInteger(String.valueOf(clauses.get(0).size()));

        // store the most number of literal groups in a clause without compression
        // if we assume the clause reduction in preprocess doesn't shorten any path
        // for most datasets, it doesn't
        int lenLongestClauseLG = 0;
        // store the total number of literal groups without compression
        // if we assume the clause reduction in preprocess doesn't shorten any path
        // for most datasets, it doesn't
        BigInteger totalLenClauseLG = new BigInteger("0");
        for (ClausePair antClause : clausePairs.get(0)) {
            lenLongestClauseLG = Math.max(lenLongestClauseLG, antClause.body.size());
            totalLenClauseLG = totalLenClauseLG.add(new BigInteger(String.valueOf(antClause.body.size())));
        }
        // store the total number of clauses without compression
        BigInteger totalNumberClausesLG = new BigInteger(String.valueOf(clausePairs.get(0).size()));

        long total_combine_compress_time_usage = 0;
        long total_prune_time_usage = 0;
        long total_prune_extra_time_usage = 0;
        long total_iteration_update_time_usage = 0;
        for (i = 1; i < clausePairs.size(); i++) {
            //long start = System.currentTimeMillis();
            long combine_compress_start = System.currentTimeMillis();
            List<ClausePair> temp = new ArrayList<ClausePair>();
            for (ClausePair orgClause : decisionLists) {
                for (ClausePair antClause : clausePairs.get(i)) {
                    ClausePair newClause = orgClause.copy();
                    newClause.clP2 = antClause;
                    // add the potentials of the two rules
                    // if bagging, it's sum of probability
                    addNumbers(newClause, isBagging, i);
                    if (!ecote) {
                        /* Compress each clause */
                        temp.add(compressClause(newClause, subsumeMatrix, literalGroups, i));
                    } else {
                        // skip within clause subsumption reduction
                        // no subsumption when pruning
                        //newClause.bodySubsume = new ArrayList<>(newClause.body);
                        //newClause.bodySubsume.addAll(newClause.clP2.body);
                        temp.add(newClause);
                    }
                }
            }
            if (!ecote) {
                /* Compress between clauses */
                decisionLists = compressClauses(temp, subsumeMatrix, i);
            } else {
                // skip between clauses subsumption reduction
                decisionLists = new ArrayList<ClausePair>(temp);
            }

            long combine_compress_end = System.currentTimeMillis();
            long combine_compress_time_usage = combine_compress_end - combine_compress_start;
            total_combine_compress_time_usage += combine_compress_time_usage;
            //long end = System.currentTimeMillis();
            if (!ecote) {
                System.out.printf("## Iteration %d: combine and compress, time usage: %s%n", i,
                        Utils.convertMillisecondsToTimeSpan(combine_compress_time_usage, 3));
                System.out.printf("## combine_compress_time_usage: %d%n", combine_compress_time_usage);
                System.out.println();
            } else {
                System.out.printf("## Iteration %d: combine, time usage: %s%n", i,
                        Utils.convertMillisecondsToTimeSpan(combine_compress_time_usage, 3));
                System.out.printf("## combine_compress_time_usage: %d%n", combine_compress_time_usage);
                System.out.println();
            }

            /* Print number of clauses, the length of the longest clause, average clause length, time usage
               at each iteration (addition), no compression and with compression */
            // without compression
            int lenLongestOneClause = 0;
            int totalLenOneList = 0;
            for (Clause antClause : clauses.get(i)) {
                lenLongestOneClause = Math.max(lenLongestOneClause, antClause.getNegativeLiterals().size());
                totalLenOneList += antClause.getNegativeLiterals().size();
            }
            lenLongestClause += lenLongestOneClause;
            totalLenClause = totalLenClause.multiply(new BigInteger(String.valueOf(clauses.get(i).size())))
                    .add((new BigInteger(String.valueOf(totalLenOneList))).multiply(new BigInteger(String.valueOf(totalNumberClauses))));
            totalNumberClauses = totalNumberClauses.multiply(new BigInteger(String.valueOf(clauses.get(i).size())));
            // store longest clause with compression
            int lenLongestCompressedClause = 0;
            // store total length of clauses with compression
            long totalLenCompressedClause = 0;
            System.out.printf("Iteration (addition) %d:%n", i);
            System.out.println("No compression:");
            System.out.printf("The number of clauses: %d%n", totalNumberClauses);
            System.out.printf("The length of the longest clause: %d%n", lenLongestClause);
            System.out.printf("The average length of clauses: %.2f%n", totalLenClause.doubleValue() / totalNumberClauses.doubleValue());

            if (!ecote) {
                for (ClausePair oneClause : decisionLists) {
                    int oneClauseLen = 0;
                    for (Integer litGId : oneClause.bodySubsume) {
                        oneClauseLen += literalGroups.get(litGId).size();
                    }
                    lenLongestCompressedClause = Math.max(lenLongestCompressedClause, oneClauseLen);
                    totalLenCompressedClause += oneClauseLen;
                }
                System.out.println("With compression:");
                System.out.printf("The number of clauses: %d%n", decisionLists.size());
                System.out.printf("The length of the longest clause: %d%n", lenLongestCompressedClause);
                System.out.printf("The average length of clauses: %.2f%n", (double) totalLenCompressedClause / decisionLists.size());
                //System.out.printf("The time usage: %s%n", Utils.convertMillisecondsToTimeSpan(end - start, 3));
                System.out.println();
            }

            /* Print the number of clauses, the most number of literal groups in a clause, average number of literal groups in a clause,
               at each iteration (addition), no compression and with compression */
            // without compression
            // if we assume the clause reduction in preprocess doesn't shorten any path
            // for most datasets, it doesn't
            int lenLongestOneClauseLG = 0;
            int totalLenOneListLG = 0;
            for (ClausePair antClause : clausePairs.get(i)) {
                lenLongestOneClauseLG = Math.max(lenLongestOneClauseLG, antClause.body.size());
                totalLenOneListLG += antClause.body.size();
            }
            lenLongestClauseLG += lenLongestOneClauseLG;
            totalLenClauseLG = totalLenClauseLG.multiply(new BigInteger(String.valueOf(clausePairs.get(i).size())))
                    .add((new BigInteger(String.valueOf(totalLenOneListLG))).multiply(new BigInteger(String.valueOf(totalNumberClausesLG))));
            totalNumberClausesLG = totalNumberClausesLG.multiply(new BigInteger(String.valueOf(clausePairs.get(i).size())));
            // store the most number of literal groups in a clause with compression
            int lenLongestCompressedClauseLG = 0;
            // store total number of literal groups in all clauses with compression
            long totalLenCompressedClauseLG = 0;

            System.out.printf("Iteration (addition) %d:%n", i);
            System.out.println("No compression:");
            System.out.printf("The number of clauses: %d%n", totalNumberClausesLG);
            System.out.printf("The most number of literal groups in a clause: %d%n", lenLongestClauseLG);
            System.out.printf("The average number of literal groups in a clause: %.2f%n", totalLenClauseLG.doubleValue() / totalNumberClausesLG.doubleValue());

            if (!ecote) {
                for (ClausePair oneClause : decisionLists) {
                    lenLongestCompressedClauseLG = Math.max(lenLongestCompressedClauseLG, oneClause.bodySubsume.size());
                    totalLenCompressedClauseLG += oneClause.bodySubsume.size();
                }
                System.out.println("With compression:");
                System.out.printf("The number of clauses: %d%n", decisionLists.size());
                System.out.printf("The most number of literal groups in a clause: %d%n", lenLongestCompressedClauseLG);
                System.out.printf("The average number of literal groups in a clause: %.2f%n", (double) totalLenCompressedClauseLG / decisionLists.size());
                //System.out.printf("The time usage: %s%n", Utils.convertMillisecondsToTimeSpan(end - start, 3));
                System.out.println();
            }

            if (ecote) {
                /* Model-based pruning */
                long prune_start = System.currentTimeMillis();
                //long startPrune = System.currentTimeMillis();
                decisionLists = pruneClauses(decisionLists, numberOfExamples, literalGroups, litGExpLsAll, litG2Path, clausePairs, literalGroupBased, i);
                //long endPrune = System.currentTimeMillis();
                long prune_end = System.currentTimeMillis();
                long prune_time_usage = prune_end - prune_start;
                total_prune_time_usage += prune_time_usage;
                System.out.printf("## Iteration %d: prune, time usage: %s%n", i,
                        Utils.convertMillisecondsToTimeSpan(prune_time_usage, 3));
                System.out.printf("## prune_time_usage: %d%n", prune_time_usage);
                System.out.println();

                // for not literal group based pruning, try in-clause subsumption reduction
                if (!literalGroupBased[0]) {
                    long prune_extra_start = System.currentTimeMillis();
                    for (ClausePair oneClause : decisionLists) {
                        compressClauseForPrune(oneClause, subsumeMatrix, i);
                    }
                    long prune_extra_end = System.currentTimeMillis();
                    long prune_extra_time_usage = prune_extra_end - prune_extra_start;
                    total_prune_extra_time_usage += prune_extra_time_usage;
                    System.out.printf("## Iteration %d: prune, path-based, in-clause subsumption reduction, time usage: %s%n", i,
                            Utils.convertMillisecondsToTimeSpan(prune_extra_time_usage, 3));
                    System.out.printf("## prune_extra_time_usage: %d%n", prune_extra_time_usage);
                    System.out.println();
                }
            }

            // finish the update of each clause
            long iteration_update_start = System.currentTimeMillis();
            finishUpdate(decisionLists);
            long iteration_update_end = System.currentTimeMillis();
            long iteration_update_time_usage = iteration_update_end - iteration_update_start;
            total_iteration_update_time_usage += iteration_update_time_usage;
            System.out.printf("## Iteration %d: iteration update, time usage: %s%n", i,
                    Utils.convertMillisecondsToTimeSpan(iteration_update_time_usage, 3));
            System.out.printf("## iteration_update_time_usage: %d%n", iteration_update_time_usage);
            System.out.println();

            // print out intermediate decision list at each iteration
            //saveDecisionList(decisionLists, literalGroups, runClass, cmd, i, isBagging);

            // correctness check
            //checkExpListConsistent(decisionLists, literalGExpLists, numberOfExamples, literalGroups, cmd, runClass);

            if (ecote) {
                /* Print number of clauses, the length of the longest clause, average clause length, time usage
                   at each iteration (addition), for pruning */
                // store longest clause after pruning
                int lenLongestCompressedClausePrune = 0;
                // store total length of clauses after pruning
                long totalLenCompressedClausePrune = 0;
                for (ClausePair oneClause : decisionLists) {
                    int oneClauseLen = 0;
                    for (Integer litGId : oneClause.body) {
                        oneClauseLen += literalGroups.get(litGId).size();
                    }
                    lenLongestCompressedClausePrune = Math.max(lenLongestCompressedClausePrune, oneClauseLen);
                    totalLenCompressedClausePrune += oneClauseLen;
                }
                System.out.printf("Iteration (addition) %d:%n", i);
                System.out.println("After pruning:");
                System.out.printf("The number of clauses: %d%n", decisionLists.size());
                System.out.printf("The length of the longest clause: %d%n", lenLongestCompressedClausePrune);
                System.out.printf("The average length of clauses: %.2f%n", (double) totalLenCompressedClausePrune / decisionLists.size());
                //System.out.printf("The time usage: %s%n", Utils.convertMillisecondsToTimeSpan(endPrune - startPrune, 3));
                System.out.println();

                /* Print the number of clauses, the most number of literal groups in a clause, average number of literal groups
                   in a clause, at each iteration (addition), for pruning */
                // store the most number of literal groups in a clause after pruning
                int lenLongestCompressedClausePruneLG = 0;
                // store total number of literal groups in all clauses after pruning
                long totalLenCompressedClausePruneLG = 0;
                for (ClausePair oneClause : decisionLists) {
                    lenLongestCompressedClausePruneLG = Math.max(lenLongestCompressedClausePruneLG, oneClause.body.size());
                    totalLenCompressedClausePruneLG += oneClause.body.size();
                }
                System.out.printf("Iteration (addition) %d:%n", i);
                System.out.println("After pruning:");
                System.out.printf("The number of clauses: %d%n", decisionLists.size());
                System.out.printf("The most number of literal groups in a clause: %d%n", lenLongestCompressedClausePruneLG);
                System.out.printf("The average number of literal groups in a clause: %.2f%n", (double) totalLenCompressedClausePruneLG / decisionLists.size());
                //System.out.printf("The time usage: %s%n", Utils.convertMillisecondsToTimeSpan(endPrune - startPrune, 3));
                System.out.println();
            }
        }

        /*-------------- Print all time usages ---------------*/
        System.out.printf("## Final: iteration update, total time usage: %s%n",
                Utils.convertMillisecondsToTimeSpan(total_iteration_update_time_usage, 3));
        System.out.printf("## total_iteration_update_time_usage: %d%n", total_iteration_update_time_usage);
        System.out.println();

        if (!ecote) {
            System.out.printf("## Final: combine and compress, total time usage: %s%n",
                    Utils.convertMillisecondsToTimeSpan(total_combine_compress_time_usage, 3));
            System.out.printf("## total_combine_compress_time_usage: %d%n", total_combine_compress_time_usage);
            System.out.println();

            System.out.printf("## Final: combine and compress, and iteration update, total time usage: %s%n",
                    Utils.convertMillisecondsToTimeSpan(
                            total_combine_compress_time_usage + total_iteration_update_time_usage, 3));
            System.out.println();

            System.out.printf("## SCoTE: generate literal groups and build subsume matrix, combine and compress, and iteration update: %s%n",
                    Utils.convertMillisecondsToTimeSpan(
                            gen_literal_group_time_usage + build_subsume_matrix_time_usage
                                    + total_combine_compress_time_usage + total_iteration_update_time_usage, 3));
            System.out.println();
        } else {
            System.out.printf("## Final: combine, total time usage: %s%n",
                    Utils.convertMillisecondsToTimeSpan(total_combine_compress_time_usage, 3));
            System.out.printf("## total_combine_compress_time_usage: %d%n", total_combine_compress_time_usage);
            System.out.println();

            System.out.printf("## Final: prune, total time usage: %s%n",
                    Utils.convertMillisecondsToTimeSpan(total_prune_time_usage, 3));
            System.out.printf("## total_prune_time_usage: %d%n", total_prune_time_usage);
            System.out.println();

            if (!literalGroupBased[0]) {
                System.out.printf("## Final: prune, path-based, in-clause subsumption reduction, total time usage: %s%n",
                        Utils.convertMillisecondsToTimeSpan(total_prune_extra_time_usage, 3));
                System.out.printf("## total_prune_extra_time_usage: %d%n", total_prune_extra_time_usage);
                System.out.println();
            }

            System.out.printf("## Final: combine, prune, and iteration update, total time usage: %s%n",
                    Utils.convertMillisecondsToTimeSpan(
                            total_combine_compress_time_usage + total_prune_time_usage + total_iteration_update_time_usage, 3));
            System.out.println();

            if (!literalGroupBased[0]) {
                System.out.printf("## Final: combine, prune, in-clause subsumption, and iteration update, total time usage: %s%n",
                        Utils.convertMillisecondsToTimeSpan(
                                total_combine_compress_time_usage + total_prune_time_usage +
                                        total_prune_extra_time_usage + total_iteration_update_time_usage, 3));
                System.out.println();
            }

            System.out.printf("## ECoTE: generate literal groups and build example coverage, combine, prune, and iteration update: %s%n",
                    Utils.convertMillisecondsToTimeSpan(
                            gen_literal_group_time_usage + build_example_coverage_time_usage
                                    + total_combine_compress_time_usage + total_prune_time_usage + total_iteration_update_time_usage, 3));
            System.out.println();

            if (!literalGroupBased[0]) {
                System.out.printf("## ECoTE: generate literal groups and build example coverage, combine, prune, in-clause subsumption, and iteration update: %s%n",
                        Utils.convertMillisecondsToTimeSpan(
                                gen_literal_group_time_usage + build_example_coverage_time_usage
                                        + total_combine_compress_time_usage + total_prune_time_usage
                                        + total_prune_extra_time_usage + total_iteration_update_time_usage, 3));
                System.out.println();
            }
        }


        /* Convert ClausePair back to Clause */
        //List<Clause> decisionLs = new ArrayList<Clause>(decisionLists.size());
        //convertCP2C(decisionLs, decisionLists, literalGroups);

        /* Print out the final result */
        /*System.out.println("Print out clauses from the final decision list:");
        i = 0;
        for (Clause oneClause : decisionLs) {
            System.out.format("Print the %d clause:\n", i++);
            System.out.println(oneClause);
            // give the probability with each clause
            System.out.println();
        }*/

        /* Write the final decision list into a file for inference */
        // add cut operation at the end of each clause
        //List<Clause> temp = new ArrayList<Clause>();
        //for (Clause oneClause : decisionLs) {
        //    List<Literal> tmpNegLits = new ArrayList<Literal>(oneClause.getNegativeLiterals());
        //    tmpNegLits.add(oneClause.getStringHandler().getLiteral("!", (List<Term>) null));
            // size is always > 0 now
            //tmpNegLits = (tmpNegLits.size() == 0) ? null : tmpNegLits;
        //    temp.add(oneClause.getStringHandler().getClause(oneClause.posLiterals, tmpNegLits));
        //}
        //decisionLs = temp;

        // rename the models folder to oldModels
        //CommandLineArguments cmdArgs = runClass.getCmdArgs();
        //for (i = 0; i < numbModelsToMake; i++) {
        //    // Rename model bRDNs folder.
        //    for (String pred : cmdArgs.getTargetPredVal()) {
        //        String filename = BoostingUtils.getModelFile(cmdArgs, pred, true);
        //        File f = new CondorFile(filename);
        //        if (f.exists()) {
        //            renameAsOld(f.getParentFile());
        //        }
        //    }
        //}

        // initialize an empty copy from rdn with the decision list, pass in decision list
        // and call saveModel function
        //for (String pred : cmd.getTargetPredVal()) {
        //    ConditionalModelPerPredicate rdn = runClass.getFullModel().get(pred);
        //    ConditionalModelPerPredicate rdnDL = new ConditionalModelPerPredicate(rdn.getSetup());
            //rdnDL.setNumTrees(1);
            //rdnDL.setStepLength(rdn.getStepLength(0), 0);
            //rdnDL.setLog_prior(rdn.getLo);
            //for (i = 1; i < cmdArgs.getMaxTreesVal(); i++) {
            //    rdn.setStepLength(null, i);
            //}
        //    RegressionTree tree = new RegressionTree(rdn.getSetup());
        //    for (Clause oneClause : decisionLs) {
        //        tree.addClause(oneClause);
        //    }
        //    rdnDL.setTargetPredicate(rdn.getTargetPredicate());
        //    rdnDL.setTreePrefix(rdn.getTreePrefix());
        //    rdnDL.addTree(tree, rdn.getStepLength(0), 0);
        //    rdnDL.updateSetOfTrees();
        //    rdnDL.setNumTrees(1);
            // save decision list model to file
        //    String saveModelName = BoostingUtils.getModelFile(cmdArgs, pred, true);
        //    rdnDL.saveModel(saveModelName);
        //}
    }

}
