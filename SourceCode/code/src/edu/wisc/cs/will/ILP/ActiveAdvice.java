/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.ConnectedSentence;
import edu.wisc.cs.will.FOPC.ConnectiveName;
import edu.wisc.cs.will.FOPC.visitors.DefaultFOPCVisitor;
import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.visitors.DefiniteClauseCostAggregator;
import edu.wisc.cs.will.FOPC.visitors.DuplicateDeterminateRemover;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.visitors.Inliner;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.PrettyPrinter;
import edu.wisc.cs.will.FOPC.PrettyPrinterOptions;
import edu.wisc.cs.will.FOPC.RelevanceStrength;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.Utils.LinkedMapOfSets;
import edu.wisc.cs.will.Utils.MapOfLists;
import edu.wisc.cs.will.Utils.MapOfSets;
import edu.wisc.cs.will.Utils.Utils;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 *
 * @author twalker
 */
public class ActiveAdvice {

    private static final CNFClauseCollector CLAUSE_COLLECTOR = new CNFClauseCollector();

    private HandleFOPCstrings stringHandler;

    private RelevanceStrength relevanceStrength;

    private Collection<? extends Literal> positiveExamples;

    private Collection<? extends Literal> negativeExamples;

    private MapOfSets<PredicateNameAndArity, ModeInfo> adviceModes = new MapOfSets<PredicateNameAndArity, ModeInfo>();

    private MapOfSets<PredicateNameAndArity, ClauseInfo> clauses = new LinkedMapOfSets<PredicateNameAndArity, ClauseInfo>();

    private MapOfLists<PredicateNameAndArity, Clause> supportClauses = new MapOfLists<PredicateNameAndArity, Clause>();

    private Map<PredicateNameAndArity, RelevanceInfo> adviceFeaturesAndStrengths = new LinkedHashMap<PredicateNameAndArity, RelevanceInfo>();

    public ActiveAdvice(HandleFOPCstrings stringHandler, RelevanceStrength relevanceStrength, Collection<? extends Literal> positiveExamples, Collection<? extends Literal> negativeExamples) {
        this.stringHandler = stringHandler;
        this.relevanceStrength = relevanceStrength;
        this.positiveExamples = positiveExamples;
        this.negativeExamples = negativeExamples;
    }

    public void addAdviceClause(AdviceProcessor ap, String name, RelevantClauseInformation rci, List<Clause> clauses) throws IllegalArgumentException {

        if (ap.isInliningEnabled()) {
            rci = rci.getInlined(ap.getContext(), supportClauses);
        }

        // When removing double negation by failures
        // and removing duplicate determinates, we have to iteration
        // back and forth since each simplification may result
        // in additional simplications by the other visitor.
        while (true) {
            RelevantClauseInformation start = rci;
            if (ap.isRemoveDoubleNegationEnabled()) {
                rci = rci.removeDoubleNegations();
            }

            if (ap.isRemoveDuplicateDeterminatesEnabled()) {
                rci = rci.removeDuplicateDeterminates();
            }

            rci = rci.applyPruningRules(ap);

            if (start.isEquivalentUptoVariableRenaming(rci)) {
                break;
            }
        }

        MapOfLists<PredicateNameAndArity, Clause> supportClausesForExpansions = new MapOfLists<PredicateNameAndArity, Clause>();
        List<RelevantClauseInformation> expandedRCIs = rci.expandNonOperationalPredicates(ap.getContext(), supportClausesForExpansions);

        // We will add all of the support clauses...just for the hell of it...
        for (Map.Entry<PredicateNameAndArity, List<Clause>> entry : supportClausesForExpansions.entrySet()) {
            if (supportClauses.containsKey(entry.getKey()) == false) {
                supportClauses.addAllValues(entry.getKey(), entry.getValue());
            }
        }

        //List<RelevantClauseInformation> expandedRCIs = Collections.singletonList(rci);

        int count = 0;
        for (RelevantClauseInformation expandedRCI : expandedRCIs) {
            String expandedName = name;
            if (expandedRCIs.size() != 1) {
                expandedName = name + "_op" + (count++);
            }

            expandedRCI = expandedRCI.getCompressed();
            Sentence sentence = expandedRCI.getSentence();

            Sentence cnf = sentence.getConjunctiveNormalForm();  // This may still have AND connectives.
            Sentence compressedCNF = SentenceCompressor.getCompressedSentence(cnf);

            // Determine the final output variables...
            Set<Variable> outputVariables = determineOutputVariables(ap, rci, compressedCNF);

            Collection<Variable> variablesInSentence = compressedCNF.collectAllVariables();

            Example example = expandedRCI.example;
            List<TypeSpec> exampleTypeSpecs = example.getTypeSpecs();

            PredicateName pn = stringHandler.getPredicateName(expandedName);
            RelevanceStrength rs = expandedRCI.getFinalRelevanceStrength();

            List<Term> headArguments = new ArrayList<Term>();
            List<TypeSpec> headSpecList = new ArrayList<TypeSpec>();

            // Create the head arguments.
            // Only add terms that are actually used in the body somewhere...
            for (int i = 0; i < example.getArity(); i++) {
                Term term = example.getArgument(i);
                //if (term instanceof Variable == false || variablesInSentence.contains((Variable) term)) {
                headArguments.add(term);
                headSpecList.add(exampleTypeSpecs.get(i));
                //}
            }

//            // Now we need to insert the output variables into the head.
//            // Once again we are going to make an aweful assumption that
//            // the last head variable is the "State" variable.  This may
//            // lead to some weird heads if this is not the case.
//            int outputIndex = Math.max(0, headArguments.size() - 2);
//            for (Variable variable : outputVariables) {
//                headArguments.add(outputIndex++, variable);
//                headSpecList.add(variable.getTypeSpec());
//            }

            Literal head = stringHandler.getLiteral(pn, headArguments);
            PredicateNameAndArity predicateNameAndArity = head.getPredicateNameAndArity();

            Sentence impliedSentence = stringHandler.getConnectedSentence(compressedCNF, ConnectiveName.IMPLIES, head);
            List<Clause> impliedClauses = impliedSentence.convertToClausalForm();

            boolean duplicate = false;

            // Check for duplicate clauses.
            // We don't check disjunct clause cause it is hard once we have converted
            // to clausal form.  Unfortunatedly, we don't store the non-clausal implied sentence,
            // so we can't check for duplicates before clausal convertion.
            if (impliedClauses.size() == 1) {
                Clause theNewClause = impliedClauses.get(0);
                for (Clause existing : clauses) {
                    if (areClausesEqualUptoHeadAndVariableRenaming(existing, theNewClause)) {
                        duplicate = true;
                        if (AdviceProcessor.debugLevel >= 1) {
                            Utils.println("% [AdviceProcessor]  Generated advice clause " + theNewClause.getDefiniteClauseHead().getPredicateNameAndArity() + " is duplicate of " + existing.getDefiniteClauseHead().getPredicateNameAndArity() + ".  Skipping.");
                        }
                        break;
                    }
                }
            }

            if (duplicate == false) {
                RelevanceStrength strength = expandedRCI.getFinalRelevanceStrength();

                if (expandedRCI.getTypeSpecList() != null) {  // TODO SHOULD WE BE DOING THE setRelevance, add, mark, assert above if this fails?

                    List<Term> signature = new ArrayList<Term>();
                    for (int i = 0; i < head.getArity(); i++) {
                        signature.add(stringHandler.getStringConstant("constant"));
                    }

                    headSpecList = new ArrayList<TypeSpec>();
//                    // headSpecList.add(new TypeSpec(TypeSpec.constantMode, stringHandler.getType("advice_index"), stringHandler));
                    headSpecList.addAll(expandedRCI.getTypeSpecList());

                    ModeInfo mi = addModeAndRelevanceStrength(predicateNameAndArity, signature, headSpecList, rs);

                    double contentsCost = 0;
                    double cost = strength.defaultCost();

                    for (Clause clause : impliedClauses) {
                        // Calculate the average cost over all literals in the clause and across clauses for ORs.
                        contentsCost = DefiniteClauseCostAggregator.PREDICATE_COST_AGGREGATOR.getAggregateCost(DefiniteClauseCostAggregator.AggregationMode.MEAN, clause) / impliedClauses.size();

                        addClause(clause, strength);

                        if (clauses != null) {
                            clauses.add(clause);
                        }
                    }

                    mi.cost = cost + 1e-5 * contentsCost;
                }
            }
        }
    }

    public void addAdviceMode(AdviceProcessor ap, RelevantModeInformation rci) {
        PredicateNameAndArity pnaa = rci.getPredicateNameAndArity();

        // If these contain non-operations, we need to expand them just
        // like we do during addAdviceClause.
        Set<Clause> supportClause = new HashSet<Clause>();

        ConnectedSentence implication = rci.getSentence(ap.getContext());
        Sentence body = implication.getSentenceA();
        Literal head = ((DefiniteClause) implication.getSentenceB()).getDefiniteClauseHead();


        if (ap.isInliningEnabled()) {
            body = Inliner.getInlinedSentence(body, ap.getContext(), supportClauses);
        }
        //rci.toString();

        if (ap.isRemoveDuplicateDeterminatesEnabled()) {
            body = DuplicateDeterminateRemover.removeDuplicates(body);
        }

        MapOfLists<PredicateNameAndArity, Clause> supportClausesForExpansions = new MapOfLists<PredicateNameAndArity, Clause>();

        List<? extends Sentence> expansions = NonOperationalExpander.getExpandedSentences(ap.getContext(), body, supportClausesForExpansions);

        if (expansions == null || (expansions.size() == 1 && expansions.get(0).equals(body))) {
            // No sentences...
            addModeAndRelevanceStrength(pnaa, rci.getSignature(), rci.getTypeSpecs(), rci.getRelevanceStrength());
        }
        else {
            // We actually did some expansions here...
            int opIndex = 0;
            for (Sentence anExpansion : expansions) {
                anExpansion = SentenceCompressor.getCompressedSentence(anExpansion);
                anExpansion = anExpansion.getConjunctiveNormalForm();  // This may still have AND connectives.
                anExpansion = SentenceCompressor.getCompressedSentence(anExpansion); // We might need to compress again.  This should probably be built into getCNF();

                Sentence newImpliedSentence = stringHandler.getConnectedSentence(anExpansion, ConnectiveName.IMPLIES, head);
                List<Clause> impliedClauses = newImpliedSentence.convertToClausalForm();

                PredicateName newName = newImpliedSentence.getStringHandler().getPredicateName(pnaa.getPredicateName().name + "_op" + (opIndex++));

                // Finally, assemble the new clause...
                for (Clause newClause : impliedClauses) {
                    Literal newHead = ap.getContext().getStringHandler().getLiteral(newName, head.getArguments());
                    newClause = newClause.getStringHandler().getClause(Collections.singletonList(newHead), newClause.getNegativeLiterals());

                    ap.getContext().assertDefiniteClause(newClause);

                    if (AdviceProcessor.debugLevel >= 1) {
                        Utils.println("% [AdviceProcessor]  Created operational clause from " + pnaa + ":");
                        Utils.println(PrettyPrinter.print(newClause, "% [AdviceProcessor]     ", new PrettyPrinterOptions()));
                    }
                }

                addModeAndRelevanceStrength(new PredicateNameAndArity(newName, head.getArity()), rci.getSignature(), rci.getTypeSpecs(), rci.getRelevanceStrength());
            }
        }

    }

    private String getUniqueName(HornClauseContext context, String name, int arity) {
        int index = name.indexOf("_anon");
        if (index != -1) {
            name = name.substring(0, index);
        }

        String newName = null;

        int i = 1;
        while (true) {
            newName = name + "_anon" + i;
            if (context.getClausebase().checkForPossibleMatchingAssertions(context.getStringHandler().getPredicateName(name), arity) == false) {
                break;
            }
        }

        return newName;
    }

    // <editor-fold defaultstate="collapsed" desc="Accessor">
    public Collection<? extends Literal> getNegativeExamples() {
        return negativeExamples;
    }

    public void setNegativeExamples(Collection<? extends Literal> negativeExamples) {
        this.negativeExamples = negativeExamples;
    }

    public Collection<? extends Literal> getPositiveExamples() {
        return positiveExamples;
    }

    public void setPositiveExamples(Collection<? extends Literal> positiveExamples) {
        this.positiveExamples = positiveExamples;
    }

    public RelevanceStrength getRelevanceStrength() {
        return relevanceStrength;
    }

    public void setRelevanceStrength(RelevanceStrength relevanceStrength) {
        this.relevanceStrength = relevanceStrength;
    }

    public void addClause(Clause clause, RelevanceStrength strength) {
        clauses.put(clause.getDefiniteClauseHead().getPredicateNameAndArity(), new ClauseInfo(clause, strength));
    }

    public Set<ClauseInfo> getClause(PredicateNameAndArity predicateNameAndArity) {
        return clauses.getValues(predicateNameAndArity);
    }

    public MapOfSets<PredicateNameAndArity, ClauseInfo> getClauses() {
        return clauses;
    }

    public void addFeatureRelevance(PredicateNameAndArity key, RelevanceStrength value) {
        adviceFeaturesAndStrengths.put(key, new RelevanceInfo(key, value));
    }

    public RelevanceInfo getFeatureRelevanceStrength(PredicateNameAndArity key) {
        return adviceFeaturesAndStrengths.get(key);
    }

    public ModeInfo addModeAndRelevanceStrength(PredicateNameAndArity predicate, List<Term> signature, List<TypeSpec> headSpecList, RelevanceStrength relevanceStrength) {
        ModeInfo mi = new ModeInfo(predicate, signature, headSpecList, relevanceStrength);

        Set<ModeInfo> existingModeInfos = adviceModes.getValues(predicate);

        boolean add = true;
        if (existingModeInfos != null) {
            for (Iterator<ModeInfo> it = existingModeInfos.iterator(); it.hasNext();) {
                ModeInfo modeInfo = it.next();
                if (modeInfo.equals(mi)) {
                    if (modeInfo.strength.isWeaker(relevanceStrength)) {
                        it.remove();
                    }
                    else {
                        add = false;
                    }
                    break;
                }
            }
        }
        if (add) {
            adviceModes.put(predicate, mi);
        }


        return mi;
    }

    public Set<ModeInfo> getModeInfo(PredicateNameAndArity key) {
        return adviceModes.getValues(key);
    }

    public Iterable<ModeInfo> getModes() {
        return adviceModes;
    }

    public Collection<RelevanceInfo> getFeatureRelevances() {
        return adviceFeaturesAndStrengths.values();
    }

    public MapOfLists<PredicateNameAndArity, Clause> getSupportClauses() {
        return supportClauses;
    }

    public boolean hasActiveAdvice() {
        return adviceModes.isEmpty() == false || adviceFeaturesAndStrengths.isEmpty() == false;
    }

    public boolean hasActiveAdvice(RelevanceStrength thisStrengthOrStronger) {

        for (ModeInfo modeInfo : adviceModes) {
            if (modeInfo.strength.isEqualOrStronger(thisStrengthOrStronger)) {
                return true;
            }
        }

        for (RelevanceInfo ri : adviceFeaturesAndStrengths.values()) {
            if (ri.strength.isEqualOrStronger(thisStrengthOrStronger)) {
                return true;
            }
        }

        return false;
    }

    public boolean hasActiveAdvice(RelevanceStrength strongestStrength, RelevanceStrength weakestStrength) {
        for (ModeInfo modeInfo : adviceModes) {
            if (modeInfo.strength.isEqualOrWeaker(strongestStrength) && modeInfo.strength.isStronger(weakestStrength)) {
                return true;
            }
        }

        for (RelevanceInfo ri : adviceFeaturesAndStrengths.values()) {
            if (ri.strength.isEqualOrStronger(strongestStrength) && ri.strength.isStronger(weakestStrength)) {
                return true;
            }
        }

        return false;
    }// </editor-fold>

    public boolean areClausesEqualUptoHeadAndVariableRenaming(Clause clause1, Clause clause2) {

        Literal newHead1 = clause1.getStringHandler().getLiteral("head", clause1.getDefiniteClauseHead().getArguments());
        clause1 = clause1.getStringHandler().getClause(Collections.singletonList(newHead1), clause1.getNegativeLiterals());

        Literal newHead2 = clause2.getStringHandler().getLiteral("head", clause2.getDefiniteClauseHead().getArguments());
        clause2 = clause2.getStringHandler().getClause(Collections.singletonList(newHead2), clause2.getNegativeLiterals());

        return clause1.isEquivalentUptoVariableRenaming(clause2, new BindingList()) != null;
    }

    private Set<Variable> determineOutputVariables(AdviceProcessor ap, RelevantClauseInformation rci, Sentence cnf) {

        Variable outputVariable = null;

        if (ap.isOutputArgumentsEnabled()) {
            List<Clause> separatedClauses = CLAUSE_COLLECTOR.getClauses(cnf);

            Set<Variable> allPossibleOutputVariables = rci.getOutputVariables();

            for (Clause clause : separatedClauses) {
                Variable last = getLastOutputVariable(clause, allPossibleOutputVariables);
                if (last != null) {
                    if (outputVariable == null) {
                        outputVariable = last;
                    }
                    else if (last.equals(outputVariable) == false) {
                        outputVariable = null;
                        Utils.println("% [AdviceProcessor] Unable to match last output variables in OR-ed clause.");
                        break;
                    }
                }
            }

            if (outputVariable != null && rci.getExample().collectAllVariables().contains(outputVariable)) {
                // If the output variable is already in the example head, just ignore it
                // since it will be added naturally anyway.
                outputVariable = null;
            }
        }

        if (outputVariable != null) {
            return Collections.singleton(outputVariable);
        }
        else {
            return Collections.EMPTY_SET;
        }
    }

    /** Returns the variable, from a set of possible variables, that occurs last in a clause.
     * 
     * @param clause
     * @param possibleLastVariables
     * @return
     */
    private Variable getLastOutputVariable(Clause clause, Set<Variable> possibleLastVariables) {

        for (int i = clause.getPosLiteralCount() - 1; i >= 0; i--) {
            Literal literal = clause.getPosLiteral(i);
            for (int j = literal.getArity() - 1; j >= 0; j--) {
                Term term = literal.getArgument(j);

                if (term instanceof Variable) {
                    Variable v = (Variable) term;
                    if (possibleLastVariables.contains(v)) {
                        return v;
                    }
                }
            }
        }

        return null;
    }

    @Override
    public String toString() {
        StringBuilder stringBuilder = new StringBuilder();

        stringBuilder.append("ActiveAdvice:\n");
        stringBuilder.append("  Advice Clauses:\n");

        for (Set<ClauseInfo> set : clauses.values()) {
            for (ClauseInfo clauseInfo : set) {
                stringBuilder.append(clauseInfo).append(".\n\n");
            }
        }

        stringBuilder.append("  Advice Modes:\n");

        for (ModeInfo modeInfo : adviceModes) {
            stringBuilder.append("    ").append(modeInfo).append(".\n");
        }

        return stringBuilder.toString();
    }

    public static class ModeInfo {

        PredicateNameAndArity predicate;

        List<Term> signature;

        List<TypeSpec> specs;

        RelevanceStrength strength;

        double cost = Double.NaN;

        public ModeInfo(PredicateNameAndArity predicate, List<Term> signature, List<TypeSpec> specs, RelevanceStrength strength) {
            this.predicate = predicate;
            this.signature = signature;
            this.specs = specs;
            this.strength = strength;
        }

        @Override
        public String toString() {
            return predicate.getPredicateName().name + "(" + Utils.toString(specs, ", ") + "), " + strength;
        }

        @Override
        public boolean equals(Object obj) {
            if (obj == null) {
                return false;
            }
            if (getClass() != obj.getClass()) {
                return false;
            }
            final ModeInfo other = (ModeInfo) obj;
            return true;
        }

        @Override
        public int hashCode() {
            int hash = 3;
            hash = 37 * hash + (this.signature != null ? this.signature.hashCode() : 0);
            hash = 37 * hash + (this.specs != null ? this.specs.hashCode() : 0);
            hash = 37 * hash + (this.strength != null ? this.strength.hashCode() : 0);
            return hash;
        }
    }

    public static class RelevanceInfo {

        PredicateNameAndArity predicate;

        RelevanceStrength strength;

        public RelevanceInfo(PredicateNameAndArity predicate, RelevanceStrength strength) {
            this.predicate = predicate;
            this.strength = strength;
        }
    }

    public static class ClauseInfo {

        private Clause clause;

        RelevanceStrength strength;

        public ClauseInfo(Clause clause, RelevanceStrength strength) {
            this.setClause(clause);
            this.strength = strength;
        }

        @Override
        public boolean equals(Object obj) {
            if (obj == null) {
                return false;
            }
            if (getClass() != obj.getClass()) {
                return false;
            }
            final ClauseInfo other = (ClauseInfo) obj;
            if (this.getClause() != other.getClause() && (this.getClause() == null || !this.getClause().equals(other.getClause()))) {
                return false;
            }
            if (this.strength != other.strength) {
                return false;
            }
            return true;
        }

        @Override
        public int hashCode() {
            int hash = 3;
            hash = 37 * hash + (this.getClause() != null ? this.getClause().hashCode() : 0);
            hash = 37 * hash + (this.strength != null ? this.strength.hashCode() : 0);
            return hash;
        }

        public void setClause(Clause clause) {
			this.clause = clause;
		}

		public Clause getClause() {
			return clause;
		}

		@Override
        public String toString() {
            return getClause().toPrettyString("    ", Integer.MAX_VALUE, new BindingList()) + ", " + strength;
        }
    }

    public static class CNFClauseCollector extends DefaultFOPCVisitor<List<Clause>> {

        public List<Clause> getClauses(Sentence compressCNFSentence) {
            List<Clause> list = new ArrayList<Clause>();

            compressCNFSentence.accept(this, list);

            return list;
        }

        @Override
        public Sentence visitClause(Clause clause, List<Clause> data) {

            data.add(clause);

            return super.visitClause(clause, data);
        }
    }
}
