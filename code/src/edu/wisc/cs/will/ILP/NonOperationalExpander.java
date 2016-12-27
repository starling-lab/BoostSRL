/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.ConnectedSentence;
import edu.wisc.cs.will.FOPC.Constant;
import edu.wisc.cs.will.FOPC.visitors.DefaultFOPCVisitor;
import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.ListAsTerm;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.LiteralAsTerm;
import edu.wisc.cs.will.FOPC.LiteralOrFunction;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.QuantifiedSentence;
import edu.wisc.cs.will.FOPC.visitors.ReplaceLiteralsVisitor;
import edu.wisc.cs.will.FOPC.visitors.ReplacePredicatesVisitor;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.SentenceAsTerm;
import edu.wisc.cs.will.FOPC.visitors.SentenceVisitor;
import edu.wisc.cs.will.FOPC.StringConstant;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.visitors.TermVisitor;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.Utils.MapOfLists;
import edu.wisc.cs.will.Utils.MapOfSets;
import edu.wisc.cs.will.Utils.Utils;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 *
 * @author twalker
 */
public class NonOperationalExpander {

//    private static final NonOperationalExpanderVisitor NON_OPERATIONAL_EXPANDER_VISITOR = new NonOperationalExpanderVisitor();
//
//    private static final NonOperationExpansionCountVisitor EXPANSION_COUNT_VISITOR = new NonOperationExpansionCountVisitor();
    private static final CollectNonOperationalLiteralsVisitor COLLECT_NON_OPERATIONAL_LITERALS_VISITOR = new CollectNonOperationalLiteralsVisitor();

    private NonOperationalExpander() {
    }

    public static List<? extends Sentence> getExpandedSentences(HornClauseContext context, Sentence sentence, MapOfLists<PredicateNameAndArity, Clause> supportClauses) {

        List<Sentence> results = null;

        CollectorData collectorData = new CollectorData();

        sentence.accept(COLLECT_NON_OPERATIONAL_LITERALS_VISITOR, collectorData);

        if (collectorData.literals.isEmpty()) {
            results = Collections.singletonList(sentence);
        }
        else {
            List<Clause> expansionCombinations = getNonOperationalCombinations(collectorData.literals, new ExpansionData2(context));

            results = new ArrayList<Sentence>();

            for (Clause clause : expansionCombinations) {
                Map<Literal, Literal> replacementMap = getNonOperationalExpansionMap(collectorData.literals, clause.getPositiveLiterals());

                Sentence newSentence = sentence.accept(ReplaceLiteralsVisitor.REPLACE_LITERALS_VISITOR, replacementMap);

                results.add(newSentence);
            }
        }

        return results;


//        ExpansionData data = new ExpansionData(context, supportClauses);
//
//        return sentence.accept(NON_OPERATIONAL_EXPANDER_VISITOR, data);
    }

    private static Map<Literal, Literal> getNonOperationalExpansionMap(List<Literal> nonOperationalLiterals, List<Literal> operationalLiterals) {

        Map<Literal, Literal> map = new HashMap<Literal, Literal>();

        for (int i = 0; i < nonOperationalLiterals.size(); i++) {
            Literal nonOp = nonOperationalLiterals.get(i);
            Literal op = operationalLiterals.get(i);

            map.put(nonOp, op);
        }

        return map;

    }

    private static List<Clause> getNonOperationalCombinations(List<Literal> nonOps, ExpansionData2 data) {

        List<Clause> result = Collections.EMPTY_LIST;

        if (nonOps.isEmpty() == false) {

            List<Literal> firstLiteralExpansion = null;

            Literal firstLiteral = nonOps.get(0);

            Literal existingMapping = data.getExistingMapping(firstLiteral);

            if (existingMapping != null) {

                firstLiteralExpansion = Collections.singletonList(firstLiteral.getStringHandler().getLiteral(existingMapping, firstLiteral.getArguments()));
            }
            else {
                firstLiteralExpansion = new ArrayList<Literal>();
                Set<PredicateNameAndArity> operationalExpansions = firstLiteral.getPredicateName().getOperationalExpansions(firstLiteral.getArity());

                for (PredicateNameAndArity operationalPredicateNameAndArity : operationalExpansions) {
                    firstLiteralExpansion.add(firstLiteral.getStringHandler().getLiteral(operationalPredicateNameAndArity.getPredicateName(), firstLiteral.getArguments()));
                }
            }

            result = new ArrayList<Clause>();

            for (Literal aFirstExpansion : firstLiteralExpansion) {
                ExpansionData2 newData = new ExpansionData2(data);
                newData.addExistingMapping(firstLiteral, aFirstExpansion);

                List<Clause> restOfExpansions = getNonOperationalCombinations(nonOps.subList(1, nonOps.size()), newData);

                if (restOfExpansions.isEmpty()) {
                    result.add(firstLiteral.getStringHandler().getClause(aFirstExpansion, null));
                }
                else {
                    for (Clause aRestExpansion : restOfExpansions) {
                        List<Literal> newArgs = new ArrayList<Literal>();
                        newArgs.add(aFirstExpansion);
                        newArgs.addAll(aRestExpansion.getPositiveLiterals());

                        result.add(firstLiteral.getStringHandler().getClause(newArgs, null));
                    }
                }
            }

        }

        return result;
    }

    private static class CollectNonOperationalLiteralsVisitor extends DefaultFOPCVisitor<CollectorData> {

        @Override
        public Sentence visitLiteral(Literal literal, CollectorData data) {
            if (literal.getPredicateNameAndArity().isNonOperational()) {
                data.literals.add(literal);
            }
            else if (literal.getStringHandler().isNegationByFailure(literal)) {
                super.visitLiteral(literal, data);
            }

            return null;
        }

        @Override
        public Term visitFunction(Function function, CollectorData data) {
            if (function.getPredicateNameAndArity().isNonOperational()) {
                data.literals.add(function.asLiteral());
            }
            else if (function.getStringHandler().isNegationByFailure(function)) {
                super.visitFunction(function, data);
            }

            return null;
        }
    }

    private static class CollectorData {

        List<Literal> literals = new ArrayList<Literal>();

    }

    private static class ExpansionData2 {

        HornClauseContext context;

        ExpansionData2 parent;

        MapOfSets<PredicateNameAndArity, ExistingExpansion> existingExpansionsMap;

        public ExpansionData2(HornClauseContext context) {
            this.context = context;
        }

        public ExpansionData2(ExpansionData2 parent) {
            this.parent = parent;
        }

        public Literal getExistingMapping(LiteralOrFunction nonOperationLiteral) {
            Literal result = null;

            if (existingExpansionsMap != null) {

                PredicateNameAndArity pnaa = nonOperationLiteral.getPredicateNameAndArity();

                Set<TermAndIndex> set = getFreeTermSet(nonOperationLiteral);

                Set<ExistingExpansion> existingExpansions = existingExpansionsMap.getValues(pnaa);

                if (existingExpansions != null) {
                    for (ExistingExpansion existingExpansion : existingExpansions) {
                        if (existingExpansion.termAndIndices.equals(set)) {
                            // We found an existing expansion, so create a literal and return it.
                            result = nonOperationLiteral.getStringHandler().getLiteral(existingExpansion.expansion.getPredicateName(), nonOperationLiteral.getArguments());
                            break;
                        }
                    }
                }

            }

            if (result == null && parent != null) {
                result = parent.getExistingMapping(nonOperationLiteral);
            }

            return result;
        }

        public void addExistingMapping(LiteralOrFunction fromNonOperational, LiteralOrFunction toOperational) {
            if (existingExpansionsMap == null) {
                existingExpansionsMap = new MapOfSets<PredicateNameAndArity, ExistingExpansion>();
            }

            existingExpansionsMap.put(fromNonOperational.getPredicateNameAndArity(), new ExistingExpansion(toOperational.getPredicateNameAndArity(), getFreeTermSet(toOperational)));
        }

        public HornClauseContext getContext() {
            if (parent != null) {
                return parent.getContext();
            }
            else {
                return context;
            }
        }

        private Set<TermAndIndex> getFreeTermSet(LiteralOrFunction literal) {
            Set<TermAndIndex> set = new HashSet<TermAndIndex>();

            List<Term> arguments = literal.getArguments();

            for (int i = 0; i < arguments.size(); i++) {
                Term t = arguments.get(i);

                if (t.isGrounded() == false) {
                    set.add(new TermAndIndex(t, i));
                }
            }

            return set;
        }
    }

    private static class ExistingExpansion {

        PredicateNameAndArity expansion;

        Set<TermAndIndex> termAndIndices;

        public ExistingExpansion(PredicateNameAndArity expansion, Set<TermAndIndex> termAndIndices) {
            this.expansion = expansion;
            this.termAndIndices = termAndIndices;
        }

        public PredicateNameAndArity getExpansion() {
            return expansion;
        }

        public void setExpansion(PredicateNameAndArity expansion) {
            this.expansion = expansion;
        }

        public Set<TermAndIndex> getTermAndIndices() {
            return termAndIndices;
        }

        public void setTermAndIndices(Set<TermAndIndex> termAndIndices) {
            this.termAndIndices = termAndIndices;
        }

        @Override
        public String toString() {
            return "ExistingExpansion{" + "expansion=" + expansion + "termAndIndices=" + termAndIndices + '}';
        }
    }

    private static class TermAndIndex {

        Term term;

        int index;

        public TermAndIndex(Term term, int index) {
            this.term = term;
            this.index = index;
        }

        @Override
        public boolean equals(Object obj) {
            if (obj == null) {
                return false;
            }
            if (getClass() != obj.getClass()) {
                return false;
            }
            final TermAndIndex other = (TermAndIndex) obj;
            if (this.term != other.term && (this.term == null || !this.term.equals(other.term))) {
                return false;
            }
            if (this.index != other.index) {
                return false;
            }
            return true;
        }

        @Override
        public int hashCode() {
            int hash = 5;
            hash = 37 * hash + (this.term != null ? this.term.hashCode() : 0);
            hash = 37 * hash + this.index;
            return hash;
        }

        @Override
        public String toString() {
            return term + "@" + index;
        }
    }
    // <editor-fold defaultstate="collapsed" desc="Original Code">
//    private static class NonOperationalExpanderVisitor implements SentenceVisitor<List<? extends Sentence>, ExpansionData>, TermVisitor<List<? extends Term>, ExpansionData> {
//
//        public List<Sentence> visitOtherSentence(Sentence otherSentence, ExpansionData data) {
//            return Collections.singletonList(otherSentence);
//        }
//
//        public List<ConnectedSentence> visitConnectedSentence(ConnectedSentence sentence, ExpansionData data) {
//            List<? extends Sentence> a = sentence.getSentenceA() == null ? Collections.singletonList((Sentence) null) : sentence.getSentenceA().accept(this, data);
//            List<? extends Sentence> b = sentence.getSentenceB() == null ? Collections.singletonList((Sentence) null) : sentence.getSentenceB().accept(this, data);
//
//            List<ConnectedSentence> list = new ArrayList<ConnectedSentence>();
//
//            for (Sentence sentence1 : a) {
//                for (Sentence sentence2 : b) {
//                    list.add(sentence.getStringHandler().getConnectedSentence(sentence1, sentence.getConnective(), sentence2));
//                }
//            }
//
//            return list;
//        }
//
//        public List<QuantifiedSentence> visitQuantifiedSentence(QuantifiedSentence sentence, ExpansionData data) {
//            List<? extends Sentence> newBodies = sentence.body.accept(this, data);
//
//            List<QuantifiedSentence> list = new ArrayList<QuantifiedSentence>();
//
//            for (Sentence newBody : newBodies) {
//                list.add(sentence.replaceVariablesAndBody(sentence.variables, newBody));
//            }
//
//            return list;
//        }
//
//        public List<Clause> visitClause(Clause clause, ExpansionData data) {
//            List<Clause> result = null;
//
//            if (clause.getPosLiteralCount() > 0) {
//
//                result = expandLiteralList(clause.getPositiveLiterals(), data);
//            }
//
//            if (clause.getNegLiteralCount() > 0) {
//                Utils.error("Expanding negated literals in a clause is not supported.");
//            }
//
//            return result;
//        }
//
//        public List<Literal> visitLiteral(Literal literal, ExpansionData data) {
//
//            List<Literal> result = new ArrayList<Literal>();
//
//            Collection<PredicateNameAndArity> predicateExpansions;
//
//            PredicateNameAndArity pnaa = literal.getPredicateNameAndArity();
//            if (pnaa.isNonOperational()) {
//                Literal existingExpansion = data.getExistingMapping(literal);
//
//                if (existingExpansion != null) {
//                    predicateExpansions = Collections.singleton(existingExpansion.getPredicateNameAndArity());
//                }
//                else {
//                    predicateExpansions = pnaa.getOperationalExpansions();
//                }
//            }
//            else if (pnaa.isInlined() || pnaa.isSupportingPrediate()) {
//                // Support clauses might also have embedded expansions that
//                // we need to consider.  There are a little more tricky.
//                predicateExpansions = expandSupportClause(pnaa, data);
//            }
//            else {
//                predicateExpansions = Collections.singleton(pnaa);
//            }
//
//            for (PredicateNameAndArity anExpansion : predicateExpansions) {
//
//                ExpansionData newData = data;
//
//                if ((pnaa.isInlined() || pnaa.isSupportingPrediate()) && pnaa.equals(anExpansion) == false) {
//                    // If this was an inline or a supporting predicate,
//                    // we can add the pnaa to the expansion list so
//                    // this particular support clause doesn't get
//                    // expanded again.
////
////                newData = new ExpansionData(data);
////                newData.addExistingMapping( literal.getStringHandler().getLiteral(pnaa), literal.getStringHandler().);
//                }
//
//                // Create the term expansions.  Note, this is a list of
//                // Literals, but the Literal is just a being used as a
//                // data structure to hold the expanded terms.  It is
//                // better than a List<List<Term>>, sorta.
//                List<Literal> termExpansions = Collections.singletonList(null);
//
//                if (literal.getArity() > 0) {
//                    termExpansions = expandTermList(literal.getArguments(), newData);
//                }
//
//                for (Literal expandedTermsHolder : termExpansions) {
//
//                    List<Term> expandedTerms = null;
//                    if (expandedTermsHolder != null && expandedTermsHolder.getArity() > 0) {
//                        expandedTerms = expandedTermsHolder.getArguments();
//                    }
//
//                    result.add(literal.getStringHandler().getLiteral(anExpansion.getPredicateName().name, expandedTerms));
//                }
//            }
//
//            return result;
//        }
//
//        public List<? extends Term> visitFunction(Function function, ExpansionData data) {
//
//            List<Function> result = null;
//
//            Collection<PredicateNameAndArity> predicateExpansions;
//
//            PredicateNameAndArity pnaa = function.getPredicateNameAndArity();
//
//            Literal existingExpansion = data.getExistingMapping(function);
//
//            if (existingExpansion != null) {
//                result = Collections.singletonList(existingExpansion.asFunction());
//            }
//            else {
//
//                result = new ArrayList<Function>();
//
//                if (pnaa.isNonOperational()) {
//                    predicateExpansions = pnaa.getOperationalExpansions();
//                }
//                else if (pnaa.isInlined() || pnaa.isSupportingPrediate()) {
//                    // Support clauses might also have embedded expansions that
//                    // we need to consider.  There are a little more tricky.
//                    predicateExpansions = expandSupportClause(pnaa, data);
//                }
//                else {
//                    predicateExpansions = Collections.singleton(pnaa);
//                }
//
//                for (PredicateNameAndArity anExpansion : predicateExpansions) {
//
//                    ExpansionData newData = data;
//
//                    //            if ( pnaa.isInlined() || pnaa.isSupportingPrediate() ) {
//                    //                // If this was an inline or a supporting predicate,
//                    //                // we can add the pnaa to the expansion list so
//                    //                // this particular support clause doesn't get
//                    //                // expanded again.
//                    //
//                    //                newData = new ExpansionData(data);
//                    //                newData.addExistingMapping(pnaa, anExpansion);
//                    //            }
//
//                    // Create the term expansions.  Note, this is a list of
//                    // Literals, but the Literal is just a being used as a
//                    // data structure to hold the expanded terms.  It is
//                    // better than a List<List<Term>>, sorta.
//                    List<Literal> termExpansions = Collections.singletonList(null);
//
//                    if (function.getArity() > 0) {
//                        termExpansions = expandTermList(function.getArguments(), newData);
//                    }
//
//                    for (Literal expandedTermsHolder : termExpansions) {
//
//                        List<Term> expandedTerms = null;
//                        if (expandedTermsHolder != null && expandedTermsHolder.getArity() > 0) {
//                            expandedTerms = expandedTermsHolder.getArguments();
//                        }
//
//                        result.add(function.getStringHandler().getFunction(anExpansion.getPredicateName().name, expandedTerms));
//                    }
//                }
//            }
//
//            return result;
//
//        }
//
//        public List<? extends Term> visitVariable(Variable variable, ExpansionData data) {
//            return Collections.singletonList(variable);
//        }
//
//        public List<? extends Term> visitSentenceAsTerm(SentenceAsTerm sentenceAsTerm, ExpansionData data) {
//            List<Term> result = new ArrayList<Term>();
//
//            List<? extends Sentence> sentences = sentenceAsTerm.sentence.accept(this, data);
//            for (Sentence sentence : sentences) {
//                result.add(sentence.asTerm());
//            }
//            return result;
//        }
//
//        public List<? extends Term> visitLiteralAsTerm(LiteralAsTerm literalAsTerm, ExpansionData data) {
//            List<Term> result = new ArrayList<Term>();
//
//            List<? extends Sentence> sentences = literalAsTerm.itemBeingWrapped.accept(this, data);
//            for (Sentence sentence : sentences) {
//                result.add(sentence.asTerm());
//            }
//            return result;
//        }
//
//        public List<? extends Term> visitListAsTerm(ListAsTerm listAsTerm, ExpansionData data) {
//            return Collections.singletonList(listAsTerm);
//        }
//
//        public List<? extends Term> visitNumericConstant(NumericConstant numericConstant, ExpansionData data) {
//            return Collections.singletonList(numericConstant);
//        }
//
//        public List<? extends Term> visitStringConstant(StringConstant stringConstant, ExpansionData data) {
//            return Collections.singletonList(stringConstant);
//        }
//
//        public List<? extends Term> visitOtherConstant(Constant constant, ExpansionData data) {
//            return Collections.singletonList(constant);
//        }
//
//        public List<? extends Term> visitOtherTerm(Term term, ExpansionData data) {
//            return Collections.singletonList(term);
//        }
//
//        /** Expands a list of terms.
//         *
//         * The returned clause is just a place-holder to contain the terms
//         * (as opposed to creating a list of list, which is always a bit
//         * confusing).
//         *
//         * @param literals
//         * @return
//         */
//        private List<Clause> expandLiteralList(List<Literal> literals, ExpansionData data) {
//
//            List<Clause> result = Collections.EMPTY_LIST;
//
//            if (literals.isEmpty() == false) {
//                Literal firstLiteral = literals.get(0);
//
//                List<Literal> firstTermExpansions = (List<Literal>) firstLiteral.accept(this, data);
//
//                // Create the cross product...
//                result = new ArrayList<Clause>();
//                for (Literal aFirstLiteral : firstTermExpansions) {
//
//                    ExpansionData newData = new ExpansionData(data);
//                    if ( firstLiteral.getPredicateNameAndArity().isNonOperational()) {
//                        newData.addExistingMapping(firstLiteral, aFirstLiteral);
//                    }
//
//                    List<Clause> restOfTermsExpansions = expandLiteralList(literals.subList(1, literals.size()), newData);
//
//                    if (restOfTermsExpansions.isEmpty()) {
//                        Clause combination = data.getContext().getStringHandler().getClause(Collections.singletonList(aFirstLiteral), null);
//                        result.add(combination);
//                    }
//                    else {
//                        for (Clause restOfLiterals : restOfTermsExpansions) {
//                            List<Literal> newArgs = new ArrayList<Literal>();
//
//                            newArgs.add(aFirstLiteral);
//
//                            if (restOfLiterals.getPosLiteralCount() > 0) {
//                                newArgs.addAll(restOfLiterals.getPositiveLiterals());
//                            }
//
//                            Clause combination = data.getContext().getStringHandler().getClause(newArgs, null);
//
//                            result.add(combination);
//                        }
//                    }
//                }
//            }
//
//            return result;
//        }
//
//        /** Expands a list of terms.
//         *
//         * The returned literal is just a place-holder to contain the terms
//         * (as opposed to creating a list of list, which is always a bit
//         * confusing).
//         *
//         * @param terms
//         * @return
//         */
//        private List<Literal> expandTermList(List<Term> terms, ExpansionData data) {
//
//            List<Literal> result = Collections.EMPTY_LIST;
//
//            if (terms.isEmpty() == false) {
//                Term firstTerm = terms.get(0);
//
//                List<? extends Term> firstTermExpansions = firstTerm.accept(this, data);
//
//                // Create the cross product...
//                result = new ArrayList<Literal>();
//
//                for (Term aFirstTerm : firstTermExpansions) {
//
//                    ExpansionData newData = new ExpansionData(data);
//                    if ( firstTerm instanceof Function && ((Function)firstTerm).getPredicateNameAndArity().isNonOperational()) {
//                        newData.addExistingMapping((Function)firstTerm, (Function)aFirstTerm);
//                    }
//
//                    List<Literal> restOfTermsExpansions = expandTermList(terms.subList(1, terms.size()), newData);
//
//
//
//                    if (restOfTermsExpansions.isEmpty()) {
//                        Literal combination = data.getContext().getStringHandler().getLiteral("ignoreme", Collections.singletonList(aFirstTerm));
//                        result.add(combination);
//                    }
//                    else {
//                        for (Literal literal : restOfTermsExpansions) {
//                            List<Term> newArgs = new ArrayList<Term>();
//
//                            newArgs.add(aFirstTerm);
//                            if (literal.getArity() > 0) {
//                                newArgs.addAll(literal.getArguments());
//                            }
//
//                            Literal combination = data.getContext().getStringHandler().getLiteral("ignoreme", newArgs);
//                            result.add(combination);
//                        }
//                    }
//
//                }
//            }
//
//            return result;
//        }
//
//        public List<PredicateNameAndArity> expandSupportClause(PredicateNameAndArity supportPredicate, ExpansionData data) {
//            List<PredicateNameAndArity> expansions = Collections.singletonList(supportPredicate);
//
//
//            Collection<DefiniteClause> clauseDefinition = data.getContext().getClausebase().getAssertions(supportPredicate.getPredicateName(), supportPredicate.getArity());
//
//            if (clauseDefinition == null) {
//                // If there aren't any expansions, just return the original predicate.
//                //expansions = Collections.singletonList(supportPredicate);
//            }
//            else if (clauseDefinition.size() == 1) {
//                expansions = new ArrayList<PredicateNameAndArity>();
//
//                // Create a new set of expansion data to make sure the current support predicate doesn't
//                // get processed indefinitely.
//                ExpansionData newData = new ExpansionData(data);
//                //newData.addExistingMapping(supportPredicate, supportPredicate);
//
//                for (DefiniteClause definiteClause : clauseDefinition) {
//                    Literal head = definiteClause.getDefiniteClauseHead();
//                    List<Literal> body = definiteClause.getDefiniteClauseBody();
//
//                    List<Clause> expandedBodies = expandLiteralList(body, newData);
//
//                    if (expandedBodies.size() == 1) {
//                        expansions.add(supportPredicate);
//                    }
//                    else {
//                        int opExpansion = 0;
//                        for (Clause anExpandedBody : expandedBodies) {
//                            // Now that we have the possible expanded bodies (stored in the Clauses),
//                            // we need to recreate the definiteClause, rename the literal to something
//                            // unique, and add it to the supportClauses.
//                            PredicateName newName = data.context.getStringHandler().getPredicateName(supportPredicate.getPredicateName().name + "_op" + (opExpansion++));
//                            PredicateNameAndArity newPNAA = new PredicateNameAndArity(newName, supportPredicate.getArity());
//
//                            Clause newClause = data.getContext().getStringHandler().getClause(Collections.singletonList(head), anExpandedBody.getPositiveLiterals());
//                            Map<PredicateNameAndArity, PredicateNameAndArity> renameMap = Collections.singletonMap(supportPredicate, newPNAA);
//                            newClause = (Clause) newClause.accept(ReplacePredicatesVisitor.REPLACE_PREDICATES_VISITOR, renameMap);
//
//                            expansions.add(newPNAA);
//                            data.addSupportClause(newPNAA, newClause);
//                        }
//                    }
//                }
//            }
//            else {
//                // Opps...the support predicate is an or...we will handle those a little
//                // later, once I get around to it!
//                Utils.waitHere("Can't expand nonOperational OR supportClauss.");
//            }
//
//            return expansions;
//        }
//    }
//
//    private static class ExpansionData {
//
//        HornClauseContext context;
//
//        ExpansionData parent;
//
//        MapOfSets<PredicateNameAndArity, ExistingExpansion> existingExpansionsMap;
//
//        MapOfLists<PredicateNameAndArity, Clause> supportClauses;
//
//        public ExpansionData(HornClauseContext context, MapOfLists<PredicateNameAndArity, Clause> supportClauses) {
//            this.context = context;
//            this.supportClauses = supportClauses;
//        }
//
//        public ExpansionData(ExpansionData parent) {
//            this.parent = parent;
//        }
//
//        public Literal getExistingMapping(LiteralOrFunction nonOperationLiteral) {
//            Literal result = null;
//
//            if (existingExpansionsMap != null) {
//
//                PredicateNameAndArity pnaa = nonOperationLiteral.getPredicateNameAndArity();
//
//                Set<TermAndIndex> set = getFreeTermSet(nonOperationLiteral);
//
//                Set<ExistingExpansion> existingExpansions = existingExpansionsMap.getValues(pnaa);
//
//                if (existingExpansions != null) {
//                    for (ExistingExpansion existingExpansion : existingExpansions) {
//                        if (existingExpansion.termAndIndices.equals(set)) {
//                            // We found an existing expansion, so create a literal and return it.
//                            result = nonOperationLiteral.getStringHandler().getLiteral(existingExpansion.expansion.getPredicateName(), nonOperationLiteral.getArguments());
//                            break;
//                        }
//                    }
//                }
//
//            }
//
//            if (result == null && parent != null) {
//                result = parent.getExistingMapping(nonOperationLiteral);
//            }
//
//            return result;
//        }
//
//        public void addExistingMapping(LiteralOrFunction fromNonOperational, LiteralOrFunction toOperational) {
//            if (existingExpansionsMap == null) {
//                existingExpansionsMap = new MapOfSets<PredicateNameAndArity, ExistingExpansion>();
//            }
//
//            existingExpansionsMap.put(fromNonOperational.getPredicateNameAndArity(), new ExistingExpansion(toOperational.getPredicateNameAndArity(), getFreeTermSet(toOperational)));
//        }
//
//        public void addSupportClause(PredicateNameAndArity newPredicate, Clause clause) {
//            if (parent != null) {
//                parent.addSupportClause(newPredicate, clause);
//            }
//            else if (supportClauses != null) {
//                supportClauses.add(newPredicate, clause);
//            }
//        }
//
//        public HornClauseContext getContext() {
//            if (parent != null) {
//                return parent.getContext();
//            }
//            else {
//                return context;
//            }
//        }
//
//        private Set<TermAndIndex> getFreeTermSet(LiteralOrFunction literal) {
//            Set<TermAndIndex> set = new HashSet<TermAndIndex>();
//
//            List<Term> arguments = literal.getArguments();
//
//            for (int i = 0; i < arguments.size(); i++) {
//                Term t = arguments.get(i);
//
//                if (t.isGrounded() == false) {
//                    set.add(new TermAndIndex(t, i));
//                }
//            }
//
//            return set;
//        }
//    }
//    private static class NonOperationExpansionCountVisitor implements SentenceVisitor<Integer, ExpansionData>, TermVisitor<Integer, ExpansionData> {
//
//        public Integer visitLiteral(Literal literal, ExpansionData data) {
//
//            int result = 1;
//
//            Set<PredicateNameAndArity> predicateExpansions;
//
//            PredicateNameAndArity pnaa = literal.getPredicateNameAndArity();
//            if (pnaa.isNonOperational()) {
//                predicateExpansions = pnaa.getOperationalExpansions();
//                result = predicateExpansions.size();
//            }
//
//            if (literal.getArity() > 0) {
//                for (Term term : literal.getArguments()) {
//                    result *= term.accept(this, data);
//                }
//            }
//
//            return result;
//        }
//
//        public Integer visitOtherSentence(Sentence otherSentence, ExpansionData data) {
//            return otherSentence.accept(this, data);
//        }
//
//        public Integer visitConnectedSentence(ConnectedSentence sentence, ExpansionData data) {
//            int result = 1;
//
//            result *= sentence.getSentenceA() == null ? 1 : sentence.getSentenceA().accept(this, data);
//            result *= sentence.getSentenceB() == null ? 1 : sentence.getSentenceB().accept(this, data);
//
//            return result;
//        }
//
//        public Integer visitQuantifiedSentence(QuantifiedSentence sentence, ExpansionData data) {
//            return sentence.body.accept(this, data);
//        }
//
//        public Integer visitClause(Clause clause, ExpansionData data) {
//
//            int result = 1;
//
//            if (clause.getPosLiteralCount() > 0) {
//                for (Literal literal : clause.getPositiveLiterals()) {
//                    result *= literal.accept(this, data);
//                }
//            }
//
//            if (clause.getNegLiteralCount() > 0) {
//                for (Literal literal : clause.getNegativeLiterals()) {
//                    result *= literal.accept(this, data);
//                }
//            }
//
//            return result;
//        }
//
//        public Integer visitFunction(Function function, ExpansionData data) {
//
//            int result = 1;
//
//            Set<PredicateNameAndArity> predicateExpansions;
//
//            PredicateNameAndArity pnaa = function.getPredicateNameAndArity();
//            if (pnaa.isNonOperational()) {
//                predicateExpansions = pnaa.getOperationalExpansions();
//                result = predicateExpansions.size();
//            }
//
//            if (function.getArity() > 0) {
//                for (Term term : function.getArguments()) {
//                    result *= term.accept(this, data);
//                }
//            }
//
//            return result;
//
//        }
//
//        public Integer visitVariable(Variable variable, ExpansionData data) {
//            return 1;
//        }
//
//        public Integer visitSentenceAsTerm(SentenceAsTerm sentenceAsTerm, ExpansionData data) {
//
//            int result = sentenceAsTerm.sentence.accept(this, data);
//
//
//            return result;
//        }
//
//        public Integer visitLiteralAsTerm(LiteralAsTerm literalAsTerm, ExpansionData data) {
//
//            int result = literalAsTerm.itemBeingWrapped.accept(this, data);
//            return result;
//        }
//
//        public Integer visitListAsTerm(ListAsTerm listAsTerm, ExpansionData data) {
//            int result = 1;
//
//            return result;
//        }
//
//        public Integer visitNumericConstant(NumericConstant numericConstant, ExpansionData data) {
//            return 1;
//        }
//
//        public Integer visitStringConstant(StringConstant stringConstant, ExpansionData data) {
//            return 1;
//        }
//
//        public Integer visitOtherConstant(Constant constant, ExpansionData data) {
//            return 1;
//        }
//
//        public Integer visitOtherTerm(Term term, ExpansionData data) {
//            return 1;
//        }
//    }
// </editor-fold>
}
