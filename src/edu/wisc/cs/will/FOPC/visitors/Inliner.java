/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.visitors.DefaultFOPCVisitor;
import edu.wisc.cs.will.FOPC.visitors.Inliner.InlineData;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.LiteralOrFunction;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.Utils.MapOfLists;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

/**
 *
 * @author twalker
 */
public class Inliner {

    private static final InlinerVisitor INLINER_VISITOR = new InlinerVisitor();

    public static Sentence getInlinedSentence(Sentence sentence, HornClauseContext context, MapOfLists<PredicateNameAndArity, Clause> supportClauses) {
        return getInlinedSentence(sentence, context, null, supportClauses);
    }

    public static Sentence getInlinedSentence(Sentence sentence, Collection<? extends DefiniteClause> additionalInlinableClauses, MapOfLists<PredicateNameAndArity, Clause> supportClauses) {
        return getInlinedSentence(sentence, null, additionalInlinableClauses, supportClauses);
    }

    /** Returns the lined version of the sentence.
     *
     * If supportClauses is non-null, the support clauses encountered (including the
     * clauses mark as inlined but can't be inlined for some reason) will be placed into
     * the supportClauses map.
     *
     * @param context
     * @param sentence
     * @param supportClauses
     * @return
     */
    public static Sentence getInlinedSentence(Sentence sentence, HornClauseContext context, Collection<? extends DefiniteClause> additionalInlinableClauses, MapOfLists<PredicateNameAndArity, Clause> supportClauses) {
        return sentence.accept(INLINER_VISITOR, new InlineData(context, additionalInlinableClauses, supportClauses));
    }

    private static class InlinerVisitor extends DefaultFOPCVisitor<InlineData> {

        @Override
        public Clause visitClause(Clause clause, InlineData data) {

            // We have to make some assumptions as to what kinds of clauses
            // we might encountere here.

            // 0. An empty clause.
            //    Return the original clause.
            // 1. A clause with positive literals and no negative literals.
            //      Inline all the positive literals.
            // 2. A clause with negative literals and no positive literals.
            //      Inline all the negative literals.
            // 3. A definite rule.
            //      Inline the body, leave the head.
            // 4. A mix of positive literals and negative literals.
            //      Throw an Unsupport exception.

            Clause result = clause;

            if (clause.getPosLiteralCount() > 0 && clause.getNegLiteralCount() == 0) {

                List<Literal> expandedLiterals = new ArrayList<Literal>();
                for (Literal literal : clause.getPositiveLiterals()) {
                    Clause expansion = (Clause) literal.accept(this, data);
                    expandedLiterals.addAll(expansion.getPositiveLiterals());
                }

                result = clause.getStringHandler().getClause(expandedLiterals, null);
            }
            else if ((clause.getPosLiteralCount() == 0 && clause.getNegLiteralCount() > 0) || clause.isDefiniteClauseRule()) {
                // We can catch both case 2 & 3 here.  In the case of two, the head will just be null.

                List<Literal> expandedLiterals = new ArrayList<Literal>();
                for (Literal literal : clause.getNegativeLiterals()) {
                    Clause expansion = (Clause) literal.accept(this, data);
                    // Note: even though we are expanding negative literals,
                    // the visitLiteral method will return the expansions
                    // of the literal as the positive literals arguments
                    // of a Clause.  Essentially, it is just using the
                    // clause as a container to return the literals.
                    expandedLiterals.addAll(expansion.getPositiveLiterals());
                }

                result = clause.getStringHandler().getClause(clause.getPositiveLiterals(), expandedLiterals);
            }
            else {
                // Case 4.  Just throw an exception.
                throw new UnsupportedOperationException("Inline literals of a clause with 1 or more positive literals and 0 or more negative literals is not supported.");
            }

            return result;
        }

        /** Returns a clause containing the expanded literals.
         *
         * This clause will always contain the expanded literals
         * as positive literals, not negative literals.
         *
         * @param literal
         * @param data
         * @return
         */
        @Override
        public Clause visitLiteral(Literal literal, InlineData data) {

            Clause result = null;

            if (literal.predicateName.equals(literal.getStringHandler().standardPredicateNames.negationByFailure)) {
                result = literal.getStringHandler().getClause(handleNegationByFailure(literal, data).asLiteral(), null);
            }
            else {
                if (literal.predicateName.isContainsCallable(literal.getArity())) {
                    List<Term> newTerms = new ArrayList<Term>();
                    for (Term term : literal.getArguments()) {
                        Term newTerm = term.accept(this, data);
                        newTerms.add(newTerm);
                    }

                    literal = literal.getStringHandler().getLiteral(literal, newTerms);
                }

                List<Literal> newBodyLiterals = inlinePredicate(literal, data);

                result = literal.getStringHandler().getClause(newBodyLiterals, null);
            }

            return result;
        }

        @Override
        public Term visitFunction(Function function, InlineData data) {
            Term result = function;

            PredicateNameAndArity pnaa = function.getPredicateNameAndArity();

            if (pnaa.getPredicateName().equals(function.getStringHandler().standardPredicateNames.negationByFailure)) {
                result = handleNegationByFailure(function, data);
            }
            else {
                if (function.getPredicateName().isContainsCallable(function.getArity())) {
                    List<Term> newTerms = new ArrayList<Term>();
                    for (Term term : function.getArguments()) {
                        Term newTerm = term.accept(this, data);
                        newTerms.add(newTerm);
                    }

                    function = function.getStringHandler().getFunction(function, newTerms);
                }

                List<Literal> newBodyLiterals = inlinePredicate(function, data);

                if ( newBodyLiterals.size() == 1 ) {
                    result = newBodyLiterals.get(0).asFunction();
                }
                else {
                    result = function.getStringHandler().getSentenceAsTerm( function.getStringHandler().getClause(newBodyLiterals, null), "");
                }
            }

            return result;
        }

        public Function handleNegationByFailure(LiteralOrFunction function, InlineData data) {
            // If the function is a negation-by-failure we can iterated into the arguments...

            // Because we are inconsistent as to how we treat negation-by-failure,
            // we use the handy methods in the stringHandler to extract the body
            // and reconstruct it later.

            Clause contents = function.getStringHandler().getNegationByFailureContents(function.asLiteral());

            Clause newContents = (Clause) contents.accept(this, data);

            return function.getStringHandler().getNegationByFailure(newContents).asFunction();
        }

        public List<Literal> inlinePredicate(LiteralOrFunction literalToInline, InlineData data) {

            PredicateNameAndArity pnaa = literalToInline.getPredicateNameAndArity();

            List<Literal> result = Collections.singletonList(literalToInline.asLiteral());

            if (data.canInline(pnaa)) {
                
                List<DefiniteClause> definitions = data.getClauseDefinitions(pnaa);
                if (definitions == null || definitions.size() != 1) {
                    data.addDoNotInlinePredicate(pnaa);
                }
                else {
                    DefiniteClause definition = definitions.get(0);

                    if (definition.isDefiniteClauseRule()) {

                        // Make sure we don't expand this literal within
                        // its own body.
                        InlineData newData = new InlineData(data);
                        newData.addDoNotInlinePredicate(pnaa);

                        Literal head = definition.getDefiniteClauseHead();
                        List<Literal> body = definition.getDefiniteClauseBody();

                        BindingList bl = Unifier.UNIFIER.unify(head, literalToInline.asLiteral());

                        result = new ArrayList<Literal>();

                        for (Literal bodyLiteral : body) {
                            Clause inlinedBody = (Clause) bodyLiteral.accept(this, data);
                            inlinedBody = inlinedBody.applyTheta(bl);

                            result.addAll(inlinedBody.getPositiveLiterals());
                        }
                    }
                }
            }
            else if (pnaa.isInlined() || pnaa.isSupportingPrediate()) {
                // If we can't inline the literal, sometime it is because the
                // we are processing a literal with a recursive definition and we
                // have already inlined the head.  In this case, we treat it as a
                // support predicate and add it to the list of support predicates.
            }

            return result;
        }
    }

    public static class InlineData {

        InlineData parent;

        HornClauseContext context;

        Collection<? extends DefiniteClause> additionalInlinableClauses;

        //Set<PredicateNameAndArity> inlineSet;
        Set<PredicateNameAndArity> doNotInlineSet;

        MapOfLists<PredicateNameAndArity, Clause> supportClauses;

        public InlineData(HornClauseContext context, Collection<? extends DefiniteClause> additionalInlinableClauses, MapOfLists<PredicateNameAndArity, Clause> supportClauses) {
            this.context = context;
            this.additionalInlinableClauses = additionalInlinableClauses;
            this.supportClauses = supportClauses;
        }

        public InlineData(InlineData parent) {
            this.parent = parent;
        }

        /** Returns whether a predicate can be inlined.
         *
         * Returns true if the predicate is in the inlineSet but is not in
         * the doNotInlineSet.
         *
         * @param aPredicate
         * @return
         */
        public boolean canInline(PredicateNameAndArity aPredicate) {
            boolean result = aPredicate.isInlined() && doNotInline(aPredicate) == false;

            if ( result == false ) {
                result = (findAdditionalInlinableClause(aPredicate) != null);
            }

            return result;
        }

        public List<DefiniteClause> getClauseDefinitions(PredicateNameAndArity pnaa) {
            List<DefiniteClause> result = null;

            HornClauseContext c = getContext();
            if ( c != null ) {
                result = c.getClausebase().getAssertions(pnaa);
            }

            if ( result == null ) {
                result = findAdditionalInlinableClause(pnaa);
            }

            return result;
        }

        /** Returns whether a predicate can not be inlined.
         *
         * Returns true if the predicate is in the doNotInlineSet.  Only
         * considers the doNotInlineSet, so a false return value does not
         * indicate the literal can be inlined.
         *
         * @param aPredicate
         * @return
         */
        private boolean doNotInline(PredicateNameAndArity aPredicate) {
            boolean result = false;
            if (doNotInlineSet != null && doNotInlineSet.contains(aPredicate)) {
                result = true;
            }
            else if (parent != null) {
                result = parent.doNotInline(aPredicate);
            }
            return result;
        }

        public void addDoNotInlinePredicate(PredicateNameAndArity aPredicate) {
            if (doNotInlineSet == null) {
                doNotInlineSet = new HashSet<PredicateNameAndArity>();
            }
            doNotInlineSet.add(aPredicate);
        }

        public void addSupportClause(PredicateNameAndArity aPredicate) {
            if (parent != null) {
                parent.addSupportClause(aPredicate);
            }
            else if (supportClauses != null) {
                if (supportClauses.containsKey(aPredicate) == false) {
                    List<DefiniteClause> definitions = context.getClausebase().getAssertions(aPredicate);
                    for (DefiniteClause definiteClause : definitions) {
                        supportClauses.add(aPredicate, definiteClause.getDefiniteClauseAsClause());
                    }
                }
            }
        }

        public List<DefiniteClause> findAdditionalInlinableClause(PredicateNameAndArity pnaa) {

            List<DefiniteClause> result = null;

            if ( additionalInlinableClauses != null ) {
                for (DefiniteClause aClause : additionalInlinableClauses) {
                    if ( aClause.getDefiniteClauseHead().getPredicateNameAndArity().equals(pnaa) ) {
                        if ( result == null ) {
                            result = new LinkedList<DefiniteClause>();
                        }
                        result.add(aClause);
                    }
                }
            }

            return result;
        }
        
        public HornClauseContext getContext() {
            if (parent != null) {
                return parent.getContext();
            }
            return context;
        }
    }

    private Inliner() {
    }
}
