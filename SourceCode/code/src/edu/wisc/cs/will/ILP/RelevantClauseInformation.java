/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.AllOfFOPC;
import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.ConnectedSentence;
import edu.wisc.cs.will.FOPC.ConnectiveName;
import edu.wisc.cs.will.FOPC.ConsCell;
import edu.wisc.cs.will.FOPC.Constant;
import edu.wisc.cs.will.FOPC.visitors.DefaultFOPCVisitor;
import edu.wisc.cs.will.FOPC.visitors.DefaultSentenceVisitor;
import edu.wisc.cs.will.FOPC.visitors.DefaultTermVisitor;
import edu.wisc.cs.will.FOPC.visitors.ElementPositionVisitor;
import edu.wisc.cs.will.FOPC.visitors.ElementPath;
import edu.wisc.cs.will.FOPC.visitors.ElementPositionVisitor.ElementPositionData;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.FunctionName;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.visitors.Inliner;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.visitors.PredicateCollector;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.PrettyPrinter;
import edu.wisc.cs.will.FOPC.PrettyPrinterOptions;
import edu.wisc.cs.will.FOPC.RelevanceStrength;
import edu.wisc.cs.will.FOPC.visitors.DuplicateDeterminateRemover;
import edu.wisc.cs.will.FOPC.LiteralOrFunction;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.visitors.SentenceVisitor;
import edu.wisc.cs.will.FOPC.StringConstant;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.FOPC.visitors.DoubleNegationByFailureRemover;
import edu.wisc.cs.will.FOPC.visitors.ElementPositionListener;
import edu.wisc.cs.will.FOPC.visitors.SentencePruner;
import edu.wisc.cs.will.FOPC.visitors.VariableCounter;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.Utils.MapOfLists;
import edu.wisc.cs.will.Utils.Utils;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 *
 * @author twalker
 */
public class RelevantClauseInformation implements Cloneable, RelevantInformation {

    public static final SentenceGeneralizer GENERALIZER_SENTENCE_VISITOR = new SentenceGeneralizer();

    public static final ConstantMarkerAdderSV CONSTANT_MARKER_ADDER_SV = new ConstantMarkerAdderSV();

    private static final SentenceGeneralizerVisitor SENTENCE_GENERALIZER_VISITOR = new SentenceGeneralizerVisitor();

    private static final IsSubtermVisitor IS_SUBTERM_VISITOR = new IsSubtermVisitor();

    Example example;

    private boolean relevanceFromPositiveExample = true;

    private Sentence sentence;

    private RelevanceStrength relevanceStrength = RelevanceStrength.POSSIBLE_ANSWER;

    private List<TypeSpec> typeSpecList;

    private boolean constantsSplit = false;

    private boolean containsAllAdvicePieces = true;

    private Set<ElementPath> constantPositions = null;

    Map<Term, Term> mappings;

    private Set<Variable> outputVariables = null;

    public RelevantClauseInformation(Example example, Sentence generalizeAdviceSentence, List<TypeSpec> typeSpecList) {
        this.example = example;
        this.sentence = generalizeAdviceSentence;
        this.typeSpecList = typeSpecList;
    }

    public RelevantClauseInformation(Example generalizedExample, Sentence sentence) {
        this.example = generalizedExample;
        this.sentence = sentence;

        markConstants();
    }

    public Sentence getSentence() {
        return sentence;
    }

    public Clause getClauseWithConstantsMarker() {


        Clause origClause = sentence.asClause();

        ConstantMarkerData data = new ConstantMarkerData(constantPositions);

        Clause newClause = (Clause) origClause.accept(CONSTANT_MARKER_ADDER_SV, data);



        return newClause;
    }

    public Example getExample() {
        return example;
    }

    public ConnectedSentence getImpliedSentence() {
        ConnectedSentence newSentence = example.getStringHandler().getConnectedSentence(getSentence(), ConnectiveName.IMPLIES, example);
        return newSentence;
    }

    public RelevantClauseInformation getGeneralizeRelevantInformation() {

        Example groundExample = this.example;
        Sentence groundSentence = this.getSentence();

        Map<Term, Term> termToVariableMap = new LinkedHashMap<Term, Term>();

        Example newExample = new Example(GENERALIZER_SENTENCE_VISITOR.generalize(groundExample, null, termToVariableMap));
        Sentence newSentence = GENERALIZER_SENTENCE_VISITOR.generalize(groundSentence, constantPositions, termToVariableMap);


        // I turned off the following.  I think it might be necessary for PossiblyMarkAncestorsWithPriority, but
        // it definitely breaks others, so I am disabling it for now.
//        // Sometimes a generalization is too general.  For example,
//        // when we encounter a list [xxx] and the constant xxx,
//        // the first will be generalized to variable A and the
//        // second will be generalized to variable B.
//        // We would rather have [xxx] generalized to [B] since
//        // xxx is a subterm.
//        //
//        // To that end, we look for term in the termToVariableMap
//        // for which this occurs.
//        BindingList undoGeneralizationList = new BindingList();
//        Map<Term,Term> newMappings = new HashMap<Term, Term>();
//
//        for (Map.Entry<Term, Term> entry : termToVariableMap.entrySet()) {
//            Term termToSearchFor = entry.getKey();
//
//            for (Term termToSearch : termToVariableMap.keySet()) {
//                if ( termToSearch != termToSearchFor && isSubterm(termToSearch, termToSearchFor) ) {
//                    // we found one...
//                    // now replace occurances of termToSearchFor
//                    // in term to search with the termToSearchFor
//                    // generalization.
//
//                    Term newTermToSearch = TermReplacer.replaceTerms(termToSearch, Collections.singletonMap(termToSearchFor, entry.getValue()));
//
//                    Term originalToValue = termToVariableMap.get(termToSearch);
//
//                    if ( originalToValue instanceof Variable ) {
//                        undoGeneralizationList.addBinding((Variable)originalToValue, newTermToSearch); // This maps from A -> [B]
//                        newMappings.put(termToSearch, newTermToSearch); // This maps from [xxx] -> [B]
//                    }
//                }
//            }
//        }
//
//        // Apply the undoGeneralizationList to both the example and the newSentence
//        if ( undoGeneralizationList.isEmpty() == false ) {
//            newExample = newExample.applyTheta(undoGeneralizationList);
//            newSentence = newSentence.applyTheta(undoGeneralizationList);
//
//            // Also update the termToVariableMap...
//            termToVariableMap.putAll(newMappings);
//        }

        RelevantClauseInformation newRCI = this.copy();
        newRCI.example = newExample;
        newRCI.setSentence(newSentence);
        newRCI.mappings = termToVariableMap;
        newRCI.constantPositions = constantPositions;

//        if (leaveSingleConstants) {
//            newRCI.undoSingletonMappings();
//        }

        return newRCI;
    }

    private boolean isSubterm(Term termToSearch, Term termToSearchFor) {
        IsSubtermVisitorData data = new IsSubtermVisitorData(termToSearchFor);
        termToSearch.accept(IS_SUBTERM_VISITOR, data);
        return data.found;
    }

    public RelevantClauseInformation getConjunction(RelevantClauseInformation that) {
        RelevantClauseInformation newGAC = null;

        if (this.sentence instanceof Clause && ((Clause) this.sentence).getPosLiteralCount() == 0) {
            newGAC = that;
        }
        else if (that == null) {
            newGAC = this;
        }
        else if (that.sentence instanceof Clause && ((Clause) that.sentence).getPosLiteralCount() == 0) {
            newGAC = this;
        }
        else {
            BindingList bl = Unifier.UNIFIER.unify(this.example, that.example);

            Sentence thisRebound = this.getSentence().applyTheta(bl);
            Sentence thatRebound = that.getSentence().applyTheta(bl);

            Sentence newSentence = getStringHandler().getConnectedSentence(thisRebound, ConnectiveName.AND, thatRebound);

            Set<ElementPath> newConstantPositions = new HashSet<ElementPath>();
            for (ElementPath elementPath : this.constantPositions) {
                newConstantPositions.add(elementPath.prepend(0));
            }

            for (ElementPath elementPath : that.constantPositions) {
                newConstantPositions.add(elementPath.prepend(1));
            }

            newGAC = new RelevantClauseInformation(that.example, newSentence, this.getTypeSpecList());
            newGAC.constantPositions = newConstantPositions;
            newGAC.setConstantsSplit(this.isConstantsSplit() || that.isConstantsSplit());
            newGAC.setRelevanceFromPositiveExample(this.relevanceFromPositiveExample && that.relevanceFromPositiveExample);

            newGAC.mappings = new HashMap<Term, Term>();
            if (this.mappings != null) {
                newGAC.mappings.putAll(this.mappings);
            }
            if (that.mappings != null) {
                newGAC.mappings.putAll(that.mappings);
            }

            // Collect the output variables from each...we might want
            // to do something smarter at a latter point.
            for (Variable variable : this.getOutputVariables()) {
                newGAC.addOutputVariable((Variable) variable.applyTheta(bl));
            }

            for (Variable variable : that.getOutputVariables()) {
                newGAC.addOutputVariable((Variable) variable.applyTheta(bl));
            }
        }

        return newGAC;
    }

    public RelevantClauseInformation getDisjunction(RelevantClauseInformation that) {
        RelevantClauseInformation newGAC = null;

        if (this.sentence instanceof Clause && ((Clause) this.sentence).getPosLiteralCount() == 0) {
            newGAC = that;
        }
        else if (that == null) {
            newGAC = this;
        }
        else if (that.sentence instanceof Clause && ((Clause) that.sentence).getPosLiteralCount() == 0) {
            newGAC = this;
        }
        else {
            BindingList bl = Unifier.UNIFIER.unify(this.example, that.example);

            Sentence thisRebound = this.getSentence().applyTheta(bl);
            Sentence thatRebound = that.getSentence().applyTheta(bl);

            Sentence newSentence = getStringHandler().getConnectedSentence(thisRebound, ConnectiveName.OR, thatRebound);

            Set<ElementPath> newConstantPositions = new HashSet<ElementPath>();
            for (ElementPath elementPath : this.constantPositions) {
                newConstantPositions.add(elementPath.prepend(0));
            }

            for (ElementPath elementPath : that.constantPositions) {
                newConstantPositions.add(elementPath.prepend(1));
            }

            newGAC = new RelevantClauseInformation(that.example, newSentence, this.getTypeSpecList());
            newGAC.constantPositions = newConstantPositions;

            // Collect the output variables from each...we might want
            // to do something smarter at a latter point.
            for (Variable variable : this.getOutputVariables()) {
                newGAC.addOutputVariable((Variable) variable.applyTheta(bl));
            }

            for (Variable variable : that.getOutputVariables()) {
                newGAC.addOutputVariable((Variable) variable.applyTheta(bl));
            }

            newGAC.mappings = new HashMap<Term, Term>();
            if (this.mappings != null) {
                newGAC.mappings.putAll(this.mappings);
            }
            if (that.mappings != null) {
                newGAC.mappings.putAll(that.mappings);
            }



            newGAC.setConstantsSplit(this.isConstantsSplit() || that.isConstantsSplit());
            newGAC.setRelevanceFromPositiveExample(true);
        }

        return newGAC;
    }

    public RelevantClauseInformation getNegation() {

        Sentence newSentence;
        Set<ElementPath> newConstantPositions = new HashSet<ElementPath>();

        if (sentence instanceof ConnectedSentence && ((ConnectedSentence) sentence).getConnective() == ConnectiveName.NOT) {
            newSentence = ((ConnectedSentence) sentence).getSentenceA();

            for (ElementPath elementPath : this.constantPositions) {
                newConstantPositions.add(elementPath.removeFirstElement());
            }
        }
        else {
            newSentence = getStringHandler().getConnectedSentence(ConnectiveName.NOT, sentence);
            for (ElementPath elementPath : this.constantPositions) {
                newConstantPositions.add(elementPath.prepend(0));
            }
        }

        RelevantClauseInformation newGAC = new RelevantClauseInformation(example, newSentence, getTypeSpecList());
        newGAC.constantPositions = newConstantPositions;


        return newGAC;
    }

    public RelevantClauseInformation getNegationByFailure() {
        Sentence newSentence;
        Set<ElementPath> newConstantPositions = new HashSet<ElementPath>();
        
        if (sentence instanceof Clause && sentence.getStringHandler().isNegationByFailure((Clause) sentence)) {
            newSentence = sentence.getStringHandler().getNegationByFailureContents((Clause) sentence);
            
            for (ElementPath elementPath : this.constantPositions) {
                newConstantPositions.add(elementPath.removeFirstElement());
            }
        }
        else if (sentence instanceof Clause) {
            newSentence = sentence.getStringHandler().getNegationByFailure((Clause) sentence);
            for (ElementPath elementPath : this.constantPositions) {
                newConstantPositions.add(elementPath.prepend(0));
            }
        }
        else {
            Clause c = sentence.asClause();
            newSentence = sentence.getStringHandler().getNegationByFailure(c);
            // We can't keep track of the constant positions since the asClause() method
            // may rearrange the sentence.
        }

        RelevantClauseInformation newGAC = new RelevantClauseInformation(example, newSentence, getTypeSpecList());
        newGAC.constantPositions = newConstantPositions;

        // We purposefully ignore the output variables of the original
        // RCI.  They no longer apply once the RCI is wrapped by the
        // negation-by-failure.

        return newGAC;
    }

    public RelevantClauseInformation getInlined(HornClauseContext context, MapOfLists<PredicateNameAndArity, Clause> supportClauses) {


        Sentence newSentence = Inliner.getInlinedSentence(sentence, context, supportClauses);

        RelevantClauseInformation rci = copy();
        rci.setSentence(newSentence);

        return rci;
    }

    public RelevantClauseInformation getSimplified(HornClauseContext context, MapOfLists<PredicateNameAndArity, Clause> supportClauses) {
        Sentence newSentence = Inliner.getInlinedSentence(sentence, context, supportClauses);
        newSentence = DuplicateDeterminateRemover.removeDuplicates(newSentence);


        RelevantClauseInformation result = this;
        if (sentence.equals(newSentence) == false) {
            result = copy();
            result.setSentence(newSentence);
        }

        return result;
    }

    public RelevantClauseInformation getGroundClause() {
        BindingList bl = new BindingList();
        for (Map.Entry<Term, Term> entry : mappings.entrySet()) {
            if (entry.getValue() instanceof Variable) {
                bl.addBinding((Variable) entry.getValue(), entry.getKey());
            }
        }

        Sentence newSentence = sentence.applyTheta(bl);

        RelevantClauseInformation rci = copy();
        rci.setSentence(newSentence);

        return rci;
    }

    public RelevantClauseInformation removeDuplicateDeterminates() {


        Sentence newSentence = DuplicateDeterminateRemover.removeDuplicates(sentence);

        RelevantClauseInformation rci = copy();
        rci.setSentence(newSentence);

        return rci;
    }

    public RelevantClauseInformation removeDoubleNegations() {


        Sentence newSentence = DoubleNegationByFailureRemover.removeDoubleNegationByFailure(sentence);

        RelevantClauseInformation rci = copy();
        rci.setSentence(newSentence);

        return rci;
    }

    public RelevantClauseInformation applyPruningRules(AdviceProcessor ap) {

        RelevantClauseInformation result = this;

        if ( ap.getPruningRules() != null ) {
            ConnectedSentence implication = getImpliedSentence();
            ConnectedSentence newSentence = (ConnectedSentence)SentencePruner.pruneSentence(ap.getContext(), implication, ap.getPruningRules());

            if ( implication.equals(newSentence) == false ) {
                result = copy();
                result.setSentence(newSentence.getSentenceA());
                result.example = new Example(newSentence.getSentenceB().asClause().getPosLiteral(0));
            }
        }

        return result;
    }

    public RelevantClauseInformation getCompressed() {
        Sentence newSentence = SentenceCompressor.getCompressedSentence(sentence);

        RelevantClauseInformation rci = copy();
        rci.setSentence(newSentence);

        return rci;

    }

    public List<RelevantClauseInformation> expandNonOperationalPredicates(HornClauseContext context, MapOfLists<PredicateNameAndArity, Clause> supportClauses) {

        List<? extends Sentence> sentences = NonOperationalExpander.getExpandedSentences(context, sentence, supportClauses);

        int expansionCount = sentences.size();

        if (expansionCount > 64) {
            Utils.waitHere("Number of non-operation exapansions exceeds 64.  RCI:\n" + this + ".");
        }


        List<RelevantClauseInformation> result;

        if (sentences == null || sentences.size() == 1) {
            result = Collections.singletonList(this);
        }
        else {
            result = new ArrayList<RelevantClauseInformation>();

            for (Sentence newSentence : sentences) {
                RelevantClauseInformation newRCI = copy();
                newRCI.sentence = newSentence;
                result.add(newRCI);
            }
        }

        return result;
    }

//    public RelevantClauseInformation getDisjunction(RelevantClauseInformation that) {
//
//    }
//    public Sentence getFinalSentence() {
////        return clause;
//        if (isRelevanceFromPositiveExample()) {
//            return getSentence();
//        }
//        Clause negatedGACforNegativeByFailureArgument = getStringHandler().getClause(null, getSentence().posLiterals);
//        Literal negatedLiteral = getStringHandler().getLiteral(getStringHandler().standardPredicateNames.negationByFailure, getStringHandler().getSentenceAsTerm(negatedGACforNegativeByFailureArgument, null));
//        Clause newClause = getStringHandler().getClause(negatedLiteral, true);
//        return newClause;
//    }
    @Override
    public String toString() {
        return toString("");
    }

    public String toString(String prefix) {
        BindingList bl = null;
        //if (AllOfFOPC.renameVariablesWhenPrinting) {
        bl = new BindingList();
        // }

        PrettyPrinterOptions ppo = new PrettyPrinterOptions();
        ppo.setMaximumLiteralsPerLine(1);
        ppo.setSentenceTerminator("");
        ppo.setMaximumIndentationAfterImplication(10);
        ppo.setNewLineAfterImplication(true);

        String exampleString = PrettyPrinter.print(example, "", "", ppo, bl);
        String sentenceString = PrettyPrinter.print(sentence, prefix + "  ", prefix + "  ", ppo, bl);

        return prefix + exampleString + (isRelevanceFromPositiveExample() ? "" : ", NEGATION") + ", advice = \n" + sentenceString;

    }

    public HandleFOPCstrings getStringHandler() {
        return getSentence().getStringHandler();
    }

    public boolean isConstantsSplit() {
        return constantsSplit;
    }

    public void setConstantsSplit(boolean constantsSplit) {
        this.constantsSplit = constantsSplit;
    }

    public boolean isContainsAllAdvicePieces() {
        return containsAllAdvicePieces;
    }

    public void setContainsAllAdvicePieces(boolean containsAllAdvicePieces) {
        this.containsAllAdvicePieces = containsAllAdvicePieces;
    }

    public RelevanceStrength getOriginalRelevanceStrength() {
        return getRelevanceStrength();
    }

    public void setOriginalRelevanceStrength(RelevanceStrength relevanceStrength) {
        this.setRelevanceStrength(relevanceStrength);
    }

    public RelevanceStrength getFinalRelevanceStrength() {
        return relevanceStrength;
//        if (isConstantsSplit() == false && isContainsAllAdvicePieces() == true) {
//            if (true || isRelevanceFromPositiveExample()) {
//                return RelevanceStrength.getStrongestRelevanceStrength();
//            }
//            else {
//                return RelevanceStrength.POSSIBLE_ANSWER_NEG;
//            }
//        }
//        else if (isConstantsSplit() == true && isContainsAllAdvicePieces() == false) {
//            return RelevanceStrength.getWeakestRelevanceStrength();
//        }
//        else {
//            return RelevanceStrength.getDefaultRelevanceStrength();
//        }
    }

    public RelevantClauseInformation copy() {
        try {
            return clone();
        } catch (CloneNotSupportedException ex) {
            return null;
        }
    }

    protected RelevantClauseInformation clone() throws CloneNotSupportedException {
        RelevantClauseInformation newRCI = (RelevantClauseInformation) super.clone();
        if (newRCI.mappings != null) {
            newRCI.mappings = new HashMap<Term, Term>(this.mappings);
        }
        if (newRCI.getSentence() != null) {
            BindingList bl = null;
            newRCI.example = new Example(example.copy2(true, bl)); // JWS: if there are any things dangling off the example, we're losing them (eg, annotations).
            newRCI.setSentence(getSentence().copy2(true, bl));
        }
        return newRCI;
    }

    public Term getBackwardMappingForTerm(Term t) {
        Term result = null;

        for (Map.Entry<Term, Term> entry : mappings.entrySet()) {
            if (t == entry.getValue()) {
                Term mappedTerm = getBackwardMappingForTerm(entry.getKey());
                result = (mappedTerm == null) ? entry.getKey() : mappedTerm;
                break;
            }
        }

        return result;
    }

    @Override
    public boolean equals(Object that) {
        if (that == null) {
            return false;
        }
        if (getClass() != that.getClass()) {
            return false;
        }
        final RelevantClauseInformation other = (RelevantClauseInformation) that;
        if (this.example != other.example && (this.example == null || !this.example.equals(other.example))) {
            return false;
        }
        if (this.isRelevanceFromPositiveExample() != other.isRelevanceFromPositiveExample()) {
            return false;
        }
        if (this.getSentence() != other.getSentence() && (this.getSentence() == null || !this.sentence.equals(other.sentence))) {
            return false;
        }
        if (this.getRelevanceStrength() != other.getRelevanceStrength()) {
            return false;
        }
        if (this.getTypeSpecList() != other.getTypeSpecList() && (this.getTypeSpecList() == null || !this.typeSpecList.equals(other.typeSpecList))) {
            return false;
        }
        if (this.isConstantsSplit() != other.isConstantsSplit()) {
            return false;
        }
        if (this.isContainsAllAdvicePieces() != other.isContainsAllAdvicePieces()) {
            return false;
        }
        if (this.mappings != other.mappings && (this.mappings == null || !this.mappings.equals(other.mappings))) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        int hash = 5;
        hash = 59 * hash + (this.example != null ? this.example.hashCode() : 0);
        hash = 59 * hash + (this.isRelevanceFromPositiveExample() ? 1 : 0);
        hash = 59 * hash + (this.getSentence() != null ? this.getSentence().hashCode() : 0);
        hash = 59 * hash + (this.getRelevanceStrength() != null ? this.getRelevanceStrength().hashCode() : 0);
        hash = 59 * hash + (this.getTypeSpecList() != null ? this.getTypeSpecList().hashCode() : 0);
        hash = 59 * hash + (this.isConstantsSplit() ? 1 : 0);
        hash = 59 * hash + (this.isContainsAllAdvicePieces() ? 1 : 0);
        hash = 59 * hash + (this.mappings != null ? this.mappings.hashCode() : 0);
        return hash;
    }

    /**
     * @return the typeSpecList
     */
    public List<TypeSpec> getTypeSpecList() {
        if (typeSpecList == null) {
            List<TypeSpec> specs = example.getTypeSpecs();

            typeSpecList = new ArrayList<TypeSpec>();
            if (specs != null) {
                for (TypeSpec typeSpec : specs) {
                    TypeSpec newTypeSpec = null;
                    if (typeSpec != null) {
                        newTypeSpec = typeSpec.copy();
                    }
                    typeSpecList.add(newTypeSpec);
                }
            }
        }

        return typeSpecList;
    }

    /**
     * @param typeSpecList the typeSpecList to set
     */
    public void setTypeSpecList(List<TypeSpec> typeSpecList) {
        this.typeSpecList = typeSpecList;
    }

    public boolean isEquivalentUptoVariableRenaming(RelevantInformation ri) {
        if (ri instanceof RelevantClauseInformation) {
            RelevantClauseInformation that = (RelevantClauseInformation) ri;
            Sentence c1 = this.getImpliedSentence();
            Sentence c2 = that.getImpliedSentence();
            return c1.isEquivalentUptoVariableRenaming(c2);
        }
        else {
            return false;
        }

    }

    public boolean subsumes(RelevantInformation ri) {
        if (ri instanceof RelevantClauseInformation) {
            RelevantClauseInformation that = (RelevantClauseInformation) ri;
            Sentence c1 = this.getImpliedSentence();
            Sentence c2 = that.getImpliedSentence();

            BindingList bl1 = Unifier.UNIFIER.unify(c1, c2);

            if (bl1 == null) {
                return false;
            }

            Sentence c3 = c2.applyTheta(bl1);

            return c2.isEquivalentUptoVariableRenaming(c3);

        }
        else {
            return false;
        }
    }

    /** Undoes the constant to variable replacement for constant that only occurred a single time in body.
     *
     * If a constant only occurred once in the relevance body and never in the relevance example,
     * this method will undo the generalization to a variable.
     */
    public void undoSingletonMappings() {
        for (Term term : mappings.values()) {
            Variable var = (Variable) term;
            int exampleOccuranceCount = example.countVarOccurrencesInFOPC(var);
            if (exampleOccuranceCount == 0) {
                int bodyOccuranceCount = getSentence().countVarOccurrencesInFOPC(var);
                if (bodyOccuranceCount == 1) {
                    Term t = getBackwardMappingForTerm(var);
                    setSentence(getSentence().applyTheta(Collections.singletonMap(var, t)));
                    //System.out.println("Undoing mapping from " + t + " to " + var.getName() + ".");
                }
            }
        }
    }

    /**
     * @return the relevanceFromPositiveExample
     */
    public boolean isRelevanceFromPositiveExample() {
        return relevanceFromPositiveExample;
    }

    /**
     * @param relevanceFromPositiveExample the relevanceFromPositiveExample to set
     */
    public void setRelevanceFromPositiveExample(boolean relevanceFromPositiveExample) {
        this.relevanceFromPositiveExample = relevanceFromPositiveExample;
    }

    /**
     * @return the relevanceStrength
     */
    public RelevanceStrength getRelevanceStrength() {
        return relevanceStrength;
    }

    /**
     * @param relevanceStrength the relevanceStrength to set
     */
    public void setRelevanceStrength(RelevanceStrength relevanceStrength) {
        this.relevanceStrength = relevanceStrength;
    }

    @Override
    public boolean prove(HornClauseContext context) {

        Map<Term, Term> termToVariableMap = new LinkedHashMap<Term, Term>();

        Literal newExample = GENERALIZER_SENTENCE_VISITOR.generalize(example, null, termToVariableMap);
        Sentence newSentence = GENERALIZER_SENTENCE_VISITOR.generalize(getSentence(), constantPositions, termToVariableMap);

        BindingList bl = new BindingList();
        Unifier.UNIFIER.unify(example, newExample, bl);
        newSentence = newSentence.applyTheta(bl);

        List<Clause> clauses = newSentence.convertToClausalForm();

        boolean result = false;

        for (Clause clause : clauses) {
            if (context.prove(clause) != null) {
                result = true;
                break;
            }
        }

        return result;
    }

//    public void replacePositiveTerm(TermPosition position, Term newTerm) {
//        Literal lit = getSentence().getPosLiteral(position.literalPosition);
//
//        Variable v = (Variable) lit.getArgument(position.termPosition);
//
//        lit.setArgument(position.termPosition, newTerm);
//        mappings.put(v, newTerm);
//    }
    private void markConstants() {
        ConstantMarkerRemover sv = new ConstantMarkerRemover();
        ConstantMarkerData data = new ConstantMarkerData();

        setSentence((Clause) getSentence().accept(sv, data));
        constantPositions = data.constantPositions;
        //System.out.println("TAKE ME OUT");
    }

    public boolean isValidAdvice(AdviceProcessor ap) {

        Set<PredicateNameAndArity> usedPredicate = PredicateCollector.collectPredicates(sentence, ap.getContext());

        if ( ap.isVerifyAllPredicateExist() ) {
            for (PredicateNameAndArity pnaa : usedPredicate) {
                // We want to check that all predicates that are used are defined in the clausebase.
                // However, if it is a non-operational, we assume the operationals are defined somewhere.
                if (pnaa.isNonOperational() == false && ap.getContext().getClausebase().isDefined(pnaa) == false && pnaa.getPredicateName().name.startsWith("linked") == false) {
                    Utils.waitHere("Unknown predicate name in advice: " + pnaa + ".");
                	return false;
                }
            }
        }

        if (ap.isVerifyInputsToFunctionsAsPredAreBoundEnabled()) {
            // Look for Singleton variables that occur as inputs to Functions...

            Sentence s = getImpliedSentence();

            Collection<Variable> headVariables = example.collectAllVariables();


            Map<Variable, Integer> counts = VariableCounter.countVariables(sentence);

            PositionData positions = null;


            for (Map.Entry<Variable, Integer> entry : counts.entrySet()) {
                if (entry.getValue() == 1) {
                    // Here is a singleton.  See if it is an argument to a functionAsPred.

                    // What we are going to do here is look up the position of the
                    // variable in the sentence.  Once we have the position, we will
                    // grap the variables "parent", i.e., the literal or function that
                    // is using it.  Once we have the literal/function, we will first
                    // check if it is a FunctionAsPred.  If it is, we will check if
                    // the singleton variable is in the output position.  If it isn't,
                    // we will assume that the advice was improperly bound and toss it.
                    Variable v = entry.getKey();

                    if (headVariables.contains(v) == false) {

                        if (positions == null) {
                            positions = new PositionData();
                            ElementPositionVisitor<PositionData> epv = new ElementPositionVisitor<PositionData>(new PositionRecorder());
                            s.accept(epv, positions);
                        }

                        ElementPath path = positions.elementToPathMap.getValue(v, 0);

                        ElementPath parentPath = path.getParent();

                        AllOfFOPC parent = positions.pathToElementMap.get(parentPath);

                        if (parent instanceof LiteralOrFunction) {
                            LiteralOrFunction literalOrFunction = (LiteralOrFunction) parent;
                            PredicateName pn = literalOrFunction.getPredicateName();

                            if (pn.isDeterminateOrFunctionAsPred(literalOrFunction.getArity())) {
                                // Damn output indices count from 1!!!!
                                if (pn.getDeterminateOrFunctionAsPredOutputIndex(literalOrFunction.getArity()) - 1 != path.getIndex() && literalOrFunction.getPredicateName().name.equals("ilField_Composite_name") == false) {
                                    // The ilField_Composite_name is a total hack for the BL project.  ilField_Composite_name is a function, but it is one
                                    // in which can either translate from argument 1 to 2 as in: ilField_Composite_name(world, nonSymbol, ?Symbol, state),
                                    // or translate from argument 2 to 1: ilField_Composite_name(world, nonSymbol, ?Symbol, state).
                                    // Thus, either argument could be unbound.  We really need a pruning rule for this, but
                                    // until I get around to writing pruning for the AdviceProcessor, I think I will just hack this up.
                                	Utils.waitHere("isVerifyInputsToFunctionsAsPredAreBoundEnabled caused invalid advice: " + pn + ".");
                                    return false;
                                }
                            }
                        }
                    }
                }
            }
        }

        return true;
    }

    /**
     * @param clause the clause to set
     */
    public void setSentence(Sentence sentence) {
        this.sentence = sentence;
    }

    public boolean addOutputVariable(Variable e) {
        if (outputVariables == null) {
            outputVariables = new HashSet<Variable>();
        }

        return outputVariables.add(e);
    }

    public Set<Variable> getOutputVariables() {
        if (outputVariables == null) {
            return Collections.EMPTY_SET;
        }
        else {
            return outputVariables;
        }
    }

    public static class ConstantMarkerData {

        ElementPath currentPosition = new ElementPath(0);

        Set<ElementPath> constantPositions;

        public ConstantMarkerData() {
            this(null);
        }

        public ConstantMarkerData(Set<ElementPath> constantPositions) {
            if (constantPositions == null) {
                constantPositions = new HashSet<ElementPath>();
            }
            this.constantPositions = constantPositions;
        }

        public void markCurrentPositionAsConstant() {
            constantPositions.add(currentPosition);
        }

        public ElementPath getCurrentPosition() {
            return currentPosition;
        }

        public boolean isMarkedConstant() {
            return constantPositions.contains(currentPosition);
        }

        @Override
        public String toString() {
            return "GeneralizerData{" + "\n  currentPosition=" + currentPosition + "\n  constantPositions=" + constantPositions + "\n}";
        }
    }

    public static class GeneralizerData extends ConstantMarkerData {

        Map<Term, Term> currentMappings;

        public GeneralizerData(Set<ElementPath> constantPositions, Map<Term, Term> currentMappings) {
            super(constantPositions);
            this.currentMappings = currentMappings;
        }

        public GeneralizerData(Map<Term, Term> currentMappings) {
            if (currentMappings == null) {
                currentMappings = new HashMap<Term, Term>();
            }
            this.currentMappings = currentMappings;
        }

        public boolean isCurrentPositionConstant() {
            return constantPositions != null && constantPositions.contains(getCurrentPosition());
        }

        @Override
        public String toString() {
            return "GeneralizerData{" + "\n  currentPosition=" + currentPosition + "\n  constantPositions=" + constantPositions + "\n  currentMappings=" + currentMappings + "\n}";
        }
    }

    public static class ConstantMarkerRemover extends DefaultFOPCVisitor<ConstantMarkerData> {

        public ConstantMarkerRemover() {
        }

        public Clause visitClause(Clause clause, ConstantMarkerData data) {
            List<Literal> positiveLits = null;
            List<Literal> negativeLits = null;

            ElementPath oldPath = null;
            if (data != null) {
                oldPath = data.currentPosition;
            }

            if (clause.getPosLiteralCount() > 0) {
                positiveLits = new ArrayList<Literal>();
                for (int i = 0; i < clause.getPosLiteralCount(); i++) {
                    Literal literal = clause.getPosLiteral(i);
                    if (data != null) {
                        data.currentPosition = new ElementPath(oldPath, i);
                    }
                    Literal newLit = (Literal) literal.accept(this, data);
                    positiveLits.add(newLit);
                }
            }

            if (clause.getNegLiteralCount() > 0) {
                negativeLits = new ArrayList<Literal>();
                for (int i = 0; i < clause.getNegLiteralCount(); i++) {
                    Literal literal = clause.getNegLiteral(i);
                    if (data != null) {
                        data.currentPosition = new ElementPath(oldPath, -1 * i);
                    }
                    Literal newLit = (Literal) literal.accept(this, data);
                    negativeLits.add(newLit);
                }
            }

            if (data != null) {
                data.currentPosition = oldPath;
            }

            return clause.getStringHandler().getClause(positiveLits, negativeLits);
        }

        public Literal visitLiteral(Literal literal, ConstantMarkerData data) {

            Literal result = processTermsOfLOT(literal, data);

            return result;
        }

        @Override
        public Term visitFunction(Function function, ConstantMarkerData data) {
            Term result = getConstantTerm(function, data);

            if (result == null) {
                result = processTermsOfLOT(function, data).asFunction();
            }

            return result;
        }

        /** If this is a constant marker, return the constant, otherwise returns null.
         * 
         * @param literalOrFunction
         * @param data
         * @return
         */
        private Term getConstantTerm(LiteralOrFunction literalOrFunction, ConstantMarkerData data) {

            PredicateName marker = literalOrFunction.getStringHandler().getPredicateName("constant");

            Term result = null;

            if (literalOrFunction.getPredicateName().equals(marker) && literalOrFunction.getArity() == 1) {

                data.markCurrentPositionAsConstant();

                result = literalOrFunction.getArgument(0);
            }

            return result;
        }

        private Literal processTermsOfLOT(LiteralOrFunction literal, ConstantMarkerData data) {
            Literal result = literal.asLiteral();

            if (literal.getArity() != 0) {
                List<Term> newTerms = null;

                ElementPath oldPath = null;
                if (data != null) {
                    oldPath = data.currentPosition;
                }

                newTerms = new ArrayList<Term>();
                for (int i = 0; i < literal.getArity(); i++) {
                    Term term = literal.getArgument(i);
                    if (data != null) {
                        data.currentPosition = new ElementPath(oldPath, i);
                    }
                    Term newTerm = term.accept(this, data);
                    newTerms.add(newTerm);
                }

                if (data != null) {
                    data.currentPosition = oldPath;
                }

                result = literal.getStringHandler().getLiteral(literal.asLiteral(), newTerms);
            }

            return result;
        }
    }

    public static class ConstantMarkerAdderSV extends DefaultSentenceVisitor<ConstantMarkerData> {

        public ConstantMarkerAdderSV() {
            ConstantMarkerAdderTV termVisitor = new ConstantMarkerAdderTV(this);
            setTermVisitor(termVisitor);
        }

        public Clause visitClause(Clause clause, ConstantMarkerData data) {
            List<Literal> positiveLits = null;
            List<Literal> negativeLits = null;

            ElementPath oldPath = null;
            if (data != null) {
                oldPath = data.currentPosition;
            }

            if (clause.getPosLiteralCount() > 0) {
                positiveLits = new ArrayList<Literal>();
                for (int i = 0; i < clause.getPosLiteralCount(); i++) {
                    Literal literal = clause.getPosLiteral(i);
                    if (data != null) {
                        data.currentPosition = new ElementPath(oldPath, i);
                    }
                    Literal newLit = (Literal) literal.accept(this, data);
                    positiveLits.add(newLit);
                }
            }

            if (clause.getNegLiteralCount() > 0) {
                negativeLits = new ArrayList<Literal>();
                for (int i = 0; i < clause.getNegLiteralCount(); i++) {
                    Literal literal = clause.getNegLiteral(i);
                    if (data != null) {
                        data.currentPosition = new ElementPath(oldPath, -1 * i);
                    }
                    Literal newLit = (Literal) literal.accept(this, data);
                    negativeLits.add(newLit);
                }
            }

            if (data != null) {
                data.currentPosition = oldPath;
            }

            return clause.getStringHandler().getClause(positiveLits, negativeLits);
        }

        public Literal visitLiteral(Literal literal, ConstantMarkerData data) {

            Literal result = literal;



            if (literal.getArity() != 0) {
                List<Term> newTerms = null;

                ElementPath oldPath = null;
                if (data != null) {
                    oldPath = data.currentPosition;
                }

                newTerms = new ArrayList<Term>();
                for (int i = 0; i < literal.getArity(); i++) {
                    Term term = literal.getArgument(i);
                    if (data != null) {
                        data.currentPosition = new ElementPath(oldPath, i);
                    }
                    Term newTerm = term.accept(getTermVisitor(), data);
                    newTerms.add(newTerm);
                }

                if (data != null) {
                    data.currentPosition = oldPath;
                }

                result = literal.getStringHandler().getLiteral(literal, newTerms);
            }


            return result;
        }
    }

    public static class ConstantMarkerAdderTV extends DefaultTermVisitor<ConstantMarkerData> {

        public ConstantMarkerAdderTV(SentenceVisitor<Sentence, ConstantMarkerData> sentenceVisitor) {
            super(sentenceVisitor);
        }

        @Override
        public Term visitFunction(Function function, ConstantMarkerData data) {
            return wrapTermInConstantMarker(function, data);
        }

        @Override
        public Term visitNumericConstant(NumericConstant numericConstant, ConstantMarkerData data) {
            return wrapTermInConstantMarker(numericConstant, data);
        }

        @Override
        public Term visitOtherConstant(Constant constant, ConstantMarkerData data) {
            return wrapTermInConstantMarker(constant, data);
        }

        @Override
        public Term visitStringConstant(StringConstant stringConstant, ConstantMarkerData data) {
            return wrapTermInConstantMarker(stringConstant, data);
        }

        private Term wrapTermInConstantMarker(Term term, ConstantMarkerData data) {

            Term result = term;

            if (data.isMarkedConstant()) {
                FunctionName marker = term.getStringHandler().getFunctionName("constant");
                Function c = term.getStringHandler().getFunction(marker, Collections.singletonList(term), null);

                result = c;
            }

            return result;
        }
    }

    public static class GeneralizerData2 extends ElementPositionData {

        Set<ElementPath> constantPositions;

        Map<Term, Term> currentMappings;

        public GeneralizerData2(Set<ElementPath> constantPositions, Map<Term, Term> currentMappings) {
            this.constantPositions = constantPositions;
            this.currentMappings = currentMappings;
        }

        public boolean isCurrentPositionConstant() {
            return constantPositions != null && constantPositions.contains(getCurrentPosition());
        }

        @Override
        public String toString() {
            return "GeneralizerData{" + "\n  currentPosition=" + currentPosition + "\n  constantPositions=" + constantPositions + "\n  currentMappings=" + currentMappings + "\n}";
        }
    }

    public static class SentenceGeneralizer {

        public SentenceGeneralizer() {
        }

        public <T extends Sentence> T generalize(T clause, Set<ElementPath> constantPositions, Map<Term, Term> mappings) {
            GeneralizerData2 data = new GeneralizerData2(constantPositions, mappings);

            return (T) clause.accept(SENTENCE_GENERALIZER_VISITOR, data);
        }
    }

    private static class SentenceGeneralizerVisitor extends ElementPositionVisitor<GeneralizerData2> {

        @Override
        public Term visitFunction(Function function, GeneralizerData2 data) {
            Term newTerm = function;

            if (data.isCurrentPositionConstant() == false) {
                Term mappedVariable = null;
                if ((mappedVariable = data.currentMappings.get(function)) != null) {
                    newTerm = mappedVariable;
                }
                else if (function.functionName.name.startsWith("linked") && function.getArity() == 1) {
                    mappedVariable = function.getStringHandler().getNewUnamedVariable();
                    data.currentMappings.put(function, mappedVariable);
                    newTerm = mappedVariable;
                }
                else {
                    newTerm = super.visitFunction(function, data);
                }
            }

            return newTerm;
        }

        @Override
        public Term visitConsCell(ConsCell consCell, GeneralizerData2 data) {
            // Here we are going to generalize any given list as a single variable.
            // This probably won't work when if there is important structure in the
            // the list it's self.
            Term newTerm = consCell;
            if (data.isCurrentPositionConstant() == false) {
                Term mappedVariable = null;
                if ((mappedVariable = data.currentMappings.get(consCell)) != null) {
                    newTerm = mappedVariable;
                }
                else {
                    mappedVariable = consCell.getStringHandler().getNewUnamedVariable();
                    data.currentMappings.put(consCell, mappedVariable);
                    newTerm = mappedVariable;
                }
            }

            return newTerm;
        }

        @Override
        public Term visitNumericConstant(NumericConstant term, GeneralizerData2 data) {
            return handleConstant(term, data);
        }

        @Override
        public Term visitOtherConstant(Constant term, GeneralizerData2 data) {
            return handleConstant(term, data);
        }

        @Override
        public Term visitOtherTerm(Term term, GeneralizerData2 data) {
            return handleNonConstant(term, data);
        }

        @Override
        public Term visitStringConstant(StringConstant term, GeneralizerData2 data) {
            return handleConstant(term, data);
        }

        @Override
        public Term visitVariable(Variable term, GeneralizerData2 data) {

            return handleNonConstant(term, data);
        }

        private Term handleNonConstant(Term term, GeneralizerData2 data) {
            Term newTerm = term;
            Term mappedVariable = null;
            if ((mappedVariable = data.currentMappings.get(term)) != null) {
                newTerm = mappedVariable;
            }
            return newTerm;
        }

        private Term handleConstant(Constant term, GeneralizerData2 data) {
            Term newTerm = term;

            if (data.isCurrentPositionConstant() == false) {
                Term mappedVariable = null;
                if ((mappedVariable = data.currentMappings.get(term)) != null) {
                    newTerm = mappedVariable;
                }
                else {
                    mappedVariable = term.getStringHandler().getNewUnamedVariable();
                    data.currentMappings.put(term, mappedVariable);
                    newTerm = mappedVariable;
                }
            }

            return newTerm;
        }
    }

    public static class GeneralizerSentenceVisitor extends DefaultSentenceVisitor<GeneralizerData> {

        public GeneralizerSentenceVisitor() {
            GeneralizerTV termVisitor = new GeneralizerTV(this);
            setTermVisitor(termVisitor);
        }

        public <T extends Sentence> T generalize(T clause, Set<ElementPath> constantPositions, Map<Term, Term> mappings) {
            GeneralizerData data = new GeneralizerData(constantPositions, mappings);

            return (T) clause.accept(this, data);
        }

        public Clause visitClause(Clause clause, GeneralizerData data) {
            List<Literal> positiveLits = null;
            List<Literal> negativeLits = null;

            ElementPath oldPath = null;
            if (data != null) {
                oldPath = data.currentPosition;
            }

            if (clause.getPosLiteralCount() > 0) {
                positiveLits = new ArrayList<Literal>();
                for (int i = 0; i < clause.getPosLiteralCount(); i++) {
                    Literal literal = clause.getPosLiteral(i);
                    if (data != null) {
                        data.currentPosition = new ElementPath(oldPath, i);
                    }
                    Literal newLit = (Literal) literal.accept(this, data);
                    positiveLits.add(newLit);
                }
            }

            if (clause.getNegLiteralCount() > 0) {
                negativeLits = new ArrayList<Literal>();
                for (int i = 0; i < clause.getNegLiteralCount(); i++) {
                    Literal literal = clause.getNegLiteral(i);
                    if (data != null) {
                        data.currentPosition = new ElementPath(oldPath, -1 * i);
                    }
                    Literal newLit = (Literal) literal.accept(this, data);
                    negativeLits.add(newLit);
                }
            }

            if (data != null) {
                data.currentPosition = oldPath;
            }

            return clause.getStringHandler().getClause(positiveLits, negativeLits);
        }

        public Literal visitLiteral(Literal literal, GeneralizerData data) {

            Literal result = literal;

            if (literal.getArity() != 0) {
                List<Term> newTerms = null;

                ElementPath oldPath = null;
                if (data != null) {
                    oldPath = data.currentPosition;
                }

                newTerms = new ArrayList<Term>();
                for (int i = 0; i < literal.getArity(); i++) {
                    Term term = literal.getArgument(i);
                    if (data != null) {
                        data.currentPosition = new ElementPath(oldPath, i);
                    }
                    Term newTerm = term.accept(getTermVisitor(), data);
                    newTerms.add(newTerm);
                }

                if (data != null) {
                    data.currentPosition = oldPath;
                }

                result = literal.getStringHandler().getLiteral(literal, newTerms);
            }


            return result;
        }
    }

    public static class GeneralizerTV extends DefaultTermVisitor<GeneralizerData> {

        public GeneralizerTV(SentenceVisitor<Sentence, GeneralizerData> sentenceVisitor) {
            super(sentenceVisitor);
        }

        @Override
        public Term visitFunction(Function function, GeneralizerData data) {
            Term newTerm = function;

            if (data.isCurrentPositionConstant() == false) {
                Term mappedVariable = null;
                if ((mappedVariable = data.currentMappings.get(function)) != null) {
                    newTerm = mappedVariable;
                }
                else if (function.functionName.name.startsWith("f") && function.getArity() == 1) {
                    mappedVariable = function.getStringHandler().getNewUnamedVariable();
                    data.currentMappings.put(function, mappedVariable);
                    newTerm = mappedVariable;
                }
                else {
                    ElementPath oldPath = null;
                    oldPath = data.currentPosition;


                    List<Term> newArguments = new ArrayList<Term>();
                    for (int i = 0; i < function.getArity(); i++) {

                        data.currentPosition = new ElementPath(oldPath, -1 * i);

                        Term term1 = function.getArgument(i);
                        newArguments.add(term1.accept(this, data));
                    }

                    data.currentPosition = oldPath;

                    newTerm = function.getStringHandler().getFunction(function, newArguments);
                }
            }

            return newTerm;
        }

        @Override
        public Term visitNumericConstant(NumericConstant term, GeneralizerData data) {
            return handleConstant(term, data);
        }

        @Override
        public Term visitOtherConstant(Constant term, GeneralizerData data) {
            return handleConstant(term, data);
        }

        @Override
        public Term visitOtherTerm(Term term, GeneralizerData data) {
            return handleNonConstant(term, data);
        }

        @Override
        public Term visitStringConstant(StringConstant term, GeneralizerData data) {
            return handleConstant(term, data);
        }

        @Override
        public Term visitVariable(Variable term, GeneralizerData data) {

            return handleNonConstant(term, data);
        }

        private Term handleNonConstant(Term term, GeneralizerData data) {
            Term newTerm = term;
            Term mappedVariable = null;
            if ((mappedVariable = data.currentMappings.get(term)) != null) {
                newTerm = mappedVariable;
            }
            return newTerm;
        }

        private Term handleConstant(Constant term, GeneralizerData data) {
            Term newTerm = term;

            if (data.isCurrentPositionConstant() == false) {
                Term mappedVariable = null;
                if ((mappedVariable = data.currentMappings.get(term)) != null) {
                    newTerm = mappedVariable;
                }
                else {
                    mappedVariable = term.getStringHandler().getNewUnamedVariable();
                    data.currentMappings.put(term, mappedVariable);
                    newTerm = mappedVariable;
                }
            }

            return newTerm;
        }
    }

    public static class IsSubtermVisitorData {

        boolean found = false;

        Term termToSearchFor;

        public IsSubtermVisitorData(Term termToSearchFor) {
            this.termToSearchFor = termToSearchFor;
        }
    }

    public static class IsSubtermVisitor extends DefaultTermVisitor<IsSubtermVisitorData> {

        @Override
        public Term visitFunction(Function function, IsSubtermVisitorData data) {
            if (function.equals(data.termToSearchFor)) {
                data.found = true;
            }

            return super.visitFunction(function, data);
        }

        @Override
        public Term visitConsCell(ConsCell consCell, IsSubtermVisitorData data) {
            if (consCell.equals(data.termToSearchFor)) {
                data.found = true;
            }

            return super.visitConsCell(consCell, data);
        }

        @Override
        public Term visitStringConstant(StringConstant stringConstant, IsSubtermVisitorData data) {
            if (stringConstant.equals(data.termToSearchFor)) {
                data.found = true;
            }

            return super.visitStringConstant(stringConstant, data);
        }

        @Override
        public Term visitNumericConstant(NumericConstant numericConstant, IsSubtermVisitorData data) {
            if (numericConstant.equals(data.termToSearchFor)) {
                data.found = true;
            }

            return super.visitNumericConstant(numericConstant, data);
        }
    }

    public static class PositionData extends ElementPositionData {

        Map<ElementPath, AllOfFOPC> pathToElementMap = new HashMap<ElementPath, AllOfFOPC>();

        MapOfLists<AllOfFOPC, ElementPath> elementToPathMap = new MapOfLists<AllOfFOPC, ElementPath>();

    }

    public static class PositionRecorder implements ElementPositionListener<PositionData> {

        public boolean visiting(Sentence s, PositionData data) {
            data.pathToElementMap.put(data.getCurrentPosition(), s);
            data.elementToPathMap.add(s, data.getCurrentPosition());
            return true;
        }

        public boolean visiting(Term t, PositionData data) {
            data.pathToElementMap.put(data.getCurrentPosition(), t);
            data.elementToPathMap.add(t, data.getCurrentPosition());
            return true;
        }
    }
}
