/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.AllOfFOPC;
import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.visitors.DefaultSentenceVisitor;
import edu.wisc.cs.will.FOPC.visitors.DefaultTermVisitor;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings.VarIndicator;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.PredicateSpec;
import edu.wisc.cs.will.FOPC.PredicateSpec.TypeModeAndSignature;
import edu.wisc.cs.will.FOPC.PrettyPrinter;
import edu.wisc.cs.will.FOPC.PrettyPrinterOptions;
import edu.wisc.cs.will.FOPC.Pruner;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.StringConstant;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Type;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.ResThmProver.DefaultProof;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.ResThmProver.Proof;
import edu.wisc.cs.will.Utils.LinkedMapOfSets;
import edu.wisc.cs.will.Utils.MapOfSets;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.BestFirstSearch;
import java.io.FileNotFoundException;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 *
 * set(check_useless,+V)
 *    V is one of: true or false (default false). If set to true, removes literals in
 *    the bottom clause that do not contribute to establishing variable chains to output
 *    variables in the positive literal, or produce output variables that are not used by
 *    any other literal in the bottom clause.
 *
 * set(clauselength,+V)
 *    V is a positive integer (default 4). Sets upper bound on number of literals in an acceptable clause.
 *
 * set(i,+V)
 *    V is a positive integer (default 2). Set upper bound on layers of new variables.
 *
 * @author twalker
 */
public class BottomClauseUnused {

    protected static final boolean useRenamedVarsForPrinting = false;

    LearnOneClause learnOneClause;

    HornClauseContext context;

    Example example;

    int maximumVariableLayers = 4;

    int maximumClauseLength = 2;

    ModeToVariableSV modeVisitor = new ModeToVariableSV();

    Set<PredicateNameAndArity> excludedModes = null;

    public BottomClauseUnused(LearnOneClause learnOneClause, Example example) {
        this.learnOneClause = learnOneClause;
        this.example = example;
        this.context = learnOneClause.getContext();
    }

    public void generate() {
        System.out.println("\n\n\n");

        MapOfSets<PredicateNameAndArity, ModeInfo> allModes = collectAllModes();

        List<Node> seedNodes = expandSeed(allModes);

        LinkedList<Node> openList = new LinkedList<Node>(seedNodes);

        LinkedList<Node> allNodes = new LinkedList<Node>();

        while (openList.isEmpty() == false) {
            LinkedList<Node> newOpenNodes = new LinkedList<Node>();
            LinkedList<Node> allNewNodes = new LinkedList<Node>();
            Node firstNode = openList.pop();

            if (canExpandNode(firstNode)) {
                expandNode(firstNode, allModes, newOpenNodes, allNewNodes);

                openList.addAll(newOpenNodes);
                allNodes.addAll(allNewNodes);
            }
        }

        for (Node node : allNodes) {
            System.out.println(node.toModesString(node.getPath()));
            System.out.println(node.toLiteralsString(node.getPath()));
        }

        for (Node node : allNodes) {
            System.out.println(node.literal + " depth = " + node.getNodeVariableDepth());
        }
    }

    private LinkedList<Node> expandSeed(MapOfSets<PredicateNameAndArity, ModeInfo> allModes) {
        LinkedList<Node> newNodes = new LinkedList<Node>();

        Set<ModeInfo> seedModes = allModes.getValues(example.getPredicateNameAndArity());

        if (seedModes.isEmpty()) {
            throw new IllegalStateException("Target predicate " + example.getPredicateNameAndArity() + " must have at least one mode.");
        }

        for (ModeInfo modeInfo : seedModes) {
            BindingList printBindingList = new BindingList();
            System.out.println(modeInfo.toString(printBindingList));
            // This is the seed, so just need to unify modeLiteral and example
            BindingList bl = Unifier.UNIFIER.unify(modeInfo.variablizedMode, example);
            if (bl != null) {
                System.out.println(bl.toString(printBindingList));
                Node node = new Node(example, modeInfo, bl);
                newNodes.add(node);
                System.out.println(node);
            }
            else {
                System.out.println("Warning: Example " + example + " did bind to mode " + modeInfo.variablizedMode + ".");
            }
        }

        return newNodes;
    }

    private void expandNode(Node nodeToExpand, MapOfSets<PredicateNameAndArity, ModeInfo> allModes, LinkedList<Node> newOpenNodes, LinkedList<Node> allNewNodes) {

        System.out.println("Extending: " + nodeToExpand + "\n");

        for (Set<ModeInfo> modeSet : allModes.values()) {
            for (ModeInfo modeInfo : modeSet) {
                if (modeInfo.variablizedMode.getPredicateNameAndArity().equals(example.getPredicateNameAndArity()) == false) {
                    expandNodeViaMode(nodeToExpand, modeInfo, newOpenNodes, allNewNodes);
                }
            }
        }
    }

    private void expandNodeViaMode(Node nodeToExpand, ModeInfo modeInfo, LinkedList<Node> newOpenNodes, LinkedList<Node> allNewNodes) {

        Map<Variable, TypeSpec> aMap = new HashMap<Variable, TypeSpec>(modeInfo.variableToTypeMap);

        List<PossibleBinding> possibleBindings = expandBindings(nodeToExpand, aMap);

        if (possibleBindings != null) {
            for (PossibleBinding pb : possibleBindings) {
                proveBindings(nodeToExpand, modeInfo, pb, newOpenNodes, allNewNodes);
            }
        }
    }

    private void proveBindings(Node nodeToExpand, ModeInfo modeInfo, PossibleBinding pb, LinkedList<Node> newOpenNodes, LinkedList<Node> allNewNodes) {

        // This is some crappy code.
        //
        // We get a variablize mode, in terms a variable set 1.
        // The possible bindings are also in terms of variable set 1.
        //
        // However, we want to maintain a canonical mapping of variables
        // with a string of nodes.  Essentially, we need to be using
        // the variable set 2 (the one existing in node to expand.
        //
        // For example:
        //
        // nodeToExample:    p(_1).  ( _1 is from variable set 2)
        // modeInfo:         q(_3).  ( _3 is from variable set 2)
        // possibleBinding:  _3 -> {_1:someValue} .
        //
        // What we need from that is:
        //
        // modeInfo:         q(_1).  ( _3 was mapped to _1 )

        // In order to accomplish this, we rebind all the variables
        // in the mode info.
        BindingList varToVarBindings = pb.getVariableToVariableBindings();
        ModeInfo reboundMode = modeInfo.rebind(varToVarBindings);
        BindingList varToTermBindings = pb.getVariableToTermBindings();

        if (nodeToExpand.isPossibleBindingAllowed(reboundMode, varToTermBindings)) {

            // Now we create the new term.  Here we have to be careful.
            // PossibleBinding.getVariableToTermBindings() return bindings
            // from variable set 2 to ground terms.  Since modeInfo is in
            // terms of set 1 and reboundMode is in terms of set 2, we want
            // to work with reboundMode from now on.


            Literal newLiteral = reboundMode.variablizedMode.applyTheta(varToTermBindings);
            List<Literal> literals = nodeToExpand.getLiterals();
            literals.add(newLiteral);

            Clause fullClause = context.getStringHandler().getClause(literals, true);
            Proof p = new DefaultProof(context, fullClause);

            BindingList proofBindings = null;
            while ((proofBindings = p.prove()) != null) {

                Literal boundNewLiteral = newLiteral.applyTheta(proofBindings);
                BindingList proofToModeBinding = Unifier.UNIFIER.unify(boundNewLiteral, reboundMode.variablizedMode);

                if (nodeToExpand.isNewLiteralAllowed(nodeToExpand, reboundMode, varToTermBindings, boundNewLiteral)) {

                    Node newNode = new Node(nodeToExpand, boundNewLiteral, reboundMode, proofToModeBinding);

                    if (pruneNode(newNode) == false) {
                        allNewNodes.add(newNode);

                        if (newNode.outputs == null) {
                            newOpenNodes.add(newNode);
                        }

                        System.out.println("New Node: " + newNode + ".\n");
                    }
                }
            }
        }

    }

    private Set<VariableInfo[]> getVariableInfoForLiteral(PredicateNameAndArity predicate, Set<VariableInfo> variableInfos) {

        for (int i = 0; i < predicate.getArity(); i++) {
            System.out.println("Types: " + predicate.getTypes() + ".");
        }

        for (PredicateSpec predicateSpec : predicate.getPredicateSpecs()) {
            System.out.println(predicateSpec.getTypeModeAndSignatureList());

            List<Literal> eligibleLiterals = getEligibleLiterals(predicate, predicateSpec.getTypeModeAndSignatureList(), variableInfos);
        }


        return null;
    }

    private List<Literal> getEligibleLiterals(PredicateNameAndArity predicate, List<TypeModeAndSignature> typeSpecAndSignatures, Set<VariableInfo> variableInfos) {

        // Generate all of the current eligible expansions of the predicate and typeSpec.

//        boolean eligible = true;
//        List<Literal> result = Collections.EMPTY_LIST;
//
//        List<List<VariableInfo>> allVariableInfos = new ArrayList<List<VariableInfo>>();
//        for (TypeModeAndSignature typeSpecAndSignature : typeSpecAndSignatures) {
//            List<VariableInfo> variableInfoForSingleArgument = getMatchingVariableInfo(typeSpecAndSignature.signature, typeSpecAndSignature.typeSpec, variableInfos);
//
//            if (variableInfoForSingleArgument.isEmpty()) {
//                eligible = false;
//                break;
//            }
//
//            allVariableInfos.add(variableInfoForSingleArgument);
//
//        }
//
//        if (eligible) {
//            List<List<VariableInfo>> combinations = Utils.getCombinations(allVariableInfos);
//
//
//        }

        return null;
    }

    private Set<Literal> getModes(Literal example) {
        Set<Literal> modes = new HashSet<Literal>();

        VarIndicator oldValue = context.getStringHandler().getVariableIndicatorNoSideEffects();
        Literal modeProofLiteral = context.getFileParser().parseLiteral("mode(X)");
        Variable xVar = (Variable) modeProofLiteral.getArgument(0);

        Proof modeProof = new DefaultProof(context, modeProofLiteral);
        BindingList bl = null;
        while ((bl = modeProof.prove()) != null) {
            Term mode = bl.getMapping(xVar);
            if (mode instanceof Function) {
                Function function = (Function) mode;
                if (function.getPredicateNameAndArity().equals(example.getPredicateNameAndArity())) {
                    // This is a matching variablizedMode.  Return it...
                    modes.add(function.asLiteral());
                }
            }
        }

        context.getStringHandler().setVariableIndicator(oldValue);

        return modes;
    }

    private ModeInfo getModeInfo(Literal typedMode) {
        ModeToVariableData data = new ModeToVariableData();

        Literal variablizedMode = (Literal) typedMode.accept(modeVisitor, data);

        return new ModeInfo(variablizedMode, data.variableToTypeMap);
    }

    private List<VariableInfo> getMatchingVariableInfo(Term signature, TypeSpec spec, Map<Variable, VariableInfo> variableInfos) {
        throw new UnsupportedOperationException("Not yet implemented");
    }

    public MapOfSets<PredicateNameAndArity, ModeInfo> collectAllModes() {

        MapOfSets<PredicateNameAndArity, ModeInfo> modes = new LinkedMapOfSets<PredicateNameAndArity, ModeInfo>();

        VarIndicator oldValue = context.getStringHandler().getVariableIndicatorNoSideEffects();
        context.getStringHandler().setVariableIndicator(VarIndicator.uppercase);
        Literal modeProofLiteral = context.getFileParser().parseLiteral("mode(X)");
        Variable xVar = (Variable) modeProofLiteral.getArgument(0);

        Proof modeProof = new DefaultProof(context, modeProofLiteral);
        BindingList bl = null;
        while ((bl = modeProof.prove()) != null) {
            Term modeWrapper = bl.getMapping(xVar);
            if (modeWrapper instanceof Function) {
                Function function = (Function) modeWrapper;
                Literal typedMode = function.asLiteral();

                if ( excludedModes.contains(typedMode.getPredicateNameAndArity()) == false ) {
                    ModeInfo modeInfo = getModeInfo(typedMode);
                    modes.put(typedMode.getPredicateNameAndArity(), modeInfo);
                }
            }
        }

        context.getStringHandler().setVariableIndicator(oldValue);

        return modes;
    }

    public void addExcludedMode(PredicateNameAndArity pnaa) {
        if ( excludedModes == null) {
            excludedModes = new HashSet<PredicateNameAndArity>();
        }

        excludedModes.add(pnaa);
    }

    private List<PossibleBinding> expandBindings(Node nodeToExpand, Map<Variable, TypeSpec> aMap) {

        if (aMap.isEmpty()) {
            return Collections.EMPTY_LIST;
        }
        else {

            Variable var = aMap.keySet().iterator().next();
            TypeSpec spec = aMap.remove(var);

            List<PossibleBinding> restOfTheBindings = expandBindings(nodeToExpand, aMap);
            if (restOfTheBindings == null) {
                return null;
            }
            else {
                List<PossibleBinding> result = new ArrayList<PossibleBinding>();

                if (spec.canBeBound()) {
                    Set<VariableInfo> variableInfos = new HashSet<VariableInfo>();
                    nodeToExpand.getAvailableInputs(spec, variableInfos);

                    if (spec.mustBeBound() && variableInfos.isEmpty()) {
                        return null;
                    }

                    if (variableInfos.isEmpty()) {
                        result.addAll(restOfTheBindings);
                    }
                    else {
                        crossBindings(var, variableInfos, restOfTheBindings, result);
                    }
                }

                if (spec.canBeNewVariable()) {
                }

                if (spec.canBeConstant()) {
                }

                return result;
            }
        }
    }

    private void crossBindings(Variable newVariable, Set<VariableInfo> newInfos, List<PossibleBinding> currentBindings, List<PossibleBinding> list) {
        if (currentBindings.isEmpty()) {
            for (VariableInfo variableInfo : newInfos) {
                list.add(new PossibleBinding(newVariable, variableInfo));
            }
        }
        else {
            for (VariableInfo variableInfo : newInfos) {
                for (PossibleBinding possibleBinding : currentBindings) {
                    list.add(new PossibleBinding(possibleBinding, newVariable, variableInfo));
                }
            }
        }
    }

//    private Set<Map<Variable, Term>> getPossibleVariableBindings(Literal typedMode, Node nodeToExpand) {
//
//    }
    public static void main(String[] args) throws FileNotFoundException {

        String facts =
                "a(x(inputA), outputA).\n"
                + "b(outputA, outputB1).\n"
                + "b(outputA, outputB2).\n"
                + "c(outputB1, outputB2, outputC).\n";

        String pos =
                "ex(pos1, inputA).\n";

        String neg =
                "ex(neg1, xxx).\n";

        String background =
                "setParam: loadAllBasicModes = false\n"
                + "setParam: loadAllLibraries  = false.\n"
                + "mode: ex(#label, +inputA).\n"
                //    + "mode: ex(+label, -outputB).\n"
                + "mode: a(x(+inputA), -outputA).\n"
                + "mode: b(+outputA, -outputB).\n"
                + "mode: c(+outputB, +outputB, -outputC).\n";




        LearnOneClause learnOneClause = new LearnOneClause(".", "Bottom", new StringReader(pos), new StringReader(neg), new StringReader(background), new StringReader(facts), new BestFirstSearch(), null, null);

        Example example = new Example(learnOneClause.getParser().parseLiteral(pos));

        BottomClauseUnused bc = new BottomClauseUnused(learnOneClause, example);

    }

    private boolean canExpandNode(Node nodeBeingExpanded) {

        return true;
    }

    private boolean pruneNode(Node newNode) {
        if (newNode.getNodeVariableDepth() > maximumVariableLayers) {
            return true;
        }

        return false;
    }
    private static PrettyPrinterOptions options;

    public static String print(Term term, BindingList bl) {
        PrettyPrinterOptions ppo = getPrettyPrintOptions();

        return PrettyPrinter.print(term, "", "", ppo, bl);
    }

    public static String print(Sentence term, BindingList bl) {
        PrettyPrinterOptions ppo = getPrettyPrintOptions();

        return PrettyPrinter.print(term, "", "", ppo, bl);
    }

    private static PrettyPrinterOptions getPrettyPrintOptions() {
        if (options == null) {
            options = new PrettyPrinterOptions();
            options.setRenameVariables(false);
            options.setSentenceTerminator("");
        }


        return options;
    }

    private enum VariableMode {

        INPUT,
        OUTPUT,
        CONSTANT;

    }

    private static class VariableInfo {

        Variable variable;

        Term value;

        TypeSpec typeSpec;

        public VariableInfo(Variable variable, Term value, TypeSpec spec) {
            this.variable = variable;
            this.value = value;
            this.typeSpec = spec;
        }

        @Override
        public String toString() {
            return "VariableInfo{" + variable + "=" + value + ", typeSpec=" + typeSpec + '}';
        }
    }

    public static class ModeInfo {

        Literal variablizedMode;

        Map<Variable, TypeSpec> variableToTypeMap;

        List<TypeSpec> inputTypes;

        List<TypeSpec> outputTypes;

        public ModeInfo(Literal variablizedMode, Map<Variable, TypeSpec> variableToTypeMap) {
            this.variablizedMode = variablizedMode;
            this.variableToTypeMap = variableToTypeMap;

            setupTypeLists();
        }

        private void setupTypeLists() {
            for (Term term : variablizedMode.getArguments()) {
                TypeSpec spec = term.getTypeSpec();

                if (spec == null && term instanceof Variable) {
                    spec = variableToTypeMap.get((Variable) term);
                }

                if (spec.mustBeBound()) {
                    if (inputTypes == null) {
                        inputTypes = new ArrayList<TypeSpec>();
                    }
                    inputTypes.add(spec);
                }
                else if (spec.canBeNewVariable()) {
                    if (outputTypes == null) {
                        outputTypes = new ArrayList<TypeSpec>();
                    }
                    outputTypes.add(spec);
                }
            }
        }

        public Literal getVariablizedMode() {
            return variablizedMode;
        }

        public TypeSpec getTypeForVariable(Variable variable) {
            return variableToTypeMap.get(variable);
        }

        public TypeSpec getTypeForArgument(int i) {
            Term term = variablizedMode.getArgument(i);
            if (term.getTypeSpec() != null) {
                return term.getTypeSpec();
            }
            else if (term instanceof Variable) {
                Variable variable = (Variable) term;
                return getTypeForVariable(variable);
            }
            else {
                return null;
            }
        }

        public String toString() {
            return toString(null);
        }

        public String toString(BindingList bl) {

            boolean hold = AllOfFOPC.renameVariablesWhenPrinting;
            AllOfFOPC.renameVariablesWhenPrinting = useRenamedVarsForPrinting;
            if (bl == null && useRenamedVarsForPrinting) {
                bl = new BindingList();
            }
            StringBuilder stringBuilder = new StringBuilder();

            stringBuilder.append("ModeInfo{" + " variablizedMode=").append(print(variablizedMode, bl)).append(", variableToTypeMap=[");

            if ( variableToTypeMap != null ) {
                boolean first = true;
                for (Map.Entry<Variable, TypeSpec> entry : variableToTypeMap.entrySet()) {
                    if (first == false) {
                        stringBuilder.append(", ");

                    }
                    stringBuilder.append(print(entry.getKey(), bl)).append(" => ").append(entry.getValue());
                    first = false;
                }
            }

            stringBuilder.append("] }");

            AllOfFOPC.renameVariablesWhenPrinting = hold;

            return stringBuilder.toString();
        }

        /** Rebinds the variable in the ModeInfo according to the binding list.
         *
         * The BindingList must contain only variable to variable bindings.  If
         * non-variable bindings are included, an IllegalArgumentException will
         * be thrown.
         * @param bl
         * @return
         */
        public ModeInfo rebind(BindingList bl) {

            Map<Variable, TypeSpec> reboundVarToTypeMap = new HashMap<Variable, TypeSpec>();
            for (Map.Entry<Variable, TypeSpec> entry : variableToTypeMap.entrySet()) {
                Term newVar = bl.getMapping(entry.getKey());
                if (newVar != null) {
                    if (newVar instanceof Variable == false) {
                        throw new IllegalArgumentException("ModeInfo.rebind requires Var-to-Var new bindings only, but " + entry.getKey() + " was mapped to " + newVar + " in the binding list.");
                    }
                    else {
                        reboundVarToTypeMap.put((Variable) newVar, entry.getValue());
                    }
                }
                else {
                    reboundVarToTypeMap.put(entry.getKey(), entry.getValue());
                }
            }

            return new ModeInfo(variablizedMode.applyTheta(bl), reboundVarToTypeMap);
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
            if (this.variablizedMode != other.variablizedMode && (this.variablizedMode == null || !this.variablizedMode.equals(other.variablizedMode))) {
                return false;
            }
            if (this.variableToTypeMap != other.variableToTypeMap && (this.variableToTypeMap == null || !this.variableToTypeMap.equals(other.variableToTypeMap))) {
                return false;
            }
            return true;
        }

        public int getInputVariableCount() {
            return inputTypes == null ? 0 : inputTypes.size();
        }

        public int getOutputVariableCount() {
            return outputTypes == null ? 0 : outputTypes.size();
        }

        @Override
        public int hashCode() {
            int hash = 7;
            hash = 97 * hash + (this.variablizedMode != null ? this.variablizedMode.hashCode() : 0);
            hash = 97 * hash + (this.variableToTypeMap != null ? this.variableToTypeMap.hashCode() : 0);
            return hash;
        }
    }

    private class Node {

        Node parent;

        Literal literal;

        ModeInfo modeInfo;

        // A set of all the variable binding introduced
        // as output from the literal.
        Set<VariableInfo> outputs;

        // A set of all the variable binding consumed
        // as input by the literal.
        Set<VariableInfo> inputs;

        // The constants variables that aren't allowed
        // to be output to the next stage.
        Set<VariableInfo> constants;

        Set<Node> children;

        public Node(Literal literal) {
            this.literal = literal;
        }

        public Node(Node parent, Literal literal, ModeInfo modeInfo, BindingList bl) {
            this.literal = literal;
            this.modeInfo = modeInfo;
            this.parent = parent;

            setupVariableInfo(bl);
        }

        private Node(Example literal, ModeInfo modeInfo, BindingList bl) {
            this.literal = literal;
            this.modeInfo = modeInfo;

            setupVariableInfo(bl);
        }

        public boolean add(Node e) {
            return children.add(e);
        }

        public Set<Node> getChildren() {
            return children;
        }

        public Literal getLiteral() {
            return literal;
        }

        public Node getParent() {
            return parent;
        }

        public void getAvailableInputs(TypeSpec specToFind, Set<VariableInfo> matches) {
            if (parent != null) {
                parent.getAvailableInputs(specToFind, matches);
            }

            if (outputs != null) {
                for (VariableInfo variableInfo : outputs) {
                    TypeSpec aSpec = variableInfo.typeSpec;
                    Type aType = aSpec.getType();

                    if (context.getStringHandler().isaHandler.isa(aType, specToFind.getType())) {
                        matches.add(variableInfo);
                    }
                }
            }
        }

        private void addConstant(VariableInfo vi) {
            // Constants???
            if (constants == null) {
                constants = new HashSet<VariableInfo>();
            }
            constants.add(vi);
        }

        private void addInput(VariableInfo vi) {
            if (parent != null) {
                if (inputs == null) {
                    inputs = new HashSet<VariableInfo>();
                }
                inputs.add(vi);
            }
            else {
                if (outputs == null) {
                    outputs = new HashSet<VariableInfo>();
                }
                outputs.add(vi);
            }
        }

        private void addOutput(VariableInfo vi) {
            if (parent == null) {
                if (inputs == null) {
                    inputs = new HashSet<VariableInfo>();
                }
                inputs.add(vi);
            }
            else {
                if (outputs == null) {
                    outputs = new HashSet<VariableInfo>();
                }
                outputs.add(vi);
            }
        }

        private int getOccuranceCount(PredicateNameAndArity predicateNameAndArity) {

            int occuranceCount = parent == null ? 0 : parent.getOccuranceCount(predicateNameAndArity);

            if (literal.getPredicateNameAndArity().equals(predicateNameAndArity)) {
                occuranceCount++;
            }

            return occuranceCount;
        }

        private String toLiteralsString(List<Node> nodes) {
            StringBuilder stringBuilder = new StringBuilder();
            BindingList bl = null;
            if (useRenamedVarsForPrinting) {
                bl = new BindingList();
            }
            boolean first = true;
            for (Node node : nodes) {
                if (first == false) {
                    stringBuilder.append(", ");
                }
                stringBuilder.append(print(node.literal, bl));
                first = false;
            }
            return stringBuilder.toString();
        }

        private String toModesString(List<Node> nodes) {
            StringBuilder stringBuilder = new StringBuilder();
            BindingList bl = null;
            if (useRenamedVarsForPrinting) {
                bl = new BindingList();
            }
            boolean first = true;
            for (Node node : nodes) {
                if (first == false) {
                    stringBuilder.append(", ");
                }
                stringBuilder.append(print(node.modeInfo.variablizedMode, bl));
                first = false;
            }
            return stringBuilder.toString();
        }

        private void setupVariableInfo(BindingList bl) {

            BindingList newOutputBindings = new BindingList();

            for (Variable variable : bl.getVariables()) {
                TypeSpec variableType = modeInfo.variableToTypeMap.get(variable);

                VariableInfo vi = new VariableInfo(variable, bl.getMapping(variable), variableType);
                if (variableType.canBeNewVariable()) {

                    Variable newVariable = context.getStringHandler().getNewUnamedVariable();
                    newOutputBindings.addBinding(vi.variable, newVariable);

                    addOutput(vi);
                }
                else if (variableType.mustBeBound()) {
                    addInput(vi);
                }
                else {
                    addConstant(vi);
                }
            }

            if (newOutputBindings.isEmpty() == false) {
                rebind(newOutputBindings);
            }
        }

        private void rebind(BindingList bindingList) {
            literal = literal.applyTheta(bindingList);
            modeInfo = modeInfo.rebind(bindingList);

            if (inputs != null) {
                for (VariableInfo variableInfo : inputs) {
                    variableInfo.variable = (Variable) variableInfo.variable.applyTheta(bindingList);
                    variableInfo.value = variableInfo.value.applyTheta(bindingList);
                }
            }

            if (outputs != null) {
                for (VariableInfo variableInfo : outputs) {
                    variableInfo.variable = (Variable) variableInfo.variable.applyTheta(bindingList);
                    variableInfo.value = variableInfo.value.applyTheta(bindingList);
                }
            }

            if (constants != null) {
                for (VariableInfo variableInfo : constants) {
                    variableInfo.variable = (Variable) variableInfo.variable.applyTheta(bindingList);
                    variableInfo.value = variableInfo.value.applyTheta(bindingList);
                }
            }
        }

        private List<Node> getPath() {
            Node n = this;

            List<Node> list = new LinkedList<Node>();

            while (n != null) {
                list.add(0, n);
                n = n.parent;
            }

            return list;
        }

        private List<Literal> getLiterals() {
            Node n = this;

            List<Literal> list = new LinkedList<Literal>();

            while (n != null) {
                if (n.parent != null) {
                    list.add(0, n.literal);
                }
                n = n.parent;
            }

            return list;
        }

        /** Returns the clauses length, excluding the head literal.
         * 
         * @return
         */
        public int getClauseLength() {
            if (parent == null) {
                return 0;
            }
            else {
                return parent.getClauseLength() + 1;
            }
        }

        /** Returns the maximum depth of all variables.
         *
         * @return
         */
        public int getNodeVariableDepth() {
            if (parent == null) {
                return 0;
            }
            else {
                int maxDepth = 0;
                if (inputs != null) {
                    for (VariableInfo variableInfo : inputs) {
                        int parentDepth = parent.getVariableDepth(variableInfo.variable);
                        assert (parentDepth != -1);
                        maxDepth = Math.max(maxDepth, parentDepth + 1);
                    }
                }
                return maxDepth;
            }
        }

        /** Returns the depth of a single variable.
         *
         * @param variable
         * @return
         */
        public int getVariableDepth(Variable variable) {
            if (isOutputVariable(variable)) {
                int myDepth = getNodeVariableDepth();
                int parentDepth = -1;

                if (parent != null) {
                    parentDepth = parent.getVariableDepth(variable);
                }

                if (parentDepth != -1) {
                    return Math.min(myDepth, parentDepth);
                }
                else {
                    return myDepth;
                }
            }
            else if (parent != null) {
                // It was an input, so just pass it up the chain...
                return parent.getVariableDepth(variable);
            }
            else {
                return -1;
            }
        }

        public boolean isOutputVariable(Variable variable) {
            if (outputs != null) {
                for (VariableInfo variableInfo : outputs) {
                    if (variableInfo.variable.equals(variable)) {
                        return true;
                    }
                }
            }
            return false;
        }

        public boolean isInputVariable(Variable variable) {
            if (inputs != null) {
                for (VariableInfo variableInfo : inputs) {
                    if (variableInfo.variable.equals(variable)) {
                        return true;
                    }
                }
            }
            return false;
        }

//        public void getOutputsForType(TypeSpec type, Set<VariableInfo> matches) {
//            for (VariableInfo variableInfo : outputs) {
//                if ( context.getStringHandler().isaHandler.isa(type.isaType, variableInfo.typeSpec.isaType)) {
//                    matches.add(variableInfo);
//                }
//            }
//
//            if ( parent != null ) {
//                parent.getOutputsForType(type, matches);
//            }
//        }
        @Override
        public String toString() {

            List<Node> nodes = getPath();

            StringBuilder stringBuilder = new StringBuilder();
            stringBuilder.append("\n  Ground:       ").append(toLiteralsString(nodes));
            stringBuilder.append("\n  Variablized:  ").append(toModesString(nodes));
            if (inputs != null && inputs.size() > 0) {
                stringBuilder.append("\n  Input Vars:   ").append(inputs);
            }
            if (outputs != null && outputs.size() > 0) {
                stringBuilder.append("\n  OutputVars:   ").append(outputs);
            }
            if (constants != null && constants.size() > 0) {
                stringBuilder.append("\n  Constant Vars:").append(constants);
            }

            return stringBuilder.toString();
        }

        private boolean isPossibleBindingAllowed(ModeInfo extensionMode, BindingList extensionBindings) {
            return true;
            // If we are going to extend the node, we need to make sure that the
            // extension mode hasn't already be used with this set of input bindings.
//            if (this.modeInfo.equals(extensionMode)) {
//                for (VariableInfo variableInfo : inputs) {
//                    Variable myInputVar = variableInfo.variable;
//                    Term myInputTerm = variableInfo.value;
//
//                    Term theirInputTerm = extensionBindings.getMapping(myInputVar);
//
//                    if ( theirInputTerm != null && theirInputTerm.equals(myInputTerm) ) {
//                        return false;
//                    }
//                }
//            }
//
//           return parent == null || parent.isPossibleBindingAllowed(extensionMode, extensionBindings);
        }

        private boolean isNewLiteralAllowed(Node nodeToExpand, ModeInfo extensionMode, BindingList extensionBindings, Literal boundNewLiteral) {

            if (getClauseLength() > maximumClauseLength) {
                return false;
            }

            if (prune(nodeToExpand, extensionMode, extensionBindings, boundNewLiteral)) {
                return false;
            }


            // If we are going to extend the node, we need to make sure that the
            // extension mode hasn't already be used with this set of input bindings.
            if (this.modeInfo.equals(extensionMode)) {

                // Track if the new literal is a copy of
                // an existing literal.  If it is,
                // do not allow it.
                boolean newLiteralMatches = true;

                if (inputs != null) {
                    for (VariableInfo variableInfo : inputs) {
                        Variable myInputVar = variableInfo.variable;

                        Term theirInputTerm = extensionBindings.getMapping(myInputVar);

                        if (theirInputTerm == null) {
                            newLiteralMatches = false;
                            break;
                        }
                    }
                }

                if (newLiteralMatches == true) {
                    if (outputs != null) {
                        for (VariableInfo variableInfo : outputs) {
                            Variable myOutputVar = variableInfo.variable;
                            Term myOutputTerm = variableInfo.value;

                            Term theirOutputTerm = extensionBindings.getMapping(myOutputVar);
                            if (theirOutputTerm == null || theirOutputTerm.equals(myOutputTerm) == false) {
                                newLiteralMatches = false;
                                break;
                            }
                        }
                    }
                }

                if (newLiteralMatches) {
                    return false;
                }
            }

            if (parent != null && parent.isNewLiteralAllowed(nodeToExpand, extensionMode, extensionBindings, boundNewLiteral) == false) {
                return false;
            }


            return true;
        }

        public boolean prune(Node nodeToExpand, ModeInfo extensionMode, BindingList extensionBindings, Literal boundNewLiteral) {

            PredicateName addedPredicate = boundNewLiteral.predicateName;

            List<Pruner> matchingPruners = addedPredicate.getPruners(boundNewLiteral.getArity(), literal.getPredicateNameAndArity());
            if (matchingPruners != null) {
                for (Pruner pruner : matchingPruners) {
                    if (pruner.isaMatch(boundNewLiteral, literal)) {
                        return true;
                    }
                }
            }

            if (parent != null && parent.prune(nodeToExpand, extensionMode, extensionBindings, boundNewLiteral)) {
                return true;
            }

            return false;
        }
    }

    public static class ModeToVariableData {

        Map<Variable, TypeSpec> variableToTypeMap = new HashMap<Variable, TypeSpec>();

    }

    public static class ModeToVariableSV extends DefaultSentenceVisitor<ModeToVariableData> {

        public ModeToVariableSV() {
            super(new ModeToVariableTV());
        }
    }

    public static class ModeToVariableTV extends DefaultTermVisitor<ModeToVariableData> {

        @Override
        public Term visitStringConstant(StringConstant stringConstant, ModeToVariableData data) {

            Term result = stringConstant;

            if (stringConstant.getTypeSpec() != null) {
                Variable newVar = stringConstant.getStringHandler().getNewUnamedVariable();

                data.variableToTypeMap.put(newVar, stringConstant.getTypeSpec());

                result = newVar;
            }

            return result;
        }
    }

    private static class PossibleBinding {

        protected Map<Variable, VariableInfo> possibleBindings;

        public PossibleBinding(Variable variable, VariableInfo binding) {
            possibleBindings = new HashMap<Variable, VariableInfo>();
            possibleBindings.put(variable, binding);
        }

        public PossibleBinding(PossibleBinding pb, Variable variable, VariableInfo binding) {
            possibleBindings = new HashMap<Variable, VariableInfo>();
            possibleBindings.putAll(pb.possibleBindings);
            possibleBindings.put(variable, binding);
        }

        /** Returns the variable bindings from the VariableInfo structures.
         *
         * If the pb contains the mapping:
         *   _1 -> {_2:someTerm}
         *
         * this method will return a binding list of
         *
         *   _2 -> someTerm.
         *
         * By applying both the gerVariableToVariableBindings(), followed by the
         * getVariableToTermBindings() you get from the initial variable set
         * to the ground instantiation.
         *
         * @return
         */
        public BindingList getVariableToTermBindings() {
            BindingList bl = new BindingList();
            for (Map.Entry<Variable, VariableInfo> entry : possibleBindings.entrySet()) {
                bl.addBinding(entry.getValue().variable, entry.getValue().value);
            }
            return bl;
        }

        /** Returns the variable bindings from the VariableInfo structures.
         *
         * If the pb contains the mapping:
         *   _1 -> {_2:someTerm}
         *
         * this method will return a binding list of
         *
         *   _1 -> _2
         *
         * @return
         */
        public BindingList getVariableToVariableBindings() {
            BindingList bl = new BindingList();
            for (Map.Entry<Variable, VariableInfo> entry : possibleBindings.entrySet()) {
                bl.addBinding(entry.getKey(), entry.getValue().variable);
            }
            return bl;
        }

        @Override
        public String toString() {
            return possibleBindings.toString();
        }
    }
}
