/**
 * 
 */
package edu.wisc.cs.will.ILP;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PrettyPrinter;
import edu.wisc.cs.will.FOPC.PrettyPrinterOptions;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.ResThmProver.DefaultHornClauseContext;
import edu.wisc.cs.will.ResThmProver.HornClauseContext;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author vsc
 * 
 * This is a clause optimiser in the style of  [VSC,AS,HB et al, JMLR03].
 * 
 *      
 */
public class ClauseOptimiser {

    private final static int debugLevel = -1; // Used to control output from this class (0 = no output, 1=some, 2=much, 3=all).

    HandleFOPCstrings stringHandler;

    public ClauseOptimiser(HandleFOPCstrings stringHandler) {
        this.stringHandler = stringHandler;
    }

    public Clause rewriteWithCuts(Clause clause) {
        Literal head = clause.getDefiniteClauseHead();
        List<Literal> body = componentsToLits(head, clause.getDefiniteClauseBody());

        Clause newClause = stringHandler.getClause(clause.posLiterals, body);
        newClause.setBodyContainsCut(true);

        return newClause;
    }

    @SuppressWarnings("unchecked")
    public List<List<Literal>> bodyToBodies(Literal head, List<Literal> body) {
        if (body.size() == 0) {
            return (List<List<Literal>>) Collections.EMPTY_LIST;
        }
        else if (body.size() == 1) {
            return Collections.singletonList(body);
        }
        else {
            return separateComponents(head, body);
        }
    }

    /** Constructs a new optimised clause.
     *
     * @param head
     * @param body
     * @return
     *
     *
     */
    protected int[] clauseToComponents(Literal head, List<Literal> body) {
        Collection<Variable> headvars = head.collectAllVariables();
        if (debugLevel > 1) {
            Utils.println("clauseToComponents: head = " + head);
            if (body == null) {
                Utils.waitHere("clauseToComponents: head = null.");
            }
            if (body != null) {
                for (Literal lit : body) {
                    Utils.println("   literal = " + lit);
                }
            }
        }

        int[] components;

        components = new int[body.size()];
        ArrayList<Collection<Variable>> lvarsets = new ArrayList<Collection<Variable>>(components.length);

        int i = 0;
        // check independence
        // by dividing into independent components.
        for (Literal lit : body) {
            int component = i;

            Collection<Variable> litvars = lit.collectAllVariables();
            if (debugLevel > 2) {
                Utils.println("  litvars = " + litvars + " for literal " + lit);
            }
            // mark as being in its own component
            components[i] = i;
            // literals have no variable
            if (litvars == null) {
                // component has these variables
                lvarsets.add(i, null);
                continue;
            }
            // head vars are assume to be ground
            litvars.removeAll(headvars);
            // component has these variables
            lvarsets.add(i, litvars);
            for (int j = 0; j < i; j++) {
                // get the variables again
                Collection<Variable> next = lvarsets.get(j);
                if (litvars != null) {
                    for (Variable v : litvars) {
                        if (next.contains(v)) {
                            component = component_merge(j, component, components);
                        }
                    }
                }
            }
            components[i] = component;
            i++;
        }
        return components;
    }

    protected List<Literal> componentsToLits(Literal head, List<Literal> body) {

        if (body == null) {
            return null;
        }

        int[] components = clauseToComponents(head, body);
        int total_components = normalise_components(components);

        if (total_components == 1) {
            return body;
        }

        //	we need to add components-1 cuts.	
        List<Literal> lits = new ArrayList<Literal>(body.size() + (total_components - 1));
        int component_id = 0;

        for (int i = 0; i < total_components; i++) {
            if (i != 0) {
                // add a cut
                lits.add(stringHandler.cutLiteral);
            }
            while (component_id != components[component_id]) {
                component_id++;
            }
            // add literals for this component.
            for (int k = component_id; k < components.length; k++) {
                if (components[k] == component_id) {
                    lits.add(body.get(k));
                }
            }
            component_id++;
        }
        // System.out.println("new clause = " + lits);
        // System.out.println("new clause = " + newClause );
        return lits;
    }

    protected List<List<Literal>> separateComponents(Literal head, List<Literal> body) {

        if (body == null) {
            return null;
        }

        try {
            int[] components = clauseToComponents(head, body);
            int total_components = normalise_components(components);

            int[] ids = new int[body.size()], map = new int[body.size()], size = new int[total_components];

            int next_component = 0;
            for (int i = 0; i < body.size(); i++) {
                int component;
                if (i == components[i]) {
                    size[next_component] = 0;
                    map[i] = next_component++;
                }
                component = map[components[i]];
                ids[i] = component;
                size[component]++;
            }

            List<List<Literal>> listOfLits = new ArrayList<List<Literal>>(total_components);
            for (int i = 0; i < total_components; i++) {
                listOfLits.add(new ArrayList<Literal>(size[i]));
            }

            for (int i = 0; i < body.size(); i++) {
                listOfLits.get(map[components[i]]).add(body.get(i));
            }
            return listOfLits;
        } catch (Exception e) {
            Utils.reportStackTrace(e);
            Utils.error("Problem running emulator.");
            return null;
        }
    }

    // make sure we are pointing to the representative
    private int deref_component(int j, int[] components) {
        while (components[j] != j) {
            j = components[j];
        }
        return j;
    }

    // if two components share variables
    // make sure one points to the other
    private int component_merge(int j, int component, int[] components) {
        int k = deref_component(j, components);
        if (k > component) {
            components[k] = component;
            //	System.out.println(k + " -> " + component);

            return component;
        }
        else {
            components[component] = k;
//            System.out.println(component + " -> " + k);
            return k;
        }
    }

    private int normalise_components(int[] components) {
        int total_components = 0;

        for (int i = 0; i < components.length; i++) {
            components[i] = deref_component(i, components);
            if (components[i] == i) {
                total_components++;
            }
        }
        return total_components;
    }

    public static void main(String[] args) {

        HornClauseContext context = new DefaultHornClauseContext();
        ClauseOptimiser co = new ClauseOptimiser(context.getStringHandler());
        context.getStringHandler().setVariablesStartWithQuestionMarks();

        FileParser fp = context.getFileParser();

        String string = " mega_posAnd_notNegOr0(?A, ?B, ?C, ?D, ?E) :- "
                + "               ilField_TheList_list(?A, theOfficialCPTList, ?F, ?E), "
                + "               member(?G, ?F), "
                + "               ilType_ConditionalProbability_Types(?A, ?G, ?E), "
                + "               compositeSymbolMap(?A, ?H, ?B, ?E), "
                + "               ilField_Composite_name(?A, ?H, ?B, ?E), "
                + "               member(?I, ?F), "
                + "               ilField_ConditionalProbability_Types_arg1(?A, ?I, ?B, ?E), "
                + "               sameAsIL(?A, ?B, ?B, ?E), "
                + "               compositeSymbolMap(?A, ?J, ?C, ?E), "
                + "               ilField_Composite_name(?A, ?J, ?C, ?E), "
                + "               member(?K, ?F), "
                + "               ilField_ConditionalProbability_Types_arg2(?A, ?K, ?C, ?E), "
                + "               sameAsIL(?A, ?C, ?C, ?E), "
                + "               ilField_ConditionalProbability_Types_arg3(?A, ?L, ?M, ?E), "
                + "               member(?L, ?F), "
                + "               ilType_AtLeastPlausible(?A, ?M, ?E), "
                + "               member(?N, ?F), "
                + "               compositeSymbolMap(?A, ?P, ?B, ?E), "
                + "               ilField_Composite_name(?A, ?P, ?B, ?E), "
                + "               ilField_ConditionalProbability_Types_arg1(?A, ?N, ?B, ?E), "
                + "               compositeSymbolMap(?A, ?Q, ?C, ?E), "
                + "               ilPred_Ancestors(?A, ?N, ?Q, iLBoolean_true, ?E), "
                + "               ilField_ConditionalProbability_Types_arg3(?A, ?N, ?R, ?E), "
                + "               ilType_AtLeastPlausible(?A, ?R, ?E), "
                + "               compositeSymbolMap(?A, ?S, ?B, ?E), "
                + "               ilField_Composite_name(?A, ?S, ?B, ?E), "
                + "               ilField_ConditionalProbability_Types_arg1(?A, ?T, ?B, ?E), "
                + "               member(?T, ?F), "
                + "               ilField_ConditionalProbability_Types_arg3(?A, ?U, ?W, ?E), "
                + "               member(?U, ?F), "
                + "               ilType_AtLeastPlausible(?A, ?W, ?E), "
                + "               compositeSymbolMap(?A, ?X, ?B, ?E), "
                + "               ilField_Composite_name(?A, ?X, ?B, ?E), "
                + "               member(?Y, ?F), "
                + "               ilField_ConditionalProbability_Types_arg1(?A, ?Y, ?B, ?E), "
                + "               member(?Z, ?F), "
                + "               ilField_ConditionalProbability_Types_arg3(?A, ?Z, ?AB, ?E), "
                + "               ilType_AtLeastPlausible(?A, ?AB, ?E), "
                + "               \\+("
                + "                  neverTrue("
                + "                            ?BB, ?F, "
                + "                            ("
                + "                              compositeSymbolMap(?A, ?CB, ?B, ?E), "
                + "                              ilField_Composite_name(?A, ?CB, ?B, ?E), "
                + "                              ilField_ConditionalProbability_Types_arg1(?A, ?BB, ?DB, ?E), "
                + "                              sameAsIL(?A, ?B, ?DB, ?E)"
                + "                            )"
                + "                           )"
                + "                 ), "
                + "               \\+("
                + "                  neverTrue("
                + "                            ?EB, ?F, "
                + "                            ("
                + "                              compositeSymbolMap(?A, ?FB, ?C, ?E), "
                + "                              ilPred_Ancestors(?A, ?EB, ?FB, iLBoolean_true, ?E)"
                + "                            )"
                + "                           )"
                + "                 ), "
                + "               \\+("
                + "                  neverTrue("
                + "                            ?GB, ?F, "
                + "                            ("
                + "                              compositeSymbolMap(?A, ?HB, ?B, ?E), "
                + "                              ilField_Composite_name(?A, ?HB, ?B, ?E), "
                + "                              ilField_ConditionalProbability_Types_arg1(?A, ?GB, ?IB, ?E), "
                + "                              sameAsIL(?A, ?B, ?IB, ?E), "
                + "                              compositeSymbolMap(?A, ?JB, ?C, ?E), "
                + "                              ilField_Composite_name(?A, ?JB, ?C, ?E), "
                + "                              ilField_ConditionalProbability_Types_arg2(?A, ?GB, ?KB, ?E), "
                + "                              sameAsIL(?A, ?C, ?KB, ?E), "
                + "                              ilField_ConditionalProbability_Types_arg3(?A, ?GB, ?LB, ?E), "
                + "                              ilType_AtLeastPlausible(?A, ?LB, ?E)"
                + "                            )"
                + "                           )"
                + "                 ).";


        Clause clause = fp.parseDefiniteClause(string);

        Clause clause2 = co.rewriteWithCuts(clause);

        PrettyPrinterOptions ppo = new PrettyPrinterOptions();
        ppo.setMaximumLiteralsPerLine(1);
        ppo.setSentenceTerminator("");
        ppo.setMaximumIndentationAfterImplication(10);
        ppo.setNewLineAfterImplication(true);

        System.out.println(PrettyPrinter.print(clause2, "", ppo));


    }
}
