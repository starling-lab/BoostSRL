/**
 * 
 */
package edu.wisc.cs.will.ResThmProver;

import java.util.Collection;
import java.util.List;

import edu.wisc.cs.will.FOPC.Binding;
import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchNode;

/**
 * @author shavlik
 *
 */
@SuppressWarnings("serial")
public class HornSearchNode extends SearchNode {

    private static final int DEBUG = 0;

	Clause      clause;
	BindingList bindings;
    long        parentProofCounter;
    int         parentExpansionIndex;


	public HornSearchNode(HornClauseProver task, Clause clause, BindingList bindings, long parentProofCounter, int parentExpansionIndex) { // Used for the initial call (i.e., to create the root of the search space).
		super(task);
		this.clause   = clause;
		this.bindings = bindings; // I don't think there will ever be bindings at the root, but leave a hook in here just in case.
        this.parentProofCounter = parentProofCounter;
        this.parentExpansionIndex = parentExpansionIndex;
	}
	public HornSearchNode(HornSearchNode parentNode, Clause clause, BindingList bindings, long parentProofCounter, int parentExpansionIndex) {
		super(parentNode);
		this.clause   = clause;
		this.bindings = bindings;
        this.parentProofCounter = parentProofCounter;
        this.parentExpansionIndex = parentExpansionIndex;
	}
	
	/**
	 * See if this node contains this literal as its first literal (should be the only literal and the predicateName should be cutPredMarker, but assume the caller checks for this).
	 * 
	 * @param lit
	 * @return Whether the given literal is the cut marker for this node.
	 */
	public boolean isThisCutMarker(Literal lit) {
		return Utils.getSizeSafely(clause.negLiterals) > 0 && clause.negLiterals.get(0) == lit;
	}
	
	// Note that the bindings returned by this might look confusing since two different instances of the variable x will print the same,
	// and since they are really two different variables, they may well bind to different things.
	public List<Binding> collectBindingsToRoot() {

        List<Binding> bindingList = null;

        if ( getParentNode() != null ) {
            bindingList = getParentNode().collectBindingsToRoot();
        }

        if ( bindings != null ) {
            if ( bindingList == null ) {
                bindingList = bindings.collectBindingsInList();
            }
            else {
                List<Binding> moreBindings = bindings.collectBindingsInList();
                if ( moreBindings != null ) {
                    bindingList.addAll(moreBindings);
                }
            }
        }
		
		return bindingList;
	}

//    public BindingList collectQueryBindings() {
//
//        // Pass this off to the helper which tracks the childBindings.
//        //return collectQueryBindings(null);
//        BindingList queryVariables = getQueryVariables();
//
//        if ( queryVariables.theta.size() > 0 ) {
//            BindingList proofBindings = collectForwardBindings();
//            queryVariables.applyThetaInPlace(proofBindings.theta);
//        }
//
//        return queryVariables;
//    }

    public BindingList getQueryVariables() {

        BindingList bl = null;

        if ( getParentNode() != null ) {
            bl = getParentNode().getQueryVariables();
        }
        else {
            Collection<Variable> queryVariables = clause.collectAllVariables();

            bl = new BindingList();

            if ( queryVariables != null ) {
                for (Variable variable : queryVariables) {
                    bl.addBinding(variable, variable);
                }
            }
        }

        return bl;
    }

    public BindingList collectQueryBindings() {

        BindingList bl;

        if ( getParentNode() != null ) {
            bl = getParentNode().collectQueryBindings();

            if ( bindings != null && bindings.theta != null ) {
                bl.applyThetaInPlace(bindings.theta);

//                for (Variable v : bindings.theta.keySet()) {
//                    Term t1 = bl.lookup( v );
//                    Term t2 = bindings.lookup(v);
//
//                    if ( t1 != null ) {
//                        if ( t1.equals(t2) == false ) {
//                            throw new RuntimeException("Trying to add " + v + " => " + t2 + ", but it is already mapped to " + t1 + "!\nNew Bindings: " + bindings  );
//                        }
//                    }
//                    else {
//                        bl.addBinding(v, t2);
//                    }
//
//                }
//
                if ( DEBUG >= 1 ) System.out.println(bl + ".         Applied " + clause + "'s bindings = " + bindings + ".");
            }
        }
        else {
            bl = getQueryVariables();

            if ( DEBUG >= 1 ) System.out.println(bl + ".         Query Variables for goal " + clause + ".");
        }

        return bl;

    }

    /** Returns the binding for variable, or null if no binding is found.
     *
     * @param variable
     * @return
     */
    public Term getBinding(Variable variable) {

        Term result = variable;

        HornSearchNode currentNode = this;

        while(result instanceof Variable && currentNode != null) {
            if ( bindings != null ) {
               Term newResult = bindings.getMapping((Variable)result);
               if ( newResult != null ) {
                   result = newResult;
               }
            }

            currentNode = currentNode.getParentNode();
        }

        return result == variable ? null : result;
    }

//
//    private BindingList collectQueryBindings(BindingList childBindings) {
//
//        BindingList bl;
//
//        if ( childBindings != null ) {
//            if ( bindings != null && bindings.theta != null ) {
//                bl = new BindingList();
//
//                for (Entry<Variable, Term> entry : bindings.theta.entrySet()) {
//                    Term t2 = entry.getValue().applyTheta(childBindings.theta);
//                    bl.addBinding(entry.getKey(), t2);
//                }
//
//                bl.addBindings(childBindings);
//            }
//            else {
//                // Also add the childBindings to the list...
//                bl = childBindings;
//            }
//        }
//        else if ( bindings != null && bindings.theta != null) {
//           bl = new BindingList();
//           bl.addBindings(bindings);
//        }
//        else {
//            bl = null;
//        }
//
//        if ( getParentNode() != null ) {
//            return getParentNode().collectQueryBindings(bl);
//        }
//        else {
//            // This is the parent query, so lets remove any of
//            // the variable bindings that where not in the query.
//            Collection<Variable> vars = clause.collectAllVariables();
//
//            if ( vars != null ) {
//                Iterator<Variable> it = bl.theta.keySet().iterator();
//                while(it.hasNext()) {
//                    Variable var = it.next();
//
//                    if ( vars.contains(var) == false ) {
//                        it.remove();
//                    }
//                }
//            }
//            else {
//                bl.theta.clear();
//            }
//        }
//
//        return bl;
//    }

    /** Returns the ParentNode.
     *
     * Jude, I know you don't like getters/setters, but this is a place where they
     * really help.  The HornSearchNode's parent must also be a HornSearchNode.
     * We use the setParentNode method to enforce that restriction.
     * <p>
     * Also, a nice side effect is that Java allows you to change the
     * return type of a overriden method.  SearchNode.getParentNode()
     * returns a SearchNode.  However, here I know that the parentNode
     * is a HornSearchNode, so I change the return type appropriately.
     * Previous to this, you just did the typecast when you used it.  Now,
     * the cast is located just in the getter.
     *
     * @return the parentNode
     */
    @Override
    public HornSearchNode getParentNode() {
        return (HornSearchNode) super.getParentNode();
    }

    public boolean isSolution() {
        return ( clause != null && clause.isEmptyClause());
    }

    /**
     * @param parentNode the parentNode to set
     */
    @Override
    public void setParentNode(SearchNode parentNode) {
        if (parentNode != null && parentNode instanceof HornSearchNode == false ) {
            throw new IllegalArgumentException("parentNode must be a HornSearchNode");
        }

        super.setParentNode(parentNode);
    }
	
    @Override
	public String toString() {
    	//if (task.verbosity > 0) { reportNodePredicates(); return ""; } // TEMP patch for debugging.
		//return (getParentNode() == null ? "" : getParentNode().toString() + " -> ") + clause.toString();
        return (getParentNode() == null ? "" : "parent -> ") + clause.toString();
	}
    
	public void reportNodePredicates() {
		if (clause != null) {
			Utils.print("%     Predicates in this node: ");
			for (int i = 0; i < clause.getLength(); i++) { Utils.print(" " + clause.getIthLiteral(i).predicateName); }
			Utils.println("");
		}
	}

}
