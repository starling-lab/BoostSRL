/**
 * 
 */
package edu.wisc.cs.will.ILP;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.wisc.cs.will.DataSetUtils.ArgSpec;
import edu.wisc.cs.will.FOPC.Constant;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateSpec;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Type;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.Utils.MessageType;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.StateBasedSearchTask;

/**
 * @author shavlik
 *
 *
 */
@SuppressWarnings("serial")
public class SingleClauseRootNode extends SingleClauseNode {
	protected Literal        target;          // For now, only work on one target (at a time? to do).
	protected List<ArgSpec>  targetArgSpecs;  // The info about the target argument being used and the variable matched with the type.
	protected List<Term>     variablesInTarget             = null;  // These should be typed.
	protected Set<Variable>  requiredBodyVariablesInTarget = null;
	protected PredicateName  targetPredicate               = null;
	protected int            targetPredicateArity          =   -1;
	
	/**
	 * @param task
	 * @param head
	 * @param enabler
	 * @param typesPresentInHead
	 * @param typesMapInHead
	 * @throws SearchInterrupted 
	 */
	public SingleClauseRootNode(StateBasedSearchTask task, Literal head, List<ArgSpec> argSpecs, List<Term> variables,
								PredicateSpec enabler, List<Type> typesPresentInHead, Map<Type,List<Term>> typesMapInHead) throws SearchInterrupted {
		super(task);
		target               = head;
		targetArgSpecs       = argSpecs;  // Utils.println("% targetArgSpecs: " + targetArgSpecs);  // DOES THIS ONLY DO THE TOP-LEVEL OF TERMS?  OR ALL VARIABLES DEEPLY EMBEDDED?
		targetPredicate      = head.predicateName;
		targetPredicateArity = head.numberArgs();
		variablesInTarget    = variables;
		literalAdded = head; // The root has with the empty body (i.e., it is an implicit 'true').  So we'll store the head literal here.
		depthOfArgs = new HashMap<Term,Integer>(head.numberArgs());
		markDepthOfLeafTerms(head.getArguments(), 0); // The depth of all the 'leaf' terms in the root (i.e., the head) is zero.
		this.enabler = enabler;
		typesPresent = typesPresentInHead;
		typesMap     = typesMapInHead;
		if (argSpecs != null) {
			for (ArgSpec argSpec : argSpecs) { //Utils.println("%   argSpec: " + argSpec);
				addTypeOfNewTerm(argSpec.arg, argSpec.typeSpec.isaType);
			}
		}
		computeCoverage();
		Utils.println(MessageType.ILP_INNERLOOP, "\n% target           = " + target);
		//Utils.println(  "%   targetArgSpecs = " + targetArgSpecs);
		checkForRequiredBodyVars(target.getArguments());
		//Utils.println(  "%   requiredBodyVariablesInTarget: " + requiredBodyVariablesInTarget); 
		//nodeID = nodeCounter++;
	}
	
	private void checkForRequiredBodyVars(List<Term> arguments) {
		if (arguments == null) { return; }
		for (Term arg : arguments) {
			if (arg instanceof Variable) {
				Variable var = (Variable) arg;
				// This is a linear lookup - but targets should not be so complex that this inefficiency matters.
				for (ArgSpec aSpec : targetArgSpecs) if (aSpec.arg == var && aSpec.typeSpec.mustBeInBody()) {
					addRequiredBodyVariable((Variable) arg);
				}
			} else if (arg instanceof Constant) {
				 
			} else if (arg instanceof Function) { // Should be ok to dive into ConsCells here.
				Function f = (Function) arg;
				checkForRequiredBodyVars(f.getArguments());
			} else { Utils.error("Should never reach here."); }
		}
	}
	
	public void addRequiredBodyVariable(Variable var) {
		if (requiredBodyVariablesInTarget == null) {
			requiredBodyVariablesInTarget = new HashSet<Variable>(4);
		}
		requiredBodyVariablesInTarget.add(var);
	}

}
