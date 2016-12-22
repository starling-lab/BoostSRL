/**
 * 
 */
package edu.wisc.cs.will.DataSetUtils;

import java.util.ArrayList;
import java.util.List;

import edu.wisc.cs.will.FOPC.Binding;
import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.Unifier;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.ResThmProver.HornClauseProver;
import edu.wisc.cs.will.ResThmProver.ProofDone;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

/**
 * @author shavlik
 *
 */
public class WeightedSumModel extends Function {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	public  List<Clause>  clauses;
	public  List<Double>  weightsOnClauses;
	public  double        offset = 0.0;
	public  Literal       function;     // Eg, functionXYZ(A, Value, C).  This is the function for which this weighted sum is a model.
	public  Literal       featureQuery; // Eg, featureFor_functionXYZ(A, CountOfUniqueBindings, C).  
	private int           length;       // For now, we'll assume that functions and features have at least THREE arguments: Example, ..., Value, Step.
	@SuppressWarnings("unused")
	private Variable      worldVar;
	@SuppressWarnings("unused")
	private Variable      stateVar;
	private Variable      outputVar;
	
	public WeightedSumModel(HandleFOPCstrings stringHandler, Literal function, Literal featureQuery, List<Clause> clauses, List<Double> weightsOnClauses, double offset) {
		this.function         = function;     
		this.featureQuery     = featureQuery; // Probably don't need both of these, but keep for future development.
		this.clauses          = clauses;
		this.weightsOnClauses = weightsOnClauses;
		this.offset           = offset;
		
		if (clauses.size() != weightsOnClauses.size()) {
			Utils.error("Need to have |clauses| = |weights| - you provided " + clauses.size() + " vs. " +  weightsOnClauses.size());
		}
		
		length = featureQuery.numberArgs();
		if (length                < 3)       { Utils.error("This code assumes that heads of features have at least three arguments.  You provided: " + featureQuery); }
		if (function.numberArgs() < 3)       { Utils.error("This code assumes that the function for which this is a model has at least three arguments.  You provided: " + function); }
		if (length != function.numberArgs()) { Utils.error("Length of '" + function + "' and '" + featureQuery + "' must be the same."); }
		int locOfWorldVar              = stringHandler.getArgumentPosition(stringHandler.locationOfWorldArg,         length);
		int locOfStepVar               = stringHandler.getArgumentPosition(stringHandler.locationOfStateArg,         length);
		int locationOfNumericOutputArg = stringHandler.getArgumentPosition(stringHandler.locationOfNumericOutputArg, length);
		worldVar  = (Variable) function.getArguments().get(locOfWorldVar);
		stateVar  = (Variable) function.getArguments().get(locOfStepVar);
		outputVar = (Variable) function.getArguments().get(locationOfNumericOutputArg);
	}
	
	public double evaluate(Literal query, Unifier unifier,HornClauseProver prover, HandleFOPCstrings stringHandler) throws SearchInterrupted  {
		double      total = offset;		
		BindingList theta = unifier.unify(function, query);	
		
		for (int i = 0; i < clauses.size(); i++) {
			Clause c   = clauses.get(i);
			double wgt = weightsOnClauses.get(i);
			
			// Utils.println(" clause: " + c);
			Literal        head            = c.posLiterals.get(0);
			List<Literal>  body            = c.negLiterals;
			int            locOfNumericVar = stringHandler.getArgumentPosition(stringHandler.locationOfNumericOutputArg, head.numberArgs());
			Variable       queryVar        = (Variable) head.getArgument(locOfNumericVar); // This should really be the same variable in all features, but play it safe and pull it out each time.
			List<Literal>  newBody         = new ArrayList<Literal>(body.size());
				
			for (Literal lit : body) {
					newBody.add(lit.applyTheta(theta.theta)); // Apply the binding list to a COPY of the body (since applyTheta works 'in place').
			}
			prover.proveConjunctiveQuery(newBody); // Evaluate this body.
			// Utils.println("   newBody: " + newBody);
			List<Binding>  bindings = ((ProofDone) prover.terminator).collectQueryBindings();
			if (bindings != null) { // For clauses that cannot be proven, we use a value of 0.
				boolean foundIt = false;
				for (Binding b : bindings) if (b.var == queryVar) { 
					// Utils.println("   " + wgt + " * " +  ((NumericConstant) b.term).value.doubleValue() + " bindings: " + bindings);
					total += wgt * ((NumericConstant) b.term).value.doubleValue();
					foundIt = true;
					break;
				}
				if (!foundIt) { Utils.error("Could not find '" + queryVar + "' in bindings = " + bindings); }
			}
		}
		return total;
	}
	
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		String basic  = function + " = " + outputVar + " is " + offset;
		String result = (precedenceOfCaller < 0 ? "(" + basic : basic);
		int length = weightsOnClauses.size();
		for (int i = 0; i < length; i++) {
			result += "\n + (" + weightsOnClauses.get(i) + ") * " + clauses.get(i).toString(Integer.MIN_VALUE, bindingList);
		}
		return (precedenceOfCaller < 0 ? result + ")" : result);
	}

}
