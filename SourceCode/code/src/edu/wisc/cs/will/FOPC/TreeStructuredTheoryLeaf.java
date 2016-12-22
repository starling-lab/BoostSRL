package edu.wisc.cs.will.FOPC;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import com.sun.org.apache.bcel.internal.generic.INSTANCEOF;

import edu.wisc.cs.will.Utils.Utils;

public class TreeStructuredTheoryLeaf extends TreeStructuredTheoryNode {
	private Term   leafValue;
	private double variance;
	private String extraLabel = null; // Allow examples to be marked with a string that can be used in whatever way some algorithm wishes.
	
	public TreeStructuredTheoryLeaf(double weightedCountOfPositiveExamples, double weightedCountOfNegativeExamples, double variance, Term leafValue, String extraLabel) {
		super();
		this.leafValue  = leafValue;
		this.variance   = variance; // Use a negative number if this is a discrete-valued tree.
		this.extraLabel = extraLabel;
		this.weightedCountOfPositiveExamples = weightedCountOfPositiveExamples;
		this.weightedCountOfNegativeExamples = weightedCountOfNegativeExamples;
		/*if (((NumericConstant) leafValue).value.doubleValue() == 0) {
			// Utils.waitHere("Zero leaf ");
		}*/
	//	if (weightedCountOfNegativeExamples >  0.0) { Utils.error("Why does weightedCountOfNegativeExamples = " + weightedCountOfNegativeExamples); }
	//	if (weightedCountOfPositiveExamples <= 0.0) { Utils.error("Why does weightedCountOfPositiveExamples = " + weightedCountOfPositiveExamples); }
	}

	public Term getLeafValue() {
		return leafValue;
	}
	public void setLeafValue(Term leafValue) {
		this.leafValue = leafValue;
	}

	public String getExtraLabel() {
		return extraLabel;
	}
	public void setExtraLabel(String extraLabel) {
	//	Utils.waitHere(" adding extraLabel = " + extraLabel);
		this.extraLabel = extraLabel;
	}
	
	@Override
	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return printRelationalTree(newLineStarter, precedenceOfCaller, 0, bindingList);
	}
	@Override
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return toPrettyString("", precedenceOfCaller, bindingList);
	}

	@Override
	public String printRelationalTree(String newLineStarter, int precedenceOfCaller, int depth, BindingList bindingList) {
		String prefix = "return " + leafValue.toPrettyString(newLineStarter, precedenceOfCaller, bindingList) + (variance >= -0.000001 ? ";  // std dev = " + Utils.truncate(Math.sqrt(Math.max(0.0, variance)), 3)+ ", " : ";  // ") ;
		if (weightedCountOfNegativeExamples <= 0.0) {
			return prefix + Utils.truncate(weightedCountOfPositiveExamples, 3) + " (wgt'ed) examples reached here."                                     + (extraLabel != null ? "  " + extraLabel : "");
		}
		return     prefix + Utils.truncate(weightedCountOfPositiveExamples, 3) + "pos, " + Utils.truncate(weightedCountOfNegativeExamples, 3) + "neg]." + (extraLabel != null ? "  " + extraLabel : "");
	}

	@Override
	public List<Clause> collectPathsToRoots(TreeStructuredTheory treeTheory) {		
		if (leafValue == treeTheory.stringHandler.falseIndicator) { return null; } // If classification tree, only return the TRUE leaves.
				
		List<Clause> results = new ArrayList<Clause>(1);		
		if (leafValue == treeTheory.stringHandler.trueIndicator) {
			Literal head = treeTheory.getHeadLiteral();
			Clause  c    = treeTheory.stringHandler.getClause(head, true, extraLabel);
			
			results.add(c);
			return results;
		}
		
		// If regression, add the value to the head (if constants at leaves - otherwise need to add a literal that computes Value).
		Literal      headCopy = treeTheory.getHeadLiteral().copy(false);
		List<Term>   args     = headCopy.getArguments();
		List<String> argNames = headCopy.getArgumentNames();
		args.add(leafValue);
		if (argNames != null) { argNames.add("OutputVarTreeLeaf"); } // Presumably this is a unique name ...
		Literal lit  = treeTheory.stringHandler.getLiteral(headCopy.predicateName, args, argNames);
		//Clause  c    = treeTheory.stringHandler.getClause(lit,true);//(lit, treeTheory.stringHandler.cutLiteral);
		Clause  c    = treeTheory.stringHandler.getClause(lit, treeTheory.stringHandler.cutLiteral, extraLabel);
		//c.setWeightOnSentence(((NumericConstant)leafValue).value.doubleValue());
		// System.out.println("Set wt as " + c.getWeightOnSentence() + ":Term=" + leafValue);
		
		results.add(c);
		return results;
		
	}

	@Override
	public TreeStructuredTheoryLeaf applyTheta(Map<Variable,Term> bindings) {
		return new TreeStructuredTheoryLeaf(weightedCountOfPositiveExamples, weightedCountOfNegativeExamples, variance, leafValue == null ? null : leafValue.applyTheta(bindings), extraLabel);
	}

	@Override
	public Collection<Variable> collectAllVariables() {
		if (leafValue == null) { return null; }
		return leafValue.collectAllVariables();
	}

	@Override
	public Collection<Variable> collectFreeVariables(Collection<Variable> boundVariables) {
		if (leafValue == null) { return null; }
		return leafValue.collectFreeVariables(boundVariables);
	}

	@Override
	public String writeDotFormat() {
		String labelStr = "";
		if (leafValue instanceof NumericConstant) {
			double reg = ((NumericConstant) leafValue).value.doubleValue();
			double prob = Math.exp(reg) / (1 + Math.exp(reg));
			labelStr = String.format("%.3f(%.3f)",reg, prob);
		} else {
			labelStr = leafValue.toPrettyString();
		}
		String result = nodeNumber + "[shape = box,label = \"" + labelStr + "\"];\n";
		return result;
	}

	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return 0;
	}
}
