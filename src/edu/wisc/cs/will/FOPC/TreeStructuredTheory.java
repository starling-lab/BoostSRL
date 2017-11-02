package edu.wisc.cs.will.FOPC;

import java.io.BufferedWriter;
import edu.wisc.cs.will.Utils.condor.CondorFileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.wisc.cs.will.Boosting.RDN.CombinedTree; //Kaushik
import edu.wisc.cs.will.ILP.InlineManager;
import edu.wisc.cs.will.Utils.Utils;


public class TreeStructuredTheory extends Theory {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;	
	private Literal                  headLiteral;
	private TreeStructuredTheoryNode root;
	private static int uniqueVarCounter = 1; // This is shared across multiple WILL threads, but that should be OK (if not, place counter in stringHander).
	private static Map<String,StringConstant> flattenedVarMap = new HashMap<String,StringConstant>(4); // Ditto.
	private Set<Literal> uniqueFlattenedLiterals = new HashSet<Literal>(4);
	
	private List<Clause> flattenedClauses;

	public TreeStructuredTheory(HandleFOPCstrings stringHandler) {
		super(stringHandler);
	}

	public TreeStructuredTheory(HandleFOPCstrings stringHandler, Literal headLiteral, TreeStructuredTheoryNode root) {
		this(stringHandler);
		this.headLiteral = headLiteral;
		this.root        = root;
	}
	
	private Variable getNextUniqueBodyVar() {
		return stringHandler.getGeneratedVariable("uniqueVar" + (uniqueVarCounter++), true); // We're counting on this being a unique name.
	}
	private StringConstant flattenedThisVar(Variable var) {
		StringConstant lookup = flattenedVarMap.get(var.getName());
		
		if (lookup != null) { return lookup; }
		
		lookup = convertNameToStringConstant(var.getName());
		flattenedVarMap.put(var.getName(), lookup);
		return lookup;
	}	
	// Drop an leading '?' if that is used to indicate a constant.
	private StringConstant convertNameToStringConstant(String name) {
		if (name == null || name.length() < 1) { return stringHandler.getStringConstant("emptyName"); }
		if (name.equals("_")) { return stringHandler.getStringConstant("underscore"); }
		if (stringHandler.doVariablesStartWithQuestionMarks()) {
			if (name.charAt(0) == '?') { return convertNameToStringConstant(name.substring(1)); } // The ?'s aren't stored, but check anyway.
			return stringHandler.getStringConstant(name); // I (JWS) left this here rather than combining the two IFs in case we need to do something different here.  
		}
		
		return stringHandler.getStringConstant(name);
	}

	public Literal getHeadLiteral() {
		return headLiteral;
	}

	public void setHeadLiteral(Literal headLiteral) {
		this.headLiteral = headLiteral;
	}

	public TreeStructuredTheoryNode getRoot() {
		return root;
	}

	public void setRoot(TreeStructuredTheoryNode root) {
		this.root = root;
	}
	
	public String writeDotFormat() {
		TreeStructuredTheoryNode.counter=1;
		String result = "digraph G{ \n";
		result = result + root.writeDotFormat();
		result = result + "}\n";
		return result;
	}
	
	public TreeStructuredTheory convertToStandardTheory(InlineManager checkForInlinersAndSupportingClauses) {
		List<Clause> results = root.collectPathsToRoots(this);
		
		// for (Clause c : results) { Utils.println("%  convertToStandardTheory: " + c); }	// Utils.waitHere("in convertToStandardTheory");
		addAllMainClauses(results, checkForInlinersAndSupportingClauses); 
		return this;
	}
	
	public TreeStructuredTheory renameAllClausesWithUniqueBodyVariables() {
    	if (getClauses() != null) {
    		List<Clause> newClauses = new ArrayList<Clause>(getClauses().size());
    		for (Clause c : getClauses()) if (c.isDefiniteClause()) {
    			Clause newClause = c;
    	    	Collection<Variable> headVars = c.posLiterals.get(0).collectFreeVariables(null);
    			Collection<Variable> bodyVars = c.collectFreeVariables(headVars);
    			BindingList bl = new BindingList();
    			if (bodyVars != null) for (Variable bVar : bodyVars) if (!"_".equals(bVar.getName())) {
    				bl.addBinding(bVar, getNextUniqueBodyVar());
    			}
    			newClauses.add(newClause.applyTheta(bl.theta));
    		} else { Utils.error("Expecting a definite clause: " + c); }
    		setClauses(newClauses);
    	}
    	if (getSupportClauses() != null) {
    		List<Clause> newSupportClauses = new ArrayList<Clause>(getSupportClauses().size() + 4);
    		for (Clause c : getSupportClauses()) if (c.isDefiniteClause()) {
    			Clause newSupportClause = c;
    	    	Collection<Variable> headVars = c.posLiterals.get(0).collectFreeVariables(null);
    			Collection<Variable> bodyVars = c.collectFreeVariables(headVars);
    			BindingList bl = new BindingList();
    			if (bodyVars != null) for (Variable bVar : bodyVars) if (!"_".equals(bVar.getName())) {
    				bl.addBinding(bVar, getNextUniqueBodyVar());
    			}
    			newSupportClauses.add(newSupportClause.applyTheta(bl.theta));
    		} else { Utils.error("Expecting a definite clause: " + c); }
    		setSupportClauses(newSupportClauses);
    	}
		return this;
	}
	
	public TreeStructuredTheory createFlattenedClauses() {
    	if (getClauses() != null) {
    		List<Clause> newClauses = new ArrayList<Clause>(getClauses().size());
    		Set<Clause> clauses = new HashSet<Clause>(); //to store set of clauses//Kaushik
    		for (Clause c : getClauses()) if (c.isDefiniteClause()) {
    			clauses.add(c); //add every clause//added by Kaushik because he's super cool
    			Clause newClause = c;
    			Collection<Variable> bodyVars = c.collectFreeVariables(null); // Need to flatten the head variables as well.
    			BindingList bl = new BindingList();
    			if (bodyVars != null) for (Variable bVar : bodyVars){
    				bl.addBinding(bVar, flattenedThisVar(bVar));
    			}
    			Clause finalC = newClause.applyTheta(bl.theta);
    			newClauses.add(finalC);
    			addToUniqueFlattenedLiterals(finalC.negLiterals);
    		} else { Utils.error("Expecting a definite clause: " + c); }
    		CombinedTree.addTreeClauses(clauses); //add the clausal representation of the tree to add//also added by Kaushik
    		flattenedClauses = newClauses;
    	}
		return this;
	}
	
	private void addToUniqueFlattenedLiterals(Collection<Literal> lits) {
		if (lits == null) { return; }
		for (Literal lit : lits) if (lit.predicateName != stringHandler.cutLiteral.predicateName)  {			
			if (lit.member(uniqueFlattenedLiterals, false)) { 
				// Utils.println(" " + lit + " already in " + uniqueFlattenedLiterals); 
			}
			else { uniqueFlattenedLiterals.add(lit); } 
		}
	}

	private String getFlattenedClauseStrings() {
		if (flattenedClauses == null) { return ""; }
		String result = "\n% The flattened versions of these clauses:\n\n";
		int counter = 1;
		for (Clause c : flattenedClauses) {
			result += "flattened_" + c.toPrettyString("   ", Integer.MAX_VALUE) + ". // Flattened version of clause #" + counter++ + ".\n\n";
		}
		
		result += "\n% The unique flattened literals:\n";
		for (Literal lit : uniqueFlattenedLiterals) {
			CombinedTree.addToPredicates(""+lit); //to keep track of unique predicates//Kaushik was here
			result += "%   " + lit + "\n";
		}
		return result;
	}
	public Collection<Variable> collectAllVariables() {
		return collectFreeVariables(null);
	}
	
	public Collection<Variable> collectFreeVariables(Collection<Variable> boundVariables) {
    	Collection<Variable> headVars = headLiteral.collectFreeVariables(boundVariables);
    	Collection<Variable> rootVars = root.collectFreeVariables(       boundVariables);
		return Variable.combineSetsOfVariables(headVars, rootVars);
	}
	
	// NOTE: if convertToStandardTheory has occurred, it will need to be redone in the new copy after renaming.
	public TreeStructuredTheory renameAllVariables() {
		Collection<Variable> vars = collectAllVariables();
		BindingList bl = stringHandler.renameAllVariables(vars, null);
		return new TreeStructuredTheory(stringHandler, headLiteral.applyTheta(bl.theta), root.applyTheta(bl.theta));
	}
	// In this version we ensure that the body variables in the tree-structured theory are all unique.
	public TreeStructuredTheory renameAllVariablesWithUniqueBodyVariables() {
    	Collection<Variable> headVars = headLiteral.collectFreeVariables(null);
		Collection<Variable> bodyVars = root.collectFreeVariables(       headVars);
		BindingList bl = stringHandler.renameAllVariables(headVars, null);
		if (bl == null) { bl = new BindingList(); }
		if (bodyVars != null) for (Variable bVar : bodyVars){
			bl.addBinding(bVar, getNextUniqueBodyVar());
		}
		return new TreeStructuredTheory(stringHandler, headLiteral.applyTheta(bl.theta), root.applyTheta(bl.theta));
	}
	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return printRelationalTree(newLineStarter, precedenceOfCaller, bindingList);
	}

    public String toPrettyString(String newLineStarter, int precedenceOfCaller) {
		return printRelationalTree(newLineStarter, precedenceOfCaller, null);
	}

	public String toPlainString() {
		return printRelationalTree("", Integer.MIN_VALUE, null);
	}

	public String printOriginalTheory() {
		return printRelationalTree("", Integer.MIN_VALUE, null);
	}

	public String printRelationalTree(String newLineStarter, int precedenceOfCaller) {
		return printRelationalTree(newLineStarter, precedenceOfCaller, null);
	}
	public String printRelationalTree(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		if (root == null) { return "\n" + newLineStarter + "  THERE IS NO STORED TREE FOR " + headLiteral.toPrettyString(newLineStarter, precedenceOfCaller, bindingList) + "."; }
		if (bindingList == null) {
			// Create a  new bl for the children
			bindingList = new BindingList(); 
			
		}
		return "% FOR " + headLiteral.toPrettyString("%" + newLineStarter, defaultPrecedence, bindingList) + ":\n% " + newLineStarter + "  "
				+ root.printRelationalTree("% " + newLineStarter + "  ", precedenceOfCaller, 0, bindingList)
				+ "\n\n" + super.toPrettyString(newLineStarter, precedenceOfCaller, bindingList) + // Also print the version as a set of Horn clauses.
				getFlattenedClauseStrings();
	}

	public void writeDOTFile(String fname) {
		Utils.ensureDirExists(fname);
		BufferedWriter wr;
		try {
			wr = new BufferedWriter(new CondorFileWriter(fname, false)); // Create a new file.
			String res = writeDotFormat();
			wr.write(res);
			wr.close();
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Problem writing DOTFile: " + fname);
		}
	}
	
	private int inventedPredNameCounter = 0;
	public PredicateName getInventedPredName() {
		PredicateName pname = stringHandler.getPredicateName("inventedPred" + (inventedPredNameCounter++) + stringHandler.getInventedPredicateNameSuffix());
		// pname.addTemporary(-1);
		return pname;
	}

	public Set<Literal> getUniqueFlattenedLiterals() {
		return uniqueFlattenedLiterals;
	}

	public void setUniqueFlattenedLiterals(Set<Literal> uniqueFlattenedLiterals) {
		this.uniqueFlattenedLiterals = uniqueFlattenedLiterals;
	}

}
