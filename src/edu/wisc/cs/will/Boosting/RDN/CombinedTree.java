package edu.wisc.cs.will.Boosting.RDN;
import java.io.IOException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.wisc.cs.will.Boosting.Trees.RegressionTree;
import edu.wisc.cs.will.Boosting.Utils.CommandLineArguments;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.Theory;
import edu.wisc.cs.will.FOPC.TreeStructuredTheory;
/*class added by Kaushik Roy
 * 
 */
public class CombinedTree {
	private static Set<String> predicates = new HashSet<String>(); //This has all unique predicates across all trees
	private static Set<Set<Clause>> setOfClauses = new HashSet<Set<Clause>>(); //This has the collection of trees as clauses
	private static HashMap<String, Double> finalTree = new HashMap<>(); //This is the combined tree as a Hash Map --> not needed for any major output.
	private static ArrayList<String> finalClauses = new ArrayList<String>(); //This is the final set of clauses after combination
	private static Set<HashMap<String, Double>> treesToAdd = new HashSet<HashMap<String, Double>>(); //This contains the collection of trees to add
	private static List<RegressionRDNExample> finalDataSet = new ArrayList<RegressionRDNExample>(); //it will store the final example and regression values to fit the tree on.
	private static RegressionTree finalRegTree; //will store finalRegression Tree
	public static CommandLineArguments cmd = null;
	
	public static List<RegressionRDNExample> getFinalDataSet(){
		return CombinedTree.finalDataSet; //returns the final regression values per example to learn the combined regression tree on.
	}
	public static void addTreeClauses(Set<Clause> clauses){
		//This method adds the set of clauses that form a tree to total setOfClauses across all trees
		setOfClauses.add(clauses);
	}
	
	public static void addToFinalSet(List <RegressionRDNExample> dataset){
		//this function is to add the trees analytically, implemented but not yet tested by calling the analytical combine function.
		if (CombinedTree.finalDataSet.size() == 0){
			CombinedTree.finalDataSet = dataset;
		}
		else{
			for(RegressionRDNExample example: dataset){
				int index = CombinedTree.finalDataSet.indexOf(example);
				if(index>=0){
					RegressionRDNExample relevantExample = CombinedTree.finalDataSet.get(index);
					double currentValue = relevantExample.getOutputValue();
					double valueToSet = currentValue + example.getOutputValue(); //addition step to add current cumulative value and new tree regression value
					relevantExample.setOutputValue(valueToSet);
					CombinedTree.finalDataSet.add(relevantExample);
				}	
			}
		}
	}
	
	public static void combineTrees(){
		//Combines the trees contained in treesToAdd analytically, implemented but not yet tested.
		System.out.println("% Combining all boosted trees");
		for(HashMap<String, Double> tree: CombinedTree.treesToAdd){
			//Basic idea: Don't take combinations of unique predicates that don't occur across any of the trees
			for(String key: tree.keySet()){
				if(CombinedTree.finalTree.keySet().contains(key))
					CombinedTree.finalTree.put(key, CombinedTree.finalTree.get(key)+tree.get(key));
				else
					CombinedTree.finalTree.put(key, tree.get(key));
			}
		}
	}
	
	public static void printCombinedTree(){
		//method to print the combined tree in clausal form.This is called when the trees are added analytically
		for(String key: CombinedTree.finalTree.keySet()){
			String clause="";
			List<String> predicates = new ArrayList<String>(CombinedTree.predicates);
			int sizeOfKey = key.length();
			int noOfUniquePredicates = predicates.size();
			char[] characterKey = new StringBuilder(key).reverse().toString().toCharArray();
			for(int i=0;i<sizeOfKey;i++){
				if(characterKey[i] == '1'){
					clause += predicates.get(noOfUniquePredicates-i-1)+" ^ ";
				}
			}
			clause += "! => "+CombinedTree.finalTree.get(key);
			CombinedTree.finalClauses.add(clause);
		}
		System.out.println("% Clauses after combining boosted trees are:");
		for(String clause: CombinedTree.finalClauses) System.out.println(clause); //print out each clause in final clause
	}
	
	public static void addTrees(String target){
		//method to add the trees by adding regression values and learning new tree
		String tree_dot_path = CombinedTree.cmd.getModelDirVal(); //come back here
		List<Clause> clauses = finalRegTree.getRegressionClauses();
		Theory th = finalRegTree.getSetup().getOuterLooper().getLearnedTheory();
		try {
			finalRegTree.saveToFile(tree_dot_path + "bRDNs/Trees/CombinedTreesTreeFile"+target+".tree");
		} catch (IOException e) {
			e.printStackTrace();
		}
		TreeStructuredTheory thry = (TreeStructuredTheory)th;
		thry.writeDOTFile(tree_dot_path + "bRDNs/dotFiles/CombinedTrees"+target+".dot");
		for(Clause clause: clauses){
			System.out.println(clause);
		}
	}
	
	public static void CreateTreesFromSetOfClauses(){
		//method to create bit vector from clauses contained in set of clauses to extract regression value pertaining to bit vector
		CombinedTree.printPredicates(); //print unique predicates
		CombinedTree.printSetOfClauses(); //print all clauses across all trees
		for(Set<Clause> clauses: setOfClauses){
			HashMap<String, Double> tree = new HashMap<>();
			for(Clause clause: clauses){
				List<Literal> bodyList = clause.getDefiniteClauseBody();
				Literal head = clause.getDefiniteClauseHead();
				int noOfArgumentsInHead = head.getArguments().size();
				Double regressionValue = Double.parseDouble(head.getArgument(noOfArgumentsInHead-1)+"");
				int sizeOfBody = bodyList.size();
				BigInteger decimal = new BigInteger("0");
				if(sizeOfBody>1){
					for(int i=0;i<sizeOfBody-1;i++){
						String lit = (bodyList.get(i)+"").toLowerCase().replace("\"", "");
						if(CombinedTree.predicates.contains(lit)){
							BigInteger base = new BigInteger("2");
							int exponent = CombinedTree.predicates.size()-1-CombinedTree.getPredicateIndex(lit);
							BigInteger addition = base.pow(exponent);
							decimal = decimal.add(addition);
						}
					}
					tree.put(decimal.toString(2), regressionValue); //creates bit vector and regression value pair and puts it in the tree
				}
				else{
					tree.put(Integer.toBinaryString(0), regressionValue); //this is if clauses body is empty, this corresponds to the 0000 bit vector.
				}
			}
			CombinedTree.treesToAdd.add(tree); //add tree with bit vector regression value tuples to treesToAdd
		}
		CombinedTree.combineTrees(); //combine the treesToAdd i.e. add them TODO --> other operations like multiplication etc.
		CombinedTree.printCombinedTree(); //print the combined tree as clauses
	}
	
	public static void printSetOfClauses(){
		int setCount = 0;
		for(Set<Clause> clauses: setOfClauses){
			setCount++;
			System.out.println("% Tree number: "+setCount);
			for(Clause clause: clauses){
				System.out.println(clause.getDefiniteClauseAsClause());
			}
		}
	}
	
	public static void addToPredicates(String predicate){
		CombinedTree.predicates.add(predicate.toLowerCase().replace("\"", ""));
	}
	
	 public static int getPredicateIndex(Object value) {
		 List<String> predicates = new ArrayList<String>(CombinedTree.predicates);
		 return predicates.indexOf(value);
	 }
	
	public static void printPredicates(){
		System.out.println("% Unique predicates across all trees: ");
		for(String predicate:CombinedTree.predicates){
			System.out.println(predicate);
		}
	}
	public static void setFinalRegTree(RegressionTree finalRegTree) {
		CombinedTree.finalRegTree = finalRegTree;
	}
}