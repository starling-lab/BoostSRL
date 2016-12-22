/**
 * 
 */
package edu.wisc.cs.will.Boosting.Trees;

import java.io.BufferedReader;
import edu.wisc.cs.will.Utils.condor.CondorFileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.Theory;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author Tushar Khot
 *
 */
public class LearnRegressionTree {

	///private RegressionTree tree;
	
	private WILLSetup setup;
	
	public LearnRegressionTree(WILLSetup setup) {
		this.setup = setup;
	}

	public RegressionTree parseTheory(Theory th) {
		RegressionTree tree = null;
		if (!setup.useMLNs) {
			tree = new RegressionTree(setup);
		} else {
			tree = new RegressionMLNModel(setup);
		}
		if (th.getClauses() == null) {
			Utils.error("No regular clauses!!!");
		}
		for (Clause cl : th.getClauses()) {
			if (cl == null)
				continue;
			tree.addClause(cl);
		}
		// Add supporting clauses to bk
		if(th.getSupportClauses() != null) {
			for (Clause cl : th.getSupportClauses()) {
				if (cl == null)
					continue;
				tree.addSupportingClause(cl);
				setup.getInnerLooper().getContext().getClausebase().assertBackgroundKnowledge(cl);
			}
		}
		return tree;
	}
	
	public RegressionTree parsePrologRegressionTrees(String filename) throws NumberFormatException, IOException {
		RegressionTree tree = new RegressionTree(setup);
		// TODO use a more generic parser rather than line after line
		Pattern tree_head = Pattern.compile("tree\\((.*\\(.*\\)).*");
		String head_clause = null;
		Pattern node = Pattern.compile("\\s*node\\(([^\\(]*\\([^\\)]*\\)).*");
		List<String> nodes = new ArrayList<String>();
		Pattern leaf = Pattern.compile("\\s*leaf\\((.*),\\[.*");
		BufferedReader reader = new BufferedReader(new CondorFileReader(filename));
		String line = null;
		while((line = reader.readLine())!= null) {
			Matcher m=null;
			// Tree head
			m = tree_head.matcher(line);
			if (m.matches()) {
				head_clause = m.group(1);
			}

			// Nodes
			m = node.matcher(line);
			if (m.matches()) {
				String node_pred = m.group(1);
				node_pred = node_pred.replace("~", RegressionTree.NOT_PREFIX);
				nodes.add(node_pred);
			}

			// Leaf
			m = leaf.matcher(line);
			if (m.matches()) {
				String reg_values = m.group(1);
				double regression_value = Double.parseDouble(reg_values);
				Clause cl = null;
				if(!nodes.isEmpty()) {
					String tail = joinStringUsing(nodes, ",");
					String clause = "";
					if (tail.isEmpty()) {
						clause = head_clause +".";
					} else {
						clause = head_clause + ":-" + tail + ".";
					}
					//System.out.println(clause);
					// A clause to a sentence
					cl = setup.convertFactToClause(clause);
					//System.out.println(cl);
				}
				// regressionClauseToWeight.put(cl, regression_value);
				tree.addClause(createRegressionClause(cl, regression_value));
				// Remove all nodes that are done
				int i = nodes.size()-1;
				for (; i >= 0; i--) {
					if (doneWithPredicate(nodes.get(i))) {
						nodes.remove(i);
					} else {
						break;
					}
				}
				// Now push the negation of the last fact
				if (i != -1) {
					String last_pred = nodes.remove(i);
					String new_pred = ""; // LearnBoostedRDN.togglePredicate(last_pred, true);
					nodes.add("  " + new_pred);
				}
			}
		}
		reader.close();
		return tree;
	}

	private String joinStringUsing(List<String> nodes, String string) {
		String result="";
		for (String str : nodes) {
			if (str.matches("\\s+")) {
				continue;
			}
					
			if (!result.isEmpty()) {
				result = result + ",";
			}
			result = result + str;
		}
		return result;
	}
	
	private boolean doneWithPredicate(String predname) {
		if (predname.startsWith("  ")) {
			return true;
		}
		return false;
	}

	protected Clause createRegressionClause(Clause clause, double regressionValue) {
		HandleFOPCstrings handler = setup.getHandler();
		Literal head = clause.posLiterals.get(0);
		head.addArgument(handler.getNumericConstant(regressionValue));
		return clause;
	}

}

