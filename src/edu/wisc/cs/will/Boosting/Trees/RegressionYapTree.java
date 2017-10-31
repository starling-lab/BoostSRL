package edu.wisc.cs.will.Boosting.Trees;

import java.io.BufferedReader;
import edu.wisc.cs.will.Utils.condor.CondorFileReader;
import java.io.IOException;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.Utils.Utils;
@Deprecated
public class RegressionYapTree extends RegressionTree implements Serializable {


	/**
	 * 
	 */
	private static final long serialVersionUID = -2890400900570315419L;

	


	public RegressionYapTree(WILLSetup setup) {
		super(setup);
	}
	
	public boolean parsePrologRegressionTrees(String filename) throws NumberFormatException, IOException {
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
				regressionClauses.add(createRegressionClause(cl, regression_value));
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
		return false;
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





	public static void main(String[] args) {
		RegressionYapTree rtree = new RegressionYapTree(null);

		try {
			rtree.parsePrologRegressionTrees("cooltree.pl");
		} catch (NumberFormatException e) {
			Utils.reportStackTrace(e);
			Utils.error("Problem in main: " + args);
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Problem in main: " + args);
		}
		rtree.printTrees();
	}


}

// ***  HERE CODE COMES TO REST



/*
public double getRegressionValue(Example ex) {
	double sum = 0;
	double count=0;
	//System.out.println(fact);
	for (Clause clause : regressionClauseToWeight.keySet()) {
		if (clause == null || clauseSatisfiesExample(clause, ex)) {
			sum = sum + regressionClauseToWeight.get(clause);
			ex.numOfclauses = ex.numOfclauses + 1;
			count=count+1;
		}
	}
	//if (count>0)
	//	return sum/count;
	return sum;
}

protected boolean clauseSatisfiesExample(Clause clause, Example ex) {

	return setup.outerLooper.proveExample(clause, ex);
}

 */	/*private boolean clauseSatisfiesFacts(UserHornClauseProver prover, Clause clause, Literal fact) {
//	System.out.println(prover.getClausebase().getFacts().size());
	// TODO Auto-generated method stub
	prover.assertDefiniteClause(clause);
	if(prover.getClausebase().getFacts().contains(fact))
		Utils.waitHere("Fact already present!!");
	//System.out.println(fact);

	BindingList result = prover.prove(fact);
   // System.out.println(goal + " = " + (result == null ? "fail." : "true. " + result));
    prover.getClausebase().retractAllClausesWithUnifyingBody(clause);
    // Find better way or fix the bug
    ((DefaultHornClausebase)prover.getClausebase()).resetIndexes();
//	System.out.println(prover.getClausebase().getFacts().size());

    if (result == null)
    	return false;
   // System.out.println("ret true");
    return true;
}
  */


/*
//Utils.println(fact);
List<Sentence> clauses = LearnBoostedRDNs.parser.parse(fact + ".");
if (clauses.size() != 1) {
	Utils.waitHere("More than one sentence ??!" + fact);
}
List<Clause> cls = clauses.get(0).convertToClausalForm();
if(cls.size()!= 1) {
	Utils.waitHere("More than one clause ??!" + clauses.get(0));
}
return cls.get(0);
 */
/*
public double returnRegressionValue(BindingList bindings) {
	// TODO Implement this. 
	// If no clauses, assume uniform distribution
	if (regressionClauseToWeight.size() == 0)
		return 0.5;

	return 0.0;
}

public double returnProbability(UserHornClauseProver prover, Literal fact) {
	double sum = 0;
	GroundedLiteral glit = (GroundedLiteral)fact;
	String pname= glit.predicateName.name;
	if (LearnBoostedRDNs.isNegatedPredicate(pname))
		Utils.waitHere("Didn't expect negated literal");
	//System.out.println(fact);
	for (Clause clause : regressionClauseToWeight.keySet()) {
		if (clause == null || clauseSatisfiesFacts(prover, clause, fact)) {
			sum = sum + regressionClauseToWeight.get(clause);
			glit.addDebug_log("\nSatisfies clause: "+clause);
		//	System.out.println("sum:" + sum);
		}
	}

	return sum;
}
 */
//System.out.println(fact);
/*for (Clause clause : regressionClauseToWeight.keySet()) {
	if (clause == null || clauseSatisfiesExample(clause, ex)) {
		sum = sum + regressionClauseToWeight.get(clause);
		ex.numOfclauses = ex.numOfclauses + 1;
		count=count+1;
	}
}*/