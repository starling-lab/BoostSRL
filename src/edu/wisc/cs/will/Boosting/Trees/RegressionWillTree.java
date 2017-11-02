/**
 * 
 */
package edu.wisc.cs.will.Boosting.Trees;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import edu.wisc.cs.will.Utils.condor.CondorFileReader;
import edu.wisc.cs.will.Utils.condor.CondorFileWriter;
import java.io.IOException;
import java.util.HashSet;


import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.Theory;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author Tushar Khot
 *
 */
@Deprecated
public class RegressionWillTree extends RegressionTree {


	/**
	 * 
	 */
	private static final long serialVersionUID = 6109427707095387764L;

	
	
	/**
	 * 
	 */
	public RegressionWillTree(WILLSetup setup) {
		// TODO Auto-generated constructor stub
		super(setup);
		//suppClauses = new HashSet<Clause>();
	}

	public void reparseRegressionTrees() {
		super.reparseRegressionTrees();
		for (Clause cl : suppClauses) {
			Clause cl2 = setup.convertFactToClause(cl.toString() + ".");
			setup.getInnerLooper().getContext().getClausebase().assertBackgroundKnowledge(cl2);
		}
	}

	public void parseTheory(Theory th) {
		if (th.getClauses() == null) {
			Utils.error("No regular clauses!!!");
		}
		for (Clause cl : th.getClauses()) {
			if (cl == null)
				continue;
			regressionClauses.add(cl);
		}
		// Add supporting clauses to bk
		if(th.getSupportClauses() != null) {
			for (Clause cl : th.getSupportClauses()) {
				if (cl == null)
					continue;
				addSupportingClause(cl);
			}
			suppClauses.addAll(th.getSupportClauses());
		}

	}
	
	/*private void addSupportingClause(Clause cl) {
		setup.getInnerLooper().getContext().getClausebase().assertBackgroundKnowledge(cl);
	}*/

	// JWS: this is pretty hacked up and needs cleaning.
	private static final String suppClauseSep = "// SUPPORTING CLAUSES:";
	public void saveToFile(String filename) throws IOException {
		Utils.ensureDirExists(filename);
		BufferedWriter wr = new BufferedWriter(new CondorFileWriter(filename, false)); // Create a new file.
		for (Clause cl : suppClauses) {
			wr.write(cl.toString() +".\n");	
		}
		wr.write(suppClauseSep + "\n");
		super.saveToStream(wr);
		wr.close();
	}
	
	// JWS: this is pretty hacked up and needs cleaning.
	public void loadFromFile(String filename) {
		try {
			BufferedReader rdr=new BufferedReader(new CondorFileReader(filename));	
			String line=null;
			while((line = rdr.readLine())!=null) {
				if (line.equals(suppClauseSep)) { break; }
				Clause cl = setup.convertFactToClause(line);
				suppClauses.add(cl);
				addSupportingClause(cl);
			}
			super.loadFromStream(rdr);
			rdr.close();
		} catch (Exception e) {
			Utils.error("Something went wrong: " + e);
		}
	}



}
