/**
 * 
 */
package edu.wisc.cs.will.DataSetUtils;

import java.io.File;
import java.io.IOException;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings.VarIndicator;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Type;
import edu.wisc.cs.will.ILP.Gleaner;
import edu.wisc.cs.will.ILP.ILPouterLoop;
import edu.wisc.cs.will.ILP.ScoreSingleClause;
import edu.wisc.cs.will.ILP.ScoreSingleClauseByAccuracy;
import edu.wisc.cs.will.ResThmProver.DefaultHornClauseContext;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.stdAIsearch.BestFirstSearch;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchStrategy;

/**
 * @author tkhot
 *
 */
public class ComputeDatasetSize {

	
	private String prefix = null;
	private ILPouterLoop outerLooper = null;
	
	public ComputeDatasetSize() {
		
	}
	
	public void loadDirectory(String directory) {
		
		 File dir = new CondorFile(directory);
         

         if ( dir.isDirectory() == false ) {
            throw new IllegalArgumentException("Unable to find task directory: " + directory + ".");
         }

         directory = dir.getPath();
         if ( prefix == null ) {
             prefix = dir.getName();
         }

		// Slice the / off the prefix if it was passed in with one...
		if ( prefix.endsWith("/" ) ) {
			prefix = prefix.substring(0, prefix.length()-1);
		}

		
		String fileExtension = Utils.defaultFileExtension;
		String[] newArgList = new String[5];
		newArgList[0] = directory + "/" + prefix + "_pos."   + fileExtension;
		newArgList[1] = directory + "/" + prefix + "_neg."   + fileExtension;
		newArgList[2] = directory + "/" + prefix + "_bk."    + fileExtension;
		newArgList[3] = directory + "/" + prefix + "_facts." + fileExtension;

		Utils.createDribbleFile(directory + "/" + prefix +  "." + fileExtension);
		Utils.touchFile(    directory + "/" + prefix + "_started" + "." + fileExtension);
		

		try {
			HandleFOPCstrings stringHandler = new HandleFOPCstrings(VarIndicator.questionMarks); // Let's use leading caps in these tasks since NLP involves lower and upper case.
			stringHandler.keepQuoteMarks = true;
			ScoreSingleClause scorer = new ScoreSingleClauseByAccuracy() ;
			SearchStrategy strategy = new BestFirstSearch();

         	outerLooper = new ILPouterLoop(directory, prefix, newArgList, strategy, scorer, new Gleaner(), new DefaultHornClauseContext(stringHandler), false, true);
         	
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Encountered a problem: " + e);
		}
		try {
			getStringHandler().dontComplainIfMoreThanOneTargetModes = true;
			outerLooper.initialize(false);
		} catch (SearchInterrupted e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	public HandleFOPCstrings getStringHandler() {
		return outerLooper.innerLoopTask.getStringHandler();
	}
	
	public int numTypes() {
		return getStringHandler().getKnownConstantsOfThisType().keySet().size();
	}
	
	public int numConstants() {
		/*
		Set<Term> constants = new HashSet<Term>();
		for (Type type : getStringHandler().knownConstantsOfThisType.keySet()) {
			constants.addAll(getStringHandler().knownConstantsOfThisType.get(type));
		}
		return constants.size();*/
		return getConstants().size();
	}
	
	public Set<String> getConstants() {
		Set<String> constants = new HashSet<String>();
		for (Type type : getStringHandler().getKnownConstantsOfThisType().keySet()) {
			for (Term consts : getStringHandler().getKnownConstantsOfThisType().get(type)) {
				constants.add(consts.toString());
			}
		}
		return constants;
	}
	public int numPredicates() {
		Set<String> preds = new HashSet<String>();
		Iterator<Literal> lits = getFacts();
		while(lits.hasNext()) {
			Literal lit = lits.next();
			
			if (preds.add(lit.getPredicateName().name)) {
				//System.out.println(lit.getPredicateName().name);
			}
		}
		for (Literal lit : outerLooper.getPosExamples()) {
			if (preds.add(lit.getPredicateName().name)) {
			//	System.out.println(lit.getPredicateName().name);
			}
		}
		return preds.size();
	}
	public Iterator<Literal> getFacts() {
		return outerLooper.innerLoopTask.getContext().getClausebase().getFacts().iterator();
	}
	public int numTrueLiterals() {
		int counter = 0;
		Iterator<Literal> lits = getFacts();
		while(lits.hasNext()) {
			counter++;
			lits.next();
		}
		counter += outerLooper.getPosExamples().size();
		return counter;
	}
	public int numGroundLiterals() {
		int count = 0;
		Set<String> seenpreds = new HashSet<String>();
		for (PredicateNameAndArity pred : outerLooper.innerLoopTask.getBodyModes()) {
			int prod = 1;
			String pname = pred.getPredicateName().name;
			if (seenpreds.contains(pname) || pname.contains("recursive_")) {
				continue;
			}
			seenpreds.add(pname);
			for (Type type : pred.getTypes()) {
				int tSize = getStringHandler().getConstantsOfExactlyThisType(type).size();
				prod *= tSize;
			}
		//	System.out.println(pred + ":" + prod);
			count += prod;
		}
		for (PredicateNameAndArity pred : outerLooper.innerLoopTask.getTargetModes()) {
			int prod = 1;
			String pname = pred.getPredicateName().name;
			if (seenpreds.contains(pname) || pname.contains("recursive_")) {
				continue;
			}
			seenpreds.add(pred.getPredicateName().name);
			for (Type type : pred.getTypes()) {
				int tSize = getStringHandler().getConstantsOfExactlyThisType(type).size();
				prod *= tSize;
			}
			//System.out.println(pred + ":" + prod);
			count += prod;
		}
		
		return count;
	}
	
	/**
	 * @param args
	 */
	public static void main(String[] args) {
		ComputeDatasetSize datasize = new ComputeDatasetSize();
		//datasize.loadDirectory("Z:/sharkbkup/workspace/Testbeds/RDNs/imdb/test5_imdb");
		//datasize.loadDirectory("Z:/sharkbkup/workspace/Testbeds/RDNs/uw-cse_rdn/train1_advisedby");
		//datasize.loadDirectory("D:/Users/tkhot/data/OldTestbeds/cora-er/train2_same");
		datasize.loadDirectory("D:/Users/tkhot/data/OldTestbeds/webkb_busl/test2_courseta");
		System.out.println("Constants=" + datasize.numConstants());
		System.out.println("Types=" + datasize.numTypes());
		System.out.println("Predicates=" + datasize.numPredicates());
		System.out.println("TrueLiterals=" + datasize.numTrueLiterals());
		System.out.println("GndLiterals=" + datasize.numGroundLiterals());
	}

}
