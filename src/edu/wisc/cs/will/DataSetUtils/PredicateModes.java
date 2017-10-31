package edu.wisc.cs.will.DataSetUtils;



import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.PredicateSpec;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.ILP.ILPMain;
import edu.wisc.cs.will.ILP.LearnOneClause;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

public class PredicateModes {

	private LearnOneClause learnClause;

	public PredicateModes(LearnOneClause learn) {
		learnClause = learn;
	}

	public void printModes(boolean printHTML) {
		if (learnClause == null) {
			Utils.printlnErr("LearnOneClause not initialized!!");
		}

		if (learnClause.getBodyModes() == null) {
			Utils.printlnErr("LearnOneClause Body modes not initialized!!");
		}
		if (printHTML) {
			System.out.println("<DL>");
		}
		for (PredicateNameAndArity predicateNameAndArity : learnClause.getBodyModes()) {
			String arglist = "";
			for (PredicateSpec spec : predicateNameAndArity.getPredicateName().getTypeList()) {
				if (spec.getTypeSpecList() != null) {
					for (TypeSpec tspec : spec.getTypeSpecList()) {
						arglist += "," + tspec.getModeString() + tspec.getType();
					}
					arglist = arglist.replaceFirst(",", "");
					//	break;
					if (printHTML) {
						System.out.print("<DT> <i>");
					}
					System.out.print(predicateNameAndArity.getPredicateName().name +"(" + arglist + ").");
					if (printHTML) {
						System.out.print("</i>");
					}
					System.out.println();

					arglist="";
				}
			}
			if (printHTML) {
				System.out.println("<DD>");
			}

			//System.out.println(predicate.name +"(" + arglist + ").");
		}
		if (printHTML) {
			System.out.println("</DL>");
		}

	}

	public static void main(String[] args) {
		ILPMain main = new ILPMain();
		try {
			main.setup(args);
			main.outerLooper.initialize(false);
		} catch (SearchInterrupted e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		PredicateModes modes = new PredicateModes(main.outerLooper.innerLoopTask);
		modes.printModes(true);

	}


}
