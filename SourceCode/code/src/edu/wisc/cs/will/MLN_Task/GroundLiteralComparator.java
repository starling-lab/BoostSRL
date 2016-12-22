/**
 * 
 */
package edu.wisc.cs.will.MLN_Task;

import java.util.Comparator;

import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author shavlik
 *
 */
public class GroundLiteralComparator implements Comparator<Literal> { // Since the literals in ground clauses are of type Literal, we use that here as well.

	/**
	 *
	 */
	public GroundLiteralComparator() {
	}

	/* (non-Javadoc)
	 * @see java.util.Comparator#compare(java.lang.Object, java.lang.Object)
	 */
	public int compare(Literal lit0, Literal lit1) {
		if (lit0 == lit1) { return 0; }
		if (lit0 == null || lit1 == null) { Utils.error("Should not call GroundLiteralComparator.compare with a lit=null."); }

		int int0 = lit0.predicateName.hashCode();
		int int1 = lit1.predicateName.hashCode();
		
		if (int0 != int1) { return int0 - int1; }
		
		int len0 = lit0.numberArgs();
		int len1 = lit1.numberArgs();
		
		if (len0 != len1) { return len0 - len1; }
		
		for (int i = 0; i < len0; i++) {
			Term arg0 = lit0.getArgument(i);
			Term arg1 = lit1.getArgument(i);
			
			if (arg0 == arg1) { continue; }  // Sort based on the first non-matching term.
			int arg0int = arg0.hashCode();  // TODO should recur inside of these, in case there are functions.
			int arg1int = arg1.hashCode();  // TODO probably should implement hashCode for all FOPC classes.
			
			return arg0int - arg1int;
		}
		
		return 0;  // Could find no difference.
	}
}
