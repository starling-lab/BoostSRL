/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import java.util.Comparator;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author shavlik
 *
 */
public class LiteralComparator implements Comparator<Literal> {

	/**
	 * 
	 */
	public LiteralComparator() {
	}

	/* (non-Javadoc)
	 * @see java.util.Comparator#compare(java.lang.Object, java.lang.Object)
	 */
	public int compare(Literal lit0, Literal lit1) {
		if (lit0 == lit1) { return 0; }
		if (lit0 == null || lit1 == null) { Utils.error("Should not call LiteralComparator.compare with a lit=null."); }

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
			if (arg0 instanceof Variable) {
				if (arg1 instanceof Variable) {  // Sort variables based on their name.
					Variable v0 = (Variable) arg0;
					Variable v1 = (Variable) arg1;
					String   s0 = v0.toString();
					String   s1 = v1.toString();
					if (s0.equals(s1)) {
						if (v0.counter > v1.counter) { return  1; } // These are longs and we need an int, so cannot simply subtract.
						if (v0.counter < v1.counter) { return -1; }
						else                         { return  0; }
					}
					return s0.hashCode() - s1.hashCode();
				}
				return -1;
			}
			if (arg1 instanceof Variable) { return 1; } 
			
			int arg0int = arg0.hashCode();  // TODO should recur inside of these, in case there are functions.
			int arg1int = arg1.hashCode();  // TODO probably should implement hashCode for all FOPC classes.
			
			return arg0int - arg1int;
		}
		
		return 0;  // Could find no difference.
	}

}
