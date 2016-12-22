/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * @author shavlik
 *
 */
public abstract class AllOfFOPC {
	protected final static int debugLevel = 0;   // Used to control output from this project (0 = no output, 1=some, 2=much, 3=all).
	protected final static int defaultPrecedence = Integer.MIN_VALUE;  // This plays it safe and uses a lot of parentheses. 
	public          static boolean renameVariablesWhenPrinting = false;
	public          static boolean truncateStrings             = true; // Prevent printing very long strings if true.
	public          static boolean printUsingAlchemyNotation   = false;  
 
    /**
	 * This class is a superclass of all FOPC constructs.
	 */
	public AllOfFOPC() {
	}
	
	public static List<AllOfFOPC> makeList(AllOfFOPC item) {
		List<AllOfFOPC> result = new ArrayList<AllOfFOPC>(1);
		result.add(item);
		return result;
	}	
	public static List<AllOfFOPC> makeList(AllOfFOPC item, List<AllOfFOPC> rest) {
		List<AllOfFOPC> result = new ArrayList<AllOfFOPC>(1 + rest.size());
		result.add(item);
		result.addAll(rest); // Do this safely so no shared lists.
		return result;
	}
	public abstract AllOfFOPC applyTheta(Map<Variable,Term> bindings);
	public abstract int       countVarOccurrencesInFOPC(Variable v);

    public abstract String    toString(                             int precedenceOfCaller, BindingList bindingList);
	public abstract String    toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList);
	  
	public String toString(int precedence, List<Term> items) {
		String result = "";
		boolean firstTime = true;
		for(Term t : items) {
			if (firstTime) { firstTime = false; } else { result += ", "; }
			result += t.toString(precedence);
		}
		return result;
	}
	public String toPrettyString() {
		return toPrettyString("", defaultPrecedence); // Use some average value?
	}
	public String toPrettyString(String newLineStarter) {
		return toPrettyString(newLineStarter, defaultPrecedence); // Use some average value?
	}
    @Override
	public String toString() {
		return toString(defaultPrecedence); // Use some average value?
	}

    public String toString(BindingList bindingList) {
        return toString(defaultPrecedence, bindingList);
    }

    public String toString(int precedenceOfCaller) {
        if ( renameVariablesWhenPrinting ) {
            return toString(precedenceOfCaller, new BindingList());
        }
		return toString(precedenceOfCaller, (BindingList)null);
    }

    public String toPrettyString(String newLineStarter, int precedenceOfCaller) {
        if ( renameVariablesWhenPrinting ) {
            return toPrettyString(newLineStarter, precedenceOfCaller, new BindingList());
        }
		return toPrettyString(newLineStarter, precedenceOfCaller, (BindingList)null);
    }


//    /** Appends a string representation of the object to the appendable.
//     *
//     * If approximateMaximumLength is positive then this method will attempt to constrain
//     * itself to printing only the requested amount.  Additionally, it should return the
//     * number of characters appended to the stream.
//     *
//     * @param appendable Appendable to append to.
//     * @param newLineStarter String to append prior to starting a new line.
//     * @param precedenceOfCaller Precedence of the caller.
//     * @param maximumLength If positive, the approximate number of character to
//     * append to the stream.
//     * @return Number of character appended to the stream.
//     * @throws IOException IOExceptions from the appendable.append are forwarded.
//     */
//    public abstract int appendString(Appendable appendable, String newLineStarter, int precedenceOfCaller, int maximumLength);
//
//    public final int appendString(Appendable appendable, int precedenceOfCaller) {
//        return appendString(appendable, "", precedenceOfCaller, -1);
//    }
//    public final int appendString(Appendable appendable, String newLineStarter, int precedenceOfCaller) {
//        return appendString(appendable, newLineStarter, precedenceOfCaller, -1);
//    }
//
//    /** Appends a string representation of the object to the appendable.
//     *
//     * If approximateMaximumLength is positive then this method will attempt to constrain
//     * itself to printing only the requested amount.  Additionally, it should return the
//     * number of characters appended to the stream.
//     *
//     * @param appendable Appendable to append to.
//     * @param newLineStarter String to append prior to starting a new line.
//     * @param precedenceOfCaller Precedence of the caller.
//     * @param maximumLength If positive, the approximate number of character to
//     * append to the stream.
//     * @return Number of character appended to the stream.
//     * @throws IOException IOExceptions from the appendable.append are forwarded.
//     */
//    public abstract int appendPrettyString(Appendable appendable, String newLineStarter, int precedenceOfCaller, int maximumLength);
//
//    public final int appendPrettyString(Appendable appendable, int precedenceOfCaller) {
//        return appendString(appendable, "", precedenceOfCaller, -1);
//    }
//    public final int appendPrettyString(Appendable appendable, String newLineStarter, int precedenceOfCaller) {
//        return appendString(appendable, newLineStarter, precedenceOfCaller, -1);
//    }

}
