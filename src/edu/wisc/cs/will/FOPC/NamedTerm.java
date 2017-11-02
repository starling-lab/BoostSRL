/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import java.util.Comparator;

import edu.wisc.cs.will.Utils.Utils;

/**
 * Create a pair of a term and its name.
 * 
 * @author shavlik
 *
 */
public class NamedTerm {
	public Term   term;
	public String name;
	
	public static Comparator<NamedTerm> comparator = new NamedTermComparator(); 
	
	public NamedTerm(Term term, String name) {
		super();
		this.term = term;
		this.name = name;
	}	
	
	public String toString() {
		return term + "=" + name;
	}
	
	public static final String nameField          = "name";
	public static final String worldNameField     = "wiWorld"; // These are used for situation calculus.
	public static final String stateNameField     = "wiState";
	public static final String returnedValueField = "value"; // Do NOT use 'returnValue' here since that is treated specially in IL.

    static class NamedTermComparator implements Comparator<NamedTerm> {

	/**
	 *
	 */
	public NamedTermComparator() {
	}

	/* (non-Javadoc)
	 * @see java.util.Comparator#compare(java.lang.Object, java.lang.Object)
	 */
	public int compare(NamedTerm o1, NamedTerm o2) {
		if (o1 == o2) { return 0;}
		if (o1 == null || o2 == null) { Utils.error("Should not have a null name being compared to a non-null name."); }

        if (o1.name == null && o2.name == null ) { return 0; }
        if (o1.name == null && o2.name != null ) { return 1; }
        if (o2.name == null && o1.name != null ) { return -1; }

		if (o1.name.equalsIgnoreCase(NamedTerm.nameField))      { return -1; } // Always keep NAME in the first field.
		if (o2.name.equalsIgnoreCase(NamedTerm.nameField))      { return  1; }
		if (o1.name.equalsIgnoreCase(NamedTerm.worldNameField)) { return -1; } // The WORLD goes second.
		if (o2.name.equalsIgnoreCase(NamedTerm.worldNameField)) { return  1; }
		if (o1.name.equalsIgnoreCase(NamedTerm.stateNameField)) { return  1; } // The STATE goes at the END.
		if (o2.name.equalsIgnoreCase(NamedTerm.stateNameField)) { return -1; }
		if (o1.name.equalsIgnoreCase(NamedTerm.returnedValueField))  { return  1; }  // The returnValue goes second from last.
		if (o2.name.equalsIgnoreCase(NamedTerm.returnedValueField))  { return -1; }
		return o1.name.compareToIgnoreCase(o2.name);
	}

}
	
}

