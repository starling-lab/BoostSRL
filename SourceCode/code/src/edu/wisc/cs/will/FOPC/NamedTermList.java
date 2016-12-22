/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import java.util.List;

/**
 * Allow a list of arguments to have an accompanying list of names (mainly used for the Bootstrap Learning project, but might have other uses).
 * This is an awkward 'add in' rather than being designed in from scratch, since this is not generally used.
 * 
 * @author shavlik
 *
 */
public class NamedTermList {
	List<Term>   terms;
	List<String> names;
	
	public NamedTermList(List<Term> terms, List<String> names) {
		this.terms = terms;
		this.names = names;
	}

	public List<Term> getTerms() {
		return terms;
	}
	public void setTerms(List<Term> terms) {
		this.terms = terms;
	}

	public List<String> getNames() {
		return names;
	}
	public void setNames(List<String> names) {
		this.names = names;
	}

    @Override
    public String toString() {


        StringBuilder stringBuilder = new StringBuilder();
        stringBuilder.append("[");


        for (int i = 0; i < terms.size(); i++) {
            if ( i > 0 ) stringBuilder.append(", ");

            if ( names != null ) {
                stringBuilder.append(names.get(i)).append("=");
            }
            stringBuilder.append(terms.get(i));
        }
        stringBuilder.append("]");

        return stringBuilder.toString();
    }


}
