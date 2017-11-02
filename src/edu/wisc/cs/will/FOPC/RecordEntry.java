package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.Utils.Utils;

//Written by Trevor Walker.

public class RecordEntry {
	Term term;
	
	private int hashCode;
	
	public RecordEntry(Term term) {
		this.term = term;
		this.hashCode = (int)(Utils.random() * Integer.MAX_VALUE);
	}
	
	public String toString() {
		return term.toString();
	}
	
	public boolean equals(Object that) {
		return this == that;
	}
	
	public int hashCode() {
		return hashCode;
	}
}
