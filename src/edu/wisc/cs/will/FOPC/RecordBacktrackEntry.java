package edu.wisc.cs.will.FOPC;

import java.util.Iterator;

//Written by Trevor Walker.

public class RecordBacktrackEntry {
	Iterator<RecordEntry> recordIterator;
	
	public RecordBacktrackEntry() {
		
	}
	
	public Iterator<RecordEntry> getRecordIterator() {
		return recordIterator;
	}
	
	public void setRecordIterator(Iterator<RecordEntry> recordIterator) {
		this.recordIterator = recordIterator;
	}
}
