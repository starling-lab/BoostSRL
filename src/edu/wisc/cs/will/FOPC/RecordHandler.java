package edu.wisc.cs.will.FOPC;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.Utils.Utils;

//Written by Trevor Walker.

public class RecordHandler {

	protected RecordReferenceMap     referenceMap;
	protected Map<String,RecordList> recordMap = new HashMap<String,RecordList>();
	
	public RecordHandler() {
		this.referenceMap = new RecordReferenceMap();
	}
	
	/** Records s as the first term under key.
	 * 
	 * @param key
	 * @param s
	 * @return Reference to the record
	 */
	public RecordReference recorda(String key, Term s) {
		RecordList rl = recordMap.get(key);
		
		if ( rl == null ) {
			rl = new RecordList();
			recordMap.put(key,rl);
		}
		
		RecordReference result = rl.recorda(key,s);
		
		return result;
	}
	
	/** Records s as the last term under key.
	 * 
	 * @param key
	 * @param s
	 * @return Reference to the record
	 */
	public RecordReference recordz(String key, Term s) {
		
		RecordList rl = recordMap.get(key);
		
		if ( rl == null ) {
			rl = new RecordList();
			recordMap.put(key,rl);
		}
		
		RecordReference result = rl.recordz(key,s);
		
		return result;
	}
	
	/**
         * Erases the references record.
         * 
         * @param recordReference
         * @return False.
         */
	public boolean erase(RecordReference recordReference) {
		boolean result = false;
		
		RecordList rl = recordMap.get(recordReference.key);
		
		if ( rl != null ) {
			rl.erase(recordReference);
		}
		
		return result;
	}
	
	/** Removes all entries under key.
	 * 
	 * @param key
	 */
	public void eraseall(String key) {
		recordMap.remove(key);
	}
	
	/** Performs a DB lookup of for the key, unifying Term with the first appropriate entry and updating bindingList.
	 *
	 * This version of recorded does not allow backtracking.  If you need backtracking, use the
	 * recorded version which allows a RecordBacktrackEntry to be provided.
	 * 
	 * @param key DB Key to use
	 * @param Term Term to unify against.  Term will be modified with the appropriate bindings.
	 * @param bindingList BindingList to place unified bindings into
	 * @param u Unifier to use.
	 * @return RecordReference to the record which was unified against.
	 */
	public RecordReference recorded(String key, Term Term, BindingList bindingList, Unifier u) {
		return recorded(key,Term,bindingList,u,null);
	}
	
	/**
         * Performs a DB lookup of for the key, unifying Term with the first
         * appropriate entry and updating bindingList. This version allows for
         * backtracking if a non-null backtrackEntry is provided. Note,
         * backtracking currently does not support concurrent modification. If
         * the record db is modified, backtracking will fail.
         * 
         * @param key
         *                DB Key to use
         * @param Term
         *                Term to unify against. Term will be modified with the
         *                appropriate bindings.
         * @param bindingList
         *                BindingList to place unified bindings into
         * @param u
         *                Unifier to use.
         * @param backtrackEntry
         *                Entry to track backtracking...
         * @return RecordReference to the record which was unified against.
         */
	public RecordReference recorded(String key, Term Term, BindingList bindingList, Unifier u, RecordBacktrackEntry backtrackEntry) {

		RecordReference result = null;
		
		RecordList rl = recordMap.get(key);
		if ( rl != null ) {
			result = rl.recorded(key,Term, bindingList, u, backtrackEntry);
		}
		
		return result;
	}
	
	/** Retrieves an instance from the D.B. based upon the reference.
	 * 
	 * @param recordReference Reference to the record.
	 * @param term Term to unify against
	 * @param bindingList BindingList to fill, should be initially empty, may be modified even under failure
	 * @param u Unifier
	 * @return true if the references was valid and we could unify against term
	 */
	public boolean instance(RecordReference recordReference, Term term, BindingList bindingList, Unifier u) {
		boolean result = false;
		
		RecordList rl = recordMap.get(recordReference.key);
		if ( rl != null && rl.completeEntryList.contains(recordReference.recordEntry)) {
			if ( u.unify(recordReference.recordEntry.term, term, bindingList) != null ) {
				result = true;
			}
		}
		
		return result;
	}
	
	private class RecordList {
		private List<RecordEntry> completeEntryList = new LinkedList<RecordEntry>();
		private Map<Pair<String,Integer>,List<RecordEntry>> predicateNameIndex;
		
		public RecordList() {
		}

		public RecordReference recorda(String key, Term term) {
			RecordEntry re = new RecordEntry(term);
			
			completeEntryList.add(0, re);
			
			LiteralAsTerm lat = LiteralAsTerm.class.cast(term);
			if(lat != null) {
				Pair<String,Integer> indexKey = new Pair<String,Integer>(lat.itemBeingWrapped.predicateName.name,lat.itemBeingWrapped.numberArgs());
				addIndexedEntry( createPredicateNameIndex(), indexKey, re, true);
			}
			
			return referenceMap.getReference(key, re);
		}
		
		public RecordReference recordz(String key, Term term) {
			RecordEntry re = new RecordEntry(term);
			completeEntryList.add(re);
			
			LiteralAsTerm lat = LiteralAsTerm.class.cast(term);
			if(lat != null) {
				Pair<String,Integer> indexKey = new Pair<String,Integer>(lat.itemBeingWrapped.predicateName.name,lat.itemBeingWrapped.numberArgs());
				addIndexedEntry( createPredicateNameIndex(), indexKey, re, false);
			}
			
			return referenceMap.getReference(key, re);
		}
		
		public RecordReference recorded(String key, Term term, BindingList bindingList, Unifier u, RecordBacktrackEntry backtrackEntry) {
			RecordReference result = null;
			
			Iterator<RecordEntry> recordIterator = null;
			if ( backtrackEntry != null && backtrackEntry.recordIterator != null ) {
				recordIterator = backtrackEntry.recordIterator;
			}
			else {
				recordIterator = getIndexedIteratorForTerm(term);
				
			}
			
			bindingList.theta.clear();
			
			while(recordIterator != null && recordIterator.hasNext()) {
				RecordEntry recordEntry = recordIterator.next();
				Term recordedTerm = recordEntry.term;
				BindingList newList = u.unify(term, recordedTerm, bindingList);
				if ( newList != null ) {
					result = referenceMap.getReference(key, recordEntry);
					break;
				}
			}
			
			if ( result != null && backtrackEntry != null ) {
				backtrackEntry.recordIterator = recordIterator;
			}
			
			return result;
		}
		
		public boolean erase(RecordReference recordReference) {
			boolean result = completeEntryList.remove(recordReference.recordEntry);
			
			if ( predicateNameIndex != null ) {
				LiteralAsTerm lat = LiteralAsTerm.class.cast(recordReference.recordEntry.term);
				if(lat != null) {
					Pair<String,Integer> key = new Pair<String,Integer>(lat.itemBeingWrapped.predicateName.name,lat.itemBeingWrapped.numberArgs());
					removeIndexedEntry( predicateNameIndex, key, recordReference.recordEntry);
				}
			}
			
			return result;
		}
		
		private Map<Pair<String,Integer>,List<RecordEntry>> createPredicateNameIndex() {
			if ( predicateNameIndex == null ) predicateNameIndex = new HashMap<Pair<String,Integer>,List<RecordEntry>>();
			return predicateNameIndex;
		}
		
		private void addIndexedEntry(Map<Pair<String,Integer>,List<RecordEntry>> index, Pair<String,Integer> key, RecordEntry re, boolean atFront) {
	
			List<RecordEntry> records = index.get(key);
			
			if ( records == null ) {
				records = new LinkedList<RecordEntry>();
				index.put(key, records);
			}
			
			if ( atFront ) {
				records.add(0,re);
			}
			else {
				records.add(re);
			}
			
			System.out.println("Added index: " + key + ":" + re.term +  " -> " + records.toString());
		}
		
		private void removeIndexedEntry(Map<Pair<String,Integer>,List<RecordEntry>> index, Pair<String,Integer> key, RecordEntry re) {
			
			List<RecordEntry> records = index.get(key);
			
			if ( records != null ) {
				records.remove(re);
				//System.out.println("Removed index: " + key + ":" + re.term + " from " + records.toString());
			}
		}
		
		private Iterator<RecordEntry> getIndexedIteratorForTerm(Term term) {
			
			if ( term instanceof LiteralAsTerm ) {
				if(predicateNameIndex == null) {
					// we have no literals as terms so far, so return null
					return null;
				}
				else {
					LiteralAsTerm lat = LiteralAsTerm.class.cast(term);
					Pair<String,Integer> key = new Pair<String,Integer>(lat.itemBeingWrapped.predicateName.name,lat.itemBeingWrapped.numberArgs());
					List<RecordEntry> records = predicateNameIndex.get(key);
					if ( records == null ) {
						// No records with that name, so return null
						return null;
					}
					else {
						// Return an iterator over the records...
						System.out.println("Iterating over " + records);
						return records.iterator();
					}
				}
			}
			else {
				//System.out.println("Iterating over " + completeEntryList);
				return completeEntryList.iterator();
			}
		}
	}
	
	private static class Pair<S,T> {
		S s;
		T t;
		
		public Pair(S s, T t) {
			this.s = s;
			this.t = t;
		}
		
		@SuppressWarnings("unchecked")
		public boolean equals(Object that) {
			return s == ((Pair)that).s && t == ((Pair)that).t;
		}
		
		public int hashCode() {
			return (s == null ? 0 : s.hashCode()) + (t == null ? 0 : t.hashCode());
		}
	}
	 
	public static void main(String args[]) {
		args = Utils.chopCommentFromArgs(args);
		
		Unifier unifier = new Unifier();
		HandleFOPCstrings stringHandler = new HandleFOPCstrings();
		RecordHandler recordHandler = stringHandler.getRecordHandler();
		String key = "test";		
		RecordReference rr = null;
		
		int literalCount = 10;
		for(int i = 0; i < literalCount; i++) {
			LiteralAsTerm literal = new LiteralAsTerm(stringHandler, new Literal(stringHandler, stringHandler.getPredicateName("my_pred"), stringHandler.getNumericConstant(i))); 
			rr = recordHandler.recordz(key, literal);
			System.out.println("Recording " + key + " -> " + literal + "  (" + rr + ")");
		}
		
		for(int i = 0; i < literalCount; i++) {
			for(int j = 0; j < i; j++) {
				LiteralAsTerm literal = new LiteralAsTerm(stringHandler, new Literal(stringHandler, stringHandler.getPredicateName("my_pred"), stringHandler.getNumericConstant(i), stringHandler.getNumericConstant(j))); 
				rr = recordHandler.recordz(key, literal);
				if ( Utils.random() < .5 ) {
					System.out.println("Recording " + key + " -> " + literal + "  (" + rr + ")");
				} else {
					recordHandler.erase(rr);
				}
			}
		}
		
		for(int i = 0; i < literalCount; i++) {
			LiteralAsTerm literal = new LiteralAsTerm(stringHandler, new Literal(stringHandler, stringHandler.getPredicateName("your_pred"), stringHandler.getNumericConstant(i))); 
			rr = recordHandler.recordz(key, literal);
			System.out.println("Recording " + key + " -> " + literal + "  (" + rr + ")");
		}
		
		System.gc();
		
		BindingList bl = new BindingList();
		RecordBacktrackEntry rbe;
		Term u;
		
		u = new LiteralAsTerm(stringHandler, new Literal(stringHandler, stringHandler.getPredicateName("my_pred"), stringHandler.getExternalVariable("X", false))); 
		rbe = new RecordBacktrackEntry();
		
		System.out.println("Called recorded " + u);
		while( (rr = recordHandler.recorded(key, u, bl, unifier, rbe)) != null ) {
			System.out.println("Result: " + bl + "  (" + rr + ")" );
			bl = new BindingList();
		}
		
		u = new LiteralAsTerm(stringHandler, new Literal(stringHandler, stringHandler.getPredicateName("my_pred"), stringHandler.getExternalVariable("X", false), stringHandler.getExternalVariable("X", false))); 
		rbe = new RecordBacktrackEntry();
		
		System.out.println("Called recorded " + u);
		while( (rr = recordHandler.recorded(key, u, bl, unifier, rbe)) != null ) {
			System.out.println("Result: " + bl + "  (" + rr + ")" );
			bl = new BindingList();
		}
		
		u = new LiteralAsTerm(stringHandler, new Literal(stringHandler, stringHandler.getPredicateName("my_pred"), stringHandler.getExternalVariable("X", false), stringHandler.getExternalVariable("Y", false))); 
		rbe = new RecordBacktrackEntry();
		
		System.out.println("Called recorded " + u);
		while( (rr = recordHandler.recorded(key, u, bl, unifier, rbe)) != null ) {
			System.out.println("Result: " + bl + "  (" + rr + ")" );
			bl = new BindingList();
		}
		
		u = new LiteralAsTerm(stringHandler, new Literal(stringHandler, stringHandler.getPredicateName("my_pred"), stringHandler.getNumericConstant(3), stringHandler.getExternalVariable("Y", false))); 
		rbe = new RecordBacktrackEntry();
		
		System.out.println("Called recorded " + u);
		while( (rr = recordHandler.recorded(key, u, bl, unifier, rbe)) != null ) {
			System.out.println("Result: " + bl + "  (" + rr + ")" );
			bl = new BindingList();
		}
		
		u = new LiteralAsTerm(stringHandler, new Literal(stringHandler, stringHandler.getPredicateName("your_pred"), stringHandler.getExternalVariable("Y", false))); 
		rbe = new RecordBacktrackEntry();
		
		System.out.println("Called recorded " + u);
		while( (rr = recordHandler.recorded(key, u, bl, unifier, rbe)) != null ) {
			System.out.println("Result: " + bl + "  (" + rr + ")" );
			bl = new BindingList();
		}

		
	}
}
