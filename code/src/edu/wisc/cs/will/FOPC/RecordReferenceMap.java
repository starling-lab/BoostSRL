package edu.wisc.cs.will.FOPC;

import java.lang.ref.WeakReference;
import java.util.Map;
import java.util.WeakHashMap;

// Written by Trevor Walker.

public class RecordReferenceMap {
	
	private Map<RRKey,WeakReference<RecordReference>> map = new WeakHashMap<RRKey, WeakReference<RecordReference>>();
	
	protected RecordReferenceMap() {
	}

	public RecordReference getReference(String dbKey, RecordEntry recordEntry) {
		
		RecordReference canonicalReference = null;
		
		RRKey mapKey = new RRKey(dbKey,recordEntry);
		
		WeakReference<RecordReference> wr = map.get(mapKey);
		
		if ( wr != null && wr.get() != null ) {
			canonicalReference = wr.get();
		}
		
		if ( canonicalReference == null ) {
			canonicalReference = new RecordReference(dbKey,recordEntry);
			map.put(mapKey, new WeakReference<RecordReference>(canonicalReference));
		}
		
		return canonicalReference;
	}
	
	protected static class RRKey {
		String key;
		RecordEntry recordEntry;
		
		public RRKey(String key, RecordEntry recordEntry) {
			this.key = key;
			this.recordEntry = recordEntry;
		}
		
		public boolean equals(Object that) {
			return ((RRKey)that).key == key && ((RRKey)that).recordEntry == recordEntry;
		}
		
		public int hashCode() {
			return key.hashCode() + recordEntry.hashCode();
		}
		
	}
}
