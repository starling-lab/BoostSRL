/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.Utils;

import edu.wisc.cs.will.FOPC.DefiniteClause;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.List;
import java.util.Set;

/** A Map that maps Keys to List of values.
 *
 * Each key can be mapped to a list of values.
 *
 * @author twalker
 */
public class MapOfLists<Key, Value> implements Iterable<Value> {

    private Map<Key, List<Value>> map;

    public MapOfLists() {
    }

    /** Returns the number of Key entries in the map.
     * 
     * @return
     */
    public int size() {
        return map == null ? 0 : map.size();
    }

    public boolean isEmpty() {
        return map == null ? true : map.isEmpty();
    }

    public boolean containsKey(Key key) {
        return map == null ? false : map.containsKey(key);
    }

    public boolean containsValue(Key key, Value value) {

        if (map == null) {
            return false;
        }
        else {
            List<Value> list;
            return (list = map.get(key)) != null && list.contains(value);
        }
    }

    public Value setValue(Key key, int index, Value element) {

        if ( map == null ) {
            map = createMap();
        }

        List<Value> result = map.get(key);
        if ( result == null ) {
            result = createValueList();
            map.put(key, result);
        }

        return result.set(index, element);
    }

    public Value removeValue(Key key, int index) {
        if ( map == null ) {
            return null;
        }
        else {
            List<Value> list = map.get(key);

            if ( list != null ) {
                Object removedObject = list.remove(index);
                if ( list.isEmpty() ) {
                    map.remove(key);
                }
                return (Value)removedObject;
            }
            else {
                return null;
            }
        }
    }

    public boolean removeValue(Key key, Value value) {
        if ( map == null ) {
            return false;
        }
        else {
            List<Value> list = map.get(key);

            if ( list != null ) {
                boolean objectWasRemoved = list.remove(value);
                if ( list.isEmpty() ) {
                    map.remove(key);
                }
                return objectWasRemoved;
            }
            else {
                return false;
            }
        }
    }

    public int indexOfValue(Key key, Value value) {
        if ( map == null ) {
            return -1;
        }
        else {
            List<Value> list;
            return (((list = map.get(key)) != null) ? list.indexOf(value) : -1);
        }
    }

    public Value getValue(Key key, int index) {
        if ( map == null ) {
            throw new IndexOutOfBoundsException("List does not exist for key " + key + ".");
        }
        else {
            List<Value> list;
            return (((list = map.get(key)) != null) ? list.get(index) : null);
        }
    }

    public boolean containsAllValues(Key key, Collection c) {
        if ( map == null ) {
            return false;
        }
        else {
            List<Value> list;
            return (((list = map.get(key)) != null) ? list.containsAll(c) : false);
        }
    }

    public boolean contains(Key key, Value o) {
        if ( map == null ) {
            return false;
        }
        else {
            List<Value> list;
            return (((list = map.get(key)) != null) ? list.contains(o) : false);
        }
    }

    public void clear() {
        if ( map != null ) map.clear();
    }

    public boolean addAllValues(Key key, int index, Collection<? extends Value> c) {
        if ( map == null ) {
            map = createMap();
        }

        List<Value> result = map.get(key);
        if ( result == null ) {
            result = createValueList();
            map.put(key, result);
        }

        return result.addAll(index, c);
    }

    public boolean addAllValues(Key key, Collection<? extends Value> c) {
        if ( map == null ) {
            map = createMap();
        }

        List<Value> result = map.get(key);
        if ( result == null ) {
            result = createValueList();
            map.put(key, result);
        }

        return result.addAll(c);
    }

    public void addValue(Key key, int index, Value element) {
        if ( map == null ) {
            map = createMap();
        }

        List<Value> result = map.get(key);
        if ( result == null ) {
            result = createValueList();
            map.put(key, result);
        }

        result.add(index, element);
    }

    public boolean add(Key key, Value e) {
        if ( map == null ) {
            map = createMap();
        }

        List<Value> result = map.get(key);
        if ( result == null ) {
            result = createValueList();
            map.put(key, result);
        }

        return result.add(e);
    }


    public List<Value> getValues(Key key) {
        return map == null ? null : map.get(key);
    }

    public List<Value> remove(Key key) {
        if ( map == null ) {
            return null;
        }
        else {
            List<Value> list;
            return ((list = map.remove(key)) != null) ? list : null;
        }
    }

    public Set<Key> keySet() {
        if ( map != null) {
            return map.keySet();
        }
        else {
            return Collections.EMPTY_SET;
        }
    }

    public Collection<List<Value>> values() {
        if ( map != null ) {
            return map.values();
        }
        else {
            return Collections.EMPTY_SET;
        }
    }

    public Set<Entry<Key, List<Value>>> entrySet() {
        if ( map != null ) {
            return map.entrySet();
        }
        else {
            return Collections.EMPTY_SET;
        }
    }

    protected List<Value> createValueList() {
        return new ArrayList<Value>();
    }

    protected Map<Key, List<Value>> createMap() {
        return new HashMap<Key, List<Value>>();
    }

    public String toString(String prefix) {
        if ( map == null ) {
            return prefix + "{}";
        }
        else {
            StringBuilder stringBuilder = new StringBuilder();

            for (Entry<Key, List<Value>> entry : map.entrySet()) {
                stringBuilder.append(prefix).append(entry.getKey()).append(" => ");

                boolean first = true;
                for (Value value : entry.getValue()) {
                    if ( first == false ) {
                        stringBuilder.append(",");

                    }
                    stringBuilder.append("\n").append(prefix).append("   ").append(value);

                    first = false;
                }

                stringBuilder.append(".\n");

            }
            return stringBuilder.toString();
        }
    }

    @Override
    public String toString() {
        return toString("");
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final MapOfLists<Key, Value> other = (MapOfLists<Key, Value>) obj;
        if (this.map != other.map && (this.map == null || !this.map.equals(other.map))) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        int hash = 7;
        hash = 71 * hash + (this.map != null ? this.map.hashCode() : 0);
        return hash;
    }

    public Iterator<Value> iterator() {

        if ( map == null ) {
            return Collections.EMPTY_SET.iterator();
        }
        else {
            return new AllValueIterator(map.keySet().iterator());
        }
    }

    public class AllValueIterator implements Iterator<Value>{
        Iterator<Key> allKeysIterator;

        Iterator<Value> currentSubIterator = null;

        Value next = null;

        public AllValueIterator(Iterator<Key> allKeysIterator) {
            this.allKeysIterator = allKeysIterator;
        }



        public boolean hasNext() {
            setupNext();
            return next != null;
        }

        public Value next() {
            setupNext();
            Value result = next;
            next = null;
            return result;
        }

        public void remove() {
            throw new UnsupportedOperationException("Not supported yet.");
        }

        private void setupNext() {
            while (next == null) {
                if ( currentSubIterator != null && currentSubIterator.hasNext()) {
                    next = currentSubIterator.next();
                }
                else if ( currentSubIterator == null || currentSubIterator.hasNext() == false) {
                    if ( allKeysIterator != null && allKeysIterator.hasNext() ) {
                        currentSubIterator = getValues(allKeysIterator.next()).iterator();
                    }
                    else {
                        break;
                    }
                }
            }
        }
    }
}
