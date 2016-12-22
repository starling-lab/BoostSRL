/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.Utils;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

/** A Map that maps Keys to Set of values.
 *
 * Each key can be mapped to a set of values.
 *
 * @author twalker
 */
public class MapOfSets<Key, Value> implements Iterable<Value> {

    private Map<Key, Set<Value>> map;

    public MapOfSets() {
    }


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
            Set<Value> set;
            return (set = map.get(key)) != null && set.contains(value);
        }
    }

    public Set<Value> getValues(Key key) {
        return map == null ? null : map.get(key);
    }

    public void put(Key key, Value value) {

        if ( map == null ) {
            map = createMap();
        }

        Set<Value> result = map.get(key);
        if ( result == null ) {
            result = createValueSet();
            map.put(key, result);
        }

        result.add(value);
    }

    public Set<Value> removeValues(Key key) {
        if ( map == null ) {
            return null;
        }
        else {
            Set<Value> set;
            return ((set = map.remove(key)) != null) ? set : null;
        }
    }

    public Value removeValue(Key key, Value value) {
        if ( map == null ) {
            return null;
        }
        else {
            Set<Value> set;
            return (Value) (((set = map.remove(key)) != null) ? set.remove(value) : null);
        }
    }

    public <K extends Key, S extends Set<Value>> void putAll(Map<K, S> newMap) {

        if ( newMap != null && newMap.isEmpty() == false ) {

            if ( map == null ) {
                map = createMap();
            }

            for (Entry<K, S> entry : newMap.entrySet()) {
                Set<Value> setToAdd = entry.getValue();
                K keyToAdd = entry.getKey();

                Set<Value> existingSet = map.get(keyToAdd);
                if (existingSet == null) {
                    existingSet = createValueSet();
                    map.put(keyToAdd, existingSet);
                }
                existingSet.addAll(setToAdd);
            }
        }
    }

    public void putAll(Key key, Set<? extends Value> values) {

        if ( values.isEmpty() == false ) {

            Set<Value> set = map.get(key);
            if ( set == null ) {
                set = createValueSet();
                map.put(key, set);
            }

            set.addAll(values);

        }
    }

    public void clear() {
        if ( map == null) {
            map.clear();
        }
    }

    public void clearKey(Key key) {
        if (map != null) {
            map.remove(key);
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

    public Collection<Set<Value>> values() {
        if ( map != null ) {
            return map.values();
        }
        else {
            return Collections.EMPTY_SET;
        }
    }

    public Set<Entry<Key, Set<Value>>> entrySet() {
        if ( map != null ) {
            return map.entrySet();
        }
        else {
            return Collections.EMPTY_SET;
        }
    }

    protected Set<Value> createValueSet() {
        return new HashSet<Value>();
    }

    protected Map<Key, Set<Value>> createMap() {
        return new HashMap<Key, Set<Value>>();
    }

    public String toString(String prefix) {
        String result = null;

        if ( map == null ) {
            result = "{}";
        }
        else {
            StringBuilder stringBuilder = new StringBuilder();

            for (Entry<Key, Set<Value>> entry : map.entrySet()) {
                stringBuilder.append(entry.getKey()).append(" => {");

                boolean first = true;
                for (Value value : entry.getValue()) {
                    if ( first == false ) {
                        stringBuilder.append(",");

                    }
                    stringBuilder.append("\n");

                    String valueString = value.toString();

                    String prefixedValueString = Utils.getStringWithLinePrefix(valueString, "    ");
                    stringBuilder.append(prefixedValueString);


                    first = false;
                }

                stringBuilder.append("}. \n");

            }
            result = stringBuilder.toString();
        }

        return Utils.getStringWithLinePrefix(result, prefix);
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
        final MapOfSets<Key, Value> other = (MapOfSets<Key, Value>) obj;
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
