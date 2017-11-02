package edu.wisc.cs.will.FOPC.visitors;

import java.util.ArrayList;
import java.util.List;

public class ElementPath implements Comparable<ElementPath>{

    private ElementPath parent;

    private int index;

    public ElementPath(ElementPath parent, int index) {
        this.parent = parent;
        this.index = index;
    }

    public ElementPath(int index) {
        this.index = index;
    }

    public ElementPath(List<Integer> indices) {
        if (indices.size() > 1) {
            parent = new ElementPath(indices.subList(0, indices.size() - 1));
        }
        index = indices.get(indices.size() - 1);
    }

    @Override
    public String toString() {
        if (parent != null) {
            return parent.toString() + ":" + index;
        }
        else {
            return Integer.toString(index);
        }
    }

    public ElementPath prepend(int prependedIndex) {
        List<Integer> list = asList();
        list.add(0, prependedIndex);
        return new ElementPath(list);
    }

    public ElementPath removeFirstElement() {
        List<Integer> list = asList();
        return new ElementPath(list.subList(1, list.size() - 1));
    }

    public List<Integer> asList() {
        List<Integer> list = new ArrayList<Integer>();
        ElementPath ep = this;
        while (ep != null) {
            list.add(0, ep.index);
            ep = ep.parent;
        }
        return list;
    }

    public int getIndex() {
        return index;
    }

    public void setIndex(int index) {
        this.index = index;
    }

    public ElementPath getParent() {
        return parent;
    }

    public void setParent(ElementPath parent) {
        this.parent = parent;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final ElementPath other = (ElementPath) obj;
        if (this.parent != other.parent && (this.parent == null || !this.parent.equals(other.parent))) {
            return false;
        }
        if (this.index != other.index) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        int hash = 7;
        hash = 17 * hash + (this.parent != null ? this.parent.hashCode() : 0);
        hash = 17 * hash + this.index;
        return hash;
    }

    public int compareTo(ElementPath that) {
        List<Integer> thisList = this.asList();
        List<Integer> thatList = that.asList();

        for (int i = 0; i < thisList.size() && i < thatList.size(); i++) {
            if ( thisList.get(i) < thatList.get(i) ) {
                return -1;
            }
            else if ( thisList.get(i) > thatList.get(i) ) {
                return 1;
            }
        }

        // If we made it this far, the lists are the same up
        // to the length of the shortest path.
        // If this is true, then the path that is shorter comes first.
        return thisList.size() - thatList.size();
    }


}
