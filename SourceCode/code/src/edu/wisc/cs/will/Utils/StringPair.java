/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.Utils;

/**
 *
 * @author twalker
 */
public class StringPair {
    private String first;
    private String second;

    public StringPair(String first, String second) {
        this.first = first;
        this.second = second;
    }

    public StringPair() {
    }

    public String getFirst() {
        return first;
    }

    public void setFirst(String first) {
        this.first = first;
    }

    public String getSecond() {
        return second;
    }

    public void setSecond(String second) {
        this.second = second;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final StringPair other = (StringPair) obj;
        if ((this.first == null) ? (other.first != null) : !this.first.equals(other.first)) {
            return false;
        }
        if ((this.second == null) ? (other.second != null) : !this.second.equals(other.second)) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        int hash = 7;
        hash = 47 * hash + (this.first != null ? this.first.hashCode() : 0);
        hash = 47 * hash + (this.second != null ? this.second.hashCode() : 0);
        return hash;
    }

    
}
