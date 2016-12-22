/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.SentenceOrTerm;

/**
 *
 * @author twalker
 */
public class ElementAndPath {
    SentenceOrTerm element;
    ElementPath path;

    public ElementAndPath(SentenceOrTerm element, ElementPath path) {
        this.element = element;
        this.path = path;
    }

    public SentenceOrTerm getElement() {
        return element;
    }

    public void setElement(SentenceOrTerm element) {
        this.element = element;
    }

    public ElementPath getPath() {
        return path;
    }

    public void setPath(ElementPath path) {
        this.path = path;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final ElementAndPath other = (ElementAndPath) obj;
        if (this.element != other.element && (this.element == null || !this.element.equals(other.element))) {
            return false;
        }
        if (this.path != other.path && (this.path == null || !this.path.equals(other.path))) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        int hash = 7;
        hash = 79 * hash + (this.element != null ? this.element.hashCode() : 0);
        hash = 79 * hash + (this.path != null ? this.path.hashCode() : 0);
        return hash;
    }

    @Override
    public String toString() {
        return "{" + "element=" + element + ", path=" + path + '}';
    }


}
