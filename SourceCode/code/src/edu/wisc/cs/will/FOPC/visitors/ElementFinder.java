/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC.visitors;

import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.SentenceOrTerm;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.Utils.Filter;
import java.util.ArrayList;
import java.util.List;

/**
 *
 * @author twalker
 */
public class ElementFinder {

    private final static ElementFinderListener ELEMENT_FINDER_LISTENER = new ElementFinderListener();

    public static List<ElementAndPath> findElements(Filter<ElementAndPath> filter, Sentence sentence) {

        ElementFinderData data = new ElementFinderData(filter);

        ElementPositionVisitor<ElementFinderData> efd = new ElementPositionVisitor<ElementFinderData>(ELEMENT_FINDER_LISTENER);

        sentence.accept(efd, data);

        return data.includedElements;

    }

    public static List<ElementAndPath> findElements(Filter<ElementAndPath> filter, Term term) {

        ElementFinderData data = new ElementFinderData(filter);

        ElementPositionVisitor<ElementFinderData> efd = new ElementPositionVisitor<ElementFinderData>(ELEMENT_FINDER_LISTENER);

        term.accept(efd, data);

        return data.includedElements;

    }

    private static class ElementFinderData extends ElementPositionVisitor.ElementPositionData {
        Filter<ElementAndPath> filter;
        List<ElementAndPath> includedElements = new ArrayList<ElementAndPath>();

        public ElementFinderData(Filter<ElementAndPath> filter) {
            this.filter = filter;
        }

    }

    private static class ElementFinderListener implements ElementPositionListener<ElementFinderData> {

        public boolean visiting(Sentence s, ElementFinderData data) {
            ElementAndPath e = new ElementAndPath(s, data.getCurrentPosition());

            if ( data.filter.includeElement(e) ) {
                data.includedElements.add(e);
            }

            return true;
        }

        public boolean visiting(Term t, ElementFinderData data) {
            ElementAndPath e = new ElementAndPath(t, data.getCurrentPosition());

            if ( data.filter.includeElement(e) ) {
                data.includedElements.add(e);
            }

            return true;
        }

    }

    private ElementFinder() {
    }
}
