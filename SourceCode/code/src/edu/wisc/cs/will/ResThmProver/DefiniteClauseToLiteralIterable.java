package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.Literal;
import java.util.Iterator;
import java.util.NoSuchElementException;

public class DefiniteClauseToLiteralIterable implements Iterable<Literal> {

    Iterable<DefiniteClause> iterable;

    public DefiniteClauseToLiteralIterable(Iterable<DefiniteClause> iterable) {
        this.iterable = iterable;
    }

    public Iterator<Literal> iterator() {
        return new DefiniteClauseToLiteralIterator(iterable.iterator());
    }

    public static class DefiniteClauseToLiteralIterator implements Iterator<Literal> {

        Iterator<DefiniteClause> iterator;

        Literal next = null;

        public DefiniteClauseToLiteralIterator(Iterator<DefiniteClause> iterator) {
            this.iterator = iterator;
        }

        public boolean hasNext() {
            setupNext();
            return next != null;
        }

        public Literal next() {
            setupNext();
            if (next == null) {
                throw new NoSuchElementException();
            }
            Literal result = next;
            next = null;
            return result;
        }

        public void remove() {
            throw new UnsupportedOperationException("Not supported yet.");
        }

        private void setupNext() {
            if (next == null && iterator != null) {
                if (iterator.hasNext() == false) {
                    iterator = null;
                }
                else {
                	// 8/8/11 TVK added the following code as there might be a literal in the facts
                	// even if the current element is not a literal. This code will search for the
                	// next literal.
                	while(iterator.hasNext() && next==null) {
                		DefiniteClause aDefiniteClause = iterator.next();
                		if (aDefiniteClause.isDefiniteClauseFact()) {
                			next = aDefiniteClause.getDefiniteClauseFactAsLiteral();
                		} 
                	}
                }
            }
        }
    }
}
