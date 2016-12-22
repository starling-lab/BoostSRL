package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.DefiniteClause;
import java.util.Iterator;

public class DefiniteClauseToClauseIterable implements Iterable<Clause> {

    Iterable<DefiniteClause> iterable;

    public DefiniteClauseToClauseIterable(Iterable<DefiniteClause> iterable) {
        this.iterable = iterable;
    }

    public Iterator<Clause> iterator() {
        return new DefiniteClauseToClauseIterator(iterable.iterator());
    }

    public static class DefiniteClauseToClauseIterator implements Iterator<Clause> {

    Iterator<DefiniteClause> iterator;

    public DefiniteClauseToClauseIterator(Iterator<DefiniteClause> iterator) {
        this.iterator = iterator;
    }

    public boolean hasNext() {
        return iterator.hasNext();
    }

    public Clause next() {
        return iterator.next().getDefiniteClauseAsClause();
    }

    public void remove() {
        throw new UnsupportedOperationException("Not supported yet.");
    }


}
}
