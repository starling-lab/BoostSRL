/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.Literal;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;

/**
 *
 * @author twalker
 */
public class DefiniteClauseList extends ArrayList<DefiniteClause> {

    private boolean containsOnlyFacts = true;

    public DefiniteClauseList() {
        super(1);
    }

    public DefiniteClauseList(List<DefiniteClause> list) {
        super(list);
    }

    public boolean remove(Object o) {
        boolean result = super.remove(o);

        if (result == true && containsOnlyFacts == false && ((DefiniteClause) o).isDefiniteClauseRule()) {
            updateContainsOnlyFacts();
        }

        return result;
    }

    public boolean add(DefiniteClause e) {

        if (containsOnlyFacts && e.isDefiniteClauseRule()) {
            containsOnlyFacts = false;
        }

        return super.add(e);
    }

    private void updateContainsOnlyFacts() {
        boolean result = true;
        for (DefiniteClause definiteClause : this) {
            if (definiteClause.isDefiniteClauseRule()) {
                result = false;
                break;
            }
        }
        containsOnlyFacts = result;
    }

    public boolean containsOnlyFacts() {
        return containsOnlyFacts;
    }

    public Iterable<Literal> getFactIterable() {
        return new DefiniteClauseToLiteralIterable(this);
    }

    public Iterable<Clause> getClauseIterable() {
        return new DefiniteClauseToClauseIterable(this);
    }
}
