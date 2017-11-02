/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 *
 */
package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName; 
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/** Default implementation of a HornClauseFactbaseIndexer.
 *
 * @param <T> Type of the indexed object.  This is just for convenience if you
 * know that only Clauses or Literals are being indexed.
 *
 * @author twalker
 */
public class DefaultHornClausebaseIndexer<T extends DefiniteClause> implements HornClausebaseIndexer<T> {

    private HornClausebase clausebase;

    /** Stores the class of T.
     * 
     * Since java generics do not store the actual class of T,
     * we need to do this by hand, since we need it later.
     */
    private Class<? extends T> elementClass;

    /** The number of arguments that should be index.
     *
     */
    private int indexWidth;

    private GroundNthArgumentClauseIndex<T>[] singleGroundArgIndexArray = null;

    private GroundClauseIndex<T> groundClauseIndex = null;

    private PredicateIndex<T> predicateIndex = null;

    private long[] singleGroundArgIndexLookupCount = null;

    private long groundClauseLookupCount = 0;

    private long predicateLookupCount = 0;

    private long[] singleGroundArgIndexHitCount = null;

    private long groundClauseHitCount = 0;

    private long predicateHitCount = 0;

    private boolean built = false;

    private Set<PredicateNameAndArity> constructedIndices = null;

    private final boolean lazyIndicesEnabled = false;

    public DefaultHornClausebaseIndexer(HornClausebase clausebase, Class<? extends T> elementClass) {
        this(clausebase, elementClass, 2);
    }

    public DefaultHornClausebaseIndexer(HornClausebase clausebase, Class<? extends T> elementClass, int indexWidth) {
        this.clausebase = clausebase;
        this.elementClass = elementClass;
        this.indexWidth = indexWidth;
        resetIndex();
    }

    @Override
    public final void resetIndex() {
        singleGroundArgIndexArray = (GroundNthArgumentClauseIndex<T>[])new GroundNthArgumentClauseIndex[indexWidth];
        predicateIndex = null;
        groundClauseIndex = null;

        singleGroundArgIndexLookupCount = new long[indexWidth];
        groundClauseLookupCount = 0;
        predicateLookupCount = 0;

        singleGroundArgIndexHitCount = new long[indexWidth];
        groundClauseHitCount = 0;
        predicateHitCount = 0;

        built = false;

        constructedIndices = new HashSet<PredicateNameAndArity>();
    }

    @Override
    public boolean isBuilt() {
        return built;
    }

    @Override
    public void buildIndex(Collection<? extends T> clauses) {

        if ( lazyIndicesEnabled == false ) {
            if (clauses != null) {
                for (T definiteClause : clauses) {
                    indexAssertion(definiteClause);
                }
            }
        }

        built = true;
    }

    @Override
    public void indexAssertion(T definiteClause) {

        if (definiteClause != null && definiteClause.isDefiniteClause()) {

            PredicateNameAndArity key = new PredicateNameAndArity(definiteClause);

            if ( lazyIndicesEnabled == false || constructedIndices.contains(key) ) {
                indexDefiniteClauseByPredicate(key, definiteClause);
                indexDefiniteClauseByAllArgs(key, definiteClause);
                for (int i = 0; i < indexWidth && i < key.getArity(); i++) {
                    indexDefiniteClauseByNthArg(i, key, definiteClause);
                }
            }
        }
    }

    @Override
    public void removeAssertion(T definiteClause) {

        PredicateNameAndArity key = new PredicateNameAndArity(definiteClause);

        if ( built && (lazyIndicesEnabled == false || constructedIndices.contains(key) )) {
            removeDefiniteClauseByPredicate(key, definiteClause);
            removeDefiniteClauseByAllArgs(key, definiteClause);
            for (int i = 0; i < indexWidth && i < key.getArity(); i++) {
                removeDefiniteClauseByNthArg(i, key, definiteClause);
            }

            constructedIndices.remove(key);
        }
    }

    @Override
    public List<T> getPossibleMatchingAssertions(Literal clauseHead, BindingList currentBindings) {
        if (clauseHead != null) {
            List<T> set = null;

            PredicateNameAndArity pnaa = clauseHead.getPredicateNameAndArity();
            constructLazyIndexForPredicate(pnaa);

            // Short term, we are just going to apply the binding list to the clause head.
            Literal boundClauseHead = (clauseHead.isGrounded() || currentBindings == null) ? clauseHead : clauseHead.applyTheta(currentBindings.theta);

            set = lookupDefiniteClauseByAllArgs(boundClauseHead);
            if (set != null) {
                groundClauseHitCount++;
                return set;
            }
            else {
                List<T> aSet;

                int arity = clauseHead.numberArgs();

                if (arity >= 2) {
                    for (int i = 0; i < indexWidth && i < arity; i++) {
                        aSet = lookupDefiniteClausesByNthArgs(i, boundClauseHead);

                        if (aSet != null) {
                            singleGroundArgIndexHitCount[i]++;
                            if (set == null || aSet.size() < set.size()) {
                                set = aSet;
                            }
                        }
                    }
                }

                if (set != null) {
                    return set;
                }
                else {
                    set = lookupDefiniteClausesByPredicate(pnaa);
                    if (set != null && set.isEmpty() == false) {
                        predicateHitCount++;
                    }
                    return set;
                }
            }
        }

        return null;
    }

    @Override
    public List<T> getPossibleMatchingAssertions(PredicateName predicateName, int arity) {
        PredicateNameAndArity pnaa = new PredicateNameAndArity(predicateName, arity);

        constructLazyIndexForPredicate(pnaa);

        List<T> set = lookupDefiniteClausesByPredicate(pnaa);
        return set;
    }

    private void indexDefiniteClauseByNthArg(int indexedArgument, PredicateNameAndArity key, T sentence) {
        if (indexedArgument < indexWidth) {
            if (singleGroundArgIndexArray[indexedArgument] == null) {
                singleGroundArgIndexArray[indexedArgument] = new GroundNthArgumentClauseIndex(indexedArgument);
            }

            singleGroundArgIndexArray[indexedArgument].indexDefiniteClause(key, sentence);
        }
    }

    private void removeDefiniteClauseByNthArg(int indexedArgument, PredicateNameAndArity key, T sentence) {
        if (indexedArgument < indexWidth) {

            // We already checked that the PredicateNameAndArity indice was previously build.
            if (singleGroundArgIndexArray[indexedArgument] != null) {
                singleGroundArgIndexArray[indexedArgument].removeDefiniteClause(key, sentence);
            }
        }
    }

    private List<T> lookupDefiniteClausesByNthArgs(int indexedArgument, Literal literal) {

        // We already checked that the PredicateNameAndArity indice was previously build.

        if (singleGroundArgIndexArray[indexedArgument] != null) {
            singleGroundArgIndexLookupCount[indexedArgument]++;
            return singleGroundArgIndexArray[indexedArgument].lookupDefiniteClauses(literal);
        }

        return null;
    }

    private void indexDefiniteClauseByAllArgs(PredicateNameAndArity key, T sentence) {

        // We already checked that the PredicateNameAndArity should be indexed.

        if (groundClauseIndex == null) {
            groundClauseIndex = new GroundClauseIndex<T>();
        }

        groundClauseIndex.indexDefiniteClause(key, sentence);
    }

    private void removeDefiniteClauseByAllArgs(PredicateNameAndArity key, T sentence) {

        // We already checked that the PredicateNameAndArity indice was previously build.

        if (groundClauseIndex != null) {
            groundClauseIndex.removeDefiniteClause(key, sentence);
        }
    }

    private List<T> lookupDefiniteClauseByAllArgs(Literal literalToLookup) {

        // We already checked that the PredicateNameAndArity indice was previously build.

        if (groundClauseIndex != null && literalToLookup != null && literalToLookup.isGrounded()) {
            groundClauseLookupCount++;
            return groundClauseIndex.lookupDefiniteClauses(literalToLookup);
        }
        return null;
    }

    private void indexDefiniteClauseByPredicate(PredicateNameAndArity key, T sentence) {

        // We already checked that the PredicateNameAndArity should be indexed.

        if (predicateIndex == null) {
            predicateIndex = new PredicateIndex<T>();
        }

        predicateIndex.indexDefiniteClause(key, sentence);
    }

    private void removeDefiniteClauseByPredicate(PredicateNameAndArity key, T sentence) {

        // We already checked that the PredicateNameAndArity indice was previously build.

        if (predicateIndex != null) {
            predicateIndex.removeDefiniteClause(key, sentence);
        }
    }

    private List<T> lookupDefiniteClausesByPredicate(PredicateNameAndArity pnaa) {

        // We already checked that the PredicateNameAndArity indice was previously build.

        if (predicateIndex != null) {

            predicateLookupCount++;
            return predicateIndex.lookupDefiniteClause(pnaa);
        }

        return null;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("% DefaultHornClauseFactbaseIndexer:\n");
        sb.append("%   Indices built for ").append(constructedIndices.size()).append(" predicates.\n");
        for (int i = 0; i < indexWidth; i++) {
            sb.append(String.format("%%   Ground Argument %d  : Lookups = %d, Hits = %d, Efficiency = %.2f%%.\n", i, singleGroundArgIndexLookupCount[i], singleGroundArgIndexHitCount[i], 100.0 * singleGroundArgIndexHitCount[i] / singleGroundArgIndexLookupCount[i]));
        }

        sb.append(String.format("%%   All ground index    : Lookups = %d, Hits = %d, Efficiency = %.2f%%.\n", groundClauseLookupCount, groundClauseHitCount, 100.0 * groundClauseHitCount / groundClauseLookupCount));
        sb.append(String.format("%%   Predicates Index    : Lookups = %d, Hits = %d, Efficiency = %.2f%%.\n", predicateLookupCount, predicateHitCount, 100.0 * predicateHitCount / predicateLookupCount));

        return sb.toString();
    }

    public String toLongString() {
        StringBuilder sb = new StringBuilder();

        sb.append("DefaultHornClauseFactbaseIndexer:\n\n");

        sb.append("  Indices built for ").append(constructedIndices.size()).append(" predicates.\n");

        for (int i = 0; i < indexWidth; i++) {
            sb.append("GroundArgument ").append(i).append(" index:\n");
            sb.append(singleGroundArgIndexArray[i]);
            sb.append("\n\n");
        }

        sb.append("All argument ground index:\n");
        sb.append(groundClauseIndex);
        sb.append("\n\n");

        sb.append("Predicate index:\n");
        sb.append(predicateIndex);
        sb.append("\n\n");

        return sb.toString();
    }

    private void constructLazyIndexForPredicate(PredicateNameAndArity pnaa) {
        if ( lazyIndicesEnabled && constructedIndices.contains(pnaa) == false ) {

            constructedIndices.add(pnaa);

            Iterable<DefiniteClause> assertions = clausebase.getAssertions();

            for (DefiniteClause definiteClause : assertions) {
                if ( definiteClause.getDefiniteClauseHead().getPredicateNameAndArity().equals(pnaa) ) {
                    if ( elementClass.isInstance(definiteClause) ) {
                        indexAssertion((T)definiteClause);
                    }
                }
            }
        }
    }
}
