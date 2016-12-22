/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.Utils.Utils;
import java.util.Collection;

/**
 *
 * @author twalker
 */
public class LazyHornClausebaseIndexer implements HornClausebaseIndexer<DefiniteClause>{

  private HornClausebase clausebase;

    /** Stores the class of DefiniteClause.
     *
     * Since java generics do not store the actual class of DefiniteClause,
     * we need to do this by hand, since we need it later.
     */
    private Class<DefiniteClause> elementClass = DefiniteClause.class;

    /** The number of arguments that should be index.
     *
     */
    private int indexWidth;

    private LazyGroundNthArgumentClauseIndex[] singleGroundArgIndexArray = null;

    private LazyGroundClauseIndex groundClauseIndex = null;

    private PredicateIndex<DefiniteClause> predicateIndex = null;

    private long[] singleGroundArgIndexLookupCount = null;

    private long groundClauseLookupCount = 0;

    private long predicateLookupCount = 0;

    private long[] singleGroundArgIndexHitCount = null;

    private long groundClauseHitCount = 0;

    private long predicateHitCount = 0;

    public LazyHornClausebaseIndexer(HornClausebase clausebase) {
        this(clausebase, 2);
    }

    public LazyHornClausebaseIndexer(HornClausebase clausebase, int indexWidth) {
        this.clausebase = clausebase;
        this.indexWidth = indexWidth;
        resetIndex();
    }

    @Override
    public final void resetIndex() {
    	if (singleGroundArgIndexArray != null) { // Added by JWS to get a glimpse of how often this is happening.
    		System.out.println("\nResetting the LazyGroundNthArgumentClauseIndex.");
    	}
        singleGroundArgIndexArray = new LazyGroundNthArgumentClauseIndex[indexWidth];

        for (int indexedArgument = 0; indexedArgument < indexWidth; indexedArgument++) {
                singleGroundArgIndexArray[indexedArgument] = new LazyGroundNthArgumentClauseIndex(clausebase, indexedArgument);
        }
        
        predicateIndex = new PredicateIndex<DefiniteClause>();
        groundClauseIndex = new LazyGroundClauseIndex(clausebase);

        singleGroundArgIndexLookupCount = new long[indexWidth];
        groundClauseLookupCount = 0;
        predicateLookupCount = 0;

        singleGroundArgIndexHitCount = new long[indexWidth];
        groundClauseHitCount = 0;
        predicateHitCount = 0;
    }

    @Override
    public boolean isBuilt() {
        return true;
    }

    @Override
    public void buildIndex(Collection<? extends DefiniteClause> clauses) {
        // We are lazy, so wait for it!
    }

    @Override
    public void indexAssertion(DefiniteClause definiteClause) {

        if (definiteClause != null && definiteClause.isDefiniteClause()) {
            
            if ( LazyHornClausebase.DEBUG >= 3 ) Utils.println("% [ LazyHornClausebaseIndexer ]  Indexing " + definiteClause + ".");

            PredicateNameAndArity key = new PredicateNameAndArity(definiteClause);

            // Even though we are lazy, we still need to notify the subindices that
            // new clauses came along, just in case they have indexed that predicate
            // already.

            indexDefiniteClauseByPredicate(key, definiteClause);
            indexDefiniteClauseByAllArgs(key, definiteClause);
            for (int i = 0; i < indexWidth && i < key.getArity(); i++) {
                indexDefiniteClauseByNthArg(i, key, definiteClause);
            }
            
        }
    }

    @Override
    public void removeAssertion(DefiniteClause definiteClause) {

        PredicateNameAndArity key = new PredicateNameAndArity(definiteClause);

        removeDefiniteClauseByPredicate(key, definiteClause);
        removeDefiniteClauseByAllArgs(key, definiteClause);
        for (int i = 0; i < indexWidth && i < key.getArity(); i++) {
            removeDefiniteClauseByNthArg(i, key, definiteClause);
        }
    }

    @Override
    public DefiniteClauseList getPossibleMatchingAssertions(Literal clauseHead, BindingList currentBindings) {
        if (clauseHead != null) {
            DefiniteClauseList set = null;

            PredicateNameAndArity pnaa = clauseHead.getPredicateNameAndArity();

            if ( clausebase.getAssertionsMap().containsKey(pnaa) == false ) {
                // Fast fail for predicates that don't exist in the clausebase.
                // We might want to move this into the clausebase itself...
                return null;
            }

            // Short term, we are just going to apply the binding list to the clause head.
            Literal boundClauseHead = (clauseHead.isGrounded() || currentBindings == null) ? clauseHead : clauseHead.applyTheta(currentBindings.theta);

            set = lookupDefiniteClauseByAllArgs(boundClauseHead);
            if (set != null) {
                groundClauseHitCount++;
                return set;
            }
            else {
                DefiniteClauseList aSet;

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
    public DefiniteClauseList getPossibleMatchingAssertions(PredicateName predicateName, int arity) {
        PredicateNameAndArity pnaa = new PredicateNameAndArity(predicateName, arity);

        DefiniteClauseList set = lookupDefiniteClausesByPredicate(pnaa);
        return set;
    }

    private void indexDefiniteClauseByNthArg(int indexedArgument, PredicateNameAndArity key, DefiniteClause sentence) {
        if (indexedArgument < indexWidth) {
            singleGroundArgIndexArray[indexedArgument].indexDefiniteClause(key, sentence);
        }
    }

    private void removeDefiniteClauseByNthArg(int indexedArgument, PredicateNameAndArity key, DefiniteClause sentence) {
        if (indexedArgument < indexWidth) {

            // We already checked that the PredicateNameAndArity indice was previously build.
            if (singleGroundArgIndexArray[indexedArgument] != null) {
                singleGroundArgIndexArray[indexedArgument].removeDefiniteClause(key, sentence);
            }
        }
    }

    private DefiniteClauseList lookupDefiniteClausesByNthArgs(int indexedArgument, Literal literal) {

        // We already checked that the PredicateNameAndArity indice was previously build.

        if (singleGroundArgIndexArray[indexedArgument] != null) {
            singleGroundArgIndexLookupCount[indexedArgument]++;
            return singleGroundArgIndexArray[indexedArgument].lookupDefiniteClauses(literal);
        }

        return null;
    }

    private void indexDefiniteClauseByAllArgs(PredicateNameAndArity key, DefiniteClause sentence) {


        groundClauseIndex.indexDefiniteClause(key, sentence);
    }

    private void removeDefiniteClauseByAllArgs(PredicateNameAndArity key, DefiniteClause sentence) {

        // We already checked that the PredicateNameAndArity indice was previously build.

        if (groundClauseIndex != null) {
            groundClauseIndex.removeDefiniteClause(key, sentence);
        }
    }

    private DefiniteClauseList lookupDefiniteClauseByAllArgs(Literal literalToLookup) {

        // We already checked that the PredicateNameAndArity indice was previously build.

        if (groundClauseIndex != null && literalToLookup != null && literalToLookup.isGrounded()) {
            groundClauseLookupCount++;
            return groundClauseIndex.lookupDefiniteClauses(literalToLookup);
        }
        return null;
    }

    private void indexDefiniteClauseByPredicate(PredicateNameAndArity key, DefiniteClause sentence) {

        // We already checked that the PredicateNameAndArity should be indexed.

        

        //predicateIndex.indexDefiniteClause(key, sentence);
    }

    private void removeDefiniteClauseByPredicate(PredicateNameAndArity key, DefiniteClause sentence) {

        // We already checked that the PredicateNameAndArity indice was previously build.

        if (predicateIndex != null) {
            predicateIndex.removeDefiniteClause(key, sentence);
        }
    }

    private DefiniteClauseList lookupDefiniteClausesByPredicate(PredicateNameAndArity pnaa) {

        // We already checked that the PredicateNameAndArity indice was previously build.

        if (predicateIndex != null) {

            predicateLookupCount++;
            //return predicateIndex.lookupDefiniteClause(pnaa);
            return clausebase.getAssertionsMap().getValues(pnaa);
        }

        return null;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("% DefaultHornClauseFactbaseIndexer:\n");
        for (int i = 0; i < indexWidth; i++) {
            sb.append(String.format("%%   Ground Argument %d  : Lookups = %d, Hits = %d, Efficiency = %.2f%%.\n", i, singleGroundArgIndexLookupCount[i], singleGroundArgIndexHitCount[i], 100.0 * singleGroundArgIndexHitCount[i] / singleGroundArgIndexLookupCount[i]));
        }

        sb.append(String.format("%%   All ground index    : Lookups = %d, Hits = %d, Efficiency = %.2f%%.\n", groundClauseLookupCount, groundClauseHitCount, 100.0 * groundClauseHitCount / groundClauseLookupCount));
        sb.append(String.format("%%   Predicates Index    : Lookups = %d, Hits = %d, Efficiency = %.2f%%.\n", predicateLookupCount, predicateHitCount, 100.0 * predicateHitCount / predicateLookupCount));

        if ( groundClauseIndex != null ) sb.append(groundClauseIndex.toString());
        for (int i = 0; i < singleGroundArgIndexArray.length; i++) {
            LazyGroundNthArgumentClauseIndex lazyGroundNthArgumentClauseIndex = singleGroundArgIndexArray[i];
            if ( lazyGroundNthArgumentClauseIndex != null ) sb.append(lazyGroundNthArgumentClauseIndex);
        }

        return sb.toString();
    }

    public String toLongString() {
        StringBuilder sb = new StringBuilder();

        sb.append("DefaultHornClauseFactbaseIndexer:\n\n");

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
}
