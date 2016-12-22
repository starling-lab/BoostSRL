/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.Utils.Utils;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

/** This is an index of definite clauses (either Clauses or Literal or a mix of both) with ground heads.
 *
 * @param <DefiniteClause> Type of object to be indexed.
 *
 * @author twalker
 */
public class LazyGroundClauseIndex {

    private HornClausebase clausebase;

    private static int maximumIndexSizeDefault = 150;
    private        int maximumIndexSize        = maximumIndexSizeDefault;
	public  static void setMaximumIndexSize(int maximumIndexSizeToUse) {
		maximumIndexSizeDefault = maximumIndexSizeToUse;
	}

	private int indicesConstructed = 0;

    private int indicesRemoved = 0;

    private Map<PredicateNameAndArity, Integer> indexBuilds;

    private Map<PredicateNameAndArity, Map<List<Term>, DefiniteClauseList>> definiteClausesAllArgsIndex = new LRUMap();

    /** Store clauses in which one or more of the args is not ground.
     *
     * This is used to as a starting place for new definiteClause lists indexed by the
     * all args.  This is necessary to make sure unseen term combinations
     * start with the unground clauses in their index.
     */
    private Map<PredicateNameAndArity, DefiniteClauseList> definiteClausesWithUngroundArgs = new HashMap<PredicateNameAndArity, DefiniteClauseList>();

    public LazyGroundClauseIndex(HornClausebase clausebase) {
    	maximumIndexSize = maximumIndexSizeDefault;
        this.clausebase = clausebase;
    }

    public void indexDefiniteClause(PredicateNameAndArity key, DefiniteClause definiteClause) {

        if (definiteClausesAllArgsIndex.containsKey(key)) {
            Literal headLiteral = definiteClause.getDefiniteClauseHead();

            Map<List<Term>, DefiniteClauseList> mapForKey = definiteClausesAllArgsIndex.get(key);
            if (mapForKey == null) {
                mapForKey = new HashMap<List<Term>, DefiniteClauseList>();
                definiteClausesAllArgsIndex.put(key, mapForKey);

                if (LazyHornClausebase.DEBUG >= -2) { // Changed by JWS.
                    Utils.println("% [ LazyGroundClauseIndex ]  Creating ground clause index for " + key + ".");
                }
            }

            if (headLiteral.isGrounded()) {

                if (LazyHornClausebase.DEBUG >= 2) {
                    Utils.println("% [ LazyGroundClauseIndex ]  Indexing ground clause " + definiteClause + ".");
                }

                DefiniteClauseList definiteClauseList = mapForKey.get(headLiteral.getArguments());

                if (definiteClauseList == null) {
                    definiteClauseList = new DefiniteClauseList(getDefiniteClausesSeedList(key));
                    mapForKey.put(headLiteral.getArguments(), definiteClauseList);
                }

                definiteClauseList.add(definiteClause);
            }
            else {

                if (LazyHornClausebase.DEBUG >= 2) {
                    Utils.println("% [ LazyGroundClauseIndex ]  Indexing non-ground clause " + definiteClause + ".");
                }

                // This is an non-ground literal, so we just need to throw into all of the appropriate
                // places was well as the seed list.
                for (DefiniteClauseList list : mapForKey.values()) {
                    list.add(definiteClause);
                }

                addDefiniteClausesSeedDefiniteClause(key, definiteClause);
            }
        }

    }

    public void removeDefiniteClause(PredicateNameAndArity key, DefiniteClause definiteClause) {

        if (definiteClausesAllArgsIndex.containsKey(key)) {
            Literal headLiteral = definiteClause.getDefiniteClauseHead();

            if (definiteClausesAllArgsIndex != null) {
                Map<List<Term>, DefiniteClauseList> mapForKey = definiteClausesAllArgsIndex.get(key);
                if (mapForKey != null) {

                    if (headLiteral.isGrounded()) {
                        DefiniteClauseList definiteClauseList = mapForKey.get(headLiteral.getArguments());

                        if (definiteClauseList != null) {
                            definiteClauseList.remove(definiteClause);
                        }

                        if (definiteClauseList.isEmpty()) {
                            mapForKey.remove(headLiteral.getArguments());
                        }
                    }
                    else {
                        // This is an non-ground literal, so we just need to throw into all of the appropriate
                        // places was well as the seed list.
                        for (DefiniteClauseList list : mapForKey.values()) {
                            list.remove(definiteClause);
                        }

                        removeDefiniteClausesSeedDefiniteClause(key, definiteClause);
                    }
                }
            }
        }
    }

    public DefiniteClauseList lookupDefiniteClauses(Literal lookupLiteral) {
        if (definiteClausesAllArgsIndex != null && lookupLiteral != null && lookupLiteral.isGrounded()) {
            PredicateNameAndArity key = lookupLiteral.getPredicateNameAndArity();
            Map<List<Term>, DefiniteClauseList> mapForKey = definiteClausesAllArgsIndex.get(key);


            if (mapForKey == null) {
                // We haven't had DefiniteClause build the index for this guy yet...we should probably do that.
                mapForKey = buildIndexForKey(key);
            }

            if (mapForKey != null) {
                DefiniteClauseList definiteClauseList = mapForKey.get(lookupLiteral.getArguments());

                // If we got this far, than we know that the predicate/arity does have entries.
                // So, if definiteClauseList is null, then there must be no completions and we
                // should return an empty list.
                if (definiteClauseList == null) {
                    return getDefiniteClausesSeedList(key);
                }
                else {
                    return definiteClauseList;
                }
            }
        }

        return null;
    }

    private DefiniteClauseList getDefiniteClausesSeedList(PredicateNameAndArity key) {

        DefiniteClauseList definiteClausesForKey = definiteClausesWithUngroundArgs.get(key);
        if (definiteClausesForKey != null) {
            return definiteClausesForKey;
        }
        else {
            DefiniteClauseList emptyList = new DefiniteClauseList();
            return emptyList;
        }
    }

    private void addDefiniteClausesSeedDefiniteClause(PredicateNameAndArity key, DefiniteClause definiteClause) {
        DefiniteClauseList definiteClausesForKey = definiteClausesWithUngroundArgs.get(key);

        if (definiteClausesForKey == null) {
            definiteClausesForKey = new DefiniteClauseList();
            definiteClausesWithUngroundArgs.put(key, definiteClausesForKey);
        }

        definiteClausesForKey.add(definiteClause);
    }

    private void removeDefiniteClausesSeedDefiniteClause(PredicateNameAndArity key, DefiniteClause definiteClause) {
        DefiniteClauseList definiteClausesForKey = definiteClausesWithUngroundArgs.get(key);

        if (definiteClausesForKey != null) {
            definiteClausesForKey.remove(definiteClause);

            if (definiteClausesForKey.isEmpty()) {
                definiteClausesWithUngroundArgs.remove(key);
            }
        }
    }

    @Override
    public String toString() {
        StringBuilder stringBuilder = new StringBuilder();

        stringBuilder.append("LazyGroundClauseIndex:\n");
        stringBuilder.append("  maximumIndexSize  : ").append(maximumIndexSize).append(".\n");
        stringBuilder.append("  currentIndexSize  : ").append(definiteClausesAllArgsIndex.size()).append(".\n");
        stringBuilder.append("  indicesConstructed: ").append(indicesConstructed).append(".\n");
        stringBuilder.append("  indicesRemoved    : ").append(indicesRemoved).append(".\n");

        if (indexBuilds != null) {
            int total = 0;
            for (Map.Entry<PredicateNameAndArity, Integer> entry : indexBuilds.entrySet()) {
                stringBuilder.append("IndexBuilt: ").append(entry.getKey()).append(", count = ").append(entry.getValue()).append(".\n");
                total += entry.getValue();
            }

            stringBuilder.append("Average indexBuilds per predicate = ").append((double) total / indexBuilds.size()).append(".");
        }

        return stringBuilder.toString();
    }

    public String toLongString() {
        StringBuilder sb = new StringBuilder();

        for (Map.Entry<PredicateNameAndArity, Map<List<Term>, DefiniteClauseList>> entry : definiteClausesAllArgsIndex.entrySet()) {


            sb.append("  ").append(entry.getKey()).append(":\n");
            for (Map.Entry<List<Term>, DefiniteClauseList> entry1 : entry.getValue().entrySet()) {
                sb.append("    ").append(entry1.getKey()).append(":\n");

                for (DefiniteClause definiteClause : entry1.getValue()) {
                    sb.append("      ").append(definiteClause).append(".\n");
                }
            }
            sb.append("\n");
        }

        return sb.toString();
    }

    private Map<List<Term>, DefiniteClauseList> buildIndexForKey(PredicateNameAndArity key) {
        if (definiteClausesAllArgsIndex.containsKey(key)) {
            throw new IllegalStateException("LazyGroundClauseIndex.buildIndexForKey(): Predicate " + key + " already indexed.");
        }




        indicesConstructed++;

        if (LazyHornClausebase.DEBUG >= 1) {
            if (indexBuilds == null) {
                indexBuilds = new HashMap<PredicateNameAndArity, Integer>();
            }

            Integer count = indexBuilds.get(key);
            indexBuilds.put(key, count == null ? 1 : count + 1);
        }

        MapOfDefiniteClauseLists assertions = clausebase.getAssertionsMap();
        DefiniteClauseList clauses = assertions.getValues(key);

        Map<List<Term>, DefiniteClauseList> mapForKey = null;

        if (clauses == null) {
            // Not sure what we should do here...this
            // is an index build for a predicate that doesn't exist in
            // the clausebase.
            //
            // One option would be to add a marker indicating there are no expansions.
            // Another would be to assume that the upper level of indexing detected this
            // this situation and didn't attempt to pass it down to here.
        }
        else {

            if (LazyHornClausebase.DEBUG >= -2) { // Changed by JWS.
                Utils.println("% [ LazyGroundClauseIndex ]  Building full index for " + key + " with " + Utils.comma(clauses) + " assertions.");
            }

            if (LazyHornClausebase.DEBUG >= 1) {
                mapForKey = new DebuggingHashMap<List<Term>, DefiniteClauseList>((int) Math.max(16, clauses.size() / 0.75 + 10), "LazyGroundClauseIndex:" + key, LazyHornClausebase.DEBUG);
            }
            else {
                mapForKey = new HashMap<List<Term>, DefiniteClauseList>((int) Math.max(16, clauses.size() / 0.75 + 10));
            }

            for (DefiniteClause definiteClause : clauses) {
                Literal headLiteral = definiteClause.getDefiniteClauseHead();

                if (headLiteral.isGrounded()) {
                    DefiniteClauseList definiteClauseList = mapForKey.get(headLiteral.getArguments());

                    if (definiteClauseList == null) {
                        definiteClauseList = new DefiniteClauseList(getDefiniteClausesSeedList(key));
                        mapForKey.put(headLiteral.getArguments(), definiteClauseList);
                    }

                    definiteClauseList.add(definiteClause);
                }
                else {
                    // This is an non-ground literal, so we just need to throw into all of the appropriate
                    // places was well as the seed list.
                    for (DefiniteClauseList list : mapForKey.values()) {
                        list.add(definiteClause);
                    }

                    addDefiniteClausesSeedDefiniteClause(key, definiteClause);
                }
            }

            definiteClausesAllArgsIndex.put(key, mapForKey);

        }


        return mapForKey;
    }

    private class LRUMap extends LinkedHashMap<PredicateNameAndArity, Map<List<Term>, DefiniteClauseList>> {

    //	protected boolean useJWSvariant = true;
    	
    	protected boolean removeEldestEntry(Map.Entry<PredicateNameAndArity, Map<List<Term>, DefiniteClauseList>> eldest) {     	
        	
            if (size() > maximumIndexSize) {          	
/*
            	if (useJWSvariant && maximumIndexSize > 8) {
            		// Remove the SMALLEST item in the OLDEST QUARTER (?).
            		int smallestSize = Integer.MAX_VALUE;
            		Map.Entry<PredicateNameAndArity, Map<List<Term>, DefiniteClauseList>> removeMe = null;
            		
            		for (int i = 0; i < maximumIndexSize / 4; i++) {
            			Map.Entry<PredicateNameAndArity, Map<List<Term>, DefiniteClauseList>> ithOldest     = this;
            			int                                                                   ithOldestSize = ithOldest.getValue().keySet().size();
            			if (ithOldestSize < smallestSize) {
            				smallestSize = ithOldestSize;
            				removeMe = ithOldest;
            			}
            		}
                    definiteClausesWithUngroundArgs.remove(removeMe.getKey());
                    indicesRemoved++;
                    return true;
            	}
*/
                definiteClausesWithUngroundArgs.remove(eldest.getKey());
                indicesRemoved++;
                return true;
            }
            else {
                return false;
            }
        }
    }
}
