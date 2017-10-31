/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.BindingList;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.SLDQuery;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;
import edu.wisc.cs.will.stdAIsearch.SearchResult;

/**
 *
 * @author twalker
 */
public class DefaultProof implements Proof {

    private HornClausebase clausebase;
    private HandleFOPCstrings stringHandler;
    private HornClauseProver prover;
    
    private SearchResult searchResult = null;

    public DefaultProof(HornClauseContext context, SLDQuery query) {
        this(context.getClausebase(), query);
    }

    public DefaultProof(HornClausebase clausebase, SLDQuery query) {
        setupProver(clausebase);

        setQuery(query);
    }

    private void setupProver(HornClausebase clausebase) {
        this.clausebase = clausebase;
        this.stringHandler = clausebase.getStringHandler();
        this.prover = new HornClauseProver(stringHandler, this.clausebase, true);
    }

    private void setQuery(SLDQuery query) {
        prover.initialize(query);
    }

    public BindingList prove()  {
        try {
            if ( isProofComplete() == false ) {
                searchResult = prover.continueSearch(true);

                if ( searchResult.goalFound() ) {
                    return new BindingList(((ProofDone) prover.terminator).collectQueryBindings());
                }
            }
        }
        catch ( SearchInterrupted si) {
            
        }
        
        return null;
        
    }

    public BindingList getBindings() {
        if ( searchResult == null ) {
            prove();
        }

        if ( searchResult.goalFound() ) {
            return new BindingList(((ProofDone) prover.terminator).collectQueryBindings());
        }
        else {
            return null;
        }
    }

    public boolean isProofComplete() {
        if ( searchResult == null ) {
            return false;
        }
        else {
            return searchResult.goalFound() == false || prover.open.isEmpty();
        }
    }

    public boolean isTrue() {
        if ( searchResult == null ) {
            prove();
        }

        return searchResult.goalFound();
    }

    public HornClauseProver getProver() {
        return prover;
    }




}
