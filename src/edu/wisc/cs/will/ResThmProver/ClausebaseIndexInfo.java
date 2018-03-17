/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ResThmProver;

import edu.wisc.cs.will.FOPC.PredicateNameAndArity;

/**
 *
 * @author twalker
 */
public class ClausebaseIndexInfo {
    
    private final PredicateNameAndArity predicate;

    private final String indexName;

    private int buildCount = 0;

    private long lastBuildTime;

    public ClausebaseIndexInfo(PredicateNameAndArity predicate, String indexName) {
        this.predicate = predicate;
        this.indexName = indexName;
    }

    public int getBuildCount() {
        return buildCount;
    }

    public void setBuildCount(int buildCount) {
        this.buildCount = buildCount;
    }

    public String getIndexName() {
        return indexName;
    }

    public long getLastBuildTime() {
        return lastBuildTime;
    }

    public void setLastBuildTime(long lastBuildTime) {
        this.lastBuildTime = lastBuildTime;
    }

    public PredicateNameAndArity getPredicate() {
        return predicate;
    }

    

}
