package edu.wisc.cs.will.stdAIsearch;

import java.util.List;

import edu.wisc.cs.will.Utils.Utils;


// TODO sampling search (eg, walksat)
// TODO how would the case of using a small dataset during initial clause generation work, with a larger one later?  look at nodesExplored, etc.
// TODO implement code for dealing with CLOSED (ie, how to do equals)
// TODO implement iterativeDeepening that works with ANY search

/**
 * The specification of a state-based search task.
 * 
 * @param <T> Class of the search nodes.
 * @author shavlik
 */
public class StateBasedSearchTask<T extends SearchNode> {
	public String taskName = "unnamedTask"; // Used in println's to clarify which task is being discussed.
    /**
     * The search strategy used to carry out this search task. One of
     * best-first, depth-first, breadth-first, random, etc.
     */
    public SearchStrategy strategy;

    /**
     * Used by best-first search to score nodes.
     */
    public ScoringFunction scorer;

    /**
     * Generates the children of the current search node and adds new ones to
     * the open list.
     */
    public ChildrenNodeGenerator<T> childrenGenerator;

    /**
     * Initializes the open list.
     */
    public Initializer initializer;

    /**
     * Controls the termination (satisfaction) of the search.
     */
    public EndTest terminator;

    /**
     * The list of nodes yet to examine in the search. Keeps track of the nodes
     * in the search space that have been generated but not yet explored.
     */
    public OpenList<T> open;

    /**
     * The list of nodes already examined in the search. Keeps track of nodes
     * already visited, to prevent infinite loops (optional).
     */
    public ClosedList closed;
    /**
     * If true, add nodes to CLOSED when created, not when EXPANDED 
     * (this will prevent duplicates in OPEN, but if OPEN is pruned, might lose some later nodes
     * would be added to OPEN if this is set to false).
     * Also, if true, CLOSED will be bigger than it otherwise would.
     */
    public boolean    addNodesToClosedListWhenCreated = true;

    /**
     * The job of this class is to "watch" the search and determine what should
     * be returned at the end.
     */
    public SearchMonitor searchMonitor;

    /**
     * If all the info is in a node, don't need a full-fledged searchMonitor.
     * Can simply access this after the search completes successfully.
     */
    public T lastNodeVisited;

    /** Stores the best node encountered so far, including ineligible nodes.
     *
     */
    public SearchNode bestNodeVisited;

    /**
     * Whether to stop the search after a certain number of nodes have been
     * generated and examined. Some searches (e.g., A*) need to continue popping
     * nodes until OPEN is empty. The default is true.
     */
    public boolean stopWhenMaxNodesCreatedReached = true;

    /**
     * Whether to stop this iteration after a certain number of nodes have been
     * generated and examined. The default is true.
     */
    public boolean stopWhenMaxNodesCreatedThisIterationReached = true;

    /**
     * Allow a max on the number of nodes POPPED from OPEN (non-positive values mean
     * infinity). The default is no limit.
     */
    public int maxNodesToConsider = -1;

    /**
     * Allow a max on the number of nodes CREATED (non-pos values mean
     * infinity). The default is no limit.
     */
    public int maxNodesToCreate = -1;

    /**
     * Allow a max depth to the search space. The default is
     * java.lang.Integer.MAX_VALUE. (I (JWS) could use -1 to mean infinity, but
     * if this value is actually reached, something has presumably gone wrong.)
     */
    public int maxSearchDepth = java.lang.Integer.MAX_VALUE;

    /**
     * The number of nodes in the beam (open list) in a beam search. If not a
     * positive value, assume no limit on size of open list. The default is -1.
     */
    public int beamWidth = -1;

    /**
     * The minimum score acceptable when using a scoring function. Only used IF
     * A SCORING FUNCTION is being used. Nodes wont be added to OPEN unless they
     * score high enough. The default is negative infinity.
     */
    public double minAcceptableScore = Double.NEGATIVE_INFINITY;

    /**
     * Unsure what this is exactly. Only used IF A SCORING FUNCTION is being
     * used. The default is true.
     */
    public boolean allowToTieMinAcceptableScore = true;

    /**
     * When sorting items into OPEN based on their score, do new items with
     * scores that tie scores of old items, go in front? The default is false.
     */
    public boolean inOpenListPutNewTiesInFront = false;

    /**
     * If true, indicates that iterative deepening should be used up to
     * maxSearchDepth. The default is false.
     */
    public boolean useIterativeDeepeningDepth = false;

    /**
     * Controls whether the search continues or stops. The default is true.
     */
    public boolean continueTheSearch = true;

    /**
     * Allow, per iterative-deepening cycle or in a random-sampling search that
     * does some local heuristic search, a max on the number of nodes POPPED
     * from OPEN (non-pos values mean infinity). The default is -1.
     */
    public int maxNodesToConsiderPerIteration = -1;

    /**
     * Allow, per iterative-deepening cycle or in a random-sampling search that
     * does some local heuristic search, a max on the number of nodes CREATED
     * (non-pos values mean infinity). The default is -1.
     */
    public int maxNodesToCreatePerIteration = -1;

    /**
     * If 0, no comments. 
     * If verbosity=1, minimal comments. 
     * If verbosity=2, moderate comments. 
     * If verbosity=3, many comments. 
     * If verbosity>3, maximal comments. 
     * The default is 0.
     */
    // TODO replace with log4j
    public int verbosity = 0;

    /**
     * The count of how many nodes have been examined.
     */
    protected int nodesConsidered = 0;

    /**
     * The count of how many nodes have been generated.
     */
    protected int nodesCreated = 0;

    /**
     * The count of how many nodes have been examined this iteration.
     */
    protected int nodesConsideredThisIteration = 0;

    /**
     * The count of how many nodes have been generated this iteration.
     */
    protected int nodesCreatedThisIteration = 0;

    protected long maximumClockTimePerIterationInMillisec = Integer.MAX_VALUE; // Units are milliseconds.

    protected long iterationStartTimeInMillisec = -1;

    protected boolean initialized = false;

    /** If true, the open list is not cleared at the end of a search.
     *
     * Since the open list is not cleared, it is possible to continue the
     * search after an answer is found via the continueSearch() method.
     */
    protected boolean redoable = false;
    
    
    /**
	 * @return the redoable
	 */
	public boolean isRedoable() {
		return redoable;
	}

	/**
	 * @param redoable the redoable to set
	 */
	public void setRedoable(boolean redoable) {
		this.redoable = redoable;
	}

	public    boolean      discardIfBestPossibleScoreOfNodeLessThanBestSeenSoFar = false; // If true, do a branch-and-bound search.
    protected double       bestScoreSeenSoFar                                    = Double.NEGATIVE_INFINITY;
    protected T   nodeWithBestScore                                     = null; // The search monitor's job is to return the best answer.  This variable is only used for reporting purposes.
    public    int          nodesNotAddedToOPENsinceMaxScoreTooLow                = 0;
    public    int          nodesRemovedFromOPENsinceMaxScoreNowTooLow            = 0;
	
    /**
     * Default constructor. Does nothing.
     */
    public StateBasedSearchTask() {
    }

    /**
     * Initializes this state-based search task.
     * 
     * @param initializer
     *                The creator of the open list.
     * @param terminator
     *                The controller of search termination/satisfaction.
     *                Optional (may be null).
     * @param searchMonitor
     *                The monitor of the search. Optional (may be null). If
     *                null, a search monitor is created.
     * @param strategy
     *                How to search. Optional (may be null). If null, a
     *                best-first search is created.
     * @param scorer
     *                The scoring function. Optional (may be null).
     * @param childrenGenerator
     *                The generator of the successor search nodes.
     * @param closed
     *                The list of nodes already searched. Optional (may be
     *                null).
     */
    public void initalizeStateBasedSearchTask(Initializer initializer,
            								  EndTest terminator, SearchMonitor searchMonitor,
            								  SearchStrategy strategy, ScoringFunction scorer,
            								  ChildrenNodeGenerator childrenGenerator, ClosedList closed) {
        // TODO convert errors to exceptions

        // First create defaults if necessary and where possible.  Otherwise complain if something is mandatory.
        if (strategy == null) {
            strategy = new BreadthFirstSearch();
            Utils.waitHere("Breadth-first search being used since no search strategy was provided.");
        }
        if (searchMonitor == null) {
            searchMonitor = new SearchMonitor(this);
        }
        if (initializer == null) {
            Utils.error("A method that initiates OPEN must be provided to initalizeStateBasedSearchTask().");
        }
        if (childrenGenerator == null) {
            Utils.error("A method that generates child nodes must be provided to initalizeStateBasedSearchTask().");
        }

        this.initializer        = initializer;
        this.terminator        = terminator;
        this.searchMonitor     = searchMonitor;
        this.strategy          = strategy;
        this.scorer            = scorer;
        this.childrenGenerator = childrenGenerator;
        this.closed            = closed;

        initializer.setSearchTask(this);
        if (terminator != null) { terminator.setSearchTask(this); } // It isn't required there be a terminator (eg, max nodes might terminate the search).
        searchMonitor.setSearchTask(this);
        strategy.setSearchTask(this);
        if (scorer != null) { scorer.setSearchTask(this); } // It isn't required that there be a node-scorer.
        childrenGenerator.setSearchTask(this);
        if (closed != null) { closed.setSearchTask(this); } // It isn't required that there be a closed list.

        if (open == null) { open = new OpenList(this); }
    }
    
    /**
     * Clears and resets basic search information such as counters.
     * 
     * @param withinInterativeDeepening
     *                Whether the search is currently doing iterative deepening.
     */
    public void clearAnySavedBasicSearchInformation(boolean withinInterativeDeepening) {
        if (withinInterativeDeepening) {
            nodesConsideredThisIteration = 0;
            nodesCreatedThisIteration    = 0;
        }
        else {
            nodesConsidered = 0; // Clear some counters, etc.
            nodesCreated    = 0;
            lastNodeVisited = null; // Allow this to persist across iterative deep. in case a future use arises.

            bestScoreSeenSoFar = Double.NEGATIVE_INFINITY;
            nodeWithBestScore  = null;
            nodesNotAddedToOPENsinceMaxScoreTooLow     = 0;
            nodesRemovedFromOPENsinceMaxScoreNowTooLow = 0;

        }
        continueTheSearch = true;
    }

    /**
     * Clears saved search information. Does nothing.
     * 
     * @param withinInterativeDeepening
     *                Whether the search is currently doing iterative deepening.
     */
    public void clearAnySavedInformation(boolean withinInterativeDeepening) {
        return;
    }

    /**
     * Some applications built on top of this general search algorithm might be
     * extra "markers" of various sorts in OPEN. This method allows them to
     * cleanup OPEN should they wish to do so. Does nothing.
     */
    public void cleanOpen() {
        return;
    }


    /** Resets the search space completely, including the open and closed list.
     *
     * This method resets the complete search state.  If you are doing iterative deepening
     * or rrr, you probably don't want to use this.  Use the somewhat confusingly named resetAll
     * which leaves the open and closed lists intact.
     */
    public void resetAllForReal() {
        resetAll(false);
        clearClosedList(false);
        clearOpenList(false);
        
        //if (open   != null) {open.reportOpenSize();     }
        //if (closed != null) {closed.reportClosedSize(); }
    }
    
    public void clearOpenList(boolean withinInterativeDeepening) {
    	if (open != null) {
            open.clear();
        }
    }

    private void initialize() throws SearchInterrupted {
        if (initialized == false) {
            if (closed != null) {
                closed.emptyClosedList();
            } // Should we allow closed lists to persist across multiple iterations?  Generally won't want to do so.  Hence another boolean would be needed.
            if (open == null) {
                open = new OpenList(this);
            }
            initializer.initializeOpen(open); // Do this AFTER clearing CLOSED.
            initialized = true;
        }
    }
    
    public void clearClosedList(boolean withinInterativeDeepening) {
        if (closed != null) {
            closed.clearAnySavedInformation(withinInterativeDeepening);
            closed.emptyClosedList();
        }   	
    }
    

    /**
     * Resets all the search state.
     * 
     * @param withinInterativeDeepening
     *                Whether the search is currently doing iterative deepening.
     */
    private void resetAll(boolean withinInterativeDeepening) {
        clearAnySavedBasicSearchInformation(withinInterativeDeepening); // Explicitly call this rather than counting on subclasses to call super().
        clearAnySavedInformation(withinInterativeDeepening);
        if (initializer       != null) { searchMonitor.clearAnySavedInformation(withinInterativeDeepening); } // Clear any remnants of any previous searches.
        if (terminator        != null) { terminator.clearAnySavedInformation(withinInterativeDeepening);    }
        if (searchMonitor     != null) { searchMonitor.clearAnySavedInformation(withinInterativeDeepening); }
        if (strategy          != null) { strategy.clearAnySavedInformation(withinInterativeDeepening);      }
        if (scorer            != null) { scorer.clearAnySavedInformation(withinInterativeDeepening);        }
        if (childrenGenerator != null) { childrenGenerator.clearAnySavedInformation(withinInterativeDeepening); }

        initialized = false;
    }

    /**
     * Conducts the search specified by this search task. All the search state
     * is reset before the search begins.
     * 
     * @return The result of the search.
     * @throws SearchInterrupted
     *                 If the search was interrupted.
     */
    public SearchResult performSearch() throws SearchInterrupted {
        
        resetAll(false);
        
        if (useIterativeDeepeningDepth) { // to do: should max nodes by PER iter. deep. run?  Probably, but then too many params?
            int holdMaxSearchDepth = maxSearchDepth;
            boolean goalFound = false;
            SearchResult result = null;

            maxSearchDepth = 0;
            while (!goalFound && maxSearchDepth < holdMaxSearchDepth) {
                resetAll(true);
                result = performSearchIteration();
                if (result.goalFound()) { goalFound = true; }
                maxSearchDepth++;
            }
            maxSearchDepth = holdMaxSearchDepth;
            return result;
        }
		if (open == null) {
		    open = new OpenList(this);
		    initializer.initializeOpen(open);
		} // Do this here so that 'verbosity' can be set before OPEN is created.

		maxNodesToConsiderPerIteration = -1; // Don't want these playing a role in a non-iterative search.
		maxNodesToCreatePerIteration   = -1; // Don't want these playing a role in a non-iterative search.
		
		return performSearchIteration();
    }

    /** Continues a search that previously returned an answer.
     *
     * This requires that redoable be set to true and that there
     * are additional valid solutions to the search.
     *
     * @return
     * @throws SearchInterrupted
     */
    public SearchResult continueSearch(boolean resetCounters) throws SearchInterrupted {

        SearchResult sr = null;

        if ( resetCounters ) {
            nodesConsidered = 0; // Clear some counters, etc.
            nodesCreated    = 0;
        }

        bestScoreSeenSoFar = Double.NEGATIVE_INFINITY;
        nodeWithBestScore  = null;

        sr = performSearchIteration();

        return sr;
    }

    

    /**
     * Creates a description of the search statistics.
     * 
     * @return A string describing the number of nodes generated and examined.
     */
    public String reportSearchStats() {
        return reportSearchStats(true); // Default is to not print out much info.
    }

    /**
     * Creates a description of the search statistics.
     * 
     * @param briefVersion
     *                Whether to only create a brief summary of the statistics.
     *                This currently has no effect.
     * @return A string describing the number of nodes generated and examined.
     */
    public String reportSearchStats(boolean briefVersion) {
        // if (briefVersion) ...
        String result = "Created " + Utils.comma(nodesCreated) + " nodes and expanded " + Utils.comma(nodesConsidered) + " of them.";
        
        if (nodesNotAddedToOPENsinceMaxScoreTooLow     > 0) { result += "\nDuring this search, " + Utils.comma(nodesNotAddedToOPENsinceMaxScoreTooLow)     + " search nodes were not added to OPEN because their maximum score could not exceed the best score found so far."; }
        if (nodesRemovedFromOPENsinceMaxScoreNowTooLow > 0) { result += "\nDuring this search, " + Utils.comma(nodesRemovedFromOPENsinceMaxScoreNowTooLow) + " search nodes were removed from OPEN because their maximum score could not exceed the best score found so far."; }
        return result;
    }

    /**
     * Performs a basic search, that is, either not an iterative deepening
     * search or one iteration of an iterative deepening search.
     * 
     * @return The result of the search.
     * @throws SearchInterrupted
     *                 If the search is interrupted.
     */
    private SearchResult performSearchIteration() throws SearchInterrupted { 
        initialize();

        return search();
    }
    
    public boolean isThereTimeLeft() {
    	if (maximumClockTimePerIterationInMillisec == Long.MAX_VALUE) { return true; }

        return (System.currentTimeMillis() - iterationStartTimeInMillisec < maximumClockTimePerIterationInMillisec);
    }
    
    public String explainTimeLeft() {
    	if (maximumClockTimePerIterationInMillisec == Long.MAX_VALUE) { return "All the time in the world is left."; }

        return "Have spent " + Utils.convertMillisecondsToTimeSpan(System.currentTimeMillis() - iterationStartTimeInMillisec)
        		+ " but only have " + Utils.convertMillisecondsToTimeSpan(maximumClockTimePerIterationInMillisec);
    }

	private int maxWarnings     = 100; // After this limit hit, be more terse in warnings.
	private int countOfWarnings =   0;
    /** Performs that actual search loop.
     *
     * This is broken out since used by both continueSearch and performSearchIteration.
     * @return
     * @throws SearchInterrupted
     */
    private SearchResult search() throws SearchInterrupted {
        boolean done = false;

        boolean useClosedList = (closed != null);

        iterationStartTimeInMillisec = System.currentTimeMillis();
        
        if (open.isEmpty() || !continueTheSearch) {
        	if (redoable) {
        		searchMonitor.searchResult = SearchMonitor.openBecameEmpty;
        	} else  {
        		Utils.waitHere("This search will never start for '" + taskName + "': continueTheSearch = " + continueTheSearch + ", |open| = " + Utils.comma(open));
        	}
        	//Utils.waitHere("This search will never start for '" + taskName + "': continueTheSearch = " + continueTheSearch + ", |open| = " + Utils.comma(open));
        }

        while (continueTheSearch && !done && !open.isEmpty()) { // continueTheSearch is a 'global' variable that can be set within a search task to cause the search to end.  The method that sets this is responsible for informing the search monitor.
        	lastNodeVisited = open.popOpenList();

        	if (verbosity > 10) { Utils.println("% VISIT for '" + taskName  + "."); } // ; + "': " + lastNodeVisited); }

            if (getMaxNodesToConsider() > 0 && nodesConsidered >= getMaxNodesToConsider()) {
                done = true;
                if (countOfWarnings++ < maxWarnings) {
                	Utils.warning(        "#" + Utils.comma(countOfWarnings) + " TOO MANY NODES CONSIDERED (i.e., 'expanded') for '" + taskName + "': nodesConsidered = " + Utils.comma(nodesConsidered) + " and maxNodesToConsider = " + Utils.comma(getMaxNodesToConsider()) + ".");  // ; node = " + lastNodeVisited);
                } else {
                	Utils.println("Warning #" + Utils.comma(countOfWarnings) + " TOO MANY NODES CONSIDERED (i.e., 'expanded') for '" + taskName + "'.");
                }
                searchMonitor.searchEndedByMaxNodesConsidered(nodesConsidered);
            }

            if (!isThereTimeLeft()) {
                done = true;
                if (countOfWarnings++ < maxWarnings) {
                    long currentTime = System.currentTimeMillis();
                  	Utils.warning(        "#" + Utils.comma(countOfWarnings) + " TOO MUCH TIME SPENT for '" + taskName + "': '" + Utils.convertMillisecondsToTimeSpan(currentTime - iterationStartTimeInMillisec) + "' vs. '" + Utils.convertMillisecondsToTimeSpan(maximumClockTimePerIterationInMillisec) + "'.");
                } else {
                  	Utils.println("Warning #" + Utils.comma(countOfWarnings) + " TOO MUCH TIME SPENT for '" + taskName + ".");
                }	
                searchMonitor.searchEndedByMaxTimeUsed();
            }

            // Some searches don't want to stop when reaching max nodes CREATED.  Instead, don't add any more children to OPEN.
            if (!done && getMaxNodesToCreate() > 0 && nodesCreated >= getMaxNodesToCreate()) {
                done = searchMonitor.searchReachedMaxNodesCreated(nodesCreated); // Since this setting of 'done' is conditional, make sure done=false when reaching here.
                if (done == true) {
                	if (countOfWarnings++ < maxWarnings) {
                    	Utils.warning(            "#" + Utils.comma(countOfWarnings) + " TOO MANY NODES CREATED for '" + taskName + "':  maxNodesToCreate = "      + Utils.comma(getMaxNodesToCreate())      + " vs nodesCreated = "   + Utils.comma(nodesCreated) + "."); // ; node = " + lastNodeVisited);
                	} else {
                    	Utils.println("\n% Warning #" + Utils.comma(countOfWarnings) + " TOO MANY NODES CREATED for '" + taskName + "'.");
                    }	
                }
            }

            if (useIterativeDeepeningDepth) {
                if (maxNodesToConsiderPerIteration > 0 && nodesConsideredThisIteration >= maxNodesToConsiderPerIteration) {
                    done = true;
                    searchMonitor.searchEndedByMaxNodesConsideredThisIteration(nodesConsideredThisIteration);
                }
                if (!done && maxNodesToCreatePerIteration > 0 && nodesCreatedThisIteration >= maxNodesToCreatePerIteration) {
                    done = searchMonitor.searchReachedMaxNodesCreatedThisIteration(nodesCreatedThisIteration); // Since this setting of 'done' is conditional, make sure done=false when reaching here.
                }
            }
            if (terminator != null && terminator.endSearch(lastNodeVisited)) {
                done = true;
                searchMonitor.searchEndedByTerminator(lastNodeVisited);
                if (verbosity > 3) { Utils.warning("Search ended for '" + taskName + "' by terminator for some reason."); }
            }
            if (!done) {
                if (useClosedList && !addNodesToClosedListWhenCreated) { closed.addNodeToClosed(lastNodeVisited); } // Need to do this before adding children to prevent self-loops.
                if (lastNodeVisited.depth < maxSearchDepth) {
                    List<T> children = childrenGenerator.collectChildren(lastNodeVisited);
                    if (verbosity > 1) {Utils.println("%  Add " + Utils.comma(children) + " to OPEN."); }
                    if (Utils.getSizeSafely(children) > 0) {

                        for (SearchNode searchNode : children) {
                            if ( bestNodeVisited == null || searchNode.score > bestNodeVisited.score ) {
                                bestNodeVisited = searchNode;
                            }
                        }

                        strategy.addChildrenToOpenList(open, children);
                    }
                } 
                else if (lastNodeVisited.depth >= maxSearchDepth) {
                	if (countOfWarnings++ < maxWarnings) {
                    	Utils.warning("Warning #" + Utils.comma(countOfWarnings) + " % Skipped expansion of first open node.  Maximum depth reached: node.depth = " + Utils.comma(lastNodeVisited.depth) + " vs maxSearchDepth = " + Utils.comma(maxSearchDepth) + "."); // ; node = " + lastNodeVisited);
                	} else {
                    	Utils.println("Warning #" + Utils.comma(countOfWarnings) + " % Skipped expansion of first open node.  Maximum depth reached for '" + taskName);
                    }
                    if (verbosity > -10) {
                        Utils.waitHere("Did you really want to hit the depth limit?");
                    }
                }
                
                if (verbosity > 2) { Utils.println("  task=" + taskName + "  |open| = " + open.size() + "  done=" + done + " continueTheSearch=" + continueTheSearch); }

                if (open.isEmpty()) {
                    done = true;
                    searchMonitor.searchEndedBecauseOPENbecameEmpty();
                } 
            }
            if (done && redoable == false) {
            	open.clear(); // Even if we worried about getting the next solution (see TAW notes below), ok to clear here since we hit limits (which prevent spending time on more solutions).
            	if (closed != null) { closed.emptyClosedList(); } // Ditto.
            	if (verbosity > 2) { Utils.println("  task=" + taskName + ";  |open| = " + open.size() + ";  done=" + done + "; continueTheSearch=" + continueTheSearch + "."); } // "; node = " + lastNodeVisited); }
            } 
        }
        SearchResult result = searchMonitor.getSearchResult(); // Return whatever was saved by the search monitor.

        return result;
    }

    public long getMaximumClockTimePerIterationInMillisec() {
        return maximumClockTimePerIterationInMillisec;
    }

    public void setMaximumClockTimePerIterationInMillisec(long maximumClockTimePerIterationInMilliseconds) {
        this.maximumClockTimePerIterationInMillisec = maximumClockTimePerIterationInMilliseconds;
    }

	public int getNodesConsidered() {
		return nodesConsidered;
	}

	public void setNodesConsidered(int nodesConsidered) {
		this.nodesConsidered = nodesConsidered;
	}

	public int getNodesConsideredThisIteration() {
		return nodesConsideredThisIteration;
	}

	public void setNodesConsideredThisIteration(int nodesConsideredThisIteration) {
		this.nodesConsideredThisIteration = nodesConsideredThisIteration;
	}

	public int getNodesCreated() {
		return nodesCreated;
	}

	public void setNodesCreated(int nodesCreated) {
		this.nodesCreated = nodesCreated;
	}

	public int getNodesCreatedThisIteration() {
		return nodesCreatedThisIteration;
	}

	public void setNodesCreatedThisIteration(int nodesCreatedThisIteration) {
		this.nodesCreatedThisIteration = nodesCreatedThisIteration;
	}

    /**
     * @return the maxNodesToConsider
     */
    public int getMaxNodesToConsider() {
        return maxNodesToConsider;
    }

    /**
     * @param maxNodesToConsider the maxNodesToConsider to set
     */
    public void setMaxNodesToConsider(int maxNodesToConsider) {
        this.maxNodesToConsider = maxNodesToConsider;
    }

    /**
     * @return the maxNodesToCreate
     */
    public int getMaxNodesToCreate() {
        return maxNodesToCreate;
    }

    /**
     * @param maxNodesToCreate the maxNodesToCreate to set
     */
    public void setMaxNodesToCreate(int maxNodesToCreate) {
        this.maxNodesToCreate = maxNodesToCreate;
    }

}
