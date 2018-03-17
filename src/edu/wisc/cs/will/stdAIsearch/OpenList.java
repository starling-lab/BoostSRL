/**
 * Keep an ordered list of search nodes being considered.  Method for inserting new items depends on the search strategy being used.
 */
package edu.wisc.cs.will.stdAIsearch;

import java.util.Iterator;
import java.util.LinkedList;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author shavlik
 *
 */
public class OpenList<T extends SearchNode> extends LinkedList<T> {

    private static final long serialVersionUID = 1L;

    public StateBasedSearchTask<T> task;

    private int countOfAdds = 0; //jwsjws

    public OpenList(StateBasedSearchTask task) {
        this.task = task;
        if (task.verbosity > 1) {
            Utils.println("Starting a search with strategy = " + task.strategy.getClass().getName() + ".");
        }
    }

    public void setSearchTask(StateBasedSearchTask task) {
        this.task = task;
    }

    private void recordNodeCreation(T node) {
        task.nodesCreated++;
        task.nodesCreatedThisIteration++;
        task.searchMonitor.recordNodeCreation(node);
        if (task.closed != null && task.addNodesToClosedListWhenCreated) {
            task.closed.addNodeToClosed(node);
        }
    }

    public T popOpenList() {
        T popped = pop();

        task.nodesConsidered++;
        task.nodesConsideredThisIteration++;
        task.searchMonitor.recordNodeExpansion(popped);
        if (task.verbosity > 1) {
            Utils.println("Popped '" + popped + "' (" + Utils.comma(task.nodesConsidered) + " nodes considered so far) from the OPEN list.");
        }
        return popped;
    }

    @Override
    public boolean add(T node) {
        throw new UnsupportedOperationException("Programmer error: Do not use add() to add to the open list.  Use a method that also informs the search monitor.");
    }

    public boolean addToEndOfOpenList(T node) {
        if (node == null) {
            Utils.error("Cannot have node=null!");
        }
        if (task.closed != null && task.closed.alreadyInClosedList(node)) {
            return false;
        }
        super.add(node);
        recordNodeCreation(node);

        if (task.verbosity > 2) {
            Utils.println("  Added " + node + " (node #" + Utils.comma(task.nodesCreated) + ") to the end of the OPEN list.");
        }
        if (task.beamWidth > 0) {
            checkBeamWidth();
        }
        return true;
    }

    public boolean addToFrontOfOpenList(T node) {
        if (node == null) {
            Utils.error("Cannot have node=null!");
        }
        if (task.closed != null && task.closed.alreadyInClosedList(node)) {
            return false;
        }
        super.add(0, node);
        recordNodeCreation(node);

        if (task.verbosity > 2) {
            Utils.println("  Added " + node + " (node #" + Utils.comma(task.nodesCreated) + ") to the front of the OPEN list.");
        }
        if (task.beamWidth > 0) {
            checkBeamWidth();
        }
        return true;
    }

    public boolean insertByScoreIntoOpenList(T node, double minAcceptableScore, boolean tiesOK) throws SearchInterrupted { // HIGHER SCORES ARE BETTER (since that is the convention in heuristic search).
        if (node == null) {
            Utils.error("Cannot have node=null!");
        }
        if (task.closed != null && task.closed.alreadyInClosedList(node)) {
            if (task.verbosity > 2) {
                Utils.println(" Already in closed: " + node);
            }
            return false;
        }
        double score = task.scorer.scoreThisNode(node);
        if (task.verbosity > 2) {
            Utils.println(" insertByScoreIntoOpenList: Score of " + Utils.truncate(score, 3) + " for " + node);
        }
        if (score < minAcceptableScore) {
            if (task.verbosity > 2) {
                Utils.println("  Discard since score less than minAcceptableScore (" + minAcceptableScore + ").");
            }
            return false;
        }
        if (!tiesOK && score <= minAcceptableScore) {
            if (task.verbosity > 2) {
                Utils.println("  Discard since score does not exceeed minAcceptableScore (" + minAcceptableScore + ").");
            }
            return false;
        }
        if (Double.isNaN(score)) {
            return false;
        } // Allow scorers to return NaN to indicate 'do not keep.'
        double bonusScore = task.scorer.computeBonusScoreForThisNode(node); // Used to play tricks when inserting into OPEN, but where the "real" score should be provided to the search monitor.
        double totalScore = score + bonusScore;
        boolean acceptable = true; // See if this node is an acceptable for setting 'bestScoreSeenSoFar.'

        if (task.verbosity > 2) {
            Utils.println("Consider adding this to OPEN: [#" + (++countOfAdds) + "] " + node);
        }
        if (task.discardIfBestPossibleScoreOfNodeLessThanBestSeenSoFar
                && task.scorer.computeMaxPossibleScore(node) <= task.bestScoreSeenSoFar) { // TODO allow this to be '<=' or '<'
            if (task.verbosity > 2) {
                Utils.println("   Discard '" + node + "' because its best possible score (" + task.scorer.computeMaxPossibleScore(node) + ") cannot exceed the best score seen so far (" + task.bestScoreSeenSoFar + " of [" + task.nodeWithBestScore + "]).");
            }
            task.nodesNotAddedToOPENsinceMaxScoreTooLow++;
            return false;
        }

        // Don't tell the monitor if pruned, since the monitor may want to compute something cpu-intensive for a node that is being rejected.
        if (task.searchMonitor != null) {
            acceptable = task.searchMonitor.recordNodeBeingScored(node, score); // Use 'real' score for the search monitor. TODO - also pass in the bonus so the monitor can see if if it wants.
        }

        if (acceptable && score > task.bestScoreSeenSoFar) { // TODO - allow '<' and '<=' the best score
            if (task.verbosity > 2) {
                Utils.println("NEW BEST SCORING (" + score + ") node: " + node);
            }
            task.bestScoreSeenSoFar = score; // Do not use BONUS here, since that should only impact sorting in the list.
            task.nodeWithBestScore = node;
            if (task.discardIfBestPossibleScoreOfNodeLessThanBestSeenSoFar) {
                // Remove items from OPEN that cannot beat.  TODO - allow '<' and '<=' the best score.
                // for (SearchNode n : this) { Utils.println("   Best possible score (" + task.scorer.computeMaxPossibleScore(n) + ") for OPEN member: " + n); }
                for (Iterator<T> iter = this.iterator(); iter.hasNext();) {
                    T n = iter.next();
                    if (task.scorer.computeMaxPossibleScore(n) <= score) {
                        if (task.verbosity > 2) {
                            Utils.println("   Can remove this existing OPEN-list node since its best possible score (" + task.scorer.computeMaxPossibleScore(n) + ") cannot beat this new node's score (" + score + "): " + n);
                        }
                        iter.remove();
                        task.nodesRemovedFromOPENsinceMaxScoreNowTooLow++;
                    }
                    else if (task.verbosity > 2) {
                        Utils.println("   Keep in OPEN: " + n);
                    }
                }
            }
        }

        if (node.dontActuallyAddToOpen()) {
            if (task.verbosity > 2) {
                Utils.println("   Do NOT insert into OPEN: " + node);
            }
            return false;
        }

        node.score = score;   // Record the score.
        node.bonusScore = bonusScore; // And any bonus.

        int position = 0;
        boolean found = false;
        boolean tiesInFront = task.inOpenListPutNewTiesInFront;
        for (SearchNode currentNode : this) {
            double currentTotalScore = currentNode.score + currentNode.bonusScore;
            if ((tiesInFront && totalScore >= currentTotalScore) || (!tiesInFront && totalScore > currentTotalScore)) {
                found = true;
                super.add(position, node);
                recordNodeCreation(node);
                if (task.verbosity > 2) {
                    Utils.println("  Added " + node + " (node #" + task.nodesCreated + ") to the OPEN list in position " + position + " based on its score of " + Utils.truncate(totalScore, 3) + ".");
                }
                break;
            }
            position++;
        }
        if (!found) { // Don't forget this might need to be the LAST item.
            super.add(node);
            recordNodeCreation(node);
            if (task.verbosity > 2) {
                Utils.println("  Added " + node + " (node #" + task.nodesCreated + ") to the END of the OPEN list (in position " + position + ") based on its score of " + Utils.truncate(totalScore, 3) + ".");
            }
        }

        if (task.beamWidth > 0) {
            checkBeamWidth();
        }
        if (task.verbosity > 3) {
            reportOpenListScores();
        }
        return true;
    }

    public boolean insertByScoreIntoOpenList(T node) throws SearchInterrupted {
        return this.insertByScoreIntoOpenList(node, task.minAcceptableScore, task.allowToTieMinAcceptableScore);
    }

    public void reportOpenSize() {
        Utils.println("% |open| = " + Utils.comma(size()));
    }

    private void checkBeamWidth() {
        if (task.beamWidth > 0 && size() > task.beamWidth) {
            int excess = size() - task.beamWidth;

            if (task.verbosity > 2) {
                Utils.println("    Reducing OPEN to max beam size of " + task.beamWidth + ".");
            }
            for (int i = 0; i < excess; i++) {
                removeLast();
            }
        }
    }

    public void reportOpenListScores() {
        Utils.print("  OPEN = [");
        boolean firstTime = true;

        for (SearchNode currentNode : this) {
            double score = currentNode.score;

            if (firstTime) {
                firstTime = false;
            }
            else {
                Utils.print(", ");
            }
            Utils.print("score(" + currentNode + ") = " + score);
        }
        Utils.println("]");
    }
}
