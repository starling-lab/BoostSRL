/*
 * Stopwatch.java
 *
 * Created on September 5, 2007, 7:36 PM
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
package edu.wisc.cs.will.Utils;

/**
 *
 * @author twalker
 */
public class Stopwatch {

    private long startTime = -1;

    private long totalTime = 0;

    /** Creates a new instance of Stopwatch and starts the watch.
     *
     */
    public Stopwatch() {
        this(true);
    }

    /** Creates a new instance of Stopwatch.
     *
     * @param start If true, the watch is started.
     */
    public Stopwatch(boolean start) {
        if (start) {
            start();
        }
    }

    /** Starts the watch.
     *
     * If the watch was already started, nothing is done.
     */
    public void start() {
        if (startTime == -1) {
            startTime = System.currentTimeMillis();
        }
    }

    /** Stops the watch, returning time accumulated so far.
     *
     * @return Total time accumulated in milliseconds.
     */
    public long stop() {
        if (startTime != -1) {
            totalTime += System.currentTimeMillis() - startTime;
            startTime = -1;
        }
        return totalTime;
    }

    /** Stop watch, resets the accumulated time.
     *
     * If called while the stopwatch is running, this will
     * start the watch again.  Otherwise, it will just reset
     * the accumulated time.
     *
     * @return Total time accumulated prior to reset in milliseconds.
     */
    public long reset() {
        boolean wasRunning = (startTime != -1);
        long time = stop();
        totalTime = 0;
        if (wasRunning == true) {
            start();
        }
        return time;
    }

    /** Returns the total time accumulated so far, in seconds.
     *
     * If called while the stopwatch is running, this will return the
     * time without stopping the stopwatch.
     *
     * @return Total time so far in seconds.
     */
    public double getTotalTimeInSeconds() {
        return getTotalTimeInMilliseconds() / 1000.0;
    }

    /** Returns the total time accumulated so far, in milliseconds.
     *
     * If called while the stopwatch is running, this will return the
     * time without stopping the stopwatch.
     *
     * @return Total time so far in milliseconds.
     */
    public long getTotalTimeInMilliseconds() {
        long time = totalTime;
        if (startTime != -1) {
            time += System.currentTimeMillis() - startTime;
        }
        return time;
    }
}
