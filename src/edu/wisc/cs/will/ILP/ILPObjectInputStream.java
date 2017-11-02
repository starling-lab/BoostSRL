/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.ILP;

import edu.wisc.cs.will.FOPC.FOPCInputStream;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.stdAIsearch.StateBasedSearchInputStream;
import edu.wisc.cs.will.stdAIsearch.StateBasedSearchTask;
import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;

/**
 *
 * @author twalker
 */
public class ILPObjectInputStream extends ObjectInputStream implements FOPCInputStream, StateBasedSearchInputStream {
    
    private HandleFOPCstrings stringHandler;

    private StateBasedSearchTask stateBasedSearchTask;

    public ILPObjectInputStream(InputStream in, HandleFOPCstrings stringHandler, StateBasedSearchTask stateBasedSearchTask) throws IOException {
        super(in);
        this.stringHandler = stringHandler;
        this.stateBasedSearchTask = stateBasedSearchTask;
    }

    /**
     * @return the stringHandler
     */
    public HandleFOPCstrings getStringHandler() {
        return stringHandler;
    }

    /**
     * @param stringHandler the stringHandler to set
     */
    public void setStringHandler(HandleFOPCstrings stringHandler) {
        this.stringHandler = stringHandler;
    }

    /**
     * @return the stateBasedSearchTask
     */
    public StateBasedSearchTask getStateBasedSearchTask() {
        return stateBasedSearchTask;
    }

    /**
     * @param stateBasedSearchTask the stateBasedSearchTask to set
     */
    public void setStateBasedSearchTask(StateBasedSearchTask stateBasedSearchTask) {
        this.stateBasedSearchTask = stateBasedSearchTask;
    }




}
