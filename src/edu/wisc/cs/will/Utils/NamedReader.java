/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.Utils;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.Reader;
import java.nio.CharBuffer;

/**
 *
 * @author twalker
 */
public class NamedReader extends BufferedReader {

    private String name;

    public NamedReader(Reader in, String name) {
        super(in);
        this.name = name;
    }

    public NamedReader(Reader in, int sz, String name) {
        super(in,sz);
        this.name = name;
    }

    
    @Override
    public String toString() {
        return name;
    }


}
