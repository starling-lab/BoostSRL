/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.Utils;

import java.io.IOException;
import java.io.InputStream;

/**
 *
 * @author twalker
 */
public class NamedInputStream extends InputStream {

    private InputStream delegate;
    private String name;

    public NamedInputStream(InputStream delegate, String name) {
        this.delegate = delegate;
        this.name = name;
    }

    public long skip(long n) throws IOException {
        return delegate.skip(n);
    }

    public synchronized void reset() throws IOException {
        delegate.reset();
    }

    public int read(byte[] b, int off, int len) throws IOException {
        return delegate.read(b, off, len);
    }

    public int read(byte[] b) throws IOException {
        return delegate.read(b);
    }

    public int read() throws IOException {
        return delegate.read();
    }

    public boolean markSupported() {
        return delegate.markSupported();
    }

    public synchronized void mark(int readlimit) {
        delegate.mark(readlimit);
    }

    public void close() throws IOException {
        delegate.close();
    }

    public int available() throws IOException {
        return delegate.available();
    }

    @Override
    public String toString() {
        return name;
    }


}
