/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.Utils.condor;

import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.chirp.ChirpInputStream;
import java.io.File;  import edu.wisc.cs.will.Utils.condor.CondorFile;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;

/**
 *
 * @author twalker
 */
public class CondorFileInputStream extends InputStream {

    InputStream stream = null;

    public CondorFileInputStream(File file) throws FileNotFoundException {
        if (CondorUtilities.isChirp()) {
            try {
                //Logger.getLogger(CondorFileInputStream.class.getCanonicalName()).fine("Opening CondorFileInputStream on '" + file.toString() + "'");
                stream = new ChirpInputStream(file.toString());
            } catch (IOException ex) {
                Utils.waitHere("Error opening Condor chirp stream for " + file + ".");
                stream = null;
            }
        }
        else {
            stream = new FileInputStream(file);
        }
    }

    public CondorFileInputStream(String fileName) throws FileNotFoundException  {

        if (CondorUtilities.isChirp()) {
            try {
                stream = new ChirpInputStream(Utils.replaceWildCards(fileName));
            } catch (IOException ex) {
                Utils.waitHere("Error opening Condor chirp stream for " + Utils.replaceWildCards(fileName) + ".");
                stream = null;
            }
        }
        else {
            stream = new FileInputStream(Utils.replaceWildCards(fileName));
        }
    }

    public long skip(long n) throws IOException {
        checkStream();
        return stream.skip(n);
    }

    public synchronized void reset() throws IOException {
        checkStream();
        stream.reset();
    }

    public int read(byte[] b, int off, int len) throws IOException {
        checkStream();
        return stream.read(b, off, len);
    }

    public int read(byte[] b) throws IOException {
        checkStream();
        return stream.read(b);
    }

    public int read() throws IOException {
        checkStream();
        return stream.read();
    }

    public boolean markSupported() {
        return (stream == null ? false : stream.markSupported());
    }

    public synchronized void mark(int readlimit) {
        if (stream != null) {
            stream.mark(readlimit);
        }
    }

    public void close() throws IOException {
        if (stream != null) {
            stream.close();
        }
    }

    public int available() throws IOException {
        checkStream();
        return stream.available();
    }

    private void checkStream() throws IOException {
        if (stream == null) {
            throw new IOException("CondorFileInputStream: delegate stream is null.  Perhaps a problem when the stream was opened?");
        }
    }
}
