/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.Utils.condor;

import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.chirp.ChirpOutputStream;
import java.io.File;  import edu.wisc.cs.will.Utils.condor.CondorFile;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 *
 * @author twalker
 */
public class CondorFileOutputStream extends OutputStream {

    OutputStream stream = null;

    public CondorFileOutputStream(File file) throws FileNotFoundException {
        if (CondorUtilities.isChirp()) {
            try {
                stream = new ChirpOutputStream(file.toString());
            } catch (IOException ex) {
                stream = null;
                throw new FileNotFoundException(ex.getMessage());
            }
        }
        else {
            stream = new FileOutputStream(file);
        }
    }

    public CondorFileOutputStream(String fileName) throws FileNotFoundException {

        if (CondorUtilities.isChirp()) {
            try {
                stream = new ChirpOutputStream(Utils.replaceWildCards(fileName));
            } catch (IOException ex) {
                stream = null;
                throw new FileNotFoundException(ex.getMessage());
            }
        }
        else {
            stream = new FileOutputStream(Utils.replaceWildCards(fileName));
        }
    }

    public CondorFileOutputStream(File file, boolean append) throws FileNotFoundException {
        if (CondorUtilities.isChirp()) {
            try {
                stream = new ChirpOutputStream(file.toString(), append);
            } catch (IOException ex) {
                stream = null;
                throw new FileNotFoundException(ex.getMessage());
            }
        }
        else {
            stream = new FileOutputStream(file, append);
        }
    }

    public CondorFileOutputStream(String fileName, boolean append) throws FileNotFoundException {

        if (CondorUtilities.isChirp()) {
            try {
                stream = new ChirpOutputStream(Utils.replaceWildCards(fileName), append);
            } catch (IOException ex) {
                stream = null;
                throw new FileNotFoundException(ex.getMessage());
            }
        }
        else {
            stream = new FileOutputStream(Utils.replaceWildCards(fileName), append);
        }
    }

    public void write(byte[] b, int off, int len) throws IOException {
        checkStream();
        stream.write(b, off, len);
    }

    public void write(byte[] b) throws IOException {
        checkStream();
        stream.write(b);
    }

    public void write(int b) throws IOException {
        checkStream();
        stream.write(b);
    }

    public void flush() throws IOException {
        checkStream();
        stream.flush();
    }

    public void close() throws IOException {
        if (stream != null) {
            stream.close();
        }
    }

    private void checkStream() throws IOException {
        if (stream == null) {
            throw new IOException("CondorFileOutputStream: delegate stream is null.  Perhaps a problem when the stream was opened?");
        }
    }
}
