/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.Utils.condor;

import edu.wisc.cs.will.Utils.condor.CondorFileInputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.zip.GZIPInputStream;

/**
 *
 * @author twalker
 */
public class CompressedInputStream extends InputStream {

    InputStream realStream = null;

    public CompressedInputStream(File file) throws IOException {
        
        File gzFile   = CompressionUtilities.getGZFile(file);
        File noGZFile = CompressionUtilities.getNonGZFile(file);

        try {
            Logger.getLogger(CompressedInputStream.class.getCanonicalName()).log(Level.FINE, "Opening compressed file ''{0}'',", gzFile.toString());
            realStream = new GZIPInputStream(new CondorFileInputStream(gzFile));
        }
        catch(FileNotFoundException ex) {
            Logger.getLogger(CompressedInputStream.class.getCanonicalName()).log(Level.FINE, "Compressed file not found.  Opening uncompressed file ''{0}'',", noGZFile.toString());
            realStream = new CondorFileInputStream(noGZFile);
        }
    }

    public CompressedInputStream(String fileName) throws FileNotFoundException, IOException {
        this(new File(fileName));
    }

    @Override
    public int read() throws IOException {
        return realStream.read();
    }

    @Override
    public int available() throws IOException {
        return realStream.available();
    }

    @Override
    public void close() throws IOException {
        realStream.close();
    }

    @Override
    public synchronized void mark(int readlimit) {
        realStream.mark(readlimit);
    }

    @Override
    public boolean markSupported() {
        return realStream.markSupported();
    }

    @Override
    public int read(byte[] b) throws IOException {
        return realStream.read(b);
    }

    @Override
    public int read(byte[] b, int off, int len) throws IOException {
        return realStream.read(b, off, len);
    }

    @Override
    public synchronized void reset() throws IOException {
        realStream.reset();
    }

    @Override
    public long skip(long n) throws IOException {
        return super.skip(n);
    }
}
