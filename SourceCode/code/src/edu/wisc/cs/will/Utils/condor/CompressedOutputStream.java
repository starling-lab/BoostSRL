/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.Utils.condor;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.OutputStream;
import java.util.zip.GZIPOutputStream;

/**
 *
 * @author twalker
 */
public class CompressedOutputStream extends OutputStream {

    private static boolean outputCompressedByDefault = false;

    private OutputStream realStream;
 
    public CompressedOutputStream(String fileName) throws FileNotFoundException, IOException {
        this(new File(fileName), outputCompressedByDefault);
    }

    public CompressedOutputStream(String fileName, boolean compressOutput) throws FileNotFoundException, IOException {
        this(new File(fileName), compressOutput);
    }
    
    public CompressedOutputStream(File file) throws IOException {
        this(file, outputCompressedByDefault);
    }

    public CompressedOutputStream(File file, boolean compressOutput) throws IOException {
        if (compressOutput) {
            File gzFile = CompressionUtilities.getGZFile(file);
            realStream = new GZIPOutputStream(new CondorFileOutputStream(gzFile));
        }
        else {
            File noGZFile = CompressionUtilities.getNonGZFile(file);
            realStream = new CondorFileOutputStream(noGZFile);
        }
    }

    /**
     * @return the compressOutput
     */
    public static boolean isOutputCompressedByDefault() {
        return outputCompressedByDefault;
    }

    /**
     * @param aCompressOutput the compressOutput to set
     */
    public static void setOutputCompressedByDefault(boolean aCompressOutput) {
        outputCompressedByDefault = aCompressOutput;
    }

    @Override
    public void write(int b) throws IOException {
        realStream.write(b);
    }

    @Override
    public void close() throws IOException {
        realStream.close();
    }

    @Override
    public void flush() throws IOException {
        realStream.flush();
    }

    @Override
    public void write(byte[] b) throws IOException {
        realStream.write(b);
    }

    @Override
    public void write(byte[] b, int off, int len) throws IOException {
        realStream.write(b, off, len);
    }
}
