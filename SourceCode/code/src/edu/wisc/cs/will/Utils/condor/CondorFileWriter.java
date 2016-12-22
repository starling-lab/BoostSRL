/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.Utils.condor;

import java.io.File;  import edu.wisc.cs.will.Utils.condor.CondorFile;
import java.io.FileWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;

/**
 *
 * @author twalker
 */
public class CondorFileWriter extends Writer {

    Writer writer = null;

    FileWriter fw;

    public CondorFileWriter(File file) throws IOException {
        writer = new OutputStreamWriter( new CondorFileOutputStream(file));
    }

    public CondorFileWriter(File file, boolean append) throws IOException {
        writer = new OutputStreamWriter( new CondorFileOutputStream(file, append));
    }

    public CondorFileWriter(String filename) throws IOException {
        writer = new OutputStreamWriter( new CondorFileOutputStream(filename));
    }

    public CondorFileWriter(String filename, boolean append) throws IOException {
        writer = new OutputStreamWriter( new CondorFileOutputStream(filename, append));
    }

    public void write(String str, int off, int len) throws IOException {
        writer.write(str, off, len);
    }

    public void write(String str) throws IOException {
        writer.write(str);
    }

    public void write(char[] cbuf, int off, int len) throws IOException {
        writer.write(cbuf, off, len);
    }

    public void write(char[] cbuf) throws IOException {
        writer.write(cbuf);
    }

    public void write(int c) throws IOException {
        writer.write(c);
    }

    public void flush() throws IOException {
        writer.flush();
    }

    public void close() throws IOException {
        writer.close();
    }

    public Writer append(char c) throws IOException {
        return writer.append(c);
    }

    public Writer append(CharSequence csq, int start, int end) throws IOException {
        return writer.append(csq, start, end);
    }

    public Writer append(CharSequence csq) throws IOException {
        return writer.append(csq);
    }


}
