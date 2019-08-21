/**
 * 
 */
package edu.wisc.cs.will.Utils;

import java.io.File;
import java.io.IOException;
import java.io.Writer;

import edu.wisc.cs.will.Utils.condor.CondorFileWriter;

/**
 * This class should be used instead of the BufferedWriter for writing to files. 
 * It buffers the contents of the file till they exceed a certain limit. Once the 
 * buffer is too big, it will write the contents to the file. This is useful when writing to remote locations. 
 * Also if the final file is too big, the file will be gzipped and the old file will be deleted.
 *  
 * @author tkhot
 *
 */
public class GzippedBufferedWriter {

	private StringBuffer buffer; 
	
	private int          maxBufferSize;
	
	private Writer       writer;
	
	private String       fileName;
	
	public GzippedBufferedWriter(String file) throws IOException {
		this.writer = new CondorFileWriter(new File(file));
		this.fileName = file;
		if (fileName.endsWith(".gz")) {
			Utils.error("Trying to write to a gzipped file: " + fileName +
					". Filename doesn't have to end with .gz for using GzippedBufferedWriter.");
		}
		maxBufferSize = 1024 * 10;  // 10K
		buffer = new StringBuffer(maxBufferSize);
	}
	
	public void write(String str) throws IOException {
		if (buffer.length() > maxBufferSize) {
			writer.write(buffer.toString());
			buffer = new StringBuffer(maxBufferSize);
		}
		buffer.append(str);
	}
	
	public void newLine() throws IOException {
		write(System.getProperty("line.separator"));
	}
	
	public void close() throws IOException {
		if (buffer.length() != 0) {
			writer.write(buffer.toString());
		}
		writer.close();
		Utils.compressFile(fileName);
		
	}
}
