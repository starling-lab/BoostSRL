/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.wisc.cs.will.Utils;

import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;  import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.Utils.condor.CondorFileInputStream;
import java.io.FileNotFoundException;
import edu.wisc.cs.will.Utils.condor.CondorFileOutputStream;
import edu.wisc.cs.will.Utils.condor.CondorFileReader;
import edu.wisc.cs.will.Utils.condor.CondorFileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintStream;
import java.io.Reader;
import java.io.Writer;
import java.util.ArrayList;
import java.util.List;

/**
 *
 * @author twalker
 */
public class Permute {

    /** Randomly permute array in place.
     *
     * @param <T>  Type of array to permute.
     * @param array Array to permute in place.
     */
    public static <T> void permute(T[] array) {
        if (array != null) {
            for (int i = 1; i < array.length; i++) {
                int j = (int) (Utils.random() * (i + 1));
                T swap = array[i];
                array[i] = array[j];
                array[j] = swap;
            }
        }
    }

    /** Randomly permute array in place.
     *
     * @param <T>  Type of list to permute.
     * @param list List to permute in place.  It is highly recommended that this
     * list be a list with quick random access (such as ArrayList).
     */
    public static <T> void permute(List<T> list) {
        if (list != null) {
            for (int i = 1; i < list.size(); i++) {
                int j = (int) (Utils.random() * (i + 1));
                T swap = list.get(i);
                list.set(i, list.get(j));
                list.set(j, swap);
            }
        }
    }

    /** Randomly permute the lines in an input stream and write the permutation out to the output stream.
     *
     * This will read all of the lines in the inputStream, store them in an array, and then
     * place the reordered lines back out to the output stream.
     *
     * This method loads the complete stream into memory.  A more memory efficient (but much slower)
     * algorithm could be used for extremely large streams,especially in the case of random access
     * files.
     *
     * Neither stream will be cleaned up or closed.  However, the method will block until it
     * detects an end of stream from the inputStream.
     *
     * @param inputStream Input stream to read lines from.
     * @param outputStream Output stream to write permuted lines to.
     * @throws IOException Throws an IOException if anything bad happens while permuting the lines.
     */
    public static void permute(InputStream inputStream, OutputStream outputStream) throws IOException {
        permute(new InputStreamReader(inputStream), new OutputStreamWriter(outputStream));
    }

    /** Randomly permute the lines from a Reader and write the permutation out to the Writer.
     *
     * This will read all of the lines in the Reader, store them in an array, and then
     * place the reordered lines back out to the Writer.
     *
     * This method loads the complete buffer into memory.  A more memory efficient (but much slower)
     * algorithm could be used for extremely large random-access buffers.
     *
     * Neither the Reader or Writer will be cleaned up or closed.  However, the method will block until it
     * detects an end of stream from the Reader.
     *
     * Reading from the reader and writing
     *
     * @param reader Reader to read lines from.
     * @param writer Writer to write permuted lines to.
     * @throws IOException Throws an IOException if anything bad happens while permuting the lines.
     */
    public static void permute(Reader reader, Writer writer) throws IOException {
        BufferedReader r = new BufferedReader(reader);
        List<String> lines = new ArrayList<String>();

        String line = null;
        while ((line = r.readLine()) != null) {
            lines.add(line);
        }

        permute(lines);

        String endOfLine = System.getProperty("line.separator");

        for (String string : lines) {
            writer.write(string);
            writer.write(endOfLine);
        }
        writer.flush();
    }

    /** Randomly permutes the lines from inputFile and writes them out to outputFile.
     *
     * InputFile and OutputFile can refer to the same file.  Care is taken to minimize
     * the chances that the file will be lost, but one should be careful when overwriting
     * the original file.
     *
     * @param inputFile File to read lines from.
     * @param outputFile File to write lines back to.
     * @throws java.io.FileNotFoundException Throws a FileNotFoundException if the input file is not found.
     * @throws java.io.IOException Propagates any IOExceptions from the file read and write operations.
     */
    public static void permute(File inputFile, File outputFile) throws FileNotFoundException, IOException {
        BufferedReader reader = new BufferedReader(new CondorFileReader(inputFile));
        List<String> lines = new ArrayList<String>();

        String line = null;
        while ((line = reader.readLine()) != null) {
            lines.add(line);
        }

        reader.close();

        permute(lines);

        BufferedWriter writer = new BufferedWriter(new CondorFileWriter(outputFile, false)); // Create a new file.

        for (String string : lines) {
            writer.write(string);
            writer.newLine();
        }
        writer.close();
    }

    /** Randomly permutes the lines from inputFileName and writes them to outputFileName.
     *
     * inputFileName and outputFileName can be the same file. Care is taken to minimize
     * the chances that the file will be lost, but one should be careful when overwriting
     * the original file.
     * @param inputFileName Name of the input file.
     * @param outputFileName Name of the output file.
     * @throws FileNotFoundException Thrown if the input file can't be found.
     * @throws IOException Thrown if an exception occurs during the permute.
     */
    public static void permute(String inputFileName, String outputFileName) throws FileNotFoundException, IOException {
        permute( new CondorFile(inputFileName), new CondorFile(outputFileName) );
    }

    /** Permutes either a file or standard in, writing the results to a file or standard out.
     *
     * <pre>
     * Usage:
     *   main [ inputFileName [outputFileName] ]
     *   main -h
     * where:
     *   inputFileName   is the name of the input file. '-' (without quotes) indicates
     *                      that standard in should be used as the source.  If not specified,
     *                      standard in will be used.
     *   outputFileName  is the name of the output file.  If not specified standard out is
     *                      used.
     *   -h              prints this message and does nothing.
     *
     * </pre>
     * @param args Arguments to main, see printUsage.
     */
    public static void main(String[] args) {
        String inputFileName = null;
        String outputFileName = null;

        if (args.length > 0 && args[0].equals("-h")  ) {
            printUsage(System.out);
            System.exit(0);
        }
        else if ( args.length > 2 ) {
            printUsage(System.err);
            System.exit(1);
        }

        if ( args.length >= 1 && args[0].equals("-") == false)  {
            inputFileName = args[0];
        }

        if ( args.length == 2 ) {
            outputFileName = args[1];
        }

        try {
            if ( inputFileName != null && outputFileName != null ) {
                // Catch the case where we are going file to file, since this
                // might be the same file.  The file to file version of permute
                // will work for this case.  The other versions of permute will likely
                // erase the input file prior to reading when the outputFile is opened
                // (if they are the same).
                permute(new CondorFile(inputFileName), new CondorFile(outputFileName));
            }
            else {
                InputStream is = System.in;
                OutputStream os = System.out;

                if ( inputFileName != null ) {
                    is = new CondorFileInputStream(inputFileName);
                }

                if ( outputFileName != null ) {
                    os = new BufferedOutputStream( new CondorFileOutputStream(outputFileName));
                }

                permute(is, os);

                is.close();
                os.close();
            }
        }
        catch(Exception ex) {
            System.err.append("An error occurred: ");
            ex.printStackTrace(System.err);
            System.exit(1);
        }
    }

    private static void printUsage(PrintStream out) {
        out.println("Usage:");
        out.println("  permute [ inputFileName [outputFileName] ]");
        out.println("  permute -h");
        out.println("where:");
        out.println("  inputFileName  is the name of the input file. '-' (without quotes) indicates");
        out.println("                    that standard in should be used as the source.  If not specified,");
        out.println("                    standard in will be used.");
        out.println("  outputFileName is the name of the output file.  If not specified standard out is ");
        out.println("                    used.");
        out.println("  -h             prints this message and does nothing.");
    }
}
