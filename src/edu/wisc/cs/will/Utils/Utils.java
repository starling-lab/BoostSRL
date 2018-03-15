/*
 * General-purpose utilities, basically a collection of functions.
 * http://www.eclipse.org/articles/Article-TPTP-Profiling-Tool/tptpProfilingArticle.html
 * http://www.eclipse.org/tptp/home/downloads/drops/TPTP-4.2.0.html#tptp-plugins
 * http://www.ibm.com/developerworks/offers/lp/demos/summary/javaprofile.html
 */

package edu.wisc.cs.will.Utils;

import java.io.BufferedInputStream;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileFilter;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.PrintStream;
import java.lang.annotation.ElementType;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Date;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.regex.Matcher;

import javax.sound.sampled.AudioFormat;
import javax.sound.sampled.AudioInputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.LineUnavailableException;
import javax.sound.sampled.Mixer;
import javax.sound.sampled.SourceDataLine;
import javax.sound.sampled.UnsupportedAudioFileException;

import edu.wisc.cs.will.FOPC.ExistentialSentence;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.Utils.condor.CompressedInputStream;
import edu.wisc.cs.will.Utils.condor.CompressedOutputStream;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.Utils.condor.CondorFileInputStream;
import edu.wisc.cs.will.Utils.condor.CondorFileOutputStream;
import edu.wisc.cs.will.Utils.condor.CondorFileReader;
import edu.wisc.cs.will.Utils.condor.CondorFileWriter;
import edu.wisc.cs.will.Utils.condor.CondorUtilities;
import java.io.BufferedWriter;
import java.io.OutputStreamWriter;
import java.io.Reader;
import java.io.Writer;
import java.util.regex.Pattern;
import java.util.zip.GZIPInputStream;


/**
 * Some general-purpose utilities. This class is basically a collection of
 * functions intended to be accessible to and used by many classes. In keeping
 * with the spirit of functions, all the fields and methods of this class are
 * static.
 * 
 * @author shavlik
 */
public class Utils {
	
	// For large-scale runs we do not want to create dribble (nor 'debug') files. 
	public static Boolean doNotCreateDribbleFiles  = false; 	
	public static Boolean doNotPrintToSystemDotOut = false;	
	public static Boolean doNotPrintToSystemDotErr = false;
	
	// If the strings MYUSERNAME, MYPATHPREFIX, or SHAREDPATHPREFIX appear in file names, they will be replaced with these settings.
	public static String MYUSERNAME       = null; // If we add to this list, edit replaceWildCards().
	public static String MYPATHPREFIX     = "MYPATHPREFIXisUnset";
	public static String SHAREDPATHPREFIX = "SHAREDPATHPREFIXisUnset";
	public static String MYSCRATCHDIR     = null;
	

	/** Stores whether this is a developer run.
     *
     * This should null initially.  The getter/setter will initialize it
     * appropriately the first time it is accessed.  Please do not use it
     * directly, as that will probably result in a null exception somewhere
     * along the line.
     */
    private static Boolean developmentRun = null; // Should be null.  See comment.

    /** Stores whether verbose output should be used.
     *
     * This should null initially.  The getter/setter will initialize it
     * appropriately the first time it is accessed.  Please do not use it
     * directly, as that will probably result in a null exception somewhere
     * along the line.
     */
    private static Boolean verbose = null; // Should be null.  See comment.

    /** Stores whether extraVerbose output should be used.
     *
     * This should null initially.  The getter/setter will initialize it
     * appropriately the first time it is accessed.  Please do not use it
     * directly, as that will probably result in a null exception somewhere
     * along the line.
     */
    private static Boolean extraVerbose = null; // Should be null.  See comment.

    /** Stores whether waitHereEnabled output should be used.
     *
     * This should null initially.  The getter/setter will initialize it
     * appropriately the first time it is accessed.  Please do not use it
     * directly, as that will probably result in a null exception somewhere
     * along the line.
     */
    private static Boolean waitHereEnabled = null; // Should be null.  See comment.

    /** Stores whether severeErrorThrowsEnabled output should be used.
     *
     * This should null initially.  The getter/setter will initialize it
     * appropriately the first time it is accessed.  Please do not use it
     * directly, as that will probably result in a null exception somewhere
     * along the line.
     */
    private static Boolean severeErrorThrowsEnabled = null; // Should be null.  See comment.

    private static Set<MessageType> filteredMessageTypes = EnumSet.noneOf(MessageType.class);

	// These relate to determining whether or not someone is a WILL developer.
	// WILL developers should create a file whose name is that stored by DEVELOPER_MACHINE_FILE_NAME 
	// in their 'home directory'.  
	//   In Windows this typically is "C:\\Documents and Settings\\shavlik", where 'shavlik' is replaced by one's login name.
	//   In Unix, this is "~/:
	// You can call getUserHomeDir() to find out.	
    public  static final String DEVELOPER_MACHINE_PROPERTY_KEY = "edu.wisc.cs.bl.devrun"; // Used to see if this is a 'developer run' - if not, less might be printed and waitHere()'s will become warnings.
    private static final String DEVELOPER_MACHINE_FILE_NAME    = "runWILLasDeveloper.txt";


    /** Some Standard verbosity levels.  
     * 
     * The verbosity level can be set via the setVerbosity method.  That actually updates
     * the verbose, extraVerbose, waitHereEnabled, and severeErrorThrowsEnabled settings.
     * 
     * These are just suggested levels.  All of the four controlling factors can be overridden by setting
     * the appropriate value through the setter.
     */
    public enum Verbosity {
        Developer(true,true,true,true,true),  // Print everything and waitHeres wait, severeError cause a throw.
        DeveloperNoWait(true,true,false,true,false),      // Print everything, waitHeres don't wait, severeError cause a throw.
        High(false,true,false,true,false),
        Medium(false,true,false,false,false),   // Print everything, waitHeres don't wait, severeError just print error
        Low(false,false,false,false,false);     // Print nothing.

        boolean developmentRun;
        boolean print;
        boolean waitHere;
        boolean severeWarningThrowsError;
        boolean extraVerbose;

        Verbosity(boolean developmentRun, boolean print, boolean waitHere, boolean severeWarningThrowsError, boolean extraVerbose) {
            this.developmentRun = developmentRun;
            this.print    = print;
            this.waitHere = waitHere;
            this.severeWarningThrowsError = severeWarningThrowsError;
            this.extraVerbose = extraVerbose;
        }
    }

    /** Sets the verbose, extraVerbose, waitHereEnabled, and severeErrorThrowsEnabled according to the indicated verbosity.
     *
     * These are just standard settings.  You can override these with the appropriate setters
     * for the specific settings.
     *
     * @param verbosity
     */
    public static void setVerbosity(Verbosity verbosity) {
        developmentRun           = verbosity.developmentRun;
        verbose                  = verbosity.print;
        extraVerbose             = verbosity.extraVerbose;
        waitHereEnabled          = verbosity.waitHere;
        severeErrorThrowsEnabled = verbosity.severeWarningThrowsError;
    }



    /** The Default file extension to add to "normal" files.
     *
     * This does not (and should not) include a . prior to the extension.
     */
    public static final String defaultFileExtension           = "txt";
    public static final String defaultFileExtensionWithPeriod = "." + defaultFileExtension;

    /**
     * How much two numbers (outside of (-1, 1) can differ before they are no longer considered
     * equivalent.
     */
    private static final double EQUIVALENCE_TOLERANCE = 0.0000001; 
    // FOr numbers in [-1, 1] use this (probably could simply use Double.MIN_NORMAL).
    private static final double EQUIVALENCE_TOLERANCE_SMALL_NUMBERS = 8 * Double.MIN_NORMAL;

    /**
     * If non-null, copy all printing to this stream as well.
     */
    // TODO NEED TO CLEAN UP DRIBBLE STREAM!
    private static PrintStream dribbleStream       = null;  // <----- 'state' being held in this static.  BUGGY if multiple threads running.
    private static PrintStream dribbleStream2      = null;  // <----- 'state' being held in this static.  BUGGY if multiple threads running.
    private static PrintStream debugStream         = null;  // <----- 'state' being held in this static.  BUGGY if multiple threads running.
    private static PrintStream warningStream       = null;  // <----- 'state' being held in this static.  BUGGY if multiple threads running.
    private static PrintStream warningShadowStream = null;  // <----- 'state' being held in this static.  BUGGY if multiple threads running.
//  private static int         maxDribbleLineWidth = 200;   // Ditto (also buggy if the caller inserts line feeds .... so we'll wait to use).

    /** The random instance for all the random utility functions. */
    // TODO clean up so that the random instance is robust to multiple runs
    private static Random randomInstance = new Random(112957);

    private static Map<String,Integer> warningCounts = new HashMap<String,Integer>();

    /**
     * Waits for input on standard input after displaying the given message.
     *
     * @param msg
     *            A message explaining the waiting. "Waiting " is prepended.
     */
	private static BufferedReader inBufferedReader;

	private static final int maxStringLength = 25000;
    /**
     * Displays a string to the standard output stream and the dribble stream if
     * applicable. Ends with a newline.
     * 
     * @param printRegardless
     */
    public static void println(String strRaw, boolean printRegardless) {
    	if (printRegardless || isVerbose() ) {
    		String str = (strRaw == null || strRaw.length() <= maxStringLength ? strRaw : strRaw.substring(0, maxStringLength) + " ... [string too long]");
    		if (!doNotPrintToSystemDotOut) { System.out.println(str); }
    		if (dribbleStream != null) { dribbleStream.println(str); }  // No need to flush since println already does so
    	}
    }
    public static void printf(String format, Object... args) {
    	println(String.format(format, args));
    }
    public static void printTEMP(String str) { // Use this when adding some temp prints so it is easy to find them when you want to later delete (or comment out) them.
    	println(str, false);
    }
    public static void printlnErr(MessageType type, String str) { // Use this when adding some temp prints so it is easy to find them when you want to later delete (or comment out) them.
    	if ( isMessageTypeEnabled(type) ) printlnErr(str);
    }
    public static void printlnErr(String strRaw) {
    	if ( isVerbose() ) {
    		String str = (strRaw == null || strRaw.length() <= maxStringLength ? strRaw : strRaw.substring(0, maxStringLength) + " ... [string too long]");
    		boolean hold = doNotPrintToSystemDotOut;
    		doNotPrintToSystemDotOut = false; // If these printout become too much, we can add a 3rd flag to override these ...
    		if (!doNotPrintToSystemDotErr) { System.err.println(str); }
    		if (dribbleStream != null) { dribbleStream.println(str); }  // No need to flush since println already does so.
            doNotPrintToSystemDotOut = hold;
    	}
    }
    public static void println(String str) {
    	println(str, false);
    }
    public static void println(MessageType type, String str) {
    	if ( isMessageTypeEnabled(type)) println(str, false);
    }
    public static void println2(String strRaw, boolean printRegardless) {
    	if (printRegardless || isVerbose() ) {
    		String str = (strRaw == null || strRaw.length() <= maxStringLength ? strRaw : strRaw.substring(0, maxStringLength) + " ...");
    		if (!doNotPrintToSystemDotOut) {  System.out.println(str); }
    		if (dribbleStream2 != null) { dribbleStream2.println(str); }  // No need to flush since println already does so
    	}
    }
    public static void println2(String str) {
    	println2(str, false);
    }

    /**
     * Displays a string to the standard output stream and the dribble stream if
     * applicable. No newline at the end.
     * 
     * @param strRaw The string to print.
     * @param printRegardless
     */
    public static void print(String strRaw, boolean printRegardless) {
    	if (printRegardless || isVerbose()) {
    		String str = (strRaw == null || strRaw.length() <= maxStringLength ? strRaw : strRaw.substring(0, maxStringLength) + " ...");
    		if (!doNotPrintToSystemDotOut) {System.out.print(str); }
    		if (dribbleStream != null) { dribbleStream.print(str); }
    	}
    }
    public static void print(String str) {
    	print(str, false);
    }
    public static void print(MessageType type, String str) {
    	if ( isMessageTypeEnabled(type)) print(str, false);
    }
    public static void print2(String strRaw, boolean printRegardless) {
    	if (printRegardless || isVerbose()) {
    		String str = (strRaw == null || strRaw.length() <= maxStringLength ? strRaw : strRaw.substring(0, maxStringLength) + " ...");
    		if (!doNotPrintToSystemDotOut) { System.out.print(str); }
    		if (dribbleStream2 != null) { dribbleStream2.print(str); }
    	}
    }
    public static void print2(String str) {
    	print2(str, false);
    }

	public static String padRight(String original, int N) {	
		int len = (original == null ? 0 : original.length());
		if (len >= N) { return original; }
		String extra = "";
		for (int i = 0; i < N - len; i++) { extra += " "; }
		return (original == null ? "" : original) + extra;
	}
	
    public static String padLeft(String value, int width) {
    	String spec = "%" + width + "s";
    	return String.format(spec, value);    	
    }
    public static String padLeft(int value, int width) {
    	String spec = "%, " + width + "d"; // Always use separators (e.g., "100,000").
    	return String.format(spec, value);    	
    }      
    public static String padLeft(long value, int width) {
    	String spec = "%, " + width + "d"; // Always use separators (e.g., "100,000").
    	return String.format(spec, value);    	
    }  
    public static String padLeft(Collection<?> collection, int width) {
    	return padLeft(getSizeSafely(collection), width);
    }
    public static String padLeft(Map<?,?> map, int width) {
    	return padLeft(getSizeSafely(map), width);
    }  
    public static String comma(int value) { // Always use separators (e.g., "100,000").
    	return String.format("%,d", value);    	
    }    
    public static String comma(long value) { // Always use separators (e.g., "100,000").
    	return String.format("%,d", value);    	
    }   
    public static String comma(double value) { // Always use separators (e.g., "100,000").
    	return String.format("%,f", value);    	
    }
    public static String comma(Collection<?> collection) {
    	return comma(getSizeSafely(collection));
    }
    public static String comma(Map<?,?> map) {
    	return comma(getSizeSafely(map));
    }
	
	public static String[] chopCommentFromArgs(String[] args) {
	  if (args == null) { return null; } // Written with help from Trevor Walker.
	  int commentStart = -1;
	  for (int i = 0; i < args.length; i++) {
		  if (args[i] != null && args[i].startsWith("//") ) {
			  commentStart = i;
			  break;
		  }
	  }  
	  if (commentStart < 0) { return args; }
	  String[] newArgs = new String[commentStart];
	  for (int i = 0; i < commentStart; i++) {
		  newArgs[i] = args[i];
	  }
	  return newArgs;
	}
	
    /**
     * Converts a list to a string that shows at most 100 elements.
     * 
     * @param list
     *            The list to print.
     * @return A string representing the first 100 elements of the given list,
     *         or null if the given list is null.
     * @see Utils#limitLengthOfPrintedList(List, int)
     */
    public static String limitLengthOfPrintedList(Collection<?> list) {
        return limitLengthOfPrintedList(list, 100);
    }

    /**
     * Converts a collection to a string that shows at most maxSize elements.
     * 
     * @param collection The collection to print.
     * @param maxItems How many elements to print, at most.
     * @return A string representing at most the first maxSize elements of the given
     *         collection, or null if the given collection is null.
     */
	   public static String limitLengthOfPrintedList(Collection<?> collection, int maxItems) {
        if (collection == null) {
            return null;
        }
        int size = getSizeSafely(collection);
        if (size <= maxItems) {
            return collection.toString();
        }
        Iterator<?> iter = collection.iterator();
        String result = "[" + iter.next();
        if (size > 1) {
            for (int i = 1; i < maxItems; i++) {
                result += ", " + iter.next();
            }
        }
        return result + ", ..., plus " + comma(size - maxItems) + " more items]";
    }
	   
    /**
     * Converts a map to a string that shows at most maxSize elements.
     * 
     * @param map The map to print.
     * @param maxItems How many set elements to print, at most.
     * @return A string representing the first maxSize elements of the given
     *         map, or null if the given map is null.
     */
	public static String limitLengthOfPrintedList(Map<?,?> map, int maxItems) {
		if (map == null) { return null; }
		return limitLengthOfPrintedList(map.entrySet(), maxItems);
	}
	public static String limitLengthOfPrintedList(Map<?,?> map) {
		return limitLengthOfPrintedList(map, 100);
	}
	
	public static String limitStringLength(String string, int maxLength) {
		if (string == null) { return null; }
		if (string.length() > maxLength) {
			return string.substring(0, maxLength) + "...";
		}
		return string;
	}
	
	public static List<String> renameDuplicateStrings(List<String> strNames) {
		if (strNames == null) { return null; }
		HashMap<String,Integer> seenBefore = new HashMap<String,Integer>(4);
		List<String>            results    = new ArrayList<String>(strNames.size());
		for (String str : strNames) {
			Integer lookup = seenBefore.get(str);
			if (lookup == null) {
				results.add(   str);
				seenBefore.put(str, 1);
			} else {
				results.add(   str + "_" + lookup);
				seenBefore.put(str, lookup + 1);
			}
		}
		return results;
	}
	
	public static void exit(String msg) {
        println("\nEXITING:   " + msg);
	    cleanupAndExit(0);
	}
	
	/**
	 * Save some typing when throwing generic errors.
     *
     * @param msg
     */
	public static void error(String msg) {
        warning_println("\nERROR:   " + msg);
		if ( CondorUtilities.isCondor() ) {
			System.err.println("\nERROR:   " + msg);
	        // Nice to print the calling stack so one can see what caused the error ...
		//	reportStackTrace(new Exception());
			(new Exception()).printStackTrace(); // Doing it this way puts the stack in the ERROR file.
            println("\n" + msg);
	        println("\nSince this is a condor job, will exit.");	       
	    //	cleanupAndExit(1); // For some reason, this causes Condor to restart.
	        cleanupAndExit(0);
		}
		throw new WILLthrownError("\n " + msg);
	}
	public static void error() {
		throw new WILLthrownError("\n Should not happen ...");
	}
	
	public static void waitHereThenThrowError(String msg) {
		error("Now throwing an error as requested ...");
	}
	public static void interrupt(String msg) {
        warning_println("\nINTERRUPT:   " + msg);
		throw new WILLinterruption("\n " + msg);
	}
	
	/**
	 * Provide a simple way to mark code that still needs to be written.
     *
     * @param msg
     */
	public static void writeMe(String msg) {
		error("writeMe: " + msg);
	}
	public static void writeMe() {
		error("writeMe");
	}

    /**
     * Flushes the standard output stream.
     */
    public static void flush() {
        if (isVerbose() && !doNotPrintToSystemDotOut) { System.out.flush(); }
    }

    /**
     * Sort (in place this list of doubles and remove duplicate values (where
     * 'duplicate(a,b)' is 'not diffDoubles(a,b).'
     *
     * Sort (in place this list of doubles and remove duplicate values (where
     * 'duplicate(a,b)' is defined by the comparator). public static <E> void
     * sortAndRemoveDuplicates(List<E> items, Comparator<E> comparator) {
     * Collections.sort(items); <--- error here E prev = null; for (Iterator<E>
     * iter = items.iterator(); iter.hasNext(); ) { E item = iter.next(); if
     * (prev == null || comparator.compare(item, prev) == 0) { prev = item; } //
     * BUG: wont remover duplicate NULLS. Use a counter to see if at first item?
     * else { iter.remove(); } } }
     *
     * @param items List to be sorted and duplicates removed.
     */
    public static void sortListOfDoublesAndRemoveDuplicates(List<Double> items, double tolerance, double toleranceSmallNumbers) {  // TODO use the above and make diffDoubles a comparator.
    	Collections.sort(items);

    	Double prev = null;
    	for (Iterator<Double> iter = items.iterator(); iter.hasNext(); ) {
    		Double d = iter.next();
    		if (prev == null || diffDoubles(prev, d, tolerance, toleranceSmallNumbers)) { prev = d; }
    		else { iter.remove(); }
    	}
	}


    public static void sortListOfDoublesAndRemoveDuplicates(List<Double> items) {
    	sortListOfDoublesAndRemoveDuplicates(items, EQUIVALENCE_TOLERANCE, EQUIVALENCE_TOLERANCE_SMALL_NUMBERS);
    }
    
    /**
     * "Safely" returns the size of a collection.
     * 
     * @param collection
     *                A collection.
     * @return The size of the given collection, or zero if the collection is null.
     */
    public static int getSizeSafely(Collection<?> collection) {
        if (collection == null) { return 0; }
        return collection.size();
    }
    public static int getSizeSafely(Map<?,?> map) {
        if (map == null) { return 0; }
        return map.size();
    }
    public static int getSizeSafely(String str) {
        if (str == null) { return 0; }
        return str.length();
    }
    public static int getSizeSafely(Iterator<?> collection) {
    	if (collection == null) { return 0; }
    	int counter = 0;
    	while(collection.hasNext()) {
    		collection.next();
    		counter++;
    	}
    	return counter;
    }
    public static int getSizeSafely(Integer integer) { // This version helps if we lookup in a <Object,Integer> map; i.e., default to 0 if not there. 
        if (integer == null) { return 0; }
        return integer;
    }

    public static String getStringWithLinePrefix(String string, String prefix) {
        if (prefix != null && prefix.isEmpty() == false && string.isEmpty() == false) {

            StringBuilder stringBuilder = new StringBuilder();


            int index = -1;
            int lastIndex = 0;

            stringBuilder.append(prefix);

            while ((index = string.indexOf("\n", index + 1)) != -1) {
                String s = string.substring(lastIndex, index + 1);

                if (s.isEmpty() == false) {
                    if (lastIndex != 0) {
                        stringBuilder.append(prefix);
                    }
                    stringBuilder.append(s);
                }

                lastIndex = index + 1;
            }

            if (lastIndex != 0) {
                stringBuilder.append(prefix);
            }
            stringBuilder.append(string.substring(lastIndex, string.length()));

            return stringBuilder.toString();
        }
        else {
            return string;
        }
    }

    /**
     * Create a file-name string from this directory and (possibly partial) fileName. 
     * (Could just return a File, but this is what other methods are expecting.)
     * 
     * @param directory
     *            The directory containing the file.
     * @param fileName
     *            The name of the file.
     * @return A path string indicating the given file within the given directory.
     */
    // TODO cleanup
    public static String createFileNameString(String directoryRaw, String fileNameRaw) {
    	String directory = replaceWildCards(directoryRaw);
    	String fileName  = replaceWildCards(fileNameRaw);
    	
        if (directory == null) { return fileName; }
        File f = new CondorFile(fileName);
        if (f.isAbsolute()) { return fileName; }

        f = new CondorFile(directory, fileName);
        ensureDirExists(f);
        return f.getPath();
    }
    
    // Should we cache?  If we do, cache needs to be cleared whenever any of these keywords are changed.
    private static Map<String,String> environmentVariableResolutionCache = new HashMap<String,String>(4);
    public static String replaceWildCards(String original) {
    	if (original == null) { return null; }
    	String lookup = environmentVariableResolutionCache.get(original);
    	if (lookup != null) { return lookup; }

        lookup = original;

    	lookup =   lookup.contains("MYUSERNAME")       == false ? lookup : lookup.replaceAll("MYUSERNAME",       getMyUserName()); // Break into multiple lines so we can localize bugs better.
    	lookup =   lookup.contains("MYPATHPREFIX")     == false ? lookup : lookup.replaceAll("MYPATHPREFIX",     getMyPathPrefix());
    	lookup =   lookup.contains("SHAREDPATHPREFIX") == false ? lookup : lookup.replaceAll("SHAREDPATHPREFIX", getSharedPathPrefix());
    	lookup =   lookup.contains("MYSCRATCHDIR")     == false ? lookup : lookup.replaceAll("MYSCRATCHDIR",     getMyScratchDir());
    	environmentVariableResolutionCache.put(original, lookup);
    	return lookup;
    }	
	public static String replaceWildCardsAndCheckForExistingGZip(String fileNameRaw) {
		String fileName = replaceWildCards(fileNameRaw);
		if (fileName.endsWith(".gz")) { return fileName; } // If already a gzip'ed file, simply return.
		
		// Otherwise see if BOTH versions exist.
		File regular = new CondorFile(fileName);
		File gZipped = new CondorFile(fileName + ".gz");
		boolean regExists = regular.exists();
		boolean zipExists = gZipped.exists();
		if (regExists && zipExists) {
			long dateReg = regular.lastModified();
			long dateZip = gZipped.lastModified();
			
			if  (dateZip >= dateReg) { 
				warning("Both regular and gzip'ed versions of this file exist; will use NEWER one:\n " + fileName + ".gz");
				return fileName + ".gz";  // Use the NEWER file.
			}
			warning(    "Both regular and gzip'ed versions of this file exist; will use NEWER one:\n " + fileName );
			return fileName;
		}
		if (gZipped.exists()) {
			return fileName + ".gz";
		}
		return fileName;
	}
    
    // Allow user names to be overwritten, though that can be dangerous.
    public static void setMyUserName(String newValue) {
    	MYUSERNAME = Matcher.quoteReplacement(newValue);
    	environmentVariableResolutionCache.clear();
    }
    public static void setMyPathPrefix(String newValue) {
    	MYPATHPREFIX = Matcher.quoteReplacement(newValue);
    	environmentVariableResolutionCache.clear();
    }
    public static void setSharedPathPrefix(String newValue) {
    	SHAREDPATHPREFIX = Matcher.quoteReplacement(newValue);
    	environmentVariableResolutionCache.clear();
    }
    public static void setMyScratchDir(String newValue) {
    	MYSCRATCHDIR = Matcher.quoteReplacement(newValue);
    	environmentVariableResolutionCache.clear();
    }
    
    public static String getMyUserName() {
    	if (MYUSERNAME == null) { setMyUserName(getUserName(true)); } 	// Probably no need for quoteReplacement on MYUSERNAME, but do on all for consistency/simplicity.
    	return MYUSERNAME;
    }
    public static String getMyPathPrefix() {
    	return MYPATHPREFIX;
    }
    public static String getSharedPathPrefix() {
    	return SHAREDPATHPREFIX;
    }	
	public static String getMyScratchDir() {
    	if (MYSCRATCHDIR == null) { setMyScratchDir(help_getScratchDirForUser()); } // Will get into an infinite loop without the "help_" prefix.
    	return MYSCRATCHDIR;
	}

    /**
     * Waits for input on standard input after displaying "Waiting for user input".
     * 
     * @return
     * @see Utils#waitHere(String)
     */
    public static boolean waitHere() {
    	return waitHere("", false, null);
    }
    public static boolean waitHere(String msg) {
    	return waitHere(msg, false, null);
    }
    public static boolean waitHeref(String msg, Object... args) {
    	return waitHere(String.format(msg, args));
    }
    public static boolean waitHere(String msg, String skipWaitString) {
        return waitHere(msg, false, skipWaitString);
    }
    public static boolean waitHereRegardless() {
    	return waitHere("", true, null);
    }
    public static boolean waitHereRegardless(String msg) {
    	return waitHere(msg, true, null);
    }
    
    // Use the 
    public static boolean waitHereErr(String msg) {
    	if ( msg != null && msg.isEmpty() == false ) {
    		printlnErr(msg);
    	   	return waitHere(msg, false, null);
    	}
    	return waitHere(msg, false, null);
    }

    /** Prints out the message msg, possibly waiting for user input prior to continuing.
     *
     * waitHere prints out the message msg and then, based on the verbosity setting,
     * possibly waits for user input prior to continuing.
     * <p>
     * If waitHereRegardless is true,this method will always wait for user input.
     * <p>
     * If skipWaitString is non-null,
     * that string will be used to cache the number of times waitHere was called for that
     * specific skipWaitString and subsequent waitHere's will the same skipWaitString will
     * not wait, regardless of the verbosity.
     *
     * @param msg Message to be printed.
     * @param waitHereRegardless If true, this method will wait regardless of verbosity settings.
     * @param skipWaitString
     * @return False if an exception occurs while reading input from the user, true otherwise.
     */
    public static boolean waitHere(String msg, boolean waitHereRegardless, String skipWaitString) {

        int occurenceCount = 1;
        if ( skipWaitString != null ) {
           Integer i = warningCounts.get(skipWaitString);
           if ( i != null ) occurenceCount = i+1;
           warningCounts.put(skipWaitString, occurenceCount);
        }

      //  println(" waitHereRegardless=" + waitHereRegardless + " isWaitHereEnabled=" + isWaitHereEnabled());
    	if (!waitHereRegardless && !isWaitHereEnabled() && occurenceCount == 1) {
            if ( msg != null && msg.isEmpty() == false ) {
                print("\n% Skipping over this 'waitHere': " + msg + "\n", true);
            }
    		return true;
    	}

        if (!waitHereRegardless && occurenceCount > 1) {
            return true;
        }

        // Let's collect these in dribble files.
        warning_println("\nWaitHere:    " + msg);


		boolean hold = doNotPrintToSystemDotOut;
		doNotPrintToSystemDotOut = false; // If these printout become too much, we can add a 3rd flag to override these ...
        print("\n% WaitHere: " + msg + "\n%  ...  Hit ENTER to continue or 'e' to interrupt. ", waitHereRegardless);
        doNotPrintToSystemDotOut = hold;

		if ( CondorUtilities.isCondor() ) {
			error("\nSince this is a condor job, will exit.");
		} else { warning_println("NOTE: Utils.java thinks this job is NOT running under Condor."); }
		
        try {
        	if (inBufferedReader == null) { inBufferedReader = new BufferedReader(new InputStreamReader(System.in)); }
        	String readThis = inBufferedReader.readLine();
        //	println("read: " + readThis);
        	if (readThis != null && readThis.startsWith("e")) { // This had been 'interrupt' instead of 'error' but then these might not be immediately caught, and doing just that is the intent of an 'e' being pressed.
        		try {
        			error("You requested the current run be interrupted by returning something that starts with 'e' (for 'esc' or 'error' or 'elmo' or 'ebola').");
        		} catch (WILLthrownError e) {
        			reportStackTrace(e);
        			println("Hit the Enter key to continue if you wish.");
        			inBufferedReader.readLine();
        		}
        	}
        } catch (IOException e) {
            // Ignore any errors here.
        	inBufferedReader = null;  // If something went wrong, reset the reader. 
        	return false;
        }
        return true; // The main reason for returning values is so that waitHere's can be placed inside conditionals.
    }

    public static void cleanupAndExit(int returnCode) {

        if (dribbleStream != null) {
            dribbleStream.close();
        	compressFile(dribbleFileName);
        }

        if (dribbleStream2 != null) {
            dribbleStream2.close();
        	compressFile(dribbleFileName2);
        }

        if (debugStream != null) {
        	debugStream.close();
        	compressFile(debugFileName);
        }

        if (warningStream != null) {
        	warningStream.close();
        	compressFile(warningFileName);
        }

        if (warningShadowStream != null) {
        	warningShadowStream.close();
        	compressFile(warningShadowFileName);
        }

        System.exit(returnCode);
    }

    /**
     * Prints a warning header on standard output.
     */
    public static void warning() {
        println("\n***** Warning *****\n"); // Don't print to warning stream since no message.
    }
    /** Prints a warning header on standard output that includes the given message.
     *
     * @param str A message describing the warning.
     */
    public static void warning(String str) {
        warning(str, null);
    }
    public static void warningf(String strFormat, Object... args) {
    	warning(String.format(strFormat, args));
    }
    public static void warning(MessageType type, String str) {
        if ( isMessageTypeEnabled(type) ) warning(str, null);
    }
    public static void warningOnce(String str) {
        warning(str, str);
    }
    /** Prints a warning header on standard output that includes the given message.
     *
     * If skipWarningString is non-null, the warning associated with that string will only be
     * printed the first time the warning occurs.
     *
     * @param str A message describing the warning.
     * @param skipWarningString
     */
    public static void warning(String str, String skipWarningString) {

        int occurenceCount = 1;
        if ( skipWarningString != null ) {
           Integer i = warningCounts.get(skipWarningString);
           if ( i != null ) occurenceCount = i+1;
           warningCounts.put(skipWarningString, occurenceCount);
        }

        if ( occurenceCount == 1 ) {
        	warning_println("\nWARNING: " + str);
            println("\n***** Warning: " + str + " *****\n");
        }
    }
    /** Prints a warning header on standard output that includes the given message and waits sleepInSeconds.
     *
     * @param str A message describing the warning.
     * @param sleepInSeconds Number of seconds to wait after printing the warning.
     */
    public static void warning(String str, int sleepInSeconds) {
        warning(str, sleepInSeconds, null);
    }
    public static void warning(MessageType type, String str, int sleepInSeconds) {
        if ( isMessageTypeEnabled(type) ) warning(str, sleepInSeconds);
    }

    /** Prints a warning header on standard output that includes the given message and waits sleepInSeconds.
     *
     * If skipWarningString is non-null, the warning associated with that string will only be
     * printed the first time the warning occurs.
     *
     * @param str A message describing the warning.
     * @param sleepInSeconds Number of seconds to wait after printing the warning.
     * @param skipWarningString
     */
    public static void warning(String str, int sleepInSeconds, String skipWarningString) {
        int occurenceCount = 1;
        if ( skipWarningString != null ) {
           Integer i = warningCounts.get(skipWarningString);
           if ( i != null ) occurenceCount = i+1;
           warningCounts.put(skipWarningString, occurenceCount);
        }

        if ( occurenceCount == 1 ) {
            warning_println("\nWARNING: " + str);

            // Make sure we only wait if the user is at a verbosity level where it
            // makes sense to wait.
            if ( isWaitHereEnabled() ) {
                println("\n***** Warning: " + str + " (Waiting " + sleepInSeconds + " seconds.) *****\n");
                sleep(sleepInSeconds);
            } else {
                println("\n***** Warning: " + str + " *****\n");
            }
        }
    }    
    public static void severeWarning(String str) {
        warning_println("\nSEVERE:  " + str);
    	if (isSevereErrorThrowsEnabled()) { error(str); }
    	else { println("\n% ***** Severe Warning: " + str + " *****\n", true); }
    }
    
    public static void sleep(int sleepInSeconds) {
        if (sleepInSeconds > 0) {
            try { // Sleep a little when giving a warning.

            Thread.sleep(1000 * sleepInSeconds); // TODO allow this to be set in a global variable.
            } catch (InterruptedException e) {  }
        }    	
    }

    /**
     * @param old
     *            A string.
     * @return A copy of the given string with the case of the first character
     *         changed (e.g., "xyz" becomes "Xyz").
     */
    public static String changeCaseFirstChar(String old) {
        // Seems String.replace can't be used to simply replace the FIRST occurrence of a char, so brute-force this.
        if (old == null || old.equals("")) {
            return old;
        }
        char    firstChar          = old.charAt(0);
        boolean firstCharLowerCase = Character.isLowerCase(firstChar);
        String oldFirstChar = Character.toString(firstChar);
        String newFirstChar = (firstCharLowerCase ? oldFirstChar.toUpperCase(): oldFirstChar.toLowerCase());
        // old is at least 1 character long, so taking the substring is guaranteed to work
        // If old is only 1 character long 'old.substring(1)' returns the empty string
        return newFirstChar + old.substring(1);
    }
    
    public static String upperCaseFirstLetter(String str) {
    	if (getSizeSafely(str) < 1) { return str; }
		if (Character.isUpperCase(str.charAt(0))) { return str; }
		else {return changeCaseFirstChar(str); }
    }

    /**
     * Creates a dribble file in the given directory.
     * 
     * @param directory
     *            The path of the directory in which to create the dribble file.
     */
    public static void createDribbleFileInDirectory(String directory) {
        createDribbleFile(directory + "/dribble.txt");
    }

    /**
     * Creates a dribble file named "dribble.txt" in the current working
     * directory.
     * 
     * @see Utils#createDribbleFile(String)
     */
    public static void createDribbleFile() {
        if ( dribbleStream == null ) {
            createDribbleFile("dribble.txt");
        }
    }

    /**
     * Creates a dribble file with the given name in the current working
     * directory.
     * 
     * @param fileName
     *            The name of the dribble file.
     */
    public static String dribbleFileName = null; // This is one place that this class maintains state (so if two threads running, their dribble files will interfere).
    public static void createDribbleFile(String fileName) {
    //	Utils.waitHere("createDribbleFile: " + fileName);
    	if (dribbleStream != null) { 
    		dribbleStream.println("\n\n// Closed by a createDribble call with file = " + fileName);
    	}
    	createDribbleFile(fileName, false);
    }
    public static void createDribbleFile(String fileNameRaw, boolean createEvenForNonDevelopmentRuns) {
    	if (doNotCreateDribbleFiles) { return; }
    	if (!isVerbose() && !createEvenForNonDevelopmentRuns) { return; }
    	closeDribbleFile();
    	String fileName = replaceWildCards(fileNameRaw);
        try {
        	ensureDirExists(fileName);
            CondorFileOutputStream outStream = new CondorFileOutputStream(fileName);
            dribbleStream = new PrintStream(outStream, false); // No auto-flush (can slow down code).
            dribbleFileName = fileName;
            println("% Running on host: " + getHostName());
        } catch (FileNotFoundException e) {
        	reportStackTrace(e);
            error("Unable to successfully open this file for writing:\n " + fileName + ".\nError message: " + e.getMessage());
        }
    }
    public static String dribbleFileName2 = null; // This is one place that this class maintains state (so if two threads running, their dribble files will interfere).
    public static void createDribbleFile2(String fileName) {
    	createDribbleFile2(fileName, false);
    }
    public static void createDribbleFile2(String fileNameRaw, boolean createEvenForNonDevelopmentRuns) {
    	if (doNotCreateDribbleFiles) { return; }
    	if (!isDevelopmentRun() && !createEvenForNonDevelopmentRuns) { return; }
    	closeDribbleFile2();
    	String fileName = replaceWildCards(fileNameRaw);
        try {
        	ensureDirExists(fileName);
            CondorFileOutputStream outStream = new CondorFileOutputStream(fileName);
            dribbleStream2 = new PrintStream(outStream, false); // No auto-flush (can slow down code).
            dribbleFileName2 = fileName;
        } catch (FileNotFoundException e) {
        	reportStackTrace(e);
            error("Unable to successfully open this file for writing: " + fileName + ".  Error message: " + e.getMessage());
        }
    }

    public static void closeDribbleFile() {
    	dribbleFileName = null;
    	if (dribbleStream == null) { return; }
    	dribbleStream.close();
    	dribbleStream = null;
    }
    public static void closeDribbleFile2() {
    	dribbleFileName2 = null;
    	if (dribbleStream2 == null) { return; }
    	dribbleStream2.close();
    	dribbleStream2 = null;
    }
    public static void closeDebugFile() {
    	debugFileName = null;
    	if (debugStream == null) { return; }
    	debugStream.close();
    	debugStream = null;
    }
    public static void closeWarningFile() {
    	warningFileName = null;
    	if (warningStream == null) { return; }
    	warningStream.close();
    	warningStream = null;
    }
    public static void closeWarningShadowFile() {
    	warningShadowFileName = null;
    	if (warningShadowStream == null) { return; }
    	warningShadowStream.close();
    	warningShadowStream = null;
    }
    public static void closeAll() {
    	closeDribbleFile();
    	closeDribbleFile2();
    	closeDebugFile();
    	closeWarningFile();
    }

    public  static String debugFileName     = null; // This is another place that this class maintains state (so if two threads running, their debug files will interfere).
    public  static int    maxDebugLineWidth = 5000;   // Ditto (buggy if the caller inserts line feeds).
    public  static void createDebugFile(String fileName) {
    	createDebugFile(fileName, false);
    }
    public static void createDebugFile(String fileNameRaw, boolean createEvenForNonDevelopmentRuns) {
    	if (doNotCreateDribbleFiles) { return; }
    	if (!isVerbose() && !createEvenForNonDevelopmentRuns) { return; }
    	closeDebugFile();
    	String fileName = replaceWildCards(fileNameRaw);
        try {
        	ensureDirExists(fileName);
            CondorFileOutputStream outStream = new CondorFileOutputStream(fileName);
            debugStream = new PrintStream(outStream, false); // No auto-flush (can slow down code).
            debugFileName = fileName;
        } catch (FileNotFoundException e) {
        	reportStackTrace(e);
            error("Unable to successfully open this file for writing: " + fileName + ".  Error message: " + e.getMessage());
        }
    }
    public  static String warningFileName = null; // This is another place that this class maintains state (so if two threads running, their debug files will interfere).
    public  static void createWarningFile(String fileName) {
    	createWarningFile(fileName, false);
    }
    public static void createWarningFile(String fileNameRaw, boolean createEvenForNonDevelopmentRuns) {
    	if (!isDevelopmentRun() && !createEvenForNonDevelopmentRuns) { return; }
    	closeWarningFile();
    	String fileName = replaceWildCards(fileNameRaw);
        try {
        	ensureDirExists(fileName);
            CondorFileOutputStream outStream = new CondorFileOutputStream(fileName);
            warningStream = new PrintStream(outStream, false); // No auto-flush (can slow down code).
            warningFileName = fileName;
        } catch (FileNotFoundException e) {
        	reportStackTrace(e);
            error("Unable to successfully open this file for writing: " + fileName + ".  Error message: " + e.getMessage());
        }
    }
    public  static String warningShadowFileName = null; // Also write warnings to this file (one might go into one directory and the other into a different directory).
    public static void createWarningShadowFile(String fileNameRaw) {
    	if (!isDevelopmentRun()) { return; }
    	closeWarningShadowFile();
    	String fileName = replaceWildCards(fileNameRaw);
        try {
        	ensureDirExists(fileName);
            CondorFileOutputStream outStream = new CondorFileOutputStream(fileName);
            warningShadowStream = new PrintStream(outStream, false); // No auto-flush (can slow down code).
            warningShadowFileName = fileName;
        } catch (FileNotFoundException e) {
        	reportStackTrace(e);
            error("Unable to successfully open this file for writing: " + fileName + ".  Error message: " + e.getMessage());
        }
    }
    
    // Keep using the same warning file if one is open.
    public static void reuseOrCreateWarningShadowFile(String fileName, String headStr) {
    	if (warningShadowFileName != null && fileName.equals(warningShadowFileName)) {
    		warningShadowStream.println("\n\n/////////////////////////////////////////////////////////////////////////\n\n");
    	} else {
    		createWarningShadowFile(fileName);
    	}
    	warning_println(headStr);
    }
    
    private static void warning_println(String str) {
		if (warningStream       != null) { warningStream.println(str);       }
		if (warningShadowStream != null) { warningShadowStream.println(str); }
    }
    
    public static void printlnALL(String str) {
    	printlnALL(str, false);
    }
    public static void printlnALL(String strRaw, boolean printRegardless) {
    	if (printRegardless || isVerbose()) {
    		String str = (strRaw == null || strRaw.length() <= maxStringLength ? strRaw : strRaw.substring(0, maxStringLength) + " ...");
    		if (!doNotPrintToSystemDotOut) { System.out.println(str); }
    		if (debugStream   != null) { debugStream.println(limitStringWidth(str, maxDebugLineWidth)); }
    		if (dribbleStream != null) { dribbleStream.println(str); }
    	}
    }
    public static void printALL(String str) {
    	printALL(str, false);
    }
    public static void printALL(String strRaw, boolean printRegardless) {
    	if (printRegardless || isVerbose()) {
    		String str = (strRaw == null || strRaw.length() <= maxStringLength ? strRaw : strRaw.substring(0, maxStringLength) + " ...");
    		if (!doNotPrintToSystemDotOut) { System.out.print(str); }
    		if (debugStream   != null) { debugStream.print(  limitStringWidth(str, maxDebugLineWidth)); }
    		if (dribbleStream != null) { dribbleStream.print(str); }
    	}
    }
    public static void debug_println(String str) {
    	debug_println(str, false);
    }
    public static void debug_println(String strRaw, boolean printRegardless) {
    	if (printRegardless || isVerbose()) {
    		String str = (strRaw == null || strRaw.length() <= maxStringLength ? strRaw : strRaw.substring(0, maxStringLength) + " ...");
    		if (!doNotPrintToSystemDotOut) { System.out.println(str); }
    		if (debugStream != null) { debugStream.println(limitStringWidth(str, maxDebugLineWidth)); }
    	}
    }
    public static void debug_print(String str) {
    	debug_print(str, false);
    }
    public static void debug_print(String strRaw, boolean printRegardless) {
    	if (printRegardless || isVerbose()) {
    		String str = (strRaw == null || strRaw.length() <= maxStringLength ? strRaw : strRaw.substring(0, maxStringLength) + " ...");
    		if (!doNotPrintToSystemDotOut) { System.out.print(str); }
    		if (debugStream != null) { debugStream.print(limitStringWidth(str, maxDebugLineWidth)); }
    	}
    }
    
    public static String limitStringWidth(String str, int maxWidth) {
    	if (str == null) { return null; }
    	int len = str.length();
    	
    	if (len <= maxWidth) { return str; }
    	return str.substring(0, maxWidth) + "...";
    }   
    
    public static boolean intersectingCollections(Collection<? extends Object> collection1, Collection<? extends Object> collection2) {
   	 if (collection1 == null || collection2 == null) { return false; }
   	 int size1 = collection1.size();
   	 int size2 = collection2.size();
   	 if (size1 < size2) {
   		 for (Object obj : collection1) if (collection2.contains(obj)) { return true; }
   		 return false;
   	 }
   	 for (Object obj : collection2) if (collection1.contains(obj)) { return true; }
   	 return false;
    }

    
    /**
     * Sets the seed on the random instance.
     * 
     * @param seed
     *            The random seed.
     */
    public static void seedRandom(long seed) {
        randomInstance.setSeed(seed);
    }

    /**
     * @return The next random double.
     */
    public static double random() {
        return randomInstance.nextDouble();
    }

    /**
     * @param upper
     *            The upper bound on the interval.
     * @return A random number in the interval [1, upper).
     * @see Utils#randomInInterval(int, int)
     */
    public static int random1toN(int upper) {
        return randomInInterval(1, upper);
    }

    /**
     * @param upper
     *            The upper bound on the interval.
     * @return A random number in the interval [1.0, upper).
     * @see Utils#randomInInterval(double, double)
     */
    public static double random1toN(double upper) {
        return randomInInterval(1.0, upper);
    }

    /**
     * @param upper
     *            The upper bound on the interval.
     * @return A random number in the interval [0, upper).
     * @see Utils#randomInInterval(int, int)
     */
    public static int random0toNminus1(int upper) {
        return randomInInterval(0, upper);
    }

    /**
     * @param upper
     *            The upper bound on the interval.
     * @return A random number in the interval [0.0, upper).
     * @see Utils#randomInInterval(double, double)
     */
    public static double random0toNminus1(double upper) {
        return randomInInterval(0.0, upper);
    }

    /**
     * @param lower
     *            The lower end of the interval.
     * @param upper
     *            The upper end of the interval. It is not possible for the
     *            returned random number to equal this number.
     * @return Returns a random integer in the given interval [lower, upper).
     */
    public static int randomInInterval(int lower, int upper) {
        return lower + (int) Math.floor(random() * (upper - lower));
    }

    /**
     * @param lower
     *            The lower end of the interval.
     * @param upper
     *            The upper end of the interval. It is not possible for the
     *            returned random number to equal this number.
     * @return Returns a random integer in the given interval [lower, upper).
     */
    public static double randomInInterval(double lower, double upper) {
        return lower + random() * (upper - lower);
    }

    /**
     * Shorten this list to maxLength by removing elements IN PLACE. Elements
     * are randomly discarded until the list is short enough. If the list is
     * already short enough, it is unchanged.
     * 
     * @param <E>
     *            The element type of the list.
     * @param items
     *            The list.
     * @param maxLength
     *            The maximum length the list should be.
     * @return The given list with maxLength or fewer elements.
     */
    public static <E> List<E> reduceToThisSizeByRandomlyDiscardingItemsInPlace(List<E> items, int maxLength) {
    	if (items == null) { return null; }
        int size = items.size();
        if (size <= maxLength) { return items; }

        int numberToDiscard = size - maxLength;
        for (int i = 0; i < numberToDiscard; i++) {
            int index = randomInInterval(0, size);
            items.remove(index);
            size--;
        }
        return items; // Probably no need to return this, since caller knows, but might as well do so (for one thing, this allows the caller to use a functional programming style).
    }
    /**
     * Reduce this set to maxLength by removing elements IN PLACE. Elements
     * are randomly discarded until the set is small enough. If the set is
     * already small enough, it is unchanged.  (Since cannot remove the ith object
     * from a set directly, this is a bit inefficient.  Will take O(m x n),
     * where m equals the number of items to remove and n is the size of the set.
     * 
     * @param <E>
     *                The element type of the list.
     * @param items
     *                The list.
     * @param maxLength
     *                The maximum length the list should be.
     * @return The given list with maxLength or fewer elements.
     */
    public static <E> Set<E> reduceToThisSizeByRandomlyDiscardingItemsInPlace(Set<E> items, int maxLength) {
    	if (items == null) { return null; }
        int size = items.size();
        if (size <= maxLength) { return items; }

        int numberToDiscard = size - maxLength;
        for (int i = 0; i < numberToDiscard; i++) {
            int index = randomInInterval(0, size);
        	int counter = 0;
        	boolean foundIt = false;
    		for (Iterator<E> iter = items.iterator(); iter.hasNext();) {
    			E next = iter.next(); // Need to do the next() else will not advance in the iterator.
    			if (counter++ == index) { 
    				if (!items.remove(next)) { error("Failed to remove item #" + index + " = " + next); }
    				foundIt = true;
    				break;
    			}
    		}
    		if (!foundIt) { error("Could not find the " + index + "th item in a set of size " + items.size()); }
            size--;
        }
        return items; // Probably no need to return this, since caller knows, but might as well do so (for one thing, this allows the caller to use a functional programming style).
    }
    
    /**
     * Get the index'th item from this set.  LinkedHashSet's have a predictable iteration order, so
     * best to use with those, but this isn't necessary (e.g., if requesting a random item) - use getIthItemInCollectionUnsafe() for this case.
     * @param <E>
     * @param items
     * @param index
     * @return
     */
    public static <E> E getIthItemInCollection(LinkedHashSet<E> items, int index) {
    	int counter = 0;
		for (Iterator<E> iter = items.iterator(); iter.hasNext();) {
			E next = iter.next(); // Need to do the next() else will not advance in the iterator.
			if (counter++ == index) { return next; }
		}
		error("Could not find the " + index + "th item in a set of size " + items.size());
		return null;
    }
    /**
     * Variant of getIthItemInCollection() that works with any collection.
     * @param <E>
     * @param items
     * @param index
     * @return
     */
    public static <E> E getIthItemInCollectionUnsafe(Collection<E> items, int index) {
    	int counter = 0;
		for (Iterator<E> iter = items.iterator(); iter.hasNext();) {
			E next = iter.next(); // Need to do the next() else will not advance in the iterator.
			if (counter++ == index) { return next; }
		}
		error("Could not find the " + index + "th item in a collection of size " + items.size());
		return null;
    }
    // Can do this potentially faster with get() - e.g., should be constant time with an ArrayList.
    public static <E> E getIthItemInCollectionUnsafe(List<E> items, int index) {
    	return items.get(index);
    }

    /**
     * Randomly select a number of items from this list.
     * 
     * @param <E>
     *            The element type of the list.
     * @param numberToChoose
     *            How many elements to return.
     * @param list
     *            The list of elements to choose from.
     * @return A new list containing the specified number of elements from the
     *         given list, or the original list if it was shorter than
     *         numberToChoose.
     * @see Utils#chooseRandomNfromThisList(int, List, boolean)
     */
    public static <E> List<E> chooseRandomNfromThisList(int numberToChoose, List<E> list) {
        return chooseRandomNfromThisList(numberToChoose, list, false);
    }
    
    /**
     * Randomly (uniformly) choose an item from this list.  If list=null or is empty, return null;
     * @param <E>
     * @param list
     * @return
     */
    public static <E> E chooseRandomFromThisCollection(List<E> list) {
    	if (list == null) { return null; }
    	int size = list.size();
    	if (size == 0) { return null; }
    	return list.get(random0toNminus1(size));
    }
    
    /**
     * Randomly (uniformly) choose an item from this collection.  If collection=null or is empty, return null;
     * @param <E>
     * @param collection
     * @return
     */
    public static <E> E chooseRandomFromThisCollection(Collection<E> collection) {
    	if (collection == null) { return null; }
    	int size = collection.size();
    	if (size == 0) { return null; }
    	return getIthItemInCollectionUnsafe(collection, random0toNminus1(size));
    }

    /**
     * Randomly select a number of items from this list. If
     * maintainOrdering=true, the order in the original list will be preserved
     * (possibly at a runtime cost).
     * 
     * @param <E>
     *            The element type of the list.
     * @param numberToChoose
     *            How many elements to return.
     * @param list
     *            The list of elements to choose from.
     * @param maintainOrdering
     *            Whether the order of the list is maintained.
     * @return A new list containing the specified number of elements from the
     *         given list, or the original list if it was shorter than
     *         numberToChoose.
     */
    public static <E> List<E> chooseRandomNfromThisList(int numberToChoose, List<E> list, boolean maintainOrdering) {
        if (list == null || numberToChoose < 0) { return null; }
        int length = list.size();

        if (numberToChoose >= length || length < 1) { return list; } // TODO make a copy in this case?

        List<E> result = new ArrayList<E>(numberToChoose);
        if (numberToChoose == 0) {  return result; }

        if (!maintainOrdering && numberToChoose < length / 4) { // We'll collect items if only a few.
            int counter = 0;
            while (counter < numberToChoose) {
                int itemToKeep = random0toNminus1(length);
                E selectedItem = list.get(itemToKeep);
                if (!result.contains(selectedItem)) {
                    result.add(selectedItem);
                    counter++;
                }
            }
        } else { // Otherwise we'll copy list then randomly discard items.  Notice there the ORDER of the list is unchanged (which is why the first version can be overridden).
            result.addAll(list); // Copy the list.
            int counter = length;
            while (counter > numberToChoose) { // Could be a FOR loop, but mirror what is done above.
                int itemToDiscard = random0toNminus1(counter);
                result.remove(itemToDiscard);
                counter--;
            }

        }
        return result;
    }
    
    /** Randomly remove (in place) this many items from this collection.
     *  This can be slow, since it can take linear time to find each item.
     * @param <E>
     * @param collection
     * @param numberToRemove
     */
    public static <E> void randomlyRemoveThisManyItems(Collection<E> collection, int numberToRemove) {
    	if (numberToRemove < 1) { return; }
    	int counter = collection.size();
    	for (int i = 0; i < numberToRemove; i++) {
            int itemOrdinalNumberToDiscard = random0toNminus1(counter);
            E item = getIthItemInCollectionUnsafe(collection, itemOrdinalNumberToDiscard);
            if (!collection.remove(item)) { error("Could not find item='" + item + "', which is item#" + itemOrdinalNumberToDiscard); }
            counter--;
    	}
    }

    /**
     * @param d
     *            A number (double).
     * @return Whether the given double is a number (not not a number). (Note
     *         that by this definition infinity is included as a number.)
     */
    public static boolean isaNumber(double d) {
        return !Double.isNaN(d);
    }

    /**
     * Compares two numbers to see if they are different.
     * 
     * @param a
     *            A number.
     * @param b
     *            A number.
     * @return True if the two given numbers differ by more than a certain
     *         tolerance.
     * @see #EQUIVALENCE_TOLERANCE
     */
    public static boolean diffDoubles(double a, double b, double tolerance, double toleranceSmallNumbers) {
    	double  diff        = Math.abs(a - b);
        boolean firstResult = diff > tolerance;
        if (firstResult) { return true; }
        // See if we're dealing with small numbers.
        if (a > -1 && a < 1 && b > -1 && b < 1) {
        	return diff > toleranceSmallNumbers;
        }
        return firstResult;
    }
    public static boolean diffDoubles(double a, double b) {
    	return diffDoubles(a, b, EQUIVALENCE_TOLERANCE, EQUIVALENCE_TOLERANCE_SMALL_NUMBERS);
    }

    public static String truncPad(double d, int decimals, int width) {
    	String spec = "%" + width + "s";
    	return String.format(spec, truncate(d, decimals));
    }
    
    /**
     * Formats the given floating point number by truncating it to one decimal
     * place.
     * 
     * @param d
     *            A number.
     * @return A string containing the given number formatted to one decimal
     *         place.
     * @see Utils#truncate(double, int)
     */
    public static String truncate(double d) {
        return truncate(d, 1);
    }

    /**
     * Format the given floating point number by truncating it to the specified
     * number of decimal places.
     * 
     * @param d
     *            A number.
     * @param decimals
     *            How many decimal places the number should have when displayed.
     * @return A string containing the given number formatted to the specified
     *         number of decimal places.
     */
    public static String truncate(double d, int decimals) {
    	double abs = Math.abs(d);
    	if (abs > 1e13)             { 
    		return String.format("%."  + (decimals + 4) + "g", d);
    	} else if (abs > 0 && abs < Math.pow(10, -decimals))  { 
    		return String.format("%."  +  decimals      + "g", d);
    	}
        return     String.format("%,." +  decimals      + "f", d);
    }
    public static String truncateNoSciNotation(double d, int decimals) {
        return String.format("%." + decimals + "f", d);
    }

    /**
     * Truncates a double and returns it as a string with at least one and at
     * most "decimals" decimal places. Notice that this does not ROUND (i.e, if
     * the first of the dropped digits was '5' or higher, could add 1 to the
     * last digit returned .. One complication of trying to implement rounding
     * is that one needs to deal with "carrying" (eg, 0.99995 becoming 1.0000).
     * Might want to check out to see if Java now handles this better, say in
     * NumberFormat or Formatter. If requested, puts space in front of positive
     * numbers - so printouts align.
     * 
     * @param d
     *            A number.
     * @param decimals
     *            The number of decimal places in the string version.
     * @param addSpaceBeforePosNumbers
     *                Whether to add space before positive numbers (so they are in alignment with the '-' sign before negative numbers).
     * @return A string containing the number formatted as described above.
     */
    // TODO convert to standard Java number formatting
    public static String truncate(double d, int decimals, boolean addSpaceBeforePosNumbers) { // This should always produce at least one decimal (by official documentation some years ago).
        String str = String.format("$,d", d);
        int index = str.indexOf(".");

        // Patch for the above bug.  (Doesn't add "decimals" 0's, but that's ok.)
        if (index < 0)  return str.concat(".0");

        int indexE = indexOfIgnoreCase(str, "e", index);
        if (indexE > 0) // In scientific notation.
        {
            String result = str.substring(0, Math.min(indexE, index + decimals + 1)) + "e" + Integer.valueOf(str.substring(indexE + 1));

            if (d < 0 || !addSpaceBeforePosNumbers)
                return result;
            else
                return " " + result;
        }
        if (d < 0 || !addSpaceBeforePosNumbers)
            return str.substring(0, Math.min(str.length(), index + decimals + 1));
        else
            return " " + str.substring(0, Math.min(str.length(), index + decimals + 1));
    }

    /**
     * A version of java.lang.String.indexOf(String, int) that ignores case.
     * (Since there isn't an CASELESS indexOf, adapt the existing code.)
     * 
     * @param str
     *            The string to search.
     * @param query
     *            The string to search for.
     * @param fromIndex
     *            The index to start at.
     * @return The index of the start of query, or -1 if the query was not
     *         found.
     * @see String#indexOf(String, int)
     */
    public static int indexOfIgnoreCase(String str, String query, int fromIndex) {
        int qlength = query.length();
        int max = (str.length() - qlength);

        test: for (int i = ((fromIndex < 0) ? 0 : fromIndex); i <= max; i++) {
            int k = 0, j = i, n = qlength;
            char schar, qchar;
            while (n-- > 0) {
                schar = str.charAt(j++);
                qchar = query.charAt(k++);
                if ((schar != qchar)
                        && (Character.toLowerCase(schar) != Character.toLowerCase(qchar)))
                    continue test;
            }
            return i;
        }
        return -1;
    }
    
    public static boolean startsWithIgnoreCase(String str, String query) {
    	int foundAt = indexOfIgnoreCase(str, query, 0); // This isn't very efficient ...
    //	Utils.waitHere("startsWithIgnoreCase(" + query + ") = " + foundAt);
    	return foundAt == 0;
    }
    
    /**
     * Convert [a,b,c] to [[a],[b],[c]]
     * @param <E>
     * @param listOfItemsToWrap
     * @return
     */
    public static <E> List<List<E>> wrapEachItemInList(List<E> listOfItemsToWrap) {
    	List<List<E>> results = new ArrayList<List<E>>(getSizeSafely(listOfItemsToWrap));
    	for (E item : listOfItemsToWrap) { results.add(wrapInList(item)); }
    	return results;
    }
    
    /**
     * Convert item to [item].
     * @param <E>
     * @param listToWrap
     * @return
     */
    public static <E> List<E> wrapInList(E listToWrap) {
    	List<E> results = new ArrayList<E>(1);
    	results.add(listToWrap);
    	return results;
    }
	
    /** Convert a set to a list, limiting the size of the list if necessary.
     * 
     * @param <E>
     * @param set
     * @param maxSize
     * @return
     */
	public static <E> List<E> convertSetToList(Set<E> set, int maxSize) {
		if (set == null || maxSize < 1) { return null; }
		List<E> result = new ArrayList<E>(set.size());
		result.addAll(set);
		if (result.size() > maxSize) { reduceToThisSizeByRandomlyDiscardingItemsInPlace(result, maxSize); }
		return result;
	}

    /**
     * Create the cross product of a list of list. I.e., { {a,b}, {c, d} -&gt; {
     * {a,c}, {a,d}, {b,c}, {b,d} }. Since this is general-purpose utility, it
     * has been placed here. If this causes memory-usage problems, convert to an
     * iterative version.
     * 
     * @param <E>
     *            The element type of the inner lists.
     * @param allArgPossibilities
     *                A list of lists containing the elements for the cross product.
     * @param maximumSize
     * @parem maximumSize
     * 				  The maximum size of the result. Items will be randomly deleted.
     * @return A list containing the cross product of the given lists.
     */
    public static <E> List<List<E>> computeCrossProduct(List<? extends Collection<E>> allArgPossibilities, int maximumSize) {
	    // NOTE: do not use Set<List<E>> since DUPLICATES will be removed.
	    // Here are some calculations for reducing the size of the cross-product set "as we go" (rather than during post-processing).
	    //   Li is the number of items that are expected to be produced after set i is recursively merged in.
	    //   L1 = maximumSize
	    //   Pi is the probability that an item in set i is added.
	    // 		L1 = P1 x S1 x L2 // L2 is the reduced set that comes from the first recursive call.
	    // 		L2 = P2 x S2 x L3 // L3                                        second
	    // 		...
	    // 		Ln = Pn x Sn      // The bottoming-out of the recursion.
	    //   After some algebra:
	    // 		P1 x P2 x ... x Pn = L1 / (S1 x S2 x ... Sn)
	    // 	 If we let Pi = Q / Si, where Q is the Nth root of L1, then we get what we want.
	    //	Note: we ignore SINGLETON sets in the calculation (i.e., of 'n'), since they don't impact size.
    	if (maximumSize < 1) { return null; }
    	double Q = -1.0;
        if (maximumSize < Integer.MAX_VALUE) {
        	int size    = 1; 
			int counter = 0;
			for (Collection<E> possibilities : allArgPossibilities) {
				size *= possibilities.size();
				if (possibilities.size() > 1) { counter++; }
			}
			if (size > maximumSize) { Q = Math.pow(maximumSize, 1.0/counter); }
        }
    	return computeCrossProduct(allArgPossibilities, Q);
    }
    /**
     * See computeCrossProduct(List<Collection<E>> allArgPossibilities, int maximumSize)
     * In this version, maximumSize defaults to infinity.
     * 
     * @param <E>
     * @param allArgPossibilities
     * @return
     */
    public  static <E> List<List<E>> computeCrossProduct(List<? extends Collection<E>> allArgPossibilities) {
    	return computeCrossProduct(allArgPossibilities, Integer.MAX_VALUE);
    }
    private static <E> List<List<E>> computeCrossProduct(List<? extends Collection<E>> allArgPossibilities, double Q) {
        if (allArgPossibilities == null) { return null; }
        int length = allArgPossibilities.size();
        if (length < 1) { return null; }
        List<List<E>> allArgPossibilitiesForRest = null;
        Collection<E> firstCollection = allArgPossibilities.get(0);
        int     sizeOfFirstCollection = firstCollection.size();
        if (length > 1) {
            allArgPossibilitiesForRest = computeCrossProduct(allArgPossibilities.subList(1, length), Q); //  Of the results of the recursion, about probOfRandomlyDiscarding * sizeOfFirstList
        }
        List<List<E>> results = new ArrayList<List<E>>(4);
        double prob =  Q / sizeOfFirstCollection;
        for (E term : firstCollection) { // For each choice for the first argument, ...
            if (allArgPossibilitiesForRest != null) {
                for (List<E> restArgs : allArgPossibilitiesForRest) { // ... combine with each possible choice for the rest of the args.
                	List<E> args = new ArrayList<E>(1 + restArgs.size());
                    args.add(term);
                    args.addAll(restArgs);
                    if (Q < 0.0 || sizeOfFirstCollection <= 1 || random() < prob) { results.add(args); }
                }
            } else { // No choices for the rest of the list, so wrap each choice for the first of the list (could save some new'ing if the first list is of length one, but that would make this code more complicated).
            	List<E> args = new ArrayList<E>(1);
                args.add(term);
                results.add(args);
            }
        }
        return results;
    }
    
    // This is specific to MLNs.  Determine the weight that a single MLN clause should have it it is to produce this probability.
	public static double getLogWeightForProb(double prob) {
		// TODO  make it a constant?
		double maxClauseWeight = Sentence.maxWeight;
		if (prob == 0) {
			return -maxClauseWeight;
		}
		if (prob == 1) {
			return maxClauseWeight;
		}
		double logWt = Math.log(prob/(1-prob));
		if (logWt > maxClauseWeight) {
			return maxClauseWeight;
		}
		if (logWt < -maxClauseWeight) {
			return -maxClauseWeight;
		}
		return logWt;
	}
    /**
     * Write these objects to this file. Start with a header string (e.g., a
     * comment) and have all lines (except the header) ends with finalEOLchars.
     * 
     * @param fileName
     *            A string containing the name of the file to use for output.
     * @param objects
     *            The objects to write to the named file.
     * @param finalEOLchars
     *            A string appended to the end of each line, but before the
     *            newline.
     * @param headerStringToPrint
     *            A description for the beginning of the file.
     */
    // TODO replace with something standard like Java serialization or XStream
    public static void writeObjectsToFile(String fileName, Collection<?> objects,
            							  String finalEOLchars, String headerStringToPrint) { // If object is a number, need an extra space so the period doesn't look like a decimal point.
        try {        	
        	ensureDirExists(fileName);
            CondorFileOutputStream outStream = new CondorFileOutputStream(fileName);
            PrintStream      stream    = new PrintStream(outStream);
            if (headerStringToPrint != null) {
                stream.println(headerStringToPrint);
            }
            int counter = 0;
            int total   = objects.size();
            for (Object obj : objects) { // If speed is an issue, could first check for COUNT and FRACTION in finalEOLchars.
            	counter++;
                stream.println(obj.toString() + finalEOLchars.replace("COUNT", comma(counter) + "").replace("FRACTION", Utils.truncate((1.0 * counter) / total, 6)));
            }
            stream.close();
        } catch (FileNotFoundException e) {
        	reportStackTrace(e);
            // TODO replace this error with an exception
            error("Unable to successfully open this file for writing: " + fileName + ".  Error message: " + e.getMessage());
        }
        
    }    
    
    public static void writeObjectsToGzippedFile(String fileName, Collection<?> objects,
            							         String finalEOLchars, String headerStringToPrint) { // If object is a number, need an extra space so the period doesn't look like a decimal point.
        try {        	
        	ensureDirExists(fileName);
    		StringBuffer buffer = new StringBuffer();
    		
            if (headerStringToPrint != null) {
            	buffer.append(headerStringToPrint + "\n");
            }
            int counter = 0;
            int total   = objects.size();
            for (Object obj : objects) {
            	counter++;
            	buffer.append(obj.toString() + finalEOLchars.replace("COUNT", comma(counter) + "").replace("FRACTION", Utils.truncate((1.0 * counter) / total, 6)) + "\n");
            }
            writeToGzippedFile(fileName, buffer.toString());
        } catch (IOException e) {
        	reportStackTrace(e);
            error("Unable to successfully open this file for gzip output: " + fileName + ".\n  Error message: " + e.getMessage());
        }
        
    }

	/**
	 * Reads file <filePath> into a string.
	 * 
	 * Works for gzipped files as well.  
	 * 
	 * @return  file as a string
	 * 
	 * This code taken directly from http://snippets.dzone.com/posts/show/1335
	 * (andrewspencer post on July 21, 2010)
	 */
	public static String readFileAsString(String fileNameRaw) throws IOException {
		String fileName = replaceWildCards(fileNameRaw);
		if (fileName.endsWith(".gz")) { // BUGGY if caller asks for *.gz file but really wanted the newer one if both * and *.gz exist.
			return readFromGzippedFile(fileName);
		} else if (fileExists(fileName + ".gz")) {
			if (!fileExists(fileName)) {
				return readFromGzippedFile(fileName + ".gz");
			}
			File regular = new CondorFile(fileName);
			File gZipped = new CondorFile(fileName + ".gz");
			boolean regExists = regular.exists();
			boolean zipExists = gZipped.exists();
			if (regExists && zipExists) {
				long dateReg = regular.lastModified();
				long dateZip = gZipped.lastModified();
				
				if  (dateZip >= dateReg) { 
					warning("Both regular and gzip'ed versions of this file exist; will read NEWER one:\n " + fileName + ".gz");
					return readFromGzippedFile(fileName + ".gz");  // Use the NEWER file.
				}
				warning("Both regular and gzip'ed versions of this file exist; will read NEWER one:\n " + fileName);
				return readFileAsString(new CondorFile(fileName));
			}
		}
	    return readFileAsString(new CondorFile(fileName));
	}

	public static String readFileAsString(File file) throws IOException {
	    byte[] buffer = new byte[(int) file.length()];
	    BufferedInputStream f = null;
	    try {
	        f = new BufferedInputStream(new FileInputStream(file));
	        f.read(buffer);
	    } finally {
	        if (f != null) try { f.close(); } catch (IOException ignored) { }
	    }
	    return new String(buffer);
	}
    public static void writeStringToFile(String stringToPrint, File file) { // Dont use TWO strings since easy for caller to mix them up.
    	writeStringToFile(stringToPrint, file, true);
    }
    public static void writeStringToFile(String stringToPrint, File file, boolean usePrintln) { 
        try {
        	ensureDirExists(file);
            CondorFileOutputStream outStream = new CondorFileOutputStream(file);
            PrintStream               stream = new PrintStream(outStream);
            if (usePrintln) { stream.println(stringToPrint); } else { stream.print(stringToPrint); }
            stream.close();
        } catch (FileNotFoundException e) {
        	reportStackTrace(e);
            // TODO replace this error with an exception
            error("Unable to successfully open this file for writing:\n " + file.getName() + ".\nError message:\n " + e.getMessage());
        }
    }  
    public static void touchFile(String fileName) {
    	touchFile(ensureDirExists(fileName));
    } 
    public static void touchFile(File file) {
    	ensureDirExists(file);
    	if (isDevelopmentRun()) { appendString(file, "\n// Touched at " + getDateTime() + ".\n", false); } // Seems unnecessar
    }

	public static <E> ArrayList<E> wrapItemInArrayList(E item) {
		ArrayList<E> result = new ArrayList<E>(1);
		result.add(item);
		return result;
	}
	
	public static String setFirstCharToRequestedCase(String str, boolean uppercaseFirstChar) {
		String result = str;

        if (str != null) {
            if (str.length() == 1) {
                char f = str.charAt(0);
                if (Character.isLetter(f) && Character.isUpperCase(f) != uppercaseFirstChar) {
                    if (uppercaseFirstChar) {
                        result = str.toUpperCase();
                    } else {
                        result = str.toLowerCase();
                    }
                }
            }
            else if (str.length() > 1) {
                char f = str.charAt(0);
                if (Character.isLetter(f) && Character.isUpperCase(f) != uppercaseFirstChar) {
                    String firstLetter = null;
                    if (uppercaseFirstChar) {
                        firstLetter = str.substring(0, 1).toUpperCase();
                    } else {
                        firstLetter = str.substring(0, 1).toLowerCase();
                    }
                    String rest = str.substring(1);
                    result = firstLetter + rest;
                }
            }
        }
        return result;
	}

	public static boolean isaInteger(String string) {
		try {
			Integer.parseInt(string);
			return true;
		} catch (NumberFormatException e) { return false; }
	}

   /** Returns a pretty String starting with prefix, ending with suffix, and contain a comma separated list of the collection items.
    *
    * @param <T> Type of the collection. Any object will do.
    * @param prefix Can be null if no prefix is wanted.
    * @param suffix Can be null if no suffix is wanted.
    * @param items Items to print.  Uses item.toString() to print each.
    * @return String in the form "&ltprefix>&gt[s]&ltitem>&gt[, &ltitem&gt ... ][ and &ltitem&gt ] &ltsuffix&gt".
    */
    public static <T> String getPrettyString(String prefix, String suffix, Collection<T> items) {
        StringBuilder sb = new StringBuilder();

        if (prefix != null) {
            sb.append(prefix);
        }

        if (items == null || items.size() == 0) {
            // Don't print anything...it probably won't be
            // very gramatically pleasing, but there isn't a good way to
            // determine how this should be filled.
        }
        else if (items.size() == 1) {
            if (prefix != null && prefix.endsWith(" ") == false) {
                sb.append(" ");
            }
            sb.append(items.iterator().next());
        }
        else {
            // Slide in an s if the prefix doesn't end in a space.
            // This assume a certain gramatical form, which may be wrong,
            // but oh well...
            if (prefix != null && prefix.endsWith(" ") == false) {
                sb.append("s ");
            }

            int count = 0;
            for (T item : items) {
                if (count > 0 ) {
                    if (count == items.size() - 1) {
                        if ( items.size() > 2) {
                            sb.append(",");
                        }
                        sb.append(" and ");
                    }
                    else {
                        sb.append(", ");
                    }
                }
                sb.append(item);
                count++;
            }
        }
        if (suffix != null && suffix.startsWith(" ") == false) {
            sb.append(" ");
        }
        if (suffix != null) {
            sb.append(suffix);
        }

        return sb.toString();
    }

    /** Returns the maximum of a list of doubles
     *
     * @param values
     * @return
     */
    public static double max(double ... values) {
        double max = Double.NEGATIVE_INFINITY;

        if ( values != null ) {
            for (int i = 0; i < values.length; i++) {
                if (values[i] > max) {
                    max = values[i];
                }
            }
        }

        return max;
    }

    /** Returns the maximum of a list of object based on a comparitor.
     *
     * @param <T> Type of object to be compared.
     * @param comparator Comparator to use for the comparison.
     * @param objects Objects to compare.
     * @return Returns the object with the highest rank according to the comparator.
     * If multiple object have the same rank, the earliest on in the list will be
     * returned.
     */
    public static <T> T argmax(Comparator<T> comparator, T ... objects) {
        T max = null;

        if ( objects != null ) {
            for (int i = 0; i < objects.length; i++) {
                T object = objects[i];
                if ( object != null && (max == null || comparator.compare(object, max) > 0)) {
                    max = object;
                }
            }
        }

        return max;
    }

    /** Calculates the precision value.
     *
     * If mEstimates are desired, they should be included in the relevant terms.
     *
     * @param truePositives True positives.
     * @param falsePositives False positives.
     * @return Precision or NaN if not calculatable.
     */
    public static double getPrecision(double truePositives, double falsePositives) {

        double numerator   = truePositives;
        double denominator = truePositives + falsePositives;

        //println(" precision = " + numerator + "/" + denominator);
        if ( denominator > 0 ) {
            return numerator / denominator;
        }
        else {
            return Double.NaN;
        }
    }

    /** Calculates the recall value.
     *
     * If mEstimates are desired, they should be included in the relevant terms.
     *
     * @param truePositives True positives.
     * @param falseNegatives False negatives.
     * @return Recall or NaN if not calculatable.
     */
    public static double getRecall(double truePositives, double falseNegatives) {

        double numerator   = truePositives;
        double denominator = truePositives + falseNegatives;

        // println(" recall = " + numerator + "/" + denominator);
        if ( denominator > 0 ) {
            return numerator / denominator;
        }
        else {
            return Double.NaN;
        }
    }

    /** Calculates the FBeta score.
     *
     * If mEstimates are desired, they should be included in the relevant terms.
     *
     * @param beta Beta parameter for FBeta-score.
     * @param truePositives True positives.
     * @param falsePositives False positives.
     * @param falseNegatives False negatives.
     * @return F(<code>beta</code>) or NaN if no calculatable.
     */
    public static double getFBeta(double beta, double truePositives, double falsePositives, double falseNegatives) {

        double p = getPrecision(truePositives, falsePositives);
        double r = getRecall(truePositives, falseNegatives);

        return getFBeta(beta,p,r);
    }

    /** Calculates the FBeta score.
    *
    * If mEstimates are desired, they should be included in the relevant terms.
    *
    * @param beta Beta parameter for FBeta-score.
     * @param precision
     * @param recall
     * @return F(<code>beta</code>) or NaN if no calculatable.
    */
   public static double getFBeta(double beta, double precision, double recall) {

       if ( Double.isNaN(precision) || Double.isNaN(recall) ) {
           return Double.NaN;
       } else {
           return (1 + beta * beta) * precision * recall / ( beta * precision + recall);
       }
   }

    /** Calculates the F1 score.
     *
     * If mEstimates are desired, they should be included in the relevant terms.
     *
     * @param truePositives True positives.
     * @param falsePositives False positives.
     * @param falseNegatives False negatives.
     * @return F1 or NaN if no calculatable.
     */
    public static double getF1(double truePositives, double falsePositives, double falseNegatives) {
        return getFBeta(1, truePositives, falsePositives, falseNegatives);
    }

    /** Calculates the F1 score.
    *
    * If mEstimates are desired, they should be included in the relevant terms.
    *
     * @param precision
     * @param recall
    * @return F1 or NaN if no calculatable.
    */
   public static double getF1(double precision, double recall) {
       return getFBeta(1, precision, recall);
   }

    /** Calculates the FBeta score.
     *
     * If mEstimates are desired, they should be included in the relevant terms.
     *
     * @param truePositives True positives.
     * @param falsePositives False positives.
     * @param trueNegatives True negatives.
     * @param falseNegatives False negatives.
     * @return F(<code>beta</code>) or NaN if no calculatable.
     */
    public static double getAccuracy(double truePositives, double falsePositives, double trueNegatives, double falseNegatives) {

        double numerator   = truePositives                  + trueNegatives;
        double denominator = truePositives + falsePositives + trueNegatives + falseNegatives;

        if ( denominator > 0 ) {
            return numerator / denominator;
        }
        else {
            return Double.NaN;
        }
    }
    
    //private static final Pattern stringRegex = Pattern.compile("\\W+"); // \\W+ means replace CONSECUTIVE special characters with ONE underscore. 
    //private static final Pattern stringRegex = Pattern.compile("[?.!#$%&()*+,-/:;<=>@[\\]^`{|}~\\s]"); // Do NOT want to change single and double quote marks, and dont bother with underscore.  \s = whitespace
//	private static final Pattern stringRegex = Pattern.compile("[\\x28\\x29?.!#$%&()*+,-/:;<=>@^`{|}~\\s]"); // x28='(' and x29=')'  Do NOT want to change single and double quote marks, and dont bother with underscore.  \s = whitespace

    private static final Pattern numberPattern = Pattern.compile("-?[0-9]+(\\.[0-9]+)?([eE]-?[0-9]+)?");

    public static boolean isNumericString(String string) {
        return string != null && numberPattern.matcher(string).matches();
    }

    /**
    * Replace all problematic characters with underscores.
    * @param string  The string to convert. 
    * */
    public static String changeMarkedCharsToUnderscores(String string) {
		if (string == null) { return null; }

        StringBuilder sb = null;
        int length = string.length();
        boolean nonDigitFound = false;
        for(int index = 0; index < length; index++) {

            char c = string.charAt(index);
            if (!nonDigitFound) { nonDigitFound = Character.isLetter(c); } // BUGGY if scientific notation.
            if (Character.isWhitespace(c) || c == '=') { nonDigitFound = false; }
            
            switch(c) {
            	case '.': // JWS: we want this to persist (to handle doubles).  BUGGY on a string like "123.4abc"
            		if ( !nonDigitFound &&
            			 index    > 0      && Character.isDigit(string.charAt(index - 1)) && 
            			(index+1) < length && Character.isDigit(string.charAt(index + 1))) {
            			break;
            		}
            	case '-':
            		if (index == 0) { break; } // Leading minus sign OK.
            		if (index > 1 && index < length - 2 && Character.isDigit(string.charAt(index - 2)) &&
            			(string.charAt(index - 1) == 'E' || string.charAt(index -1) == 'e') &&
            			Character.isDigit(string.charAt(index + 1))) {
            			// Looks like scientific notation.
            			break;
            		}
                case '?':
                case '!':
                case '#':
                case '$':
                case '%':
                case '&':
                case '(':
                case ')':
                case '{':
                case '}':
                case '[':
                case ']':
                case '|':
                case '*':
                case '+':
                case ',':
                case '/':
                case ':':
                case ';':
                case '<':
                case '=':
                case '>':
                case '@':
                case '^':
                case '`':
                case '~':
                case ' ':
                case '"':
                case '\t':
                case '\'':
                case '\\':
                    if ( sb == null ) {
                        sb = new StringBuilder(string);
                    }
                    sb.setCharAt(index, '_');
                    if (!nonDigitFound) { nonDigitFound = ((c != '-') && (c != '+')); }
                    break;
                default:
                    break;
            }
        }

        return sb == null ? string : sb.toString();
    }
    public static String cleanString(String str, HandleFOPCstrings stringHandler) {
    	return cleanString(str, stringHandler, false);
    }
	public static String cleanString(String str, HandleFOPCstrings stringHandler, boolean hadQuotesOriginally) { // TODO - do a better job when there is a leading '-' (ie, it might not be a minus sign).
		if (str == null || str.isEmpty() || (str.length() > 0 && str.charAt(0) == '-')) { return str; } // An exception to this rule.  The last disjunct (too crudely?) tests for negative numbers.
        if ( numberPattern.matcher(str).matches()) return str;
	//	return changeDashesWhiteSpaceEtcToUnderscores(str.trim());
		String trimmed = str.trim();
		if (stringHandler != null && stringHandler.doVariablesStartWithQuestionMarks() 
				&& trimmed.length() > 1 // This line added by caden, internal block assumes length of at least 2
				&& trimmed.charAt(0) == '?') {
			String subStr = trimmed.substring(1);
			if (subStr.length() > 0 && subStr.charAt(0) == '?') { // Had multiple question marks (which DO mean something in IL but we are not exploiting that).
				return cleanString(subStr, stringHandler);
			}
			return "?" + cleanString(trimmed.substring(1), stringHandler);
		}
		String result = (hadQuotesOriginally ? str : changeMarkedCharsToUnderscores(str.trim()));
		if (!hadQuotesOriginally && result != null && result.length() > 0 && result.charAt(0) == '_') { 
			// waitHere("Starts with underscore: '" + str + "' -> '" + result + "'.");
			if (stringHandler.usingStdLogicNotation()) {
				result = "U" + result;
			} else {
				result = "u" + result;  // Leading underscores have special semantics, so don't let them survive cleaning.
			}
		}
		return result;
	}
	public static String createSafeStringConstantForWILL(String string, HandleFOPCstrings stringHandler) {
		if (string == null)    { return null;   }
		if (string.equals("")) { return string; }
		
		if (stringHandler.doVariablesStartWithQuestionMarks()) {
			if (string.charAt(0) == '?') {
				return createSafeStringConstantForWILL("qm_" + string.substring(1), stringHandler); // Get rid of any leading question mark in a constant.
			}
			return cleanString(string, stringHandler);
		}
		
		String result = cleanString(string, stringHandler);
		boolean useLowerCase = stringHandler.usingPrologNotation();
		if                      (!Character.isLetter(   result.charAt(0))) { result = "c_" + result; }	// This will also handle a leading underscore, which indicates (in all notations) a variable.
		if      ( useLowerCase && Character.isLowerCase(result.charAt(0))) {  }
		else if (!useLowerCase && Character.isUpperCase(result.charAt(0))) {  }
		else { result = changeCaseFirstChar(result); }
		
		if (stringHandler == null) { return result; }
		return stringHandler.getStringConstant(result).getName(); // Make these canonical.  TODO - allow an override?
	}
	public static String createSafeStringVariableForWILL(String stringUntrimmed, HandleFOPCstrings stringHandler) {
		if (stringUntrimmed == null) { return null; }
		
		String string = stringUntrimmed.trim();
		if (stringHandler.doVariablesStartWithQuestionMarks()) {
			if (string.charAt(0) == '?') {
				return "?" + cleanString(string.substring(1), stringHandler); // Pull out the first character, standardize, then add back in the '?'.
			}
			return "?" + cleanString(string, stringHandler); // Even if starts with '_' add this, since an underscore-led variable has special semantics.
		}

		String result = cleanString(string, stringHandler);
		boolean useUpperCase = stringHandler.usingPrologNotation();
		if (!Character.isLetter(result.charAt(0))) { result = "c" + result; }		
		if      (!useUpperCase && Character.isLowerCase(result.charAt(0))) { return result; }
		else if ( useUpperCase && Character.isUpperCase(result.charAt(0))) { return result; }
		else { result = changeCaseFirstChar(result); }

		if (stringHandler == null) { return result; }
		return stringHandler.getExternalVariable(result).getName(); // Make these canonical.  TODO - allow an override?
	}
	
	public static String getUserHomeDir() {
	   return System.getProperty("user.home");
	}

    public static String getUserName() {
        return getUserName(false);
    }

    public static String getUserName(boolean makeSafeString) {
        String result = System.getProperty("user.name");
        if (!makeSafeString) { return cleanString(result, null); }
        return result;
    }
    
    public  static String getScratchDirForUser() {
    	String result = help_getScratchDirForUser();
    	if (result != null) { ensureDirExists(result); }
    	return result;
    }
    private static String help_getScratchDirForUser() { // Don't call ensureDirExists() or CondorFile() from here or will get an infinite loop.

        // Note: this will fail for any Condor jobs that flock.

    	String userName = getUserName();
    	if ("shavlik".equals(userName) || "tkhot".equals(userName) || "siddharth".equals(userName)) {
    		String dir = "";
    		if      (isRunningWindows()) { 
    			dir = "C:/WILLscratch/"; } // Be sure to end with '\\' (or '/' for Linux).  Use Linux notation since sometimes backslashes disappear as strings get pushed through many methods.
    		else if (isRunningLinux())   {
    			// tkhot runs out of space on 15K docs so using shavlikgroup
    			if ("tkhot".equals(userName)) {
    				dir = "/u/shavlikgroup/people/Tushar/WILLscratch/";
    			} else {
    				dir = "/u/" + userName + "/WILLscratch/"; // Had been (8/11) "/scratch/" but dont want these to be on every machine (sometimes didn't have 'write' privileges in Condor).
    			}
    		} else {
        		error("Unclear which OS '" + userName + "' is running.");  
    		}
    		try {
    			File f = new File(dir);
    			f.mkdirs(); // If we have problems here, rewrite to use /u/userName if /scratch doesn't exist - but maybe scratch always exists?
    		} catch (Exception e) {
    			dir = "/u/" + userName + "/WILLscratch/";
    			File f = new File(dir);
    			f.mkdirs();
    		}
    		if ((new File(dir)).exists()) { return dir; }
    		waitHere("Cannot create a scratch dir for: " + userName);
    		return dir;
    	}
    	error("getScratchDirForWisconsinUser has encountered an unknown user name: " + userName);
    	return null;
    }
    
    public static String cwd() { return getCurrentWorkingDirectory(); }
    public static String getCurrentWorkingDirectory() {
    	 File directory = new File (".");
    	 try {
    		 println("  Current directory's canonical path: " + directory.getCanonicalPath()); 
    		 println("  Current directory's absolute  path: " + directory.getAbsolutePath());
	     } catch(Exception e) {
	    	  println("Exception: " + e);
	     }
	     return directory.getAbsolutePath();
    }


	/** 
	 * Return true if user is username.
	*/    	
	public static boolean isCurrentUser(String username) {
    	if (System.getProperty("user.name").toLowerCase().contains(username)) return true;
    	return false;
    }
    
	public static boolean isRunningWindows() {
    	if (System.getProperty("os.name").toLowerCase().contains("windows")) return true;
    	return false;
    }
	
	public static boolean isRunningLinux() {
	//	Utils.waitHere("isRunningLinux: " + System.getProperty("os.name"));
	   	if (System.getProperty("os.name").toLowerCase().contains("linux")) return true;
    	return false;
	}
	
	public static Boolean fileExists(String fileName) {
		return ((new CondorFile(fileName)).exists());
	}

    public static void copyFile(String f1raw, String f2raw) {
    	copyFile(f1raw, f2raw, true);
    }
    public static void copyFile(String f1raw, String f2raw, boolean complainIfDoesntExist) {
    	String f1 = replaceWildCards(f1raw);
    	String f2 = replaceWildCards(f2raw);
    	if (f1.equals(f2)) { return; }
    	ensureDirExists(f1);
    	ensureDirExists(f2);
    	if (fileExists(f1)) {
    		copyFile(new CondorFile(f1), new CondorFile(f2));
    	} else if (fileExists(f1 + ".gz")) {
    		if (f2raw.endsWith(".gz")) {
    			copyCompressedFile(f1, f2); 
    		} else {
    			copyCompressedFile(f1, f2 + ".gz"); 
    		}
    	} else if (complainIfDoesntExist) {
    		error("Cannot copy this file since it does not exist: " + f1);
    	}
    }
	
    public static void moveFile(String f1raw, String f2raw) {
    	String f1 = replaceWildCardsAndCheckForExistingGZip(f1raw);
    	String f2 = replaceWildCards(f2raw);
    	
    	if (f1.endsWith(".gz") && !f2.endsWith(".gz")) {
    		f2 += ".gz";
    	}
    	
    	if (f1.equals(f2)) { return; }
    	ensureDirExists(f1);
    	ensureDirExists(f2);
    	moveFile(new CondorFile(f1), new CondorFile(f2));
    }
	
    public static void moveFile(File f1, File f2) {
    	ensureDirExists(f1);
    	ensureDirExists(f2);
    	if (!f1.exists()) {
        	error("moveFile: THE FILE TO BE MOVED DOES NOT EXIST:\n  " + f1);    		
    	}
    	    	
    	if (!f1.renameTo(f2)) {
    		// If this fails, need to COPY then DELETE.
    		if (f1.getName().endsWith(".gz")) {
        		println("% Copied compressed file\n%   " + f1.getPath() + " to\n%   " + f2.getPath());
    			copyCompressedFile(f1.getPath(), f2.getPath());
    		} else {
        		println("% Copied (then deleted) file\n%   " + f1.getPath() + " to\n%   " + f2.getPath());
    			copyFile(f1, f2);
    		}
    		if (!f1.delete()) {
    			println("% Failed to delete:\n%   " + f1.getPath());
    		}
    	} else {
    		println("% Renamed\n%   " + f1.getPath() + " to\n%   " + f2.getPath());
    	}
    }
    
    public static File[] collectAllFilesBelowThisDirectory(File directoryName, String extension) {
    	List<File> results = new ArrayList<File>(4);
    	
    	getAllFilesBelowThisDirectory(directoryName, results, extension);
    	println("% Found " + Utils.comma(results) + " files ending with " + extension + ".");
    	File[] arrayToReturn = new File[results.size()];
    	for (int i = 0; i < results.size(); i++) { // Seems something built in should be able to handle this ...
    		arrayToReturn[i] = results.get(i);
    	}
    	return arrayToReturn;
    }
    
    private static void getAllFilesBelowThisDirectory(File directory, List<File> allFiles, String extension) { // Code from Trevor modified by Jude.
        File[] files = directory.listFiles(new FilenameFilter() {

            public boolean accept(File dir, String name) {
                return name.endsWith("sgm"); // How to pass this in?  Should be 'extension.'
            }
        });

        println("% Found " + (files == null ? "no" : files.length) + " files in " + directory);
        if (files != null && files.length > 0) { allFiles.addAll(Arrays.asList(files)); }
        File[] dirs = directory.listFiles(new FileFilter() {

            public boolean accept(File pathname) {
                return pathname.isDirectory();
            }
        });

        if (dirs != null && dirs.length > 0) for (File dir : dirs) {
        	getAllFilesBelowThisDirectory(dir, allFiles, extension);
        }
    }
    
    /** 
     * Copy content of file f1 into file f2
     * @param f1
     * @param f2
     */
    // Found at: http://www.computer-faqs.com/2009/01/30/how-to-copy-text-file-in-java/
    public static void copyFile(File f1, File f2) {
    	if (f1.getName().endsWith(".gz")) { waitHere("Use copyCompressedFile for " + f1.getName()); }
    	if (f2.getName().endsWith(".gz")) { waitHere("Use copyCompressedFile for " + f2.getName()); }
    	try {
    		ensureDirExists(f1);
    		ensureDirExists(f2);
            CondorFileReader reader = new CondorFileReader(f1);
            CondorFileWriter writer = new CondorFileWriter(f2, false); // Create a new file.
            int line;
            while ((line = reader.read()) != -1) {  // Read line from text file and write to destination file
                writer.write(line);
            }
            reader.close();
            writer.close();
        } catch (FileNotFoundException ffx) {
        	reportStackTrace(ffx);
            error("FileNotFoundException: " + ffx);
        } catch (IOException iox) {
        	reportStackTrace(iox);
            error("IOException: " + iox);
        }
    }
    
    public static void appendString(File file, String str) {
    	appendString(file, str, true);
    }
    public static void appendString(File file, String str, boolean useLock) {
        if (str != null && str.isEmpty() == false) {
    		ensureDirExists(file);
            CondorFileWriter writer = null;
            boolean lockObtained = false;
            try { // Open the file.
                lockObtained = !useLock || obtainLock(file);

                writer = new CondorFileWriter(file, true);
                writer.append(str);
                if ( str.endsWith("\n") == false ) {
                    writer.append("\n");
                }

            } catch (IOException e) {
            	reportStackTrace(e);
                error(e.toString());
            } finally {
                if (writer != null) {
                    try {
                        writer.close();
                    } catch (IOException ex) {
                    }
                }

                if (lockObtained && useLock) {
                    releaseLock(file);
                }
            }
        }
    }

    public static boolean obtainLock(File fileToLock) throws IOException {
		ensureDirExists(fileToLock);
        File lockFile = new CondorFile(fileToLock.getParentFile(), "." + fileToLock.getName() + ".lock");

        long wait = 0; // Since starting at 1 second might be too long, start at 0 and add 1 after multiplying by 1000.
        while( !lockFile.createNewFile() ) {
        	long waitToUse = wait * 1000 + 1;
        	// Use this one so that the info on locking appears even when filtering (eg, via grep) the output.  TODO - do we care this isn't in the dribble file?  In case we might, print twice.
            System.err.println("Lock file " + lockFile + " already exists.  Waiting " + convertMillisecondsToTimeSpan(waitToUse) + " to obtain lock.");
            println(           "Lock file " + lockFile + " already exists.  Waiting " + convertMillisecondsToTimeSpan(waitToUse) + " to obtain lock.");
        	try {
                Thread.sleep(waitToUse);
            } catch (InterruptedException ex) {
            }
            wait = Math.min(55 + random1toN(11), Math.max(1, 2 * wait)); // Never wait more than 60 seconds, but add some randomness in case two waits are in synch.
        }
        return true;
    }

    public static void releaseLock(File fileToLock) {
        File lockFile = new CondorFile(fileToLock.getParentFile(), "." + fileToLock.getName() + ".lock");
        ensureDirExists(lockFile);
        if (!lockFile.delete()) { error("Could not delete: " + lockFile); }
    //	waitHereRegardless("releaseLock: " + lockFile + "\n exists? " + lockFile.exists());
    }
    
    public static String ensureIsaDirectory(String str) {
    	if (str.isEmpty()) { return str; }
    	if (str.endsWith("/") || str.endsWith("\\")) { return str; }
    	return str + "/";    	
    }
    
    private static Set<String> ensured = new HashSet<String>(4); // OK if this is global because we're simply making and never deleting directories (unless the user does so manually).
    public static File ensureDirExists(File file) {
    	if (file == null) { return null; }
    	return ensureDirExists(file.getAbsolutePath());
    }
    public static File ensureDirExists(String file) {
    	if (file == null) { return null; }
    //	System.out.println("ensureExists: " + file);
    	if (file.endsWith("/") || file.endsWith("\\")) { file += "dummy.txt"; } // A hack to deal with directories being passed in.
		File f = new CondorFile(file);

	//	System.out.println(" dir:    " + f);
	//	System.out.println(" parent: " + f.getParentFile());
	//	System.out.println(" name:   " + f.getName());
    	String parentName = f.getParent();
    	File   parentDir  = (parentName == null ? null : f.getParentFile());
		if (parentDir != null && !ensured.contains(parentName) && !parentDir.exists()) { 
			if (!parentDir.mkdirs()) { // Be careful to not make the file into a directory.
				waitHere("Unable to create (sometimes these are intermittent; will try again)\n   file      = " + file +
																						    "\n   parentDir = " + parentDir);
				parentDir.mkdirs();
			}
		//	waitHereRegardless("ensureExists: " + parentName);
			ensured.add(parentName); 
		}
		return f;
	}

    private static final int appendFilesBufferSize = 4096;
	/**
	 * Concatenates all the input files and writes them to the output file. To
	 * use with a collection of files, use {@link Collection#toArray(Object[])}
	 * to convert the collection to an array.
	 * 
	 * @param includeSeparator
	 *            Whether to separate the file contents with 80 %'s (prefaced with '// ').
     * @param outputFileName 
	 *            The name of the file to write to.
	 * @param freshOutputFile
	 * 			  Should the output file be fresh?  If not, will APPEND.
	 * @param gzipFile
	 *            Should the file be gzipped if large?
	 * @param inputFiles
	 *            The files to concatenate. (There must be at least one.)
	 */
	public static void appendFiles(boolean includeSeparator, String outputFileName, boolean freshOutputFile, boolean gzipFile, File... inputFiles) {
		// Check that there is at least one input file
		if (inputFiles.length == 0) {
			throw new IllegalArgumentException("There must be at least one input file.");
		}

		// Check that none of the input files is the same as the output file.
		// This might not work exactly without canonicalizing all files.
		for (File file : inputFiles) {
			ensureDirExists(file);
			if (file.getName().equals(outputFileName)) {
				throw new IllegalArgumentException("All the input files must be distinct from the output file.");
			}
		}
		
		if (!freshOutputFile && gzipFile) {
			writeMe("appendFiles: when freshOutputFile=false and gzipFile=true, the file is NOT gzip'ed.");
		}

		try {
			// Open the output file.
			ensureDirExists(outputFileName);
			Writer output = (gzipFile && freshOutputFile ? getGzippedFileWriter(outputFileName) : new CondorFileWriter(new File(outputFileName), !freshOutputFile));	
			// Copy all inputs to the output.
			char[] buffer = new char[appendFilesBufferSize];
			int fileIndex = 0;
			for (File file : inputFiles) { // waitHere("  appendFiles: Reading " + file.getName());
				
				// Write a separator if applicable.
				if (includeSeparator && fileIndex > 0) {
					output.write("\n\n// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% " + file.getName() + " \n\n");
				}

				// Copy the current input to the output.
				boolean isaGzipFile = file.getName().endsWith(".gz");
				Reader input = (isaGzipFile ? getGzippedFileReader(file) : new CondorFileReader(file));
				int charactersRead = input.read(buffer);
				while (charactersRead != -1) {
					if (charactersRead > appendFilesBufferSize) { error("appendFiles: Read more than " + comma(appendFilesBufferSize) + " characters."); }
					output.write(buffer, 0, charactersRead);
					charactersRead = input.read(buffer);
				}
				input.close();

				fileIndex++;
			}

			// Close the output
			output.close();
		} catch (IOException e) {
			reportStackTrace(e);
			error("Error in appendFiles: " + e);
		}
	}
    
    // Return string without the text in []'s.  This will only use the FIRST '[' and ']'.
    // For 'odd cases,' simply return the provided string.
	public static String getOutsideString(String string) {
		if (string == null)        { return null;   }
		if (!string.contains("[")) { return string; }
		if (!string.contains("]")) { return string; }
		int open   = string.indexOf('[');
		int close  = string.indexOf(']');
		int length = string.length();
		
		if (open >= close) { return string; }
		String result = string.substring(0, open) + (close + 1 < length ? string.substring(close + 1, length) : "");
		//println("% getOutsideString(" + string + ") = " + result);
		return result;
	}

	public static List<String> makeStringList(String... strings) {
		if (strings == null) { return null; }
		List<String> results = new ArrayList<String>(strings.length);
        results.addAll(Arrays.asList(strings));
		return results;
	}

	// Add '//' before all lines in this string.  Note that the string might contain some "/* */" comments, so cannot simply wrap the string with /* */.
	public static String commentAllLines(String theToStringAsStandAlone) {
		if (theToStringAsStandAlone == null) { return null; }
		return "// " + theToStringAsStandAlone.replace("\n", "\n// ");
	}
	
	public static String getDateTime() {
        DateFormat dateFormat = new SimpleDateFormat("H:mm:ss M/d/yy"); //"yyyy/MM/dd HH:mm:ss"
        Date       date       = new Date();
        return dateFormat.format(date);
    }
	
	private static final long millisecInMinute = 60000;
	private static final long millisecInHour   = 60 * millisecInMinute;
	private static final long millisecInDay    = 24 * millisecInHour;
	public static String convertMillisecondsToTimeSpan(long millisec) {
		return convertMillisecondsToTimeSpan(millisec, 0);
	}
	public static String convertMillisecondsToTimeSpan(long millisec, int digits) {
		if (millisec ==    0) { return "0 seconds"; } // Handle these cases this way rather than saying "0 milliseconds."
		if (millisec <  1000) { return comma(millisec) + " milliseconds"; } // Or just comment out these two lines?
		if (millisec > millisecInDay)    { return comma(millisec / millisecInDay)    + " days and "    + convertMillisecondsToTimeSpan(millisec % millisecInDay,    digits); }
		if (millisec > millisecInHour)   { return comma(millisec / millisecInHour)   + " hours and "   + convertMillisecondsToTimeSpan(millisec % millisecInHour,   digits); }
		if (millisec > millisecInMinute) { return comma(millisec / millisecInMinute) + " minutes and " + convertMillisecondsToTimeSpan(millisec % millisecInMinute, digits); }
		
		return truncate(millisec / 1000.0, digits) + " seconds"; 
	}
	
	public static String getHostName() { // Written largely by Trevor.
		try {
			InetAddress addr = InetAddress.getLocalHost();
			String hostName = addr.getHostName();
			if (hostName == null) { return "unknownHost"; }
			int locFirstPeriod = hostName.indexOf('.');
			if (locFirstPeriod > 0) { // Not sure what a leading period would be, but keep it if this case ever occurs.
				return hostName.substring(0, locFirstPeriod);
			}
			return hostName;
		} catch (UnknownHostException e) {
			return "unknownHost";
		}
    }
	
	private static final Runtime sys_runtime = Runtime.getRuntime();
	public static String reportSystemInfo() {
		sys_runtime.gc();
		long   memoryInUse = sys_runtime.totalMemory() - sys_runtime.freeMemory();
		
		return "Using " + comma(memoryInUse) + " memory cells.";
	}


	public static String standardizeFileID(String str) {
		return str.replace('.', '_').replace('-', '_').replace(' ', '_').toUpperCase();
	}

    /** Recursive remove an existing directory.
     * 
     * @param file
     * @return
     */
    public static boolean delete(File file) { // Also see deleteDirectory [I think I (JWS) wrote deleteDirectory and Trevor wrote this one.]
        if (file.isDirectory()) {
            File[] files = file.listFiles();
            for (int i = 0; i < files.length; i++) {
                File file1 = files[i];
                if (delete(file1) == false) {
                    return false;
                }
            }
        }

        boolean b = file.delete();
        return b;
    }
    
    public static boolean deleteIfExists(String fileName) {
       if (fileExists(fileName)) { return delete(new CondorFile(fileName)); } // Need to make work for DIRECTORIES?
       return false;
    }
    
   public static boolean delete(String fileName) {
	   return delete(new CondorFile(fileName));
   }

    public static File createTempDirectory(String prefix) throws IOException {

        File dir = null;

        if ( CondorUtilities.isCondor() ) {
            dir = CondorUtilities.getScratchDirectory();
        }

        if ( dir == null ) {
            dir = new File("/tmp");
        }

        return createTempDirectory(prefix, dir);
    }

    public static File createTempDirectory(String prefix, File directory) throws IOException {


        if ( directory.exists() == false) {
            directory = null;
        }

        File temp = File.createTempFile(prefix, "", directory);

        if (!temp.delete()) {
            throw new IOException("Could not delete temp file: " + temp.getAbsolutePath());
        }

        if (!temp.mkdirs()) {
            throw new IOException("Could not create temp directory: " + temp.getAbsolutePath());
        }

        temp.deleteOnExit();

        return temp;
    }

    private Utils() {
    }

    public static boolean isDevelopmentRun() {
        if ( developmentRun == null ) {
            setupVerbosity();
        }

        return developmentRun;
    }

    public static void setDevelopmentRun(boolean this_developmentRun) {
        if ( developmentRun == null ) {
            setupVerbosity();
        }

        developmentRun = this_developmentRun;
    }

    public static boolean isExtraVerbose() {
        if ( extraVerbose == null ) {
            setupVerbosity();
        }

        return extraVerbose;
    }

    public static void setExtraVerbose(boolean this_extraVerbose) {
        if ( extraVerbose == null ) {
            setupVerbosity();
        }

        extraVerbose = this_extraVerbose;
    }

    public static boolean isSevereErrorThrowsEnabled() {
        if ( severeErrorThrowsEnabled == null ) {
            setupVerbosity();
        }

        return severeErrorThrowsEnabled;
    }

    public static void setSevereErrorThrowsEnabled(boolean this_severeErrorThrowsEnabled) {
        if ( severeErrorThrowsEnabled == null ) {
            setupVerbosity();
        }

        severeErrorThrowsEnabled = this_severeErrorThrowsEnabled;
    }

    public static boolean isVerbose() {
        if ( verbose == null ) {
            setupVerbosity();
        }

        return verbose;
    }

    public static void setVerbose(boolean this_verbose) {
        if ( verbose == null ) {
            setupVerbosity();
        }

        verbose = this_verbose;
    }

    public static boolean isWaitHereEnabled() {
        if ( waitHereEnabled == null ) {
            setupVerbosity();
        }

        return waitHereEnabled;
    }

    public static void setWaitHereEnabled(boolean this_waitHereEnabled) {
        if ( waitHereEnabled == null ) {
            setupVerbosity();
        }

        waitHereEnabled = this_waitHereEnabled;
    }

    public static boolean isVerbositySet() {
        return verbose != null;
    }

    /** Return whether the properties indicate that we are a developer.
     *
	 * Here is some code to decide whether a run is a development run based first on Java system properties
	 * and then on the presence of a file. The system property is important because it allows more flexibility,
	 * e.g. a particular run can be specified as a development run from the command line, from a Maven run,
	 * from your Eclipse run configuration, etc.
     * <P>
     * Try to use the other isXXX settings to control what you print or do.  That will allow for
     * finer grain control by the end user.
	 */
    private static boolean checkDevelopmentProperties() {

		// Find out if this is a development run.  Err on the side of answering no.

		// If a system property is already defined with a value, use that value.
		// Otherwise, populate the system property by looking for a file.
		String value = System.getProperty(DEVELOPER_MACHINE_PROPERTY_KEY);

    	// if (!doNotPrintToSystemDotOut) { System.out.println(" checkDevelopmentProperties()=" + value); }
		if (value != null) {
		    return value.equalsIgnoreCase("true");
		}
		// Decide whether this is a development run based on the presence of a file in the user's home directory
		String userHomeDirectory  = getUserHomeDir();
		ensureDirExists(userHomeDirectory);
		File   developmentRunFile = new CondorFile(userHomeDirectory, DEVELOPER_MACHINE_FILE_NAME);
//		waitHereRegardless("useHomeDir: " + userHomeDirectory + " file = " + developmentRunFile + " result=" + developmentRunFile.exists());
//  	if (!doNotPrintToSystemDotOut) { System.out.println("useHomeDir: " + userHomeDirectory + " file = " + developmentRunFile + " result=" + developmentRunFile.exists()); }
		boolean result = developmentRunFile.exists();
		if (result) {
			// Set the system property as well (canonicalize if already set)
			System.setProperty(DEVELOPER_MACHINE_PROPERTY_KEY, Boolean.toString(result));
		}
		return result;
    }
    
    public static String getMachineName() {
    	try {
    		InetAddress addr = InetAddress.getLocalHost();
    		String hostname = addr.getHostName();
    		return hostname;
    	} catch (UnknownHostException e) {
    		println("Unable to find hostname.");
    	}
   		return "UNKNOWN_HOST";
    }

    private static void setupVerbosity() {
        if ( checkDevelopmentProperties() ) {
            setVerbosity(Verbosity.Developer);
        }
        else {
            setVerbosity(Verbosity.Medium);
        }
    }
    
	public static void reportStackTrace(Throwable e) {
		if (isDevelopmentRun()) {
			flush();
			StackTraceElement[] trace = e.getStackTrace();
			int traceSize = trace.length;
			int sizeToUse = Math.min(traceSize, 50); // <-------- change this if you need to see more of the stack.
			println("\n% Stack trace:");
			if (sizeToUse < traceSize) {
				for (int i = 0; i < sizeToUse / 2; i++) {
					println("%  Element #" + (traceSize - i) + ": " + trace[i].toString());
				}
				println("% ...");
				for (int i = sizeToUse / 2; i > 0; i--) {
					println("%  Element #" +              i  + ": " + trace[traceSize - i].toString());
				}
			} else {
				for (int i = 0; i < sizeToUse; i++) {
					println("%  Element #" + (traceSize - i) + ": " + trace[i].toString());
				}		
			}
		} else {
			e.printStackTrace();
		}
	}

    /** Creates the power set of the items in elements.
     *
     * The input set elements is not changed while generating the power set.
     *
     * @param <ElementType> Type of elements.
     * @param elements Items to create power set over.
     * @return Returns power set of elements.
     */
    public static <ElementType> Set<Set<ElementType>> getPowerSet(Set<ElementType> elements) {
        if ( elements.isEmpty() ) {
            Set<ElementType> empty = Collections.emptySet();
            return Collections.singleton(empty);
        }
        else {
            elements = new HashSet<ElementType>(elements);
            return getPowerSetDestructive(elements);
        }
    }

    /** Creates the power set of the items in elements.
     *
     * This version of the method will modify the elements list
     * as the power set is built.
     *
     * @param <ElementType> Type of elements.
     * @param elements Items to create power set over.
     * @return Returns power set of elements.
     */
    private static <ElementType> Set<Set<ElementType>> getPowerSetDestructive(Set<ElementType> elements) {
        if ( elements.isEmpty() ) {
            return Collections.EMPTY_SET;
        }
        else if ( elements.size() == 1 ) {
            HashSet<Set<ElementType>> s = new HashSet<Set<ElementType>>();
            s.add(Collections.EMPTY_SET);
            s.add(Collections.singleton(elements.iterator().next()));
            return s;
        }
        else {
            ElementType e = elements.iterator().next();  // Next is gaurantee to work, since we check isEmpty
            elements.remove(e);

            Set<Set<ElementType>> pT = getPowerSetDestructive(elements);
            Set<Set<ElementType>> cross = getCrossProduct(pT, e);
            pT.addAll(cross);

            return pT;
        }
    }

    /** Generates the cross product of a set of sets and a single elements.
     *
     * Cross = { X union { element } | X elementOf set1 }
     *
     * @param <ElementType>
     * @param setOfSets
     * @param element
     * @return
     */
    private static <ElementType> Set<Set<ElementType>> getCrossProduct(Set<Set<ElementType>> setOfSets, ElementType element) {
        Set<Set<ElementType>> cross = new HashSet<Set<ElementType>>();
        for (Set<ElementType> set : setOfSets) {
            Set<ElementType> subset = new HashSet<ElementType>(set);
            subset.add(element);
            cross.add(subset);
        }

        return cross;
    }


	public static <ElementType> List<ElementType> fromSetToList(Set<ElementType> set) {
		if (set == null) { return null; }
		List<ElementType> results = new ArrayList<ElementType>(set.size());
		results.addAll(set);
		return results;
	}
    

    public static <T> Set<Set<T>> getCrossProduct(Set<Set<T>> set1, Set<Set<T>> set2) {

        if ( set1.isEmpty() && set2.isEmpty() ) {
            return Collections.EMPTY_SET;
        }
        else if ( set1.isEmpty() ) {
            return copySetOfSets(set2);
        }
        else if ( set2.isEmpty() ) {
            return copySetOfSets(set1);
        }
        else {
            Set<Set<T>> cross = new HashSet<Set<T>>();

            for (Set<T> subset1 : set1) {
                for (Set<T> subset2 : set2) {
                    Set<T> newSubset = new HashSet<T>();
                    newSubset.addAll(subset1);
                    newSubset.addAll(subset2);

                    cross.add(newSubset);
                }
            }

            return cross;
        }
    }

    /** Make a copy of a set of sets.
     *
     * Each of the subset of aSetOfSets will be copies, but the elements
     * of the subsets will not be copied.
     *
     * The new sets will be HashSets.
     *
     * @param <T>
     * @param set
     * @return
     * @throws CloneNotSupportedException
     */
    public  static <T> Set<Set<T>> copySetOfSets(Set<Set<T>> aSetOfSets)  {
       Set<Set<T>> newSet = new HashSet<Set<T>>();

        for (Set<T> subset : aSetOfSets) {
            HashSet<T> newSubset = new HashSet<T>();
            newSubset.addAll(subset);
            newSet.add(newSubset);
        }

        return newSet;
    }

    /** Creates all combinations of the elements of the groups.
     *
     * Each generated combination contains at most a single element
     * for any give group (and may contain no elements for the group).
     * The null set is not generated.
     *
     * This is not the cross product, but is similar to the power
     * set with the addition that only one element of any sublist
     * can be added to any subset in the result.
     *
     * Example:
     *
     * Input = {  { a, b } , { 1, 2 } }
     * where {a,b} is the first group and {1,2} is the second group,
     * the returned output would be:
     * { a }, { a, 1 }, { a, 2 },
     * { b }, { b, 1 }, { b, 2 },
     * { 1 }, { 2 }.
     *
     * @param <T>
     * @param groups
     * @return
     */
    public static <T> List<List<T>> getCombinations(List<List<T>> groups) {
        List<List<T>> results = new ArrayList<List<T>>();

        if (groups != null && groups.size() > 0) {

            int groupCount = groups.size();

            int[] currentIndicies = new int[groupCount];

            boolean done = false;

            while (!done) {
                // Create the current conjunction...
                List<T> conjunction = new ArrayList<T>();
                for (int groupIndex = 0; groupIndex < groupCount; groupIndex++) {
                    int elementIndex = currentIndicies[groupIndex];
                    List<T> group = groups.get(groupIndex);
                    if (elementIndex < group.size()) {
                        conjunction.add(group.get(elementIndex));
                    }
                }

                // Add it to results...
                if (conjunction.size() > 0) {
                    results.add(conjunction);
                }

                // Increment the indicies, rolling them over when
                // they reach their max's.  Stop when all indicies
                // all indicies have rolled over once.
                for (int groupIndex = 0; groupIndex < groupCount; groupIndex++) {
                    List<T> group = groups.get(groupIndex);
                    if (currentIndicies[groupIndex] < group.size()) {
                        currentIndicies[groupIndex]++;
                        break;
                    }
                    else {
                        if (groupIndex == groupCount - 1) {
                            done = true;
                        }
                        else {
                            currentIndicies[groupIndex] = 0;
                        }
                    }
                }
            }
        }

        return results;
    }

//    /** Creates all combinations of the elements of the groups.
//     *
//     * Each generated combination contains at most a single element
//     * for any give group (and may contain no elements for the group).
//     * The null set is not generated.
//     *
//     * This is not the cross product, but is similar to the power
//     * set with the addition that only one element of any sublist
//     * can be added to any subset in the result.
//     *
//     * Example:
//     *
//     * Input = {  { a, b } , { 1, 2 } }
//     * where {a,b} is the first group and {1,2} is the second group,
//     * the returned output would be:
//     * { a }, { a, 1 }, { a, 2 },
//     * { b }, { b, 1 }, { b, 2 },
//     * { 1 }, { 2 }.
//     *
//     * @param <T>
//     * @param groups
//     * @return
//     */
//    public static <T> List<List<T>> getCombinations(Collection<T> ... groups) {
//        List<List<T>> results = new ArrayList<List<T>>();
//
//        if (groups != null && groups.length > 0) {
//
//            int groupCount = groups.length;
//
//            Iterator<T>[] currentIterators = new Iterator[groupCount];
//            T[] currentValues = (T[])new Object[groupCount];
//
//            boolean done = false;
//
//            while (!done) {
//                for(int groupIndex = groupCou)
//
//                boolean discardCombo = false;
//
//                List<T> conjunction = new ArrayList<T>();
//                for (int groupIndex = 0; groupIndex < groupCount; groupIndex++) {
//                    Iterator<T> iterator = currentIterators[groupIndex];
//
//                    if (iterator.hasNext()) {
//                        conjunction.add(iterator.next());
//                    }
//                    else {
//                        discardCombo = true;
//                        break;
//                    }
//                }
//
//                // Add it to results...
//                if (discardCombo == false && conjunction.size() > 0) {
//                    results.add(conjunction);
//                }
//
//                // Increment the indicies, rolling them over when
//                // they reach their max's.  Stop when all indicies
//                // all indicies have rolled over once.
//                for (int groupIndex = 0; groupIndex < groupCount; groupIndex++) {
//                    Iterator<T> iterator = currentIterators[groupIndex];
//                    if (iterator.hasNext()) {
//                        currentIterators[groupIndex]++;
//                        break;
//                    }
//                    else {
//                        if (groupIndex == groupCount - 1) {
//                            done = true;
//                        }
//                        else {
//                            currentIterators[groupIndex] = 0;
//                        }
//                    }
//                }
//            }
//        }
//
//        return results;
//    }

    public static <T> String toString(Collection<T> collection, String divider) {
        StringBuilder sb = new StringBuilder();

        boolean first = true;

        for (T object : collection) {
            if ( first == false ) {
                sb.append(divider);
            }
            first = false;
            sb.append(toString(object, divider));
        }
        return sb.toString();
    }

    public static <T,S> String toString(Map<T,S> map, String divider) {
        StringBuilder sb = new StringBuilder();

        boolean first = true;

        for (Map.Entry<T, S> entry : map.entrySet()) {
            if ( first == false ) {
                sb.append(divider);
            }
            first = false;
            sb.append(toString(entry.getKey(),divider)).append(" => ").append(toString(entry.getValue(), divider));
        }

        return sb.toString();
    }

    public static String toString(Object object, String divider) {
        if ( object == null ) {
            return null;
        }
        else if (object instanceof Collection) {
            Collection collection = (Collection) object;
            return toString(collection, divider);
        }
        else if (object instanceof Map) {
            Map map = (Map) object;
            return toString(map, divider);
        }
        else {
            return object.toString();
        }
    }

    public static void beep(int num) { // ASCII bell.
    	for (int i = 0; i < num; i++) {
    		System.out.print("\007");
    		System.out.flush();
    		try {
    			Thread.sleep(500);
    		} catch (InterruptedException e) {
    			// Don't care
    		}
    	}	
	 }

    /** Executes the static method specified by methodName of class thisOrClass.
     *
     * This method will return true if the method exists and is executed, otherwise it will return false.
     *
     * @param thisOrClass
     * @param methodName
     */
    public static boolean invokeMethod(Object thisOrClass, String methodName) {
        Method m = null;
        boolean isStatic = false;

        if (thisOrClass instanceof Class) {
            Class clazz = (Class) thisOrClass;
            try {
                m = clazz.getDeclaredMethod(methodName);
                if (m != null && Modifier.isStatic(m.getModifiers()) == false ) {
                    m = null;
                }
                isStatic = true;
            } catch (NoSuchMethodException ex) {
            } catch (SecurityException ex) {
            }
        }
        else {
            try {
                m = thisOrClass.getClass().getDeclaredMethod(methodName);
                if (m != null && Modifier.isStatic(m.getModifiers()) == true ) {
                    m = null;
                }
            } catch (NoSuchMethodException ex) {
            } catch (SecurityException ex) {
            }
        }
        

        if ( m != null ) {
            try {
                m.invoke( isStatic ? null : thisOrClass );
                return true;
            } catch (IllegalAccessException ex) {
                Logger.getLogger(Utils.class.getName()).log(Level.SEVERE, null, ex);
            } catch (IllegalArgumentException ex) {
                Logger.getLogger(Utils.class.getName()).log(Level.SEVERE, null, ex);
            } catch (InvocationTargetException ex) {
                Logger.getLogger(Utils.class.getName()).log(Level.SEVERE, null, ex);
            }
        }

        return false;

    }
    
    
    /**
     * Parses a string into a list of strings. Can handle formats:
     * {1,2, 3,4}
     * 1,2,3,4
     * "{","[","("," "
     * 
     * Make sure to put { in quotes if it is an input
     * Make sure that the string is not surrounded by quotes otherwise
     * we cant tell if """,""" is a list of " and "[ie {","}] or a list of two empty strings[ie {"", ""}] surrounded by quotes.
     * @param input Input string
     * @param removeAllQuotes Whether we should remove all quotes
     * @param delim the delimiter for splitting. Can be a regex too.
     * @return list of strings from the list
     */
    public static List<String> parseListOfStrings(String input, boolean removeAllQuotes, String delim) {
    	String[] items = input.split(delim);
    	    	
    	List<String> result = new ArrayList<String>();
    	for (String item : items) {
			result.add(item.trim());
		}
    	
    	String firstItem = result.get(0);     	
    	String lastItem = result.get(result.size()-1);
    	// the first item may have {
    	if (firstItem.startsWith("{")) {
    		firstItem = firstItem.substring(1).trim();
    		if (lastItem.endsWith("}")) {
    			lastItem = lastItem.substring(0, lastItem.length()-1).trim();
    		} else {
    			error("String starts with \"{\" but doesnt end with \"}\" :" + input);
    		}
    	} else {
    		if (lastItem.endsWith("}")) {
    			error("String doesnt start with \"{\" but ends with \"}\" :" + input);
    		}
    	}
    	
    	result.set(0, firstItem);
    	result.set(result.size()-1, lastItem);
    	
    	// Remove quotes
    	if (removeAllQuotes) {
    		for (int i = 0; i < result.size(); i++) {
				String item = result.get(i);
				if (item.startsWith("\"") && item.endsWith("\"")) {
					item = item.substring(1, item.length()-1);
					// Dont trim here, as the quotes would be used to prevent removing whitespace
					result.set(i, item);
				}
				
			}
    	}

    	
    	return result;
    }
    
    public static List<String> parseListOfStrings(String input, boolean removeAllQuotes) {
    	return parseListOfStrings(input, removeAllQuotes, ",");
    }
    
    public static List<String> parseListOfStrings(String input) {
    	return parseListOfStrings(input, true, ",");
    }    

	public static String removeAnyOuterQuotes(String str) {
		if (str == null || !str.startsWith("\"")) { return str; }
		return str.substring(1, str.length() - 1);
	}

	
    public static int countNumberOfCharacters(String input, char ch) {
    	int counter = 0;
    	int last = 0;
    	while((last = input.indexOf(ch, last)) != -1) {
    		counter++;
    		last++;
    	}
    	return counter;
    }
    
    public static List<Integer> getIndicesOfItems(List superList, List sublist ) {
        List<Integer> list = new ArrayList<Integer>(sublist.size());
        for (Object object : sublist) {
            list.add(superList.indexOf(object));
        }
        return list;
    }

    public static synchronized void playSound(final String url, boolean async) {
        Runnable r = new Runnable() {

            public void run() {
                SourceDataLine auline = null;
                {
                    AudioInputStream inputStream = null;
                    try {
                        Mixer.Info[] mixers = AudioSystem.getMixerInfo();
                        Mixer.Info mixerinfo = mixers[1];
                        


                        inputStream = AudioSystem.getAudioInputStream(Utils.class.getResourceAsStream(url));
                        AudioFormat format = inputStream.getFormat();
                        
                        auline = AudioSystem.getSourceDataLine(format, mixerinfo);
                        auline.open(format);
                        auline.start();
                        int nBytesRead = 0;
                        byte[] abData = new byte[524288];
                        while (nBytesRead != -1) {
                            nBytesRead = inputStream.read(abData, 0, abData.length);
                            if (nBytesRead >= 0) {
                                auline.write(abData, 0, nBytesRead);
                            }
                        }
                    } catch (LineUnavailableException ex) {
                        Logger.getLogger(Utils.class.getName()).log(Level.SEVERE, null, ex);
                    } catch (UnsupportedAudioFileException ex) {
                        Logger.getLogger(Utils.class.getName()).log(Level.SEVERE, null, ex);
                    } catch (IOException e) {
                        Logger.getLogger(Utils.class.getName()).log(Level.SEVERE, null, e);
                    } catch (IllegalArgumentException e) {
                        Logger.getLogger(Utils.class.getName()).log(Level.SEVERE, null, e);
                    } finally {
                        if (auline != null) {
                            auline.drain();
                        }
                        if (auline != null) {
                            auline.close();
                        }
                        try {
                            if ( inputStream != null ) inputStream.close();
                        } catch (IOException ex) {
                            Logger.getLogger(Utils.class.getName()).log(Level.SEVERE, null, ex);
                        }
                    }
                }
            }
        };

        if (async) {
            new Thread(r).start();
        }
        else {
            r.run();
        }
    }
   

    public static void addFilteredMessageType(MessageType ... type) {
        filteredMessageTypes.addAll(Arrays.asList(type));
    }

    public static void addFilteredMessageType(Set<MessageType> types) {
        filteredMessageTypes.addAll(types);
    }

    public static void removeFilteredMessageType(MessageType ... type) {
        filteredMessageTypes.removeAll(Arrays.asList(type));
    }

    public static void removeFilteredMessageType(Set<MessageType> types) {
        filteredMessageTypes.removeAll(types);
    }

    public static boolean isMessageTypeEnabled(MessageType type) {
        return filteredMessageTypes.contains(type) == false;
    }
	public static Boolean parseBoolean(String bool) {
		if (bool.equalsIgnoreCase("true") ||
			bool.equalsIgnoreCase("1") ||
			bool.equalsIgnoreCase("t") ||
			bool.equalsIgnoreCase("y") ||
			bool.equalsIgnoreCase("yes")) {
			return true;
		}
		
		return false;
	}
	
	public static String unzipFileIfNeeded(String fileName) throws IOException {
		if (fileName.endsWith(".gz")) {
			String readString  = readFromGzippedFile(fileName);
			String newFileName = fileName.subSequence(0, fileName.lastIndexOf(".gz")).toString();
			writeStringToFile(readString, new CondorFile(newFileName));
			return newFileName;
		}
		return null;
	}
	
	private static int minSizeToCompressInK = 1000;
    public static boolean compressFile(String fileNameRaw) {
        return compressFile(fileNameRaw, minSizeToCompressInK);
    }

	public static boolean compressFile(String fileNameRaw, int toUse_minSizeToCompressInK) {
		if (fileNameRaw == null) { return false; }
		String fileName = replaceWildCardsAndCheckForExistingGZip(fileNameRaw);
		if (fileNameRaw.endsWith(".gz")) { 
			println("%    No need to compress since already in 'gz' format: " + fileName); 
			return false; 
		}
		
		File    f = new CondorFile(fileName);
		long size = f.length() / 1000; // The units of File.length() are BYTES.
	//	Utils.println("% compressFile: size = " + size + " for " + fileName);
		if (size < toUse_minSizeToCompressInK) {
			println("%    No need to compress since small: " + fileName);
			return false;
		}
	//	println("    Compress since size is large (" + Utils.comma(size) + "): " + fileName);
		return copyAndGzip(fileName, fileName, true);
	}
	
	public static void copyCompressedFile(String fileName1, String fileName2) {
		String renamed1 = replaceWildCards(fileName1);
		String renamed2 = replaceWildCards(fileName2);	
		if (renamed1.equals(renamed2)) {
			Utils.waitHere("You are requesting a file be copied to itself: " + renamed1);
			return;
		}
		try {
			writeToGzippedFile(renamed2, readFromGzippedFile(renamed1)); // Probably a better way to do this (maybe use copyDirectory below?), but simply reading-writing line-by-line failed (at least between Windows and Linux).
		} catch (IOException e) {
			reportStackTrace(e);
			error("Problem in copyCompressedFile: " + e);
		}
	}	

	public static void copyFileToDirectory(File file, String dirRaw) throws IOException {
    	String dir = replaceWildCards(dirRaw);
    	Utils.ensureDirExists(dir);
    	copyDirectory(file, new CondorFile(dirRaw + file.getName()));
	}

    public static void copyDirectory(String sourceLocationRaw, String targetLocationRaw) throws IOException {
    	String sourceLocation = replaceWildCards(sourceLocationRaw);
    	String targetLocation = replaceWildCards(targetLocationRaw);
    	if (sourceLocation.equals(targetLocation)) { return; }
    	println("\n% Copy " + sourceLocation + "\n%  to  " + targetLocation);
    	copyDirectory(new CondorFile(sourceLocation), new CondorFile(targetLocation));
    }
	// If targetLocation does not exist, it will be created.  THIS IS A BIT MISNAMED, SINCE IT COPIES *ONE* FILE, but this make recursion simpler.
    public static void copyDirectory(File sourceLocation, File targetLocation) throws IOException { 
    	ensureDirExists(targetLocation);       
        if (sourceLocation.isDirectory()) {           
            String[] children = sourceLocation.list();
            for (int i = 0; i < children.length; i++) {
                copyDirectory(new File(sourceLocation, children[i]),
                		      new File(targetLocation, children[i]));
            }
        } else {            
            InputStream in   = new CondorFileInputStream( sourceLocation);
            OutputStream out = new CondorFileOutputStream(targetLocation);
            
            // Copy the bits from instream to outstream.  WORKS EVEN FOR COMPRESSED FILES?
            byte[] buf = new byte[1024];
            int    len;
            while ((len = in.read(buf)) > 0) {
                out.write(buf, 0, len);
            }
            in.close();
            out.close();
        }
    }  



	
	public static boolean deleteDirectory(String dirName) {
		String renamed = replaceWildCards(dirName);
		println("% Delete this directory: " + renamed);
		File f = new CondorFile(renamed);
		return deleteDirectory(f);
	}
	public static boolean deleteDirectory(File f) {
	    if ( f.exists() ) {
	      File[] files = f.listFiles();
	      for(int i = 0; i < files.length; i++) {
	         if (files[i].isDirectory()) {
	           deleteDirectory(files[i]);
	         }
	         else {
	           files[i].delete();
	         }
	      }
	      return f.delete();
	    }
	    return false;
	}
	
	public static boolean copyAndGzip(String fileName1, String fileName2, boolean removeUnzippedVersionOfFileName2) {
		// It is ok to have fileName1 = fileName2 since ".gz" might be added to fileName2.
		try {
			String  renamed1   = replaceWildCards(fileName1);
			String  renamed2   = replaceWildCards(fileName2);
			boolean compressed = false;
			
			if (!Utils.fileExists(renamed1) && Utils.fileExists(renamed1 + ".gz")) { // See if a compressed version exists if the regular version doesn't.
				copyCompressedFile(renamed1, renamed2); // TODO - check if BOTH exist and use the newer file.  (Make a utility function to do this check since it is also made elsewhere.)
				compressed = true;
			} else {
				compressed = writeToGzippedFile(renamed2, readFileAsString(renamed1));
			}
			if (compressed && removeUnzippedVersionOfFileName2) {
				File renamed2AsFile = new CondorFile(renamed2);
				if ( renamed2AsFile.exists()) { renamed2AsFile.delete(); } 
			}
			return compressed;
		} catch (IOException e) {
			reportStackTrace(e);
			error("Problem in copyAndGzip:\n   " + e);
			return false;
		}
	}
	
	public static void moveAndGzip(String fileName1raw, String fileName2raw, boolean removeUnzippedVersionOfFileName2) {
		String fileName1 = replaceWildCards(fileName1raw);
		String fileName2 = replaceWildCards(fileName2raw);
		if (fileName1.equals(fileName2)) {
			compressFile(fileName1);
			return;
		}
		if (!copyAndGzip(fileName1, fileName2, removeUnzippedVersionOfFileName2)) {
			Utils.waitHere("Something went wrong: moveAndGzip\n   " + fileName1raw + "\n   " + fileName2raw);
		}
		(new CondorFile(fileName1)).delete();
	}

    public static Reader getGzippedFileReader(String fileNameRaw) throws IOException {
		String fileName = replaceWildCards(fileNameRaw);
        return getGzippedFileReader(new CondorFile(fileName));
    }

    public static Reader getGzippedFileReader(File file) throws IOException {
        return new BufferedReader(new InputStreamReader(new CompressedInputStream(file)));
    }

    /** Create a file writer for a gzipped file.
     *
     * Don't forget to close the file, or you will corrupt your file.
     *
     * @param fileName
     * @return
     * @throws IOException
     */
    public static Writer getGzippedFileWriter(String fileNameRaw) throws IOException {
		String fileName = replaceWildCards(fileNameRaw);
        Utils.ensureDirExists(fileName);
        return new BufferedWriter( new OutputStreamWriter( new CompressedOutputStream(fileName, true)));
    }
    public static Writer getFileWriter(String fileNameRaw) throws IOException {
		String fileName = replaceWildCards(fileNameRaw);
        Utils.ensureDirExists(fileName);
        return new BufferedWriter( new OutputStreamWriter( new CompressedOutputStream(fileName, false)));
    }

    /**
     * @param filename
     * @return the buffered reader for the file with filename.  Accepts gzipped
     * and normal files, returning whichever is newest if both exist.
     */
    public static BufferedReader getBufferedReaderMaybeGZnewest(String filename) {
    	return getBufferedReaderMaybeGZ(replaceWildCardsAndCheckForExistingGZip(filename));
    }
    
    /**
     * @param filename
     * @return the buffered reader for the file with filename.  Accepts gzipped
     * and normal files, returning the gzipped file if and only if the normal
     * file doesn't exist (and the gzipped version does).
     */
    public static BufferedReader getBufferedReaderMaybeGZ(String f){
    	/*
    	 * Moved here from machinereading/.../sri/util/FileMan.
    	 * This could be combined with getReaderFromGzippedFile (but make sure
    	 * it is backwards compatible with its original users).
    	 * - NLE 5/20/11
    	 */
    	try{
    		InputStream is;

    		if (!new File(f).exists() && new File(f + ".gz").exists()) {
    			f += ".gz"; //
    		}

    		FileInputStream fis = new FileInputStream(f);
    		if(f.toLowerCase().endsWith(".gz")){
    			is = new GZIPInputStream(fis);
    		}else{
    			is = fis;
    		}
    		InputStreamReader reader = new InputStreamReader(is, "UTF8");
    		BufferedReader lreader = new BufferedReader(reader);
    		return lreader;
    	}catch(Exception e){
    		e.printStackTrace();
    	}
    	return null;
    }

    

    public static String readFromGzippedFile(String fileNameRaw) throws IOException {
		String fileName = replaceWildCards(fileNameRaw);
        StringBuilder stringBuilder = null;
        BufferedReader reader = null;
        try {
            reader = new BufferedReader(new InputStreamReader(new CompressedInputStream(new CondorFile(fileName))));
            stringBuilder = new StringBuilder();

            String s = null;

            while ((s = reader.readLine()) != null) {
                stringBuilder.append(s).append("\n");
            }

        } finally {
            if ( reader != null ) try {
                reader.close();
            } catch (IOException ex) {            	
            }
        }
        return stringBuilder.toString();
    }

    public static boolean writeToGzippedFileIfLarge(String fileNameRaw, String stringToWrite) throws IOException {
    	if (stringToWrite.length() >= 100000) { return writeToGzippedFile(fileNameRaw, stringToWrite); }
    	else {
    		writeStringToFile(stringToWrite, new CondorFile(fileNameRaw));
    		return true;
    	}
    }
    private static boolean writeToGzippedFile(String fileNameRaw, String stringToWrite) throws IOException {
		String       fileName = replaceWildCards(fileNameRaw);   
		ensureDirExists(fileName);
        BufferedWriter writer = null;
        try { // Assume the caller knows that this file is big enough to warrant compression.
        	writer = new BufferedWriter( new OutputStreamWriter(new CompressedOutputStream(fileName, true)));

            writer.append(stringToWrite);
        }
        finally {
            try {
                if (writer != null) {
                    writer.close();
                }
            } catch (IOException iOException) { return false; }
        }
        return true;
    }
    
 	public static void printClassIO(Class<?> className,	String input, String output) {
		printf("%s.class", className.getName());
		printf("  input = %s",  input);
		printf("  output = %s", output);
	}
	public static String convertToFOPC(String predicate, String ... args) {
		/**
		 * Converts a predicate and its arguments to a (quote-safe) FOPC sentence
		 * (with newline already appended).
		 */
		// This is reworked from Tushar's functions in nlp/dataobj/Predicate.java (in <machinereading>)

		ArrayList<String> arguments = new ArrayList<String>(Arrays.asList(args));
		String insideParentheses = "";
		for (int i = 0; i < arguments.size(); i++) {
			if (i > 0)
				insideParentheses += ", ";
			insideParentheses +=  arguments.get(i);	
		}
		//Before creating the predicate to write out, replace any odd quotes
		String safeInsideParentheses = insideParentheses.replace("\"", "\\\""); //double quotes
		//String safeInsideParentheses = insideParentheses.replace("'", "\\'"); //possible do single quotes
		
		String result = predicate + "(" + safeInsideParentheses + ")." + System.getProperty("line.separator"); //add a newline
		//Utils.println(result);
		return result;
	}
}

/* I (JWS) keep this here as a reminder of how to do a dual FOR LOOP

 for (ListIterator<Term> terms1 = arg1.listIterator(), terms2 = arg2.listIterator(); terms1.hasNext(); ) {
     Term term1 = terms1.next();
     Term term2 = terms2.next();
 }

 (TAW) Jude, the above bit of code actually has a small bug.  If the two lists are the same length, there isn't a
 problem, but if terms1 is longer than terms2, you will get an exception.  You need to add a check for hasNext to
 terms2 as follows:

 for (Iterator<Term> terms1 = arg1.iterator(), terms2 = arg2.iterator(); terms1.hasNext() && terms2.hasNext(); ) {
     Term term1 = terms1.next();
     Term term2 = terms2.next();
 }

 Also, note that this works for any kind of iterator (and therefore any collection), not just the ListIterator.
 In fact, I don't think I have ever used a ListIterator explicitly.  I assume it allows additional operations
 beyond a normal iterator.

 */
