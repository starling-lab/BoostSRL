package edu.wisc.cs.will.MLN_Task;

import java.io.StringReader;
import java.util.*;

import edu.wisc.cs.will.FOPC.*;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.*;
import edu.wisc.cs.will.Utils.Utils;

/**
 * This is a wrapper class essentially to instantiate the various objects of classes like
 * Clause, GroundLiteral, GroundClause etc from their String representations. One thing to keep in mind is make sure that
 * you first pass the "usePrologVariables: false." and mode definitions before the other stuff
 * like clauses, evidence, or constants (either as part of the MLN string in convertMLNStringToClauseList,
 * or by making a call to read method).
 * 
 * @author pavan
 */
public class Wrapper {
	
	/**
	 * This method can read a whole MLN file passed as a string, and returns the list
	 * of clauses in the MLN string.
	 * 
	 * @param str A whole MLN file as a string
	 * @param parser
	 * @param stringHandler
	 * @return
	 */
	public static List<Clause> convertMLNStringToClauseList(String str,	FileParser parser, HandleFOPCstrings stringHandler) {
		return getClauses(str, parser, stringHandler);
	}	

	/**
	 * Just reads some information without returning anything. Can be used to read, for instance,
	 * the initial information in an MLN string like the "usePrologVariables: false." line,
	 * and mode definitions.
	 * 
	 * @param str The string to be read by the parser.
	 * @param parser
	 * @param stringHandler
	 */
	public static void read(String str, FileParser parser, HandleFOPCstrings stringHandler) {
		getClauses(str, parser, stringHandler);
	}
	
	/**
	 * This method converts a string composed of Literals delimited by '.' or ';' to a 
	 * List of Literal objects.  For instance, this method takes "Smokes(x).Friends(x,y)." 
	 * and returns a list containing two Literal objects.
	 * 
	 * @param str The Literals in string form.
	 * @param parser
	 * @param stringHandler
	 * @return
	 */
	public static List<Literal> convertStringToLiteralList(String str, FileParser parser, HandleFOPCstrings stringHandler) {
		List<Clause> clauses = getClauses(str, parser, stringHandler);
		List<Literal> literals = new ArrayList<Literal>(1);
		for (Clause clause : clauses) {	
			if (clause.posLiterals != null) { literals.addAll(clause.posLiterals); }
			if (clause.negLiterals != null) { literals.addAll(clause.negLiterals); }
		}
		return literals;
	}

	/**
	 * Converts a string containing a single Clause to a Clause object.
	 * 
	 * @param str
	 * @param parser
	 * @param stringHandler
	 * @return
	 */
	public static Clause convertStringToClause(String str, FileParser parser, HandleFOPCstrings stringHandler) {
		List<Clause> clauses = getClauses(str, parser, stringHandler);
		return clauses.get(0);
	}
	
	/**
	 * Converts a String form of a Literal to a Literal object. For instance, it takes "Smokes(Alice)." and returns a Literal object.
	 * 
	 * @param str
	 * @param parser
	 * @param stringHandler
	 * @return
	 */
	public static Literal convertStringToLiteral(String str, FileParser parser, HandleFOPCstrings stringHandler) {
		List<Clause> clauses = getClauses(str, parser, stringHandler);
		List<Literal> posLits = clauses.get(0).posLiterals;
		if (posLits != null) { return posLits.get(0); }
		return clauses.get(0).negLiterals.get(0);
	}

	/**
	 * Reads an MLN file, and returns the list of clauses (if any) in the file.
	 * 
	 * @param fileName Path to the MLN file
	 * @param parser
	 * @param stringHandler
	 * @return
	 */
	public static List<Clause> readMLNFile(String fileName, FileParser parser, HandleFOPCstrings stringHandler) {
		List<Sentence> sentences = parser.readFOPCfile(fileName, false);
		Theory theory = new Theory(stringHandler, sentences);
		return theory.getClauses();
	}

	private static List<Clause> getClauses(String str, FileParser parser, HandleFOPCstrings stringHandler) {
		List<Sentence> sentences = null;
		try {
			sentences = parser.readFOPCreader(new StringReader(str), null); // Fine no directory here since processing a string.
		} catch (Exception e) {
			Utils.println("Error while reading string: " + str);
		}
		// Utils.println("SENTENCES: " + sentences + " from: " + str);
		if (sentences != null) { return (new Theory(stringHandler, sentences)).getClauses(); }
		return null;
	}
}