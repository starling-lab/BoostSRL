
package edu.wisc.cs.will.FOPC_MLN_ILP_Parser;

import static edu.wisc.cs.will.Utils.MessageType.PARSER_VERBOSE_FILE_INCLUDES;
import static edu.wisc.cs.will.Utils.MessageType.PARSER_VERBOSE_LIBRARY_LOADING;
import static edu.wisc.cs.will.Utils.MessageType.PARSER_VERBOSE_MODE_LOADING;
import static edu.wisc.cs.will.Utils.MessageType.STRING_HANDLER_VARIABLE_INDICATOR;

import java.io.BufferedInputStream;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.io.StreamTokenizer;
import java.io.StringReader;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import edu.wisc.cs.will.FOPC.AllOfFOPC;
import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.ConnectedSentence;
import edu.wisc.cs.will.FOPC.ConnectiveName;
import edu.wisc.cs.will.FOPC.ConsCell;
import edu.wisc.cs.will.FOPC.Constant;
import edu.wisc.cs.will.FOPC.DefiniteClause;
import edu.wisc.cs.will.FOPC.ExistentialSentence;
import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.FunctionName;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.PredicateSpec;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings.VarIndicator;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.LiteralAsTerm;
import edu.wisc.cs.will.FOPC.LiteralToThreshold;
import edu.wisc.cs.will.FOPC.NamedTermList;
import edu.wisc.cs.will.FOPC.NumericConstant;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateName.FunctionAsPredType;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.RelevanceStrength;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.StringConstant;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.TermAsLiteral;
import edu.wisc.cs.will.FOPC.TermAsSentence;
import edu.wisc.cs.will.FOPC.Type;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.FOPC.UniversalSentence;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.ResThmProver.VariantClauseAction;
import edu.wisc.cs.will.Utils.MessageType;
import edu.wisc.cs.will.Utils.NamedInputStream;
import edu.wisc.cs.will.Utils.NamedReader;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.WILLthrownError;
import edu.wisc.cs.will.Utils.condor.CompressedInputStream;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.Utils.condor.CondorFileInputStream;
import edu.wisc.cs.will.Utils.condor.CondorFileReader;





// TODO - clean up so that the currentDirectory is always intelligently set (and rest after reading a file).

// Note: WILL currently loads all of its built in libraries.  To prevent this, include:
//																	setParam: loadAllLibraries  = false.
// You might also want to so ---->                                  setParam: loadAllBasicModes = false.

// Aside: search for this: Because the silly IL language has a weird way of dealing with lists, 'correct' for that here.
//        if the parser has problems with named arguments and unbracketed lists.

// Useful when printing things: tokenizer.lineno()

/**
 * IF "FOLDED" IN ECLIPSE, UNFOLD THIS FOR IMPORTANT DOCUMENTATION.
 * Parse a file (or some other text stream) as one containing FOPC sentences as well as "directives" to MLN's, ILP, etc.
 * Directives include the following.   Note that many commands need to be terminated with a '.' or a ';'
 *
 *   define:         constant = f(&lt;constants&gt;).     // The semantics (extensional definition) of this grounded function is this constant.  E.g, Bill = neighborOf(John, Mary).
 *
 *   setParam:       paramName = paramValue.        // Set this parameter to the value.  The equal sign and EOF are optional (so must all be on one line).
 *                                                  // Note that the parser does not check for valid parameter names nor values.  Later instances check this, and hence
 *                                                  // error reports might come much later.
 *
 *                                                  // Note: if a parameter - assume its name is xyz - is set it can be referred to later by @xyz.
 *                                                  //       CURRENTLY THIS ONLY WORDS FOR NUMBERS (more specifically, only via calls to processNumber) AND SINGLE TOKENS.
 *
 * 	 import:         fileName.                      // Read in another file.  Can provide full path names; otherwise will be relative to the directory in which the current file resides.  An extension of Utils.defaultFileExtensionWithPeriod will be added if the file name w/o any extension does not exist.
 *   importIfExists: fileName.                      // Same as 'import:' but do not complain if the file doesn't exist.
 *   importLibrary:  fileName.                      // Read in a pre-existing library file.  Only file names without an extension should be provided.
 *                                                  //  Existing libraries: arithmeticInLogic
 *                                                  //                      comparisonInLogic
 *                                                  //                      differentInLogic
 *                                                  //                      listsInLogic
 *                                                  //  Modes for each of those libraries have the same names as above, but are prefixed with "modes_"
 *                                                  //  Currently all libraries are automatically loaded.  To override, do:     setParam: loadAllLibraries = false.
 *
 * 	 isa:            typeA isa typeB.               // Type A isa type B.  The 'isa' is optional as is the EOL ('.' or ';').
 *
 *   determinate:    predName/numbArgs,             // For predName/numbArgs, the specified argument (counting from 1) will have AT MOST ONE value (of the specified type).
 *   				 arg=#, type=TYPE
 *
 *   numericFunctionAsPred: predName/numbArgs,      // A special-case determinate, where the specified argument (counting from 1) is the "output"
 *                   arg=#                          // when all the other variables are bound.  In addition, this argument is NUMERIC (TODO might want to redefine this).
 *
 *   				 Besides 'numeric' other prefixes are allowed to "FunctionAsPred."  Here is the complete list:
 *   					      numeric,       bool,          categorical,       structured,       anything,  // 'Categorical' is a "string token" (ie, an atom) and 'structured' is something involving an FOPC function.
							  listOfNumeric, listOfBoolean, listOfCategorical, listOfStructured, listOfAnything
 *
 *
 *   bridger:        predName/numbArgs              // A special-case determinate, where the role of this predicate is to enable the addition of some other predicate(s).
 *
 *   inline:         predName/numbArgs              // This predicate, which needs to be a Horn clause, will have its body 'in lined' into
 *   												// learned clauses.  For example, if we inline 'Q(x) :- R(x), S(x)' and have learned
 *   												// 'P(x) :- Q(x), W(x)', the result will be 'P(x) :- R(x), S(x), W(x)'.
 *   												// It is an error if predName/arity matches more than one clause.
 *
 *   threshold:      typed_literal,                 // For this typed literal, the specified argument (counting from 1) has a NUMERIC feature (can be MANY possible values)
 *   				 arg=#, [maxCuts=#],            // and the data will be analyzed to choose good thresholds (if specified, there is a maximum number of thresholds).
 *   				 [createTiles],  		        // Boolean predicates will be created, e.g. 'f_less_than_10'.  If 'createTiles' is present, compound constraints (eg, f_between_5_and7) will also be produced.
 *                   [firstArgIsExampleID]          // Appropriate 'isaInterval' specifications will automatically be constructed to prune useless search paths.  Commas are optional.
 *                   							    // If firstArgIsExampleID is present, then the code can look at the positive and negative examples
 *                   								// and will only consider thresholds that lie between a positive and negative.
 *                   							    // maxCuts, createTiles, and firstArgIsExampleID can occur in any order.
 *                   								// New literals created by 'threshold' are automatically inline'd (see above).
 *
 *   relevant:       predName/numbArgs, strength.   // A way to give hints about the relevance of literals to the concept being learned.
 *   												// The strengths are one of those in 'enum RelevanceStrength' (if the strength is
 *   												// left out, it defaults to RELEVANT).  The comma is optional but an EOL is mandatory (since long relevance statement might require than one line for readability).
 *
 *   												// Currently the code only matches on 'predName'
 *   												// and ignores 'numbArgs' but these should be given nevertheless (the long-term intent
 *   												// is that 'numbArgs=-1' will mean "for all versions of literals that use 'predName').
 *   												// This is closely related to 'cost' but the TuneParametersForILP class uses
 *   												// relevant's but not cost's.  (The current implementation assigns 'relevant' to costs
 *   												// so no need to use both.)
 *
 *   												// Can also include the 'max' and 'maxPerInputVars' optional arguments used in 'mode'.
 *
 *                                                  // Advanced isVariant of the above.  All the new head predicates will have 'inline' asserted for them.
 *                                                  // Each 'newHead' will actually be a unique predicate name.
 *                                                  // Also, literals should be TYPED here since new modes created (if a variable appears more than once.
 *                                                  // only need to type the FIRST occurrence - additional TYPE'ing OK, but need to be consistent or an error will result).
 *                                                  // Since these lead to 'mode' specifications, can also use [maxP=#] and [maxPerInputVars=#] here (see mode: for explanation).
 *                                                  // These need to be AFTER the strength.
 *   relevant:           literal,  strength.        //   Will add:                                   'relevant: newHead/#FVs, strength'
 *   relevant:       NOT(literal), strength.        //   Will add: 'newHead(FVs) :- \+ literal.' and 'relevant: newHead/#FVs, strength'
 *    												//      Where FVs are the free variables in literal.
 *   relevant:   	 [lit1, ..., litN], strength.   //   Will add: 'newHead(allArgsInLiterals) :- literal1, ..., literalN.' and 'relevant: newHead/#allArgsInLiterals, strength'  Plus will 'inline newHead'
 *   relevant:    AND(lit1, ..., litN), strength.   //   Same as above, but []'s not used.  Note that for ANDs there cannot be embedded lists.
 *   relevant:     OR(lit1, ..., litN), strength.   //   Will add: 'newHead(allArgsInLiterals) :- literal1.' ... 'newHead(allArgsInLiterals) :- literalN.' and 'relevant: newHead/#allArgsInLiterals, strength'
 *   											    //   Note here 'newHead' is NOT inlined.  This means it needs to be carried around in any new theories learned.
 *                                                  //   Note that for OR, embedded lists and AND(lit1, lit2, ..., litN) are allowed.  Embedded lists are implicitly combined with AND.
 *                                                  //   However, in neither case can a NOT be embedded (parser would need to be extended substantially).
 *           ... head = typedHeadLiteral            // NOTE: in the above 'relevant' statements using AND, OR, and NOT, there is an other optional argument:
 *                                                  //          head = typedHeadLiteral
 *                                                  // This will be the head of the inference rule produced from the 'relevant' - if 'head' is not provided, one will be created.
 *
 *           ... noAutoNegate                       // The AND, OR, and 'bare' literal relevant's will also create not_P :- \+ P, with one lower relevance value (but never less than neutral
 *                                                  // (no provided strength is less than neutral, not additional relevant's created).  This flag overrides that.  (TODO - add a global flag that does for all relevant's.)
 *
 *   relevantClause:  exampleLit : clause, strength. // Specify a relevant clause for an example.
 *
 *   relevantFeature: exampleLit : predicate/arity, strength. // Specify a relevant predicate for an example.
 *
 *   containsCallable: predicate/arity.             // Specifies that the terms of the literal/function with the indicates predicate name may be callable elements.
 *                                                  // An example of this is negation by failure, in which the first term is the clause to execute to determine if
 *                                                  // the negation by failure succeeds or fails.
 *
 *
 *   supportingLiteral: predName/numbArgs           // The clauses that define this predicate need to be kept as 'supporting clauses' in learned theories.  Typically internally generated clauses get this marking, but users might want to do this as well.
 *
 *   cost:           predName/numbArgs, real        // The cost (e.g., for scoring clauses) associated with this predicate name (with this many arguments) is 'real.'  The comma is optional.  The EOL should be ';' if the 'real' is an integer (since otherwise the decimal point ['.'] confuses the parser).  Default cost = 1.
 *   costFinal:      predName/numbArgs, real        // Same as above, but this version will not be changed (otherwise the lower cost is chosen if there are multiple settings).
 *
 *   mode:           typed_literal                  // This states the types of the arguments in this literal.
 *                   [target=pred/numbArgs]         // Types are + (an 'input' variable; MUST be present earlier in the clause), - (an 'output' variable; need not already be present in the clause), and # (a constant; need not already be present).
 *                   [max=#]                        // Also, '$' means use a variable that only appears ONCE and '^' means only use a NEW variable.  A variable can be followed by '!k' or $k' - the former means "this predicate will be true for EXACTLY k possible values for this argument, where the latter is similar but for "AT MOST K."
 *  			     [maxPerInputVars=#].           // Optionally [not yet implemented] can say that the above mode only applies when learning this target.  A sample is 'parentOf/2' (the literal whose predicate name is 'parentOf' and which has two arguments).
 *  			     		                        // Optionally say that typed_literal can appear in a learned clauses at most # (some integer) times.
 *  			     				                // Optionally indicate that PER SETTING to the 'input' (i.e. '+') variables, can occur at most this many times (an idea taken from Aleph).
 *              // More notes on modes:
 *				//   If a +mode, then MUST use an previously added variable of same type.
 *				//   If a $mode, then MUST use into an previously added variable that APPEARS ONLY ONCE EARLIER IN THE CLAUSE.
 *				//   If a -mode, then CAN  use an previously added variable of same type.
 *				//   If a ^mode, then treat SAME as '-' but ONLY create a new variable (ie, do NOT use other new variables of this type created for this literal)
 *				//   If a #mode, then use one of the selected positive SEEDs and find a constant of that type.  TODO - use ANY seed?  maybe the negatives offer some good values?
 *				//   If a &#64;mode (at sign), then use the SPECIFIC value given (should be a constant and not a variable).
 *				//   If a &mode, then combine '-' and '#'.
 *				//   If a :mode, then combine '+' and '#'.  TODO - allow MULTIPLE CHARACTERS (eg, any pair)!
 *
 *   noMode:    same args as for 'mode:"            // Turn OFF a mode with these args (useful if a library of modes is loaded and for some runs we want to disable some).
 *   												// This works even if a mode happens AFTER the noMode.   
 *   												// CURRENTLY ONLY CHECKS *ARITY* AND IGNORES SPECIFIC TYPE OF EACH ARG (TODO - cleanup)    
 *
 *   isaInterval:    predName/numbArgs.             // Inform ILP that this predicate specifies a 1D (numbArgs=3), 2D (numbArgs=6), or 3D (numbArgs=9) number interval (a.k.a., a 'tile').  E.g.: 'isaInterval: ageInRange/3' says that ageInRange(lower, value, upper) is true when lower &lt;= value &lt; upper.  This information is used to prune search spaces.
 *
 *   constrains: 	 predName/numbArgs,         	// When this literal is in a clause, its Nth argument (counting from 1) is of this type.
 *   			     arg=#,                     	// The commas and EOL ('.' or ';') are optional, so these need to be on ONE line.
 *   				 type,                      	// This allows a "type checking" literal to restrict a type of a variable, thereby possibly allowing other modes to become applicable.  (If already a SUBCLASS of 'type' then this has no effect on a variable.)
 *                   pruneIfNoEffect.               // If X is of type 'physical object', then 'isaCar(X)' can constrain X to be a 'vehicle' and modes that are restricted to vehicles now come into play.
 *                   								// If pruneIfNoEffect is present, then do not add this literal UNLESS it has an impact on the type of the constrained argument (some constrainers might have other effects and so we do not want to ALWAYS do this).
 *                                                  // Also, if pruneIfNoEffect is present, set the cost of this literal low (e.g., 0.001) since this literal is presumably only there for 'side effect' on the argument type.
 *
 *   precompute:     fileName = string, clause.     // This Horn ('definite' actually) clause should be precomputed.  Can also use 'precompute1' to 'precompute99' to put results in separate files (so if there is a crash, only need to precompute some of the data).
 *                                                  // Precomputed facts in precomputeN will be available when precomputing M, for M > N.
 *                                                  // If the optional "fileName = string" is present (comma afterwards is optional), 'string' is used as the file name; otherwise 'precomputedN.txt' is.
 *
 *   prune:          prunableLiteral,               // If a literal that is a variant of 'ifPresentLiteral' is in already in a clause being learned,
 *                   ifPresentLiteral,              // do not add something that also a variant of 'prunableLiteral' - the commas and the final '.' (or ';') are optional.
 *                   [warnIf(N)].                   // The optional third argument says to complain if there are N or more existing rules whose head unifies with 'ifPresentLiteral' since this pruning is based on the assumption that less than N such rules exist (i.e., the 'precompute:' facility assumes N=1).
 *
 *   prune:          prunableLiteral.               // It is also possible for a literal to be pruned INDEPENDENTLY of the current clause's body, e.g. f(x,x) might be a tautalogy.
 *                                                  // Here the EOL (i.e., '.' or ';') is mandatory (to distinguish from the above version of 'prune:') and there cannot be a 'warnIf' (since they don't make sense here).
 *
 *   pruneTrue and pruneFalse                       // These can be used instead of 'prune' to state the REASON for the pruning.
 *
 *   queryPred:      predName/numbArgs.             // Used for MLNs.  The EOL ('.' or ';') is optional.
 *   hiddenPred:     predName/numbArgs.             // Used for MLNs.  The EOL ('.' or ';') is optional.
 *
 *   isVariant:      literalA, literalB.            // Specify that these two literals are equivalent.  The comma and EOL are optional.
 *
 *   filter:         predName.                      // This predicate (all arities) will always be true once learning is complete and should be filtered from learned rules.
 *
 *   range:          type = {value1, ..., valueN}.  // Specify the possible values for this type.  The outer braces are optional. The shorthand "..." can be used for integer-valued ranges.
 *
 *   usePrologVariables:   true/false/yes/no/1/0.   // These determine whether or not lower case is a variable (standard logic) or a constant (Prolog).
 *   useStdLogicVariables:   ditto                  // These can be reset in the middle of files, and the instances created will be correct, but text files produced are likely to be inconsistent (TODO: each variable and constant needs to record its case at time of creation?  Tricky, though since 'john' and 'John' might map to the same constant.)
 *   useLeadingQuestionMarkVariables: ditto         // There can be any of {true, false, yes, no, 1, 0} after these commands and an optional EOL ('.' or ';').
 *   useStdLogicNotation:             ditto
 *   usePrologNotation:               ditto
 *
 *   nonOperational:
 *      <NonOperationalPredicateName>/<Arity>   // Specifies a non-operational predicate's operational predicate names.
 *      operational=<OperationalPredicate>
 *      [, operational=<OperationalPredicate]*
 *
 *   The following all take predicateName/arity (and an optional EOL ['.' or ';']).
 *
 *      okIfUnknown:                                // It is OK if during theorem proving this predicate is undefined.  Helps catch typos.  If numberArgs='#' then applies to all versions of predName.  The EOL ('.' or ';') is optional.
 *      dontComplainAboutMultipleTypes:             // Don't warn if this predicate/arity has more than one type.
 *
 * Everything else is interpreted as an FOPC sentence (using the strings "ForAll" and "ThereExists" ["Exists" is also OK, but "All" is NOT since it is a built-in Prolog predicate] and
 * the standard logical connectives of {'and', 'or', '^', '&', 'v', '->', ':-', etc.).  FOPC sentences can be weighted using one of the following:
 *
 * 		weight = double  FOPC.
 *      wgt    = double  FOPC.
 *      weight(double)   FOPC.
 *      wgt(double)      FOPC.
 *      weight: double   FOPC.
 *      wgt:    double   FOPC.
 *
 *   Can also use this to mark examples that are not binary valued.  NOTE: this is stored in the 'weight' field and so cannot currently have weighted examples with non-Boolean output values.
 *      output = double  FOPC.
 *   All other variants of the above, where 'output' replaces 'weight' or 'out' replaces 'wgt' are acceptable.
 *   Can also do this (ie, 'regressionExample' is a special predicate name):
 * 		regressionExample(FOPC, double).  // TODO - also allow:  weightedExample(FOPC, double)?
 *   Related to this, one can also do annotatedExample(FOPC, annotationString).  See LearnOneClause.processReadExample.
 *
 * where 'double' is some real number (integers are OK). In all of these cases a comma can optionally separate the weight specification and the FOPC sentence.
 *
 * Can also add annotation to examples
 *
 * Also a "bare" double that starts a sentence and is NOT followed by an in-fix operator is interpreted as a weight on the following FOPC sentence.
 *
 * Notes: The term EOL in this file is used as shorthand to mean the GRAMMATICAL end of a statement, rather than the end of a line in a file.
 *        Case doesn't matter, except when distinguishing between variables and constants.   For predicate and function names, the first version encountered will be the one used, e.g., if "P" is encountered first, then later cases of "p" will become "P" as well.
 *
 * TODO  handle \+ w/o parens
 *
 *
 */
public class FileParser {  
	protected final static int debugLevel = 0;   // Used to control output from this project (0 = no output, 1=some, 2=much, 3=all).

    protected final static boolean traceTokenizer = true;
    protected final static boolean traceResults   = true;
    
    // Use this very carefully!
    protected static boolean    collectAllImportedSentencesInOneSpot = false; // If true, will avoid copying sentences as recursive calls, due to imports, return.
    protected static List<Sentence> collectionOfAllImportedSentences = new ArrayList<Sentence>(4);
    protected static void           clearCollectedImportedSentences() { collectionOfAllImportedSentences.clear(); }
    protected static List<Sentence> readCollectedImportedSentences( ) { return collectionOfAllImportedSentences; }
	
    // This actually also handles doubles, and even negation signs.
    public          static boolean convertQuotedAllDigitStringsToNumericConstants = false; // Hack to deal with other code that puts quote marks around numbers.  If set true, we lose the ability to distinguish between, say, the int 7 and the string "7".
    
    public                 boolean dontPrintUnlessImportant = true;
    
    public          static boolean allowSingleQuotes        = true; // If true, can use single quotes to wrap strings.
	 
	// Allows user to set it to a higher number but doesn't penalize all runs where there are fewer precomputes
	// It is mildly risky to make this a static, but acceptable.
	public    static int numberOfPrecomputeFiles = 125; 

	// The parser can create additional predicates, by negating relevance statements it receives. This is used as the prefix for such predicate names.
	// It is made static for each access w/o a parser instance and made final to cannot be changed if multiple WILLs are active.
	public static final String will_notPred_prefix  = "wiNOT_";  // "Why not?  Because I said so."

	protected              int maxWarnings  = 100; // This can be reset via 'setParameter maxWarnings = 10'
	protected              int warningCount =   0; // TODO make more use of this

	public  HandleFOPCstrings  stringHandler;
	private StreamTokenizerJWS tokenizer;
	private List<Sentence>[]   sentencesToPrecompute;
	private String[]           sentencesToPrecomputeFileNameToUse;
	private Set<LiteralToThreshold> literalsToThreshold;
	private String             directoryName      = null;
	private String             prefix             = null;
	private String             fileName           = null;
	private int                isaCounter         =    0; // Since there can be many of these, report progress.  Could inherit this from import's, but not that necessary (and then should really pass in the current counter as well).

	public boolean parsingWithNamedArguments     = false; // Indicates parsing IL ("interlingua") for the BL (Bootstrap Learning) project.
	public boolean treatAND_OR_NOTasRegularNames = false; // If true, treat AND and OR as function or predicate names.  (Used for IL parsing, for example.)


	public FileParser(HandleFOPCstrings stringHandler) {
		this.stringHandler = stringHandler;
	}
	public FileParser(HandleFOPCstrings stringHandler, boolean dontPrintUnlessImportant) {
		this.stringHandler = stringHandler;
		this.dontPrintUnlessImportant               = dontPrintUnlessImportant;
		this.stringHandler.dontPrintUnlessImportant = dontPrintUnlessImportant;
	}
	public FileParser(HandleFOPCstrings stringHandler, String workingDir) {
		this(stringHandler);

        if ( workingDir != null ) {
            File dir = new CondorFile(workingDir);
            if ( dir.exists() && dir.isDirectory() == false ) {
                try {
                    workingDir = dir.getCanonicalFile().getParent().toString();
                } catch (IOException ex) {
                    Logger.getLogger(FileParser.class.getName()).log(Level.SEVERE, null, ex);
                }
            }
        }

		directoryName      = workingDir;
	}

	public List<Sentence> getSentencesToPrecompute(int index) {
		if (sentencesToPrecompute == null) { return null; }
		return sentencesToPrecompute[index];
	}

	public String getFileNameForSentencesToPrecompute(int index) {
		if (sentencesToPrecomputeFileNameToUse == null) { return null; }
		return sentencesToPrecomputeFileNameToUse[index];
	}

	public void setFileNameForSentencesToPrecompute(int index, String nameRaw, boolean isaDefaultName) {
		String name = Utils.replaceWildCards(nameRaw);
		if (sentencesToPrecomputeFileNameToUse == null) { sentencesToPrecomputeFileNameToUse = new String[getNumberOfPrecomputeFiles()]; }
		String old = getFileNameForSentencesToPrecompute(index);
		if (old != null && (old.equals(name) || isaDefaultName)) { return; }
		if (old != null && !old.startsWith("precomputed")) { 
			Utils.waitHere("setFileNameForSentencesToPrecompute for precompute" + (index > 0 ? index : "") + ":\n  Had " + old + " but now setting\n  To  " + name + "  There cannot be multiple names for the same precompute file.");
			return;
		}
		sentencesToPrecomputeFileNameToUse[index] = stringHandler.precompute_file_prefix + name;
		if (stringHandler.precompute_file_postfix != null && 
			!sentencesToPrecomputeFileNameToUse[index].endsWith(stringHandler.precompute_file_postfix)) {
			sentencesToPrecomputeFileNameToUse[index] += stringHandler.precompute_file_postfix;
		}
	//	Utils.waitHere("setFileNameForSentencesToPrecompute[index=" + index + ", name='" + name + "', isaDefault=" + isaDefaultName + ", old='" + old + "']: " + sentencesToPrecomputeFileNameToUse[index]);
	}

	public void clearSentencesToPrecompute(int index) {
		sentencesToPrecompute[index].clear();
		sentencesToPrecomputeFileNameToUse[index] = null;
	}

	public Collection<LiteralToThreshold> getLiteralsToThreshold() {
		return literalsToThreshold == null ? Collections.EMPTY_SET : literalsToThreshold;
	}

	public void clearLiteralsToThreshold() {
		literalsToThreshold.clear();
	}

	// Return what seems to be the working directory for the current task.
	public void setDirectoryName(String name) {
		checkDirectoryName(name);
	}
	public String getDirectoryName() {
		return directoryName;
	}
	public void setPrefix(String name) {
		prefix = name;
	}
	public String getPrefix() {
		return prefix;
	}

	public List<Literal> readLiteralsInFile(String fName, boolean readQuietly) {
		return readLiteralsInFile(fName, readQuietly, false);
	}
	public List<Literal> readLiteralsInFile(String fNameRaw, boolean readQuietly, boolean okIfNoSuchFile) {
		String fName = Utils.replaceWildCards(fNameRaw);
		if (okIfNoSuchFile && !(new CondorFile(fName).exists())) { return null; }
		boolean hold_dontPrintUnlessImportant               =               dontPrintUnlessImportant; // TODO - allow this elsewhere?
		boolean hold_stringHandler_dontPrintUnlessImportant = stringHandler.dontPrintUnlessImportant;
		if (readQuietly) {
			dontPrintUnlessImportant               = true;
			stringHandler.dontPrintUnlessImportant = true;
		}
		List<Sentence> sentences = readFOPCfile(fName);
		
	//	Utils.println("readLiteralsInFile: |sentences| = " + Utils.comma(sentences));
		
		if (sentences == null) { 
			dontPrintUnlessImportant               =               hold_dontPrintUnlessImportant; 
			stringHandler.dontPrintUnlessImportant = hold_stringHandler_dontPrintUnlessImportant;
			return null;
		}
		List<Literal>  literals  = new ArrayList<Literal>(sentences.size());
		for (Sentence s : sentences) {
			if (s instanceof Literal) { literals.add((Literal) s); } else { Utils.error("readLiteralsInFile: this is not a literal: " + s); }
		}
		dontPrintUnlessImportant               =               hold_dontPrintUnlessImportant;
		stringHandler.dontPrintUnlessImportant = hold_stringHandler_dontPrintUnlessImportant;
	//	Utils.println("readLiteralsInFile: |literals| = " + Utils.comma(literals));
		return literals;
	}

	
	// Convert:   0.95 literal
	//      To:   probLiteral(0.95, literal).
	public void convertResultsFileFromAlchemyToWILLformat(String alchemyFileName, String WILLfileName) {
		try{ 
			StringBuilder  sb = new StringBuilder();
			BufferedReader br = new BufferedReader(new CondorFileReader(alchemyFileName));
			
			String strLine = null;
			// Read File Line By Line.
			while ((strLine = br.readLine()) != null) {
				sb.append("tuffyPrediction(" + strLine.trim().replaceFirst("\\s", ", ").replaceFirst("\\)", ")).") + "\n");
			}
			br.close();
			Utils.writeToGzippedFileIfLarge(WILLfileName, stringHandler.getStringToIndicateCurrentVariableNotation() + "\n" + sb);
		} catch (Exception e){
			Utils.reportStackTrace(e);
			Utils.error("Error: " + e);
		}
	}

	// TODO make readLiteralsInString and readLiteralsInStream
	
	// This does not allow any non-literals in the file (other than comments).
	// However it DOES allow a literal to NOT have a trailing '.' or ';' (some programs output their results in such a notation).
	public List<Literal> readLiteralsInPureFile(String fName) {
		return readLiteralsInPureFile(fName, false, false);
	}
	public List<Literal> readLiteralsInPureFile(String fName, boolean literalsAreWeighted) {
		return readLiteralsInPureFile(fName, literalsAreWeighted, false);
	} // TODO make readLiteralsInString and readLiteralsInStream
	private List<Literal> readLiteralsInPureFile(String fNameRaw, boolean literalsAreWeighted, boolean okIfNoSuchFile) {		
		String  fName          = Utils.replaceWildCardsAndCheckForExistingGZip(fNameRaw);
		boolean isaGzippedFile = fName.endsWith(".gz");

		List<Literal> results = new ArrayList<Literal>(4);
		try {
			File   file               = (isaGzippedFile ? new CondorFile(fName) : getFileWithPossibleExtension(fName));
			String newDirectoryName   = file.getParent();
			String hold_directoryName = directoryName;
			checkDirectoryName(newDirectoryName);
			this.fileName = fName; // Used to report errors.
			InputStream  inStream = (isaGzippedFile ? new CompressedInputStream(file) : new CondorFileInputStream(file));

			tokenizer = new StreamTokenizerJWS(new InputStreamReader(inStream), 8); // Don't need to do more than 2-3 push backs, so don't need a big buffer.
			initTokenizer(tokenizer);
			int counter = 0;
			while (tokenizer.nextToken() != StreamTokenizer.TT_EOF) {
				tokenizer.pushBack();
				double weight = (literalsAreWeighted ? processNumber(getNextToken()) : -1.0);
				Literal lit = processLiteral(false); counter++; if (debugLevel > 1) { Utils.println("% readLiteralsInFile:   " + lit + " // #" + Utils.comma(counter)); }
				if (literalsAreWeighted) {
					lit.setWeightOnSentence(weight);
				}
				results.add(lit);
				peekEOL(true); // Suck up an optional EOL.
			}			
			inStream.close();
			checkDirectoryName(hold_directoryName);
		}
		catch (FileNotFoundException e) {
			if (okIfNoSuchFile) { return null; }
			Utils.reportStackTrace(e);
			Utils.error("Unable to successfully read this file: " + fName);
		}
		catch (Exception e) {
			Utils.println("\nEncountered errors during parse:");
			Utils.reportStackTrace(e);
			Utils.error("Unable to successfully parse this file: " + fileName + ".\n  Have read " + Utils.comma(results) + " literals.\nNOTE THIS METHOD DOES NOT HANDLE PARSER INSTRUCTIONS!\nError message: " + e.getMessage());
		}
		
		if (debugLevel > 0) { Utils.println("% readLiteralsInFile: Have read " + Utils.comma(results) + " literals from: " + fName); }
		return results;
	}

	public List<Sentence> readFOPCfile(String fName) {
		List<Sentence> results = readFOPCfile(fName, false);

	//	Utils.println("readFOPCfile/1: |sentences| = " + results.size());
		return results;
	}

	private void checkDirectoryName(String newDirectoryName) {
		if (newDirectoryName == null) { return; } // If this is from a reset of a 'hold' of a directory name, don't reset back to null.
		else if (directoryName == null) {
			directoryName = newDirectoryName;
		} else if (!directoryName.equals(newDirectoryName)) {
			if (!dontPrintUnlessImportant) { Utils.println(PARSER_VERBOSE_FILE_INCLUDES, "% Formerly current directory name was:\n%   " +  directoryName + "\n% but now it is being set to:\n%   " + newDirectoryName); }
			directoryName = newDirectoryName;
		}
	}

	/**
         * A variant of readFOPCfile(String fileName) where no complaint is
         * thrown if the file does not exist.
         *
         * @param fileName
         * @param okIfNoSuchFile
         * @return A list of sentences, the contents of the given file.
         */
	public List<Sentence> readFOPCfile(String fNameRaw, boolean okIfNoSuchFile) {		
		String fName = Utils.replaceWildCardsAndCheckForExistingGZip(fNameRaw);
		
		boolean isaGzippedFile = fName.endsWith(".gz");
		try {
			File   file               = (isaGzippedFile ? new CondorFile(fName) : getFileWithPossibleExtension(fName));
			String newDirectoryName   = file.getParent();
			String hold_directoryName = directoryName;
			checkDirectoryName(newDirectoryName);
			this.fileName = fName; // Used to report errors.
			InputStream  inStream = (isaGzippedFile ? new CompressedInputStream(file) : new CondorFileInputStream(file));
			List<Sentence> result = readFOPCstream(file, inStream);
			inStream.close();
			checkDirectoryName(hold_directoryName);

		//	Utils.println("readFOPCfile/2: |sentences| = " + result.size());
			return result;
		}
		catch (FileNotFoundException e) {
			if (okIfNoSuchFile) { return null; }
			Utils.reportStackTrace(e); 
			Utils.error("Unable to successfully read this file:\n  " + fName + "\n Error message: " + e.getMessage());
		}
		catch (Exception e) {
			Utils.println("\nEncountered errors during parse:");
			Utils.reportStackTrace(e);
			Utils.error("Unable to successfully parse this file: " + fileName + ".  Error message: " + e.getMessage());
		}
		return null;
	}
	
	// If a file exists, add the default Utils.defaultFileExtensionWithPeriod extension.
	public File getFileWithPossibleExtension(String fileNameRaw) throws IOException {
		if (fileNameRaw == null) { Utils.error("Should not call with a NULL file name."); }
		String fileName = fileNameRaw.trim();
		File f = new CondorFile(fileName);
        if (!f.exists()) {
        	f = new CondorFile(fileName + Utils.defaultFileExtensionWithPeriod);
            if (!f.exists()) {
        		f = new CondorFile(fileName + ".bk"); // Try another built-in file name.
             	if (!f.exists()) {
             		f = new CondorFile(fileName + ".mln"); // Try yet another built-in file name.
             		if (!f.exists()) {
                 		f = new CondorFile(fileName + ".db"); // Try yet another built-in file name.
                 		if (!f.exists()) {
                     		f = new CondorFile(fileName + ".fopcLibrary"); // Try yet another built-in file name.
                     		if (!f.exists()) {
                     			f =  new CondorFile(fileName + ".gz");
                     			if (!f.exists()) {
                     				// The calling code should handle error.
                     				Utils.println("Cannot find '" + fileName + "', even after considering several possible extensions.");
                     				throw new FileNotFoundException();
                     			}
                     			String newFileName = Utils.unzipFileIfNeeded(fileName + ".gz"); // TODO - can we do this without unzipping?
                     			if (newFileName != null) {
                     				f = new CondorFile(newFileName); // This should be same as fileName.
                     				if (!f.exists()) {
                     					// The calling code should handle error.
                     					Utils.println("Cannot find '" + fileName + "', even after considering several possible extensions.");
                     					throw new FileNotFoundException();
                     				}
                     			}
                     		}
                 		}
             		}
             	}
            }
        }
        return f;
	}

	/**
         * A variant of readFOPCfile(String fileName) where an input stream
         * instead of a file name is provided.
         *
     * @param file
     * @param inStream
         * @return A list of sentences, the result of parsing the given file.
     * @throws ParsingException
     * @throws IOException
         */
	public List<Sentence> readFOPCstream(File file, InputStream inStream) throws ParsingException, IOException {

        // This is a big hack to pass around the name with stream.
        // There are better ways to do this, but not at this point in time.
        Reader r = null;
        if ( inStream instanceof NamedInputStream ) {
            r = new NamedReader(new InputStreamReader(inStream), inStream.toString());
	}
        else {
            r = new InputStreamReader(inStream);
        }

		return readFOPCreader(file, r);
	}

	/**
         * A variant of readFOPCfile(String fileName) where a string instead of
         * a file name is provided.
         *
         * @param string
         * @return A list of sentences, the result of parsing the given file.
         * @throws ParsingException
         */
	public List<Sentence> readFOPCstream(String string) {
		try {
			return readFOPCreader(new StringReader(string), null); // Fine that there is no directory here, since reading a string.
		}
		catch (Exception e) {
			Utils.reportStackTrace(e);
			Utils.error("Error parsing: '" + (string != null && string.length() > 1500 ? string.substring(0, 1500) + " ..." : string) + "'."); return null;
		}
	}
	public List<Sentence> readFOPCstreamDontThrowError(String string) throws IOException {
		return readFOPCreader(new StringReader(string), null); // Fine that there is no directory here, since reading a string.
	}

	
	public List<Sentence> readFOPCreaderUsingCentralListForImports(Reader inStream, String newDirectoryName) throws IOException {
		if (collectAllImportedSentencesInOneSpot) { Utils.waitHere("Should not call this when collectAllSentencesInOneSpot = true."); }
		String hold_directoryName = directoryName;
		clearCollectedImportedSentences();
		if (newDirectoryName != null) { checkDirectoryName(newDirectoryName); }
		List<Sentence> results = readFOPCreader(null, inStream);
		if (newDirectoryName != null) { checkDirectoryName(hold_directoryName); }
		if (results != null) { collectionOfAllImportedSentences.addAll(results); } // Presumably 'results' is smaller than all the imports, so add this way rather than vice-versa.
		results = collectionOfAllImportedSentences;
		collectionOfAllImportedSentences     = new ArrayList<Sentence>(4); // Could set to null until next needed, but this is not a big deal.
		collectAllImportedSentencesInOneSpot = false;
		return results;
	}

	public List<Sentence> readFOPCreader(Reader inStream, String newDirectoryName) throws IOException {
		String hold_directoryName = directoryName;
		if (newDirectoryName != null) { checkDirectoryName(newDirectoryName); }
		List<Sentence> results = readFOPCreader(null, inStream);
		if (newDirectoryName != null) { checkDirectoryName(hold_directoryName); }
		return results;
	}
	private void initTokenizer(StreamTokenizerJWS theTokenizer) {
		theTokenizer.resetSyntax();                // Clear everything so we can reset to what we want.
		theTokenizer.ordinaryChar('/');
		theTokenizer.slashSlashComments(true);     // The string "//" is interpreted as a "comment from here to end of line."
		theTokenizer.slashStarComments( true);     // The string "/* starts a comments that ends at "*/".
		theTokenizer.commentChar('%');             // Also used YAP Prolog's character for "comment from here to end of line."
		theTokenizer.lowerCaseMode(false);         // Do NOT convert everything to lower case (case differentiates variables from constants, plus we want to print things out using the case users provided).
		// In text like "p(x)." the period is interpreted for some reason as the number "0.0" so need to turn this off and parse numbers explicitly.
		//theTokenizer.parseNumbers();             // Treat strings of digits (and a possible decimal point) as a number rather than a string.
		theTokenizer.eolIsSignificant(false);      // EOL is NOT significant.  Instead need a ' or a ';' to indicate EOL.
		theTokenizer.quoteChar('"');               // Allow quoted tokens.  Quoted tokens are always constants, regardless of the case of their first letter.
		theTokenizer.quoteChar('\'');
		theTokenizer.whitespaceChars(' ', ' ');    // Specify the white-space characters.
		theTokenizer.whitespaceChars('\n', '\n');	//   Newline (aka, line feed).
		theTokenizer.whitespaceChars('\r', '\r');	//   Carriage return.
		theTokenizer.whitespaceChars('\t', '\t');	//   Tab.
		theTokenizer.wordChars('A', 'Z');          // The legal characters in tokens.  Ideally should not start with a number, but no big deal.
        theTokenizer.wordChars(192, 255);          // Mark (some) accented characters as word characters.
		theTokenizer.wordChars('a', 'z');
		theTokenizer.wordChars('\u00AA', '\u00FF'); // THIS IS DONE BOTH HERE AND IN StringConstant (though not harmful - just adds more quote marks than are necessary, when only done in one place, some problems arose).
		theTokenizer.wordChars('0', '9');
		theTokenizer.wordChars('_', '_');
		theTokenizer.wordChars('?', '?');	// TODO - only allow as the FIRST character?	NOTE: this means that we cannot use '?' as a TypeSpec in things to parse.
	}

	private static boolean                    useCacheOfReadFiles      = false;
	private static Map<String,List<Sentence>> cacheOfReadFilesContents = new HashMap<String,List<Sentence>>(4);
	private static Map<String,Long>           cacheOfReadFilesDates    = new HashMap<String,Long>(4);
	public  static void clearReadFileCaches() {
		cacheOfReadFilesContents.clear();
		cacheOfReadFilesDates.clear();
	}
    private static final Pattern precomputePattern = Pattern.compile("precompute([0-9]+)");
    
	/**
         * A variant of readFOPCfile(String fileName) where a 'reader' instead
         * of a file name is provided.
         *
     * @param file
     * @param inStream
         * @return A list of sentences, the result of parsing the given file.
         * @throws IOException
         * @throws ParsingException
         */
	public List<Sentence> readFOPCreader(File file, Reader inStream) throws IOException {
		if (file == null && inStream == null) { return null; }
		List<Sentence> lookup = (file != null && useCacheOfReadFiles ? cacheOfReadFilesContents.get(file.getCanonicalPath()) : null);
		if (lookup != null) {
			Long lookup1  = cacheOfReadFilesDates.get(file.getCanonicalPath());
			long lastDate = file.lastModified();
			if (lookup1 >= lastDate) { // Hasn't changed since last read.
				if (!dontPrintUnlessImportant) { Utils.println("% Read CACHED version of: " + file.getCanonicalPath()); }
				return lookup;
			}
			if (!dontPrintUnlessImportant) { Utils.println("% Had CACHED this file, but changed since last read and so will re-read:\n%  " + file.getCanonicalPath()); }
		}
		
		VarIndicator holdVarIndicator = stringHandler.getVariableIndicatorNoSideEffects(); // Be sure to pop back to current setting after reading.
		if (!dontPrintUnlessImportant && file != null) { Utils.println(PARSER_VERBOSE_MODE_LOADING, "\n% Reading file '" + file + "'."); }
		String fileNameForErrorReporting  = "stream";
        if ( file != null ) {
            fileNameForErrorReporting =file.getParent();
        }
        else if ( inStream instanceof NamedReader ) {
            fileNameForErrorReporting = inStream.toString();
        }

		String hold_directoryName = directoryName;
		String parent = (file == null ? null : file.getParent());
		if (file != null) {	checkDirectoryName(parent);	}

		List<Sentence> listOfSentencesReadOrCreated = new ArrayList<Sentence>(8);
		tokenizer = new StreamTokenizerJWS(inStream, 8); // Don't need to do more than 2-3 push backs, so don't need a big buffer.
		initTokenizer(tokenizer);
		
		
		// Note: the following should be "stand-alone words":  '(', ')', ',', ', ';'. '[', ']'
		int tokenRead;
		Sentence nextSentence = null;

		try {
			tokenRead = tokenizer.nextToken();
			while (tokenRead != StreamTokenizer.TT_EOF) {  // TODO discard this test code below
				/*  Code to test the buffer for pushing back more than one token.
				                                   Utils.println("0=" + reportLastItemRead());
				tokenRead = tokenizer.nextToken(); Utils.println("1=" + reportLastItemRead());
				tokenRead = tokenizer.nextToken(); Utils.println("2=" + reportLastItemRead());
				tokenRead = tokenizer.nextToken(); Utils.println("3=" + reportLastItemRead());
				tokenRead = tokenizer.nextToken(); Utils.println("4=" + reportLastItemRead());
				tokenRead = tokenizer.nextToken(); Utils.println("5=" + reportLastItemRead());
				tokenRead = tokenizer.nextToken(); Utils.println("6=" + reportLastItemRead());
				tokenRead = tokenizer.nextToken(); Utils.println("7=" + reportLastItemRead());
				tokenRead = tokenizer.nextToken(); Utils.println("8=" + reportLastItemRead());
				tokenRead = tokenizer.nextToken(); Utils.println("9=" + reportLastItemRead());
				tokenizer.pushBack();
				tokenRead = tokenizer.nextToken(); Utils.println("9=" + reportLastItemRead());
				tokenizer.pushBack();
				tokenizer.pushBack();
				tokenizer.pushBack();
				tokenRead = tokenizer.nextToken(); Utils.println("7=" + reportLastItemRead());
				tokenRead = tokenizer.nextToken(); Utils.println("8=" + reportLastItemRead());
				tokenRead = tokenizer.nextToken(); Utils.println("9=" + reportLastItemRead());
				tokenizer.dump();
				Utils.waitHere();
				*/

				nextSentence = null;
				if (debugLevel > 0) { Utils.println("At line #" + Utils.comma(tokenizer.lineno()) + " of '" + fileNameForErrorReporting + "' and read '" + tokenizer.reportCurrentToken() + "'."); }
				switch (tokenRead) {
					case StreamTokenizer.TT_WORD:
						String currentWord = tokenizer.sval();
						boolean colonNext = checkAndConsume(':'); // If the next character is a colon, it will be "sucked up" and 'true' returned.  Otherwise it will be puhsed back and 'false' returned.
						if (colonNext && currentWord.equalsIgnoreCase("define"))         { processDefinition( );  break; }
						if (colonNext && currentWord.equalsIgnoreCase("setParam"))       { processSetParameter(); break; }
						if (colonNext && currentWord.equalsIgnoreCase("setParameter"))   { processSetParameter(); break; }
						if (colonNext && currentWord.equalsIgnoreCase("mode"))           { processMode(listOfSentencesReadOrCreated, false); break; }
						//ChangedBy Navdeep Kaur
						if (colonNext && currentWord.equalsIgnoreCase("randomwalkconstraint")) 			 { processRandomWalks(listOfSentencesReadOrCreated); break; }
						if (colonNext && currentWord.equalsIgnoreCase("noMode"))         { processMode(listOfSentencesReadOrCreated, true);  break; }
						if (colonNext && currentWord.equalsIgnoreCase("constrains"))     { processConstrains( ); break; }
						if (colonNext && currentWord.equalsIgnoreCase("determinate"))    { processDeterminate(); break; }
						if (colonNext && currentWord.equalsIgnoreCase("numericFunctionAsPred"))           { processFunctionAsPred(FunctionAsPredType.numeric);           break; }
						if (colonNext && currentWord.equalsIgnoreCase("booleanFunctionAsPred"))           { processFunctionAsPred(FunctionAsPredType.bool);              break; }
						if (colonNext && currentWord.equalsIgnoreCase("categoricalFunctionAsPred"))       { processFunctionAsPred(FunctionAsPredType.categorical);       break; }
						if (colonNext && currentWord.equalsIgnoreCase("structuredFunctionAsPred"))        { processFunctionAsPred(FunctionAsPredType.structured);        break; }
						if (colonNext && currentWord.equalsIgnoreCase("anythingFunctionAsPred"))          { processFunctionAsPred(FunctionAsPredType.anything);          break; }
						if (colonNext && currentWord.equalsIgnoreCase("listOfNumericFunctionAsPred"))     { processFunctionAsPred(FunctionAsPredType.listOfNumeric);     break; }
						if (colonNext && currentWord.equalsIgnoreCase("listOfBooleanFunctionAsPred"))     { processFunctionAsPred(FunctionAsPredType.listOfBoolean);     break; }
						if (colonNext && currentWord.equalsIgnoreCase("listOfCategoricalFunctionAsPred")) { processFunctionAsPred(FunctionAsPredType.listOfCategorical); break; }
						if (colonNext && currentWord.equalsIgnoreCase("listOfStructuredFunctionAsPred"))  { processFunctionAsPred(FunctionAsPredType.listOfStructured);  break; }
						if (colonNext && currentWord.equalsIgnoreCase("listOfAnythingFunctionAsPred"))    { processFunctionAsPred(FunctionAsPredType.listOfAnything);    break; }
						if (colonNext && currentWord.equalsIgnoreCase("bridger"))        { processBridger();     break; }
						if (colonNext && currentWord.equalsIgnoreCase("temporary"))      { processTemporary();   break; }
						if (colonNext && currentWord.equalsIgnoreCase("inline"))         { processInline();      break; }
						if (colonNext && currentWord.equalsIgnoreCase("threshold"))      { processThreshold();   break; }
						if (colonNext && currentWord.equalsIgnoreCase("filter"))         { processFilter();      break; }
						if (colonNext && currentWord.equalsIgnoreCase("relevant"))       { processRelevant(       listOfSentencesReadOrCreated); break; } // Can add a sentence, so pass in the collector.
						if (colonNext && currentWord.equalsIgnoreCase("relevantClause")) { processRelevantClause( listOfSentencesReadOrCreated); break; } // Can add a sentence, so pass in the collector.
						if (colonNext && currentWord.equalsIgnoreCase("relevantFeature")){ processRelevantFeature(listOfSentencesReadOrCreated); break; } // Can add a sentence, so pass in the collector.
                        if (colonNext && currentWord.equalsIgnoreCase("nonOperational")) { processNonOperational(); break; }
                        if (colonNext && currentWord.equalsIgnoreCase("relevantMode")) {
                            processRelevantMode(listOfSentencesReadOrCreated);
                            break;
                        } // Can add a sentence, so pass in the collector.
                        if (colonNext && currentWord.equalsIgnoreCase("relevantLiteral")) {
                            processRelevantLiteralNew(listOfSentencesReadOrCreated);
                            break;
                        } // Can add a sentence, so pass in the collector.
                        if ( colonNext && currentWord.equalsIgnoreCase("alias")) {
                            processLiteralAlias();
                            break;
                        }
                        if ( colonNext && currentWord.equalsIgnoreCase("containsCallable"))  { processContainsCallables(); break; }
                        if (colonNext && currentWord.equalsIgnoreCase("supportingLiteral"))   { processSupporter();   break;}
                        if (colonNext && currentWord.equalsIgnoreCase("supportLiteral"))      { processSupporter();   break; }
                        if (colonNext && currentWord.equalsIgnoreCase("supportingPredicate")) { processSupporter();   break;}
                        if (colonNext && currentWord.equalsIgnoreCase("supportPredicate"))    { processSupporter();   break; }
						if (colonNext && currentWord.equalsIgnoreCase("cost"))                { processCost(false);   break; }
						if (colonNext && currentWord.equalsIgnoreCase("costFinal"))           { processCost(true);    break; }
						if (colonNext && currentWord.equalsIgnoreCase("disc"))          { break; } 
						if (colonNext && currentWord.equalsIgnoreCase("precompute"))          { processPrecompute(0); break; } 
						if (colonNext && currentWord.startsWith("precompute"))     {
							// Do the regex matching now.
							Matcher m = precomputePattern.matcher(currentWord);
							if (m.matches()) {
								String pMat = m.group(1);
								int numPrecompute = Integer.parseInt(pMat);
								processPrecompute(numPrecompute);
								break;
							}
							Utils.waitHere("Word starts with 'precompute' but doesn't match: " + precomputePattern);
						}
						if (colonNext && currentWord.equalsIgnoreCase("prune"))          { processPrune(false,  0); break; }
						if (colonNext && currentWord.equalsIgnoreCase("pruneTrue"))      { processPrune(false,  1); break; }
						if (colonNext && currentWord.equalsIgnoreCase("pruneFalse"))     { processPrune(false, -1); break; }
						if (colonNext && currentWord.equalsIgnoreCase("isVariant"))      { processPrune(true,   0); break; }
						if (colonNext && currentWord.equalsIgnoreCase("isa"))            { processISA(        ); break; }
						if (colonNext && currentWord.equalsIgnoreCase("isaInterval"))    { processISAInterval(); break; }
						if (colonNext && currentWord.equalsIgnoreCase("range"))          { processTypeRange(  ); break; }
						if (colonNext && currentWord.equalsIgnoreCase("queryPred"))      { processQueryPred(  ); break; }
						if (colonNext && currentWord.equalsIgnoreCase("hiddenPred"))     { processHiddenPred( ); break; }
						if (colonNext && currentWord.equalsIgnoreCase("weight"))         { nextSentence = processWeight(':'); break; }
						if (colonNext && currentWord.equalsIgnoreCase("wgt"))            { nextSentence = processWeight(':'); break; }
						if (colonNext && currentWord.equalsIgnoreCase("output"))         { nextSentence = processWeight(':'); break; }
						if (colonNext && currentWord.equalsIgnoreCase("out"))            { nextSentence = processWeight(':'); break; }
						if (colonNext && currentWord.equalsIgnoreCase("okIfUnknown"))                    { processDirective(currentWord);  break; }
						if (colonNext && currentWord.equalsIgnoreCase("dontComplainAboutMultipleTypes")) { processDirective(currentWord);  break; }
						if (colonNext && currentWord.equalsIgnoreCase("useStdLogicVariables"))           { processCaseForVariables(true);  break; }
						if (colonNext && currentWord.equalsIgnoreCase("useStdLogicNotation"))            { processCaseForVariables(true);  break; }
						if (colonNext && currentWord.equalsIgnoreCase("usePrologVariables"))             { processCaseForVariables(false); break; }
						if (colonNext && currentWord.equalsIgnoreCase("usePrologNotation"))              { processCaseForVariables(false); break; }
						if (colonNext && currentWord.equalsIgnoreCase("useLeadingQuestionMarkVariables")){ processUseQuestionMarkForVariables(); break; }
						if (colonNext && currentWord.equalsIgnoreCase("import"))      {
							List<Sentence>  sentencesInOtherFile =                         processAnotherFile(false, true);
							if (sentencesInOtherFile         == null) { break; }
							if (collectAllImportedSentencesInOneSpot) {
								collectionOfAllImportedSentences.addAll(sentencesInOtherFile);
							} else {
								if (listOfSentencesReadOrCreated == null) { listOfSentencesReadOrCreated = new ArrayList<Sentence>(sentencesInOtherFile.size()); }
								listOfSentencesReadOrCreated.addAll(sentencesInOtherFile);
							}
							break;
						}
						if (colonNext && currentWord.equalsIgnoreCase("importIfExists"))      {
							List<Sentence>  sentencesInOtherFile =                         processAnotherFile(false, false);
							if (sentencesInOtherFile         == null) { break; }
							if (collectAllImportedSentencesInOneSpot) {
								collectionOfAllImportedSentences.addAll(sentencesInOtherFile);
							} else {
								if (listOfSentencesReadOrCreated == null) { listOfSentencesReadOrCreated = new ArrayList<Sentence>(sentencesInOtherFile.size()); }
								listOfSentencesReadOrCreated.addAll(sentencesInOtherFile);
							}
							break;
						}
						if (colonNext && currentWord.equalsIgnoreCase("importLibrary"))      {
							List<Sentence>  sentencesInOtherFile =                         processAnotherFile(true, true);
							if (sentencesInOtherFile         == null) { break; }
							if (collectAllImportedSentencesInOneSpot) {
								collectionOfAllImportedSentences.addAll(sentencesInOtherFile); 
							} else {
								if (listOfSentencesReadOrCreated == null) { listOfSentencesReadOrCreated = new ArrayList<Sentence>(sentencesInOtherFile.size()); }
								listOfSentencesReadOrCreated.addAll(sentencesInOtherFile);
							}
							break;
						}
						if (colonNext) { tokenizer.pushBack(); } // Need to push the colon back if it wasn't part of a special instruction.  It can also appear in modes of terms.
						if (currentWord.equalsIgnoreCase("weight") || currentWord.equalsIgnoreCase("wgt")) { nextSentence = processWeight(getNextToken()); break; }
						if (!ignoreThisConnective(true, currentWord) && ConnectiveName.isaConnective(currentWord) && !ConnectiveName.isTextualConnective(currentWord)) { // NOT's handled by processFOPC_sentence.
							//Utils.error("Need to handle a PREFIX connective: '" + currentWord + "'.");
							// If here, there must be exactly two arguments.
							ConnectiveName connective = stringHandler.getConnectiveName(currentWord);
							if (!checkAndConsume('(')) { tokenizer.nextToken(); throw new ParsingException("Expecting a left parenthesis, but read '" + reportLastItemRead() + "'."); }
							Sentence arg1 = processFOPC_sentence(0, true);
							if (!checkAndConsume(',')) { tokenizer.nextToken(); throw new ParsingException("Expecting a comma, but read '" + reportLastItemRead() + "'."); }
							Sentence arg2 = processFOPC_sentence(0, true);
							if (!checkAndConsume(')')) { tokenizer.nextToken(); throw new ParsingException("Expecting a right parenthesis, but read  '" + reportLastItemRead() + "'."); }
							nextSentence = stringHandler.getConnectedSentence(arg1, connective, arg2);
							break;
						}
						// The default is to read an FOPC sentence.
						tokenizer.pushBack();
						nextSentence =                                                  processFOPC_sentence(0);
						break;
					case StreamTokenizer.TT_NUMBER:  throw new ParsingException("Should not happen in the parser:  Read this NUMBER: " + tokenizer.nval());  // See comment above as to why this won't be reached.
					case ':':
						if (checkAndConsume('-')) { // At a Prolog-like "instruction to the system" (as opposed to a fact/rule being stated).
							processInstructionToSystem();
							break;
						}
						throw new ParsingException("Lines should not start with ':' unless followed by '-' (i.e., ':-').");
					case '\\':  // Could be starting '\+'
					case '~':
					case '(':
					case '{':
					case '[':
					case '!':
					case '+': // Could have something like '+5 < y'
					case '-': // Or, more likely, '-5 < y'   Could also be a "bare" weight.
						tokenizer.pushBack(); // The FOPC reader can handle these characters.
						nextSentence = processFOPC_sentence(0);
						break;
					case '.': // An empty sentence is OK, plus reading an FOPC sentence never sucks up the closing EOL.
					case ';':
						break;
					case StreamTokenizer.TT_EOL:    throw new ParsingException("Should not read EOL's here."); // EOL is in the "traditional" sense here (e.g., '\n').
					case StreamTokenizer.TT_EOF:    throw new ParsingException("Should not read EOF's here.");
					default:                        if (tokenRead == '/') { Utils.println("If a file ends with '*/' add a space after the '/' to overcome an apparent bug with StringTokenizer's handling of comments."); }
													throw new ParsingException("Read this *unexpected* character: '" + (char)tokenRead + "'."); // TODO - hit this once when the last character was the '/' in a closing quote (i.e., '*/').  Added a space afterwards and all worked fine.
				}
				if (nextSentence != null) {
					if (nextSentence.containsTermAsSentence()) {
						throw new ParsingException("This is not a valid FOPC sentence: '" + nextSentence + ".'  It contains a logical term where a logical sentence should appear.");
					}
					Sentence finalSentence = nextSentence.wrapFreeVariables(); // Add any implicit ForAll.
 					//Added By Navdeep Kaur
 					Sentence finalSentence2 = null;
 					if (nextSentence instanceof Literal)
 					{
 						if(!((Literal)nextSentence).predicateName.getNoTwinValue() && ((Literal)nextSentence).predicateName.getRandomWalkFlag())
         				{
         					FunctionName fName = stringHandler.getFunctionName("_"+(((Literal)nextSentence).predicateName.name));
         					List<Term> arguments = new ArrayList<Term>();
         					arguments.add(0,((Literal)nextSentence).getArgument(1));
         					arguments.add(1,((Literal)nextSentence).getArgument(0));
         					Term possibleTerm = stringHandler.getFunction(fName, arguments,null,null);
         					Sentence invS = convertTermToLiteral(possibleTerm);
         					finalSentence2 = invS.wrapFreeVariables();
         				}
 					}

					if (debugLevel > 0) { Utils.println("Read sentence: " + finalSentence + "."); }
					if (listOfSentencesReadOrCreated == null) { listOfSentencesReadOrCreated = new ArrayList<Sentence>(128); }
					listOfSentencesReadOrCreated.add(finalSentence);
					
 					//Added By Navdeep Kaur
 					if(finalSentence2!=null)
 						listOfSentencesReadOrCreated.add(finalSentence2);
					

					if (debugLevel > 0) if ((listOfSentencesReadOrCreated.size() % 10000) == 0) { Utils.println("%    " + Utils.comma(listOfSentencesReadOrCreated.size()) + " items so far from " + fileNameForErrorReporting + "."); }
					nextSentence = null;
				} // else { Utils.println("No next sentence."); }
				stringHandler.resetAllVariables(); // Clear cache of variables, since old ones (if any) now out of scope.
				tokenRead = tokenizer.nextToken();
			}
		}
		catch (IOException e) {
			Utils.println("\nEncountered I/O exception during parsing (line = " + tokenizer.lineno() + "): ");
			Utils.reportStackTrace(e);
			Utils.error("Unable to successfully parse this file: " + fileNameForErrorReporting + ".\nError message: " + e.getMessage());
		}
		catch (WILLthrownError e) {
			Utils.println("\nEncountered WILL runtime error during parsing (line #" + tokenizer.lineno() + ") of file '" + fileNameForErrorReporting + "': ");
			Utils.reportStackTrace(e);
			Utils.error("Unable to successfully parse this file: " + fileNameForErrorReporting + ".\nError message: " + e.getMessage());
		}
		catch (Exception e) {
			Utils.println("\nEncountered an exception during parsing (line #" + Utils.comma(tokenizer.lineno()) + ") of file '" + fileNameForErrorReporting + "': ");
			Utils.reportStackTrace(e);
			Utils.error("Unable to successfully parse this file: " + fileNameForErrorReporting + ".\nError message: " + e.getMessage());
		}
		if (debugLevel > 0) { Utils.println("Read " + Utils.comma(listOfSentencesReadOrCreated) + " FOPC sentences from " + fileNameForErrorReporting + " (and any imports inside of it)."); }
		if (debugLevel > 1 && Utils.getSizeSafely(listOfSentencesReadOrCreated) > 0) for (Sentence s : listOfSentencesReadOrCreated) { Utils.println("  " + s + "."); }
		checkDirectoryName(hold_directoryName);

		if (holdVarIndicator != null) { // If previously set, revert to that setting.
			stringHandler.setVariableIndicator(holdVarIndicator);
		} else {
			Utils.warning(STRING_HANDLER_VARIABLE_INDICATOR, "% Since this is the first setting of the notation for variables, will keep:\n%   variableIndicator = " + stringHandler.getVariableIndicator(), 1);
		}

		if (file != null && !dontPrintUnlessImportant) { Utils.println("% DONE reading file '" + file + "'."); }

		if (file != null && useCacheOfReadFiles) {
			cacheOfReadFilesContents.put(file.getCanonicalPath(), listOfSentencesReadOrCreated);
			cacheOfReadFilesDates.put(   file.getCanonicalPath(), file.lastModified());
		}
		return listOfSentencesReadOrCreated;
	}

    /** Parses a string into a list of sentences.
     *
     * @param string
     * @return
     */
    public List<Sentence> parse(String string) {
        return readFOPCstream(string);
    }

    public Clause parseDefiniteClause(String definiteClause) throws ParsingException {

        Clause result = null;

        List<Sentence> sentences = null;
        
        if ( definiteClause.endsWith(".") == false ) {
            definiteClause = definiteClause + ".";
        }

        sentences = readFOPCstream(definiteClause);

        if ( sentences == null ) {
            throw new ParsingException("parseDefiniteClause generated multiple clauses from: '" + definiteClause + "'.");
        }

        if ( sentences.size() > 1 ) {
            throw new ParsingException("parseDefiniteClause generated multiple clauses from: '" + definiteClause + "'.");
        }

        if ( sentences.size() == 1) {
            Sentence s = sentences.get(0);

            List<Clause> clauses = s.convertToClausalForm();

            if ( clauses.size() > 1 ) {
                throw new ParsingException("parseDefiniteClause generated multiple clauses from: '" + definiteClause + "'.");
            }

            if ( clauses.size() == 1 ) {
                result = clauses.get(0);
            }
        }

        return result;
    }

    /** Parses a single clause containing only positive literals separated by commas.
     *
     * @param positiveLiterals
     * @return
     * @throws ParsingException
     */
    public Clause parsePositiveLiterals(String positiveLiterals) throws ParsingException {

        Clause result = null;

        List<Sentence> sentences = null;
        
        if ( positiveLiterals.endsWith(".") == false ) {
            positiveLiterals = positiveLiterals + ".";
        }
        
        sentences = readFOPCstream(positiveLiterals);

        if ( sentences == null ) {
            throw new ParsingException("parsePositiveLiterals generated multiple clauses from: '" + positiveLiterals + "'.");
        }

        if ( sentences.size() > 1 ) {
            throw new ParsingException("parsePositiveLiterals generated multiple clauses from: '" + positiveLiterals + "'.");
        }

        if ( sentences.size() == 1) {
            Sentence s = sentences.get(0);

            List<Clause> clauses = s.convertToClausalForm();

            if ( clauses.size() != 1 ) {
                throw new ParsingException("parsePositiveLiterals's expected a list of literals.");
            }

            Clause c = clauses.get(0);
            if ( c.getNegLiteralCount() != 0 ) {
                throw new ParsingException("parsePositiveLiterals's parsed form contains negated literals.");
            }
            
            result = c;

        }

        return result;
    }

    public Literal parseLiteral(String literal) throws ParsingException {

        Literal result = null;

        if ( literal.endsWith(".") == false ) {
            literal += ".";
        }

        List<Sentence> sentences = readFOPCstream(literal);
        if ( sentences == null || sentences.size() > 1 ) {
            throw new ParsingException("parseLiteral generated multiple clauses/literals from: '" + literal + "'.");
        }

        if ( sentences.size() == 1) {
            Sentence s = sentences.get(0);

            List<Clause> clauses = s.convertToClausalForm();

            if ( clauses.size() > 1 ) {
                throw new ParsingException("parseLiteral generated multiple clauses/literals from: '" + literal + "'.");
            }

            if ( clauses.size() == 1 ) {
                Clause c = clauses.get(0);

                if ( c.isDefiniteClauseFact() == false ) {
                    throw new ParsingException("parseLiteral did not result in a single literal from: '" + literal + "'.");
                }

                result = c.getDefiniteClauseFactAsLiteral();
            }
        }

        return result;
    }

    public List<DefiniteClause> parseDefiniteClauses(String definiteClauses) throws ParsingException {
        List<DefiniteClause> results = new ArrayList<DefiniteClause>();

        List<Sentence> sentences = readFOPCstream(definiteClauses);

        for (Sentence sentence : sentences) {
            List<Clause> clauses = sentence.convertToClausalForm();

            for (Clause clause : clauses) {
                if ( clause.isDefiniteClause() == false ) {
                    throw new ParsingException("parseDefiniteClauses parsed a non-definite clause sentence: " + sentence + ".");
                }

                results.add(clause);
            }
        }

        return results;
    }

	private boolean ignoreThisConnective(boolean ignoreNOTs, String str) {
		return ((ignoreNOTs                    &&  ConnectiveName.isaNOT(str)) ||
				(treatAND_OR_NOTasRegularNames && (ConnectiveName.isaAND(str)  || ConnectiveName.isaOR(str)|| ConnectiveName.isaNOT(str))));
	}

	private void processInstructionToSystem() throws IOException {
		tokenizer.nextToken();
		String nextTokenAsString = tokenizer.reportCurrentToken();

		if       (nextTokenAsString.equalsIgnoreCase("discontiguous")) {
			Utils.println("%   Currently ':- " + nextTokenAsString + "' lines are ignored.");
			//recordWarningAboutIgnored(nextTokenAsString);
		}
		else if (nextTokenAsString.equalsIgnoreCase("dynamic")) {
			Utils.println("%   Currently ':- " + nextTokenAsString + "' lines are ignored.");
			//recordWarningAboutIgnored(nextTokenAsString);
		}
		else if (nextTokenAsString.equalsIgnoreCase("multifile")) {
			Utils.println("%   Currently ':- " + nextTokenAsString + "' lines are ignored.");
			//recordWarningAboutIgnored(nextTokenAsString);
		}
		else {
			Utils.warning("% Unknown ':- " + nextTokenAsString + "' command.");
		}
		skipToEOL();
	}

	private void skipToEOL() throws IOException {  // Should this stop at StreamTokenizer.TT_EOL?  Probably not.
		if (atEOL()) { return; }
		tokenizer.nextToken();
		while (!atEOL()) {
			int tokenRead = tokenizer.nextToken();
			if (tokenRead == StreamTokenizer.TT_EOF) { throw new IOException("Unexpected EOF: " + fileName); }
		}
	}

	private void processUseQuestionMarkForVariables() throws ParsingException, IOException {
		int nextToken = tokenizer.nextToken();
		if (nextToken != StreamTokenizer.TT_WORD) { throw new ParsingException("Expecting a token after useLeadingQuestionMarkVariables, but read: '" + reportLastItemRead()); }
		if (tokenizer.sval().equalsIgnoreCase("true") || tokenizer.sval().equalsIgnoreCase("yes") || tokenizer.sval().equalsIgnoreCase("1")) {
			stringHandler.setVariablesStartWithQuestionMarks();
		} else {
			stringHandler.usePrologNotation(); // If NO is given to setVariablesStartWithQuestionMarks? then use standard Prolog notation.
		}
		peekEOL(true);
	}

	/**
	 * Allow specification of notation for logical variables.  See comments about "useStdLogicVariables" and "usePrologVariables" above.
	 *
	 * @param defaultIsUseStdLogic
	 * @throws ParsingException
	 */
	private void processCaseForVariables(boolean defaultIsUseStdLogic) throws ParsingException, IOException {
		int nextToken = tokenizer.nextToken();

		if (nextToken != StreamTokenizer.TT_WORD) { throw new ParsingException("Expecting a token after " + (defaultIsUseStdLogic ? "useStdLogicVariables" : "usePrologVariables" + ", but read: '") + reportLastItemRead()); }
		if (tokenizer.sval().equalsIgnoreCase("true") || tokenizer.sval().equalsIgnoreCase("yes") || tokenizer.sval().equalsIgnoreCase("1")) {
			if (defaultIsUseStdLogic) { stringHandler.useStdLogicNotation(); } else { stringHandler.usePrologNotation();   }
		}
		else {
			if (defaultIsUseStdLogic) { stringHandler.usePrologNotation();   } else { stringHandler.useStdLogicNotation(); }
		}
		peekEOL(true);
	}

	/**
         Read something of the form: Mary = motherOf(John). The EOL ('.' or ';') is optional.
    */
	private void processDefinition() throws ParsingException, IOException  {
		Constant  lhs       = processConstant();
		int       nextToken = tokenizer.nextToken();

		if (nextToken == '=') {
			Function rhs = processFunction();

			if (!rhs.isGrounded()) { throw new ParsingException("In a function definition, the right-hand side must be a function of constants.  You provided: '" + lhs + " = " + rhs + "'."); }
			peekEOL(true);
			if (rhs.getArguments() != null) {
				List<Constant> constants = new ArrayList<Constant>(rhs.numberArgs());
				for (Term term : rhs.getArguments()) { constants.add((Constant) term); } // Have already checked that these are all constants.
				rhs.functionName.addExtensionalDefinition(constants, lhs);
			}
			else {
				rhs.functionName.addExtensionalDefinition(null, lhs);
			}
			if (debugLevel > 1) { Utils.println("Define: " + lhs + " = " + rhs + "."); }

		}
		else { throw new ParsingException("Expecting an '=' if the specification of the semantics of a function, but read '" +  reportLastItemRead()); }
	}

	private Function processFunction() throws ParsingException, IOException {
		Term term = processTerm(false);

		if (term instanceof Function) { return (Function) term; }
		throw new ParsingException("Expecting to read a grounded function in the specification of the semantics of a function, but read '" + term + "'.");
	}

	private Constant processConstant() throws ParsingException, IOException  {
		int      nextToken = tokenizer.nextToken();
		TypeSpec typeSpec   = null; // For future expansion.

		if (nextToken != StreamTokenizer.TT_WORD) { throw new ParsingException("Was expecting a constant and read: '" + reportLastItemRead() + "'."); }
		Constant result = stringHandler.getStringConstant(typeSpec, tokenizer.sval(), false);
		if (result == null) { throw new ParsingException("The term '" + tokenizer.sval() + "' is not the proper case (upper/lower) to be a constant."); }
		return result;
	}

	private Literal processInfixLiteral(Term firstTerm, String inFixOperatorName) throws ParsingException, IOException {
		return processInfixLiteral(firstTerm, inFixOperatorName, false);
	}

	private Literal processInfixLiteral(Term firstTerm, String inFixOperatorName, boolean argumentsMustBeTyped) throws ParsingException, IOException {
		if (debugLevel > 1) { Utils.println("In processInfixLiteral.  First term = '" + firstTerm + "' and in-fix operator = '" + inFixOperatorName + "'."); }
		Term secondTerm;
        
        if (inFixOperatorName.equalsIgnoreCase("is")) {
            secondTerm = processIS(argumentsMustBeTyped);
        }
        else {
            secondTerm = processTerm(argumentsMustBeTyped);
        }
        
		if (debugLevel > 2) { Utils.println("  second term: '" + secondTerm + "'."); }
		List<Term>    args   = new ArrayList<Term>(2);
		PredicateName pName  = stringHandler.getPredicateName(inFixOperatorName); pName.printUsingInFixNotation = true;
        args.add(firstTerm);
        args.add(secondTerm);
		Literal       result = stringHandler.getLiteral(pName, args);
		if (debugLevel > 2) { Utils.println(" literal: " + result); }
		return result;
	}
	private Term processIS(boolean argumentsMustBeTyped) throws ParsingException, IOException {
		if (debugLevel > 2) { Utils.println("\nSTART processIS."); }
		Term result = processMathExpression(null, argumentsMustBeTyped, false);
		if (debugLevel > 2) { Utils.println("FINAL RESULT of processIS: " + result); }
		return result;
	}
	// This version is used if peeking ahead sees a '/' etc, e.g., 'p(x/y/z, 5)' or 'p(f(x)+f(y))'.
	private Term processMathExpression(boolean argumentsMustBeTyped, boolean insideLeftParen) throws ParsingException, IOException {
		Term result = processMathExpression(null, argumentsMustBeTyped, insideLeftParen);
		if (debugLevel > 2) { Utils.println("FINAL RESULT of processMathExpression: " + result); }
		return result;
	}
	private Term processMathExpression(Term initialTerm, boolean argumentsMustBeTyped, boolean insideLeftParen) throws ParsingException, IOException  {
		// Need to process something like "X is Y + Z / Q." where "X is" has been absorbed already.
		// When this is called, have encountered an left parenthesis or am starting a new in-fix expression.

		List<AllOfFOPC> accumulator = new ArrayList<AllOfFOPC>(4);
		boolean         lookingForTerm = true;
		if (initialTerm != null) {
			accumulator.add(initialTerm);  if (debugLevel > 2) { Utils.println("INIT processMathExpression.\n  processMathExpression('" + initialTerm + "'): accumulator = " + accumulator); }
			lookingForTerm = false;
		}
		while (true) {
			int tokenRead = getNextToken();
			if (debugLevel > 2) { Utils.println(" token read: '" + reportLastItemRead() + "'"); }
			if (processPossibleConnective(tokenRead) != null) {  // A logical connective (e.g., 'and') ends an "X is Y + Z, p(X), ..."

				if (debugLevel > 2) { Utils.println("   this token ('" + reportLastItemRead() + "') indicates the end of the math expression (so the accumulator should be compacted into one term)."); }
				if (insideLeftParen) { throw new ParsingException("Unexpectedly read '" + reportLastItemRead() + " when inside a left parenthesis in a 'X is ...' expressions."); }

				tokenizer.pushBack(); // Return the connective.
				return convertAccumulatorToTerm(accumulator);
			}
			switch (tokenRead) {
				case '(':
				case '{':
				case '[':
					Term resultLeftParens = processMathExpression(argumentsMustBeTyped, true); // Parse up the closing right parenthesis.
					accumulator.add(resultLeftParens);   if (debugLevel > 2) { Utils.println("  called processMathExpression('" + reportLastItemRead() + "') =  " + resultLeftParens + "', accumulator = " + accumulator); }
					if (!lookingForTerm) { throw new ParsingException("Encountered two terms in a row: '" + resultLeftParens + "'."); } // Could let this be implicit mulitplication?
					lookingForTerm = false;
					break;
				case ')':
				case '}':
				case ']':
					// These are ok since we now allow p(x/y).    if (!insideLeftParen) { throw new ParsingException("Read a right parenthesis unexpectedly."); }
					if (!insideLeftParen) { tokenizer.pushBack(); }
					if (debugLevel > 2) { Utils.println("   this closing-paren token ('" + reportLastItemRead() + "') indicates the current accumulator should be compressed into one token."); }
					return convertAccumulatorToTerm(accumulator);
				case '.':
				case ';':
					if (insideLeftParen) { throw new ParsingException("Read an EOL ('" + tokenRead + "') unexpectedly."); }
					tokenizer.pushBack();
					if (debugLevel > 2) { Utils.println("   this EOL token ('" + reportLastItemRead() + "') indicates the current accumulator should be compressed into one token."); }
					return convertAccumulatorToTerm(accumulator);
				case '+': // These are the only in-fix operators currently known to the system (other than 'is').
					if (accumulator.isEmpty()) { break; } // Discard any leading + signs.
				case '*':
				case '/':
				case '-':
					FunctionName fName = null;
					if (fName == null && checkAndConsume('*')) { fName = stringHandler.getFunctionName("**"); } // Exponentiation. (Check 'fName == null' here in case another IF is later added.)
					if (fName == null && checkAndConsume('@')) { fName = stringHandler.getFunctionName("/*"); } // Integer division (since '//' can't be used).
					if (fName == null) { fName = stringHandler.getFunctionName(String.valueOf((char) tokenRead)); }
					// OK if '-' is the first item.
					if (lookingForTerm && accumulator.size() > 0) { throw new ParsingException("Encountered two operators in a row: '" + reportLastItemRead() + "'."); }
					accumulator.add(fName);  if (debugLevel > 2) { Utils.println("  processMathExpression('" + reportLastItemRead() + "'): accumulator = " + accumulator); }
					lookingForTerm = true;
					break;
				case StreamTokenizer.TT_WORD:
					if (false && tokenizer.sval().equalsIgnoreCase("mod")) {  // JWS added the 'false' June 2011 because it isn't clear why MOD was treated specially (e.g., as opposed to MAX, etc).
						fName = stringHandler.getFunctionName(tokenizer.sval());
						if (lookingForTerm) { throw new ParsingException("Encountered two operators in a row: '" + reportLastItemRead() + "'."); }
						accumulator.add(fName);  if (debugLevel > 2) { Utils.println("  processMathExpression('" + reportLastItemRead() + "'): accumulator = " + accumulator); }
						lookingForTerm = true;
						break;
					}

					if (debugLevel > 2) { Utils.println("  will call processRestOfTerm('" + reportLastItemRead() + "'): accumulator = " + accumulator); }
					Term resultWord = processRestOfTerm(tokenRead, argumentsMustBeTyped, true);
					accumulator.add(resultWord);  if (debugLevel > 2) { Utils.println("  processMathExpression('" + reportLastItemRead() + "'): accumulator = " + accumulator); }
					if (!lookingForTerm) { throw new ParsingException("Encountered two terms in a row (missing comma?): '" + resultWord + "'.  Accumulator=" + accumulator); }
					lookingForTerm = false;
					break;
				default: throw new ParsingException("Read unexpected character when processing an 'X is ...' expression: '" + reportLastItemRead() + "'.");
			}
		}
	}

	/**
         * Have a list of the form: "( term operator term ... operator term )"
         * and have to use precedence rules to convert to a single term.
         * Algorithm: find the lowest precedence operator and combine it and its
         * two neighbors (break ties to the left). repeat until one term remains.
         *
         * @param accumulator
         * @return A term, the root of the abstract syntax tree created by
         *         parsing the given list.
         * @throws ParsingException
         */
	private Term convertAccumulatorToTerm(List<AllOfFOPC> accumulator) throws ParsingException, IOException {
		if (accumulator == null || accumulator.isEmpty()) { throw new ParsingException("Have an empty mathematical expression following an instance of 'X is ...'"); }
		while (accumulator.size() > 1) {
			if (debugLevel > 2) { Utils.println("  convertAccumulatorToTerm: " + accumulator); }
			//  First find the lowest-precedence operator.
			int lowestPrecedence  = Integer.MAX_VALUE;
			int countOfLowestItem = -1;
			int counter           =  0;
			for (AllOfFOPC item : accumulator) {
				if (item instanceof FunctionName) {
					int precedence = stringHandler.getOperatorPrecedence((FunctionName) item);

					if (precedence < lowestPrecedence) {
						lowestPrecedence  = precedence;
						countOfLowestItem = counter;
					}
				}
				counter++;
			}
			if (countOfLowestItem < 0) { Utils.error("Something went wrong when grouping the items in a mathematical expression: " + accumulator); }
			// Next combine the lowest-precedence operator and make a term with it and its two neighbors.
			FunctionName        fName    = (FunctionName) accumulator.get(countOfLowestItem);
			if (countOfLowestItem == 0 && fName == stringHandler.getFunctionName("-")) { // If '-' is the FIRST operator, need to handle it specially as an in-fix operator.
				Term            rightArg = (Term)         accumulator.get(countOfLowestItem + 1);
				List<Term>      args     = new ArrayList<Term>(1);
				args.add(rightArg);
				Function funct = stringHandler.getFunction(fName, args, null);
				accumulator.add(   countOfLowestItem + 2, funct); // Add after the two items combined.
				if (debugLevel > 2) { Utils.println("    ['-'] after adding  '" + funct + "' accumulator = " + accumulator); }
				AllOfFOPC removed1 = accumulator.remove(countOfLowestItem + 1); // Do this in the proper order so shifting doesn't mess up counting.
				AllOfFOPC removed2 = accumulator.remove(countOfLowestItem);
				if (debugLevel > 2) { Utils.println("    ['-'] after removing '" + removed1 + "' and '" + removed2 + "' accumulator = " + accumulator); }
			}
			else {
				if (countOfLowestItem < 1 || countOfLowestItem > accumulator.size() - 2) { Utils.error("Operators cannot be in the first or last positions: " + accumulator); }
				Term            leftArg  = (Term)         accumulator.get(countOfLowestItem - 1);
				Term            rightArg = (Term)         accumulator.get(countOfLowestItem + 1);
				List<Term>      args     = new ArrayList<Term>(2);
				args.add(leftArg);
				args.add(rightArg);
				Function funct = stringHandler.getFunction(fName, args, null);
				accumulator.add(   countOfLowestItem + 2, funct); // Add after the three items combined.
				if (debugLevel > 2) { Utils.println("          after adding  '" + funct + "' accumulator = " + accumulator); }
				AllOfFOPC removed1 = accumulator.remove(countOfLowestItem + 1); // Do this in the proper order so shifting doesn't mess up counting.
				AllOfFOPC removed2 = accumulator.remove(countOfLowestItem);
				AllOfFOPC removed3 = accumulator.remove(countOfLowestItem - 1);
				if (debugLevel > 2) { Utils.println("          after removing '" + removed1 + "', '" + removed2 + "' and '" + removed3 + "' accumulator = " + accumulator); }
			}
		}
		return (Term) accumulator.get(0);
	}

	private Sentence convertAccumulatorToFOPC(List<AllOfFOPC> accumulator) throws ParsingException, IOException {
		if (accumulator == null || accumulator.isEmpty()) {  // OK to have the empty sentence.
			if (warningCount < maxWarnings) { Utils.println("% PARSER WARNING #" + Utils.comma(++warningCount) + ": Read an empty sentence on line " + tokenizer.lineno() + "."); }
			return null;
		}
		while (accumulator.size() > 1) {
			if (debugLevel > 2) { Utils.println("  convertAccumulatorToFOPC: " + accumulator); }
			//  First find the lowest-precedence operator.
			int lowestPrecedence  = Integer.MAX_VALUE;
			int countOfLowestItem = -1;
			int counter           =  0;
			for (AllOfFOPC item : accumulator) {
				if (item instanceof ConnectiveName) {
					int precedence = stringHandler.getConnectivePrecedence((ConnectiveName) item);

					if (precedence <= lowestPrecedence) {
						lowestPrecedence = precedence;
						countOfLowestItem = counter;
					}
				}
				counter++;
			}
			if (countOfLowestItem < 0) { Utils.error("Something went wrong when grouping the items in a complex FOPC sentence: " + accumulator); }
			ConnectiveName  cName    = (ConnectiveName) accumulator.get(countOfLowestItem);
			if (ConnectiveName.isaNOT(cName.name)) { // If 'NOT' or '~' is the connective, need to handle it specially as an in-fix operator.
				Sentence rightArg = (Sentence)accumulator.get(countOfLowestItem + 1);
				Sentence cSent    = stringHandler.getConnectedSentence(cName, rightArg);
				if (cName.name.equalsIgnoreCase("\\+")) { cSent = processNegationByFailure((ConnectedSentence) cSent); }
				accumulator.add(   countOfLowestItem + 2, cSent); // Add after the two items being combined.
				accumulator.remove(countOfLowestItem + 1); // Do this in the proper order so shifting doesn't mess up counting.
				accumulator.remove(countOfLowestItem);
			}
			else { // Next combine the lowest-precedence operator and make a sentence with it and its two neighbors.
				if (countOfLowestItem < 1 || countOfLowestItem > accumulator.size() - 2) { Utils.error("Connectives cannot be in the first or last positions: " + accumulator); }
				Sentence leftArg  = (Sentence)accumulator.get(countOfLowestItem - 1);
				Sentence rightArg = (Sentence)accumulator.get(countOfLowestItem + 1);
				Sentence cSent    = stringHandler.getConnectedSentence(leftArg, cName, rightArg);
				if (cName.name.equalsIgnoreCase("then")) { cSent = processTHEN((ConnectedSentence) cSent); }
				accumulator.add(   countOfLowestItem + 2, cSent); // Add after the three items being combined.
				accumulator.remove(countOfLowestItem + 1); // Do this in the proper order so shifting doesn't mess up counting.
				accumulator.remove(countOfLowestItem);
				accumulator.remove(countOfLowestItem - 1);
			}
		}

		return (Sentence) accumulator.get(0);
	}

	private Literal processTHEN(ConnectedSentence connSent) throws ParsingException, IOException {
		// We need to treat the 'connective' THEN specially.  It is of the form 'P then Q else R' where P, Q, and R need to each convert to one clause.  E.g., (p, q then r, s else x, y, z).
		Sentence          sentenceLeft  = connSent.getSentenceA();
		Sentence          sentenceRight = connSent.getSentenceB();
		Clause            clauseP       = convertSimpleConjunctIntoClause(sentenceLeft, connSent);

		PredicateName pName  = stringHandler.standardPredicateNames.then;
		if (sentenceRight instanceof ConnectedSentence && ConnectiveName.isaOR(((ConnectedSentence) sentenceRight).getConnective().name)) {
			ConnectedSentence sentenceRightConnected = (ConnectedSentence) sentenceRight;
			Clause   clauseQ   = convertSimpleConjunctIntoClause(sentenceRightConnected.getSentenceA(), connSent);
			Clause   clauseR   = convertSimpleConjunctIntoClause(sentenceRightConnected.getSentenceB(), connSent);
			// 'P then Q else R' is implemented as 'dummy :- P, !, Q.' and 'dummy :- R' so create these two clause bodies here.
			clauseP.negLiterals.add(createCutLiteral());
			clauseP.negLiterals.addAll(clauseQ.negLiterals);
			clauseP.setBodyContainsCut(true);
			List<Term> args = new ArrayList<Term>(2);
			args.add(stringHandler.getSentenceAsTerm(clauseP, "thenInner"));
			args.add(stringHandler.getSentenceAsTerm(clauseR, "thenInner"));
			return   stringHandler.getLiteral(pName, args);
		}
		Clause clauseQ = convertSimpleConjunctIntoClause(sentenceRight, connSent);
		List<Term> args = new ArrayList<Term>(1);
		clauseP.negLiterals.add(createCutLiteral()); // No need to combine the posLiterals since there should not be any.
		clauseP.negLiterals.addAll(clauseQ.negLiterals);
		clauseP.setBodyContainsCut(true);
		args.add(stringHandler.getSentenceAsTerm(clauseP, "then"));
		return stringHandler.getLiteral(pName, args);
	}

	private Literal createCutLiteral() {
		PredicateName pName = stringHandler.standardPredicateNames.cut;
		return stringHandler.getLiteral(pName);
	}

	private Literal processNegationByFailure(ConnectedSentence connSent) throws ParsingException, IOException {
//		PredicateName pName  = stringHandler.standardPredicateNames.negationByFailure;
		Clause clause = convertSimpleConjunctIntoClause(connSent.getSentenceB(), connSent); // Remember that for unary 'connectives' the body is sentenceB.

        
        //		List<Term> args = new ArrayList<Term>(1);
//		args.add(stringHandler.getSentenceAsTerm(clause, "not"));
//		Literal result = stringHandler.getLiteral(pName, args);
//		if (debugLevel > 2) { Utils.println("% NEGATION-BY-FAILURE: result = '" + result + "' from connSent = '" + connSent + "' and clause = '" + clause + "'."); }
//		return result;

        return stringHandler.getNegationByFailure(clause);
	}

	private String isInfixTokenPredicate(int tokenRead) throws ParsingException {
		switch (tokenRead) {  // If changed, check out checkForPredicateNamesThatAreCharacters (for cases where a single-char string is returned).
		case '\\':
			if (checkAndConsume('=')) {
				if (checkAndConsume('=')) { return "\\=="; }
				return "\\=";
			}
			// if (peekThisChar('+')) { return "\\+"; }  / Allow this to be in-fix?
			return null;
		case '=': // By itself, '=' means unify (and '==' means 'equal').
			if (checkAndConsume('>')) {
				tokenizer.pushBack(); // This is a valid operator, albeit a logical connective.
				return null;
			}
			if (checkAndConsume('<')) {
				return "=<"; // This is Prolog's notation for "<=" (which apparently looks too much like an implication).
			}
            if (checkAndConsume('=')) {
				return "=="; // This is Prolog's notation for "==".
			}
			if (checkAndConsume(':')) {
				if (checkAndConsume('=')) { return "=:="; }
				tokenizer.pushBack(2); // Not sure what '=:' would be though ...
				return null;
			}
			if (checkAndConsume('\\')) {
				if (checkAndConsume('=')) { return "=\\="; }
				tokenizer.pushBack(2); // Not sure what '=\' would be though ...
				return null;
			}
			if (checkAndConsume('.')) {
				if (checkAndConsume('.')) { return "=.."; }
				tokenizer.pushBack();
				return "="; // The following period will cause a problem, but leave that for elsewhere.
			}

            return String.valueOf((char) tokenRead);
		case '<':
			if (tokenRead == '<' && (checkAndConsume('=') || checkAndConsume('-'))) {
				if (checkAndConsume('>')) {
					tokenizer.pushBack(2); // This is a valid operator, albeit a logical connective.
					return null;
				}
				tokenizer.pushBack(1);
			}
		case '>':
			if (checkAndConsume('=')) { return String.valueOf((char) tokenRead + "="); }
			return String.valueOf((char) tokenRead);
		case StreamTokenizer.TT_WORD:
			String tokenString = tokenizer.sval();
			if (tokenString.equalsIgnoreCase("is"))   { return "is";  }
			if (tokenString.equalsIgnoreCase("mod"))  { return "mod"; }
			return null;
		default: return null;	}
	}

	/*
	 * Record that a literal describes a 1D, 2D, or 3D interval.  Example:   isaInterval: ageInRange/3.
	 * The EOL ('.' or ';') is optional.
	 *
	 * In the simplest case, the boundaries for a 1D interval are the 1st and 3rd arguments, for 2D they are 1st, 3rd, 4th, and 6th, and for 3D they are 1st, 3rd, 4th, and 6th, 7th, and 9th.
	 *
	 * This can be overwritten by adding the keyword: boundariesAtEnd
	 * - in this case the last 2 (for 1D, last 4 for 2D and last 6 for 3D) are assumed to be the boundaries.
	 *
	 * Also if the number of arguments is not 3x the number of dimensions, then can use one of these keywords:
	 * 			1D
	 * 			2D
	 * 			3D
	 *
	 * @param tokenizer
	 * @throws ParsingException
	 */
	private void processISAInterval() throws ParsingException, IOException {
		// Have already read the 'isaInterval:"
		int tokenRead = checkForPredicateNamesThatAreCharacters(getNextToken());
		if (tokenRead == StreamTokenizer.TT_WORD) {
			String currentWord = tokenizer.sval();
			PredicateName pName = stringHandler.getPredicateName(currentWord);
			tokenRead = getNextToken();
			if (tokenRead != '/') { throw new ParsingException("Expecting a '/' (slash) in an isaInterval specification, but got: '" + reportLastItemRead() + "'."); }
			int arity = readInteger();
			int dimensions = arity / 3; // Integer division is the default.
			tokenRead = getNextToken();
			boolean boundariesAtEnd = false; // The default is the first and the last argument are the boundaries in the 1D case, and in 2D it is 1st, 3rd, 4th, and 6th, while in 3D it is 1st, 3rd, 4th, 6th,7th, and 9th.
			while (!atEOL()) {
				String nextTokenAsString = tokenizer.reportCurrentToken();
				if      (nextTokenAsString.equalsIgnoreCase("boundariesAtEnd")) { boundariesAtEnd = true; }
				else if (nextTokenAsString.equalsIgnoreCase("1D"))              { dimensions      = 1;    }  // If multiple specifications, simply take the last.
				else if (nextTokenAsString.equalsIgnoreCase("2D"))              { dimensions      = 2;    }
				else if (nextTokenAsString.equalsIgnoreCase("3D"))              { dimensions      = 3;    }
				tokenRead = getNextToken();
			}
			switch (dimensions) {
				case 1: pName.setIsaInterval_1D(arity, boundariesAtEnd); stringHandler.needPruner = true; break;
				case 2: pName.setIsaInterval_2D(arity, boundariesAtEnd); stringHandler.needPruner = true; break;
				case 3: pName.setIsaInterval_3D(arity, boundariesAtEnd); stringHandler.needPruner = true; break;
				default: throw new ParsingException("Can only handle 1, 2, or 3D interval specifications (which involve 3, 6, or 9 arguments, respectively), but have read arity =: '" + arity + ".");
			}
			if (debugLevel > 1) { Utils.println("isaInterval: " + pName + "/" + arity + "."); }
			return;
		}
		throw new ParsingException("Expecting the name of a predicate in an 'isaInterval' but read: '" + reportLastItemRead() + "'.");
	}

	// TODO - clean this up
	private int checkForPredicateNamesThatAreCharacters(int tokenRead) throws ParsingException, IOException {
		if (!isaPossibleTermName(tokenRead)) {
			String seeIfInfixPred = isInfixTokenPredicate(tokenRead);
			if (seeIfInfixPred == null) {
				throw new ParsingException("Expecting a predicate name but read: '" + reportLastItemRead() + "'.");
			}
			if ("=".equals(seeIfInfixPred)) {
				return tokenRead;
			}
			tokenizer.pushBack(seeIfInfixPred); // Hopefully no prevToken called here ...
			return getNextToken();
		}
		String seeIfPredNameUsingCharacters = getPredicateOrFunctionName(tokenRead);
		if (seeIfPredNameUsingCharacters != null) {
			if        ("-".equals(seeIfPredNameUsingCharacters)) {
				return tokenRead;
			} else if ("+".equals(seeIfPredNameUsingCharacters)) {
				return tokenRead;
			} else {
				tokenizer.pushBack(seeIfPredNameUsingCharacters); // Hopefully no prevToken called here ...
			}
			return getNextToken();
		}
		return tokenRead;
	}

	/**
	 * Process something like:  relevant: p/2, RELEVANT;
	 * These automatically create 'cost' statements as well.
	 * Read documentation above for all the isVariant supported.
	 *
	 * @throws ParsingException
	 */
	private void processRelevant(List<Sentence> listOfSentences) throws ParsingException, IOException {
		// Have already read the 'relevant:"
		Literal headLit = null;
		int tokenRead = getNextToken();
		if (tokenRead == '[') {
			tokenizer.pushBack();
			processRelevantAND(headLit, listOfSentences, false);
			return;
		}
		tokenRead = checkForPredicateNamesThatAreCharacters(tokenRead);

		if (tokenRead == StreamTokenizer.TT_WORD) {
			String currentWord = tokenizer.sval();

			if (currentWord.equalsIgnoreCase("head")) {
				headLit = readEqualsTypedLiteral();
				checkAndConsume(',');
				tokenRead = getNextToken();
				if (tokenRead == '[') {
					tokenizer.pushBack();
					processRelevantAND(headLit, listOfSentences, false);
					return;
				}
				tokenRead = checkForPredicateNamesThatAreCharacters(tokenRead);  // TODO clean up this duplicated code.
				if (tokenRead == StreamTokenizer.TT_WORD) {
					currentWord = tokenizer.sval();
				} else { throw new ParsingException("Expecting a string token but read " + reportLastItemRead() + "."); }
			}

			if (currentWord.equalsIgnoreCase("AND")) {
				expectAndConsume('(', null);
				processRelevantAND(headLit, listOfSentences, true);
				return;
			}
			if (currentWord.equalsIgnoreCase("OR")) {
				expectAndConsume('(', null);
				processRelevantOR(headLit, listOfSentences);
				return;
			}
			if (currentWord.equalsIgnoreCase("NOT")) {
				processRelevantNOT(headLit, listOfSentences);
				return;
			}
			if (headLit != null) { throw new ParsingException("A 'head' literal before a plain literal in a 'relevance' will be ignored: " + headLit); } // Could handle this if it seemed necessary.

			if (checkAndConsume('(')) { // Have a literal, rather than something like 'pred/2'
				tokenizer.pushBack();
				tokenizer.pushBack();
				processRelevantLiteral(listOfSentences);
				return;
			}
			if (checkAndConsume('/')) { // Have something like 'pred/2'
				processRelevantLiteralSpec(currentWord);
				return;
			}
			return;
		}

		throw new ParsingException("Expecting the name of a predicate in a 'relevant' but read: '" + reportLastItemRead() + "'.");
	}

	private void processSupporter() throws ParsingException, IOException {
		// Have already read the 'supportingLiteral:"
		int tokenRead = checkForPredicateNamesThatAreCharacters(getNextToken());
		if (tokenRead == StreamTokenizer.TT_WORD) {
			String currentWord = tokenizer.sval();
			PredicateName pName = stringHandler.getPredicateName(currentWord);
			tokenRead = getNextToken();
			if (tokenRead != '/') { throw new ParsingException("Expecting a '/' (slash) in an 'supportingLiteral' specification, but got: '" + reportLastItemRead() + "'."); }
			int arity = readInteger();


			if (debugLevel > 1) { Utils.println("supportingLiteral: " + pName + "/" + arity ); }
			pName.markAsSupportingPredicate(arity, false);
			return;
		}
		throw new ParsingException("Expecting the name of a predicate in a 'supportingLiteral' but read: '" + reportLastItemRead() + "'.");
	}

	private RelevanceStrength readRelevanceStrength() throws ParsingException, IOException {
		int    tokenRead;
		String currentWord;
		if (peekEOL(true)) {
			return RelevanceStrength.getDefaultRelevanceStrength();
		}
		checkAndConsume(','); // OK if there is a commas separating the items.
		tokenRead = getNextToken();

		if (tokenRead == '@') {  // A leading # indicates the value needs to be looked up in the list of set parameters.
			tokenRead       = getNextToken();
			String wordRead = tokenizer.sval();
			String setting  = stringHandler.getParameterSetting(wordRead);
			if (setting == null) { throw new ParsingException(" Read '@" + wordRead + "', but '" + wordRead + "' has not been set."); }
			//Utils.println("setting = " + setting);
			return RelevanceStrength.getRelevanceStrengthFromString(setting);
		}
		if (tokenRead == StreamTokenizer.TT_WORD) {
			currentWord = tokenizer.sval();
			if (currentWord.equalsIgnoreCase("max") || currentWord.equalsIgnoreCase("maxPerInputVars")) { // No relevance provided.  Use default.
				tokenizer.pushBack();
				return RelevanceStrength.getDefaultRelevanceStrength();
			}
			return RelevanceStrength.getRelevanceStrengthFromString(currentWord);
		}
		throw new ParsingException("Expecting a RelevanceStrength in a 'relevance:' but read: '" + reportLastItemRead() + "'.");
	}

	private List<Term> getArgumentsToAND(boolean needCloseParen) throws ParsingException, IOException {
		if ( checkAndConsumeToken("[")) { // Allow an implicit AND represented as a list of terms.
			if (needCloseParen) { throw new ParsingException("Should not need a closing parenthesis here."); }
			ConsCell list = processList(false, 1, false); // Should suck up the closing ']'.
			if (list == null)   { throw new ParsingException("Should not have list=null here."); }
			return list.convertConsCellToList();
		}
        else if(checkAndConsumeToken("(")) { // Allow an implicit AND represented as a list of terms.
			if (needCloseParen) { throw new ParsingException("Should not need a closing parenthesis here."); }
			ConsCell list = processList(false, 1, false); // Should suck up the closing ']'.
			if (list == null)   { throw new ParsingException("Should not have list=null here."); }
			return list.convertConsCellToList();
		}
        else if(needCloseParen) {
			return processListOfTerms('(', false).getTerms();
		}
        else {
            throw new ParsingException("Expecting a '['");
        }
	}
	// TODO - clean up common code in these four processRelevant*'s.
	private Literal processRelevantAND(Literal typedHeadLiteral, List<Sentence> listOfSentences, boolean needCloseParen) throws ParsingException, IOException {
        int        max              = Integer.MAX_VALUE;
        int        maxPerInputVars  = Integer.MAX_VALUE;
		boolean    autoNegate       = true;
        List<Term> bodyTerms        = getArgumentsToAND(needCloseParen);
		RelevanceStrength  strength = readRelevanceStrength();

		int tokenRead = (atEOL() ? 0 : getNextToken());
		while (!atEOL()) { // Have some optional arguments since not yet at EOL.
			String currentWord = tokenizer.reportCurrentToken();
			if (tokenRead == ',') {  } // OK if there are some commas separating the items.
			else if (currentWord.equalsIgnoreCase("max")) { // BUG: the user can't use 'max' nor 'maxPerInputVars' as target predicates.  TODO fix
				if (max < Integer.MAX_VALUE) { throw new ParsingException("Have already read max=" + max + " when processing a 'relevant' and have encountered 'max' again."); }
				max             = readEqualsInteger();
			} else if (currentWord.equalsIgnoreCase("maxPerInputVars")) {
				if (maxPerInputVars < Integer.MAX_VALUE) { throw new ParsingException("Have already read maxPerInputVars=" + max + " when processing a 'relevant' and have encountered 'maxPerInputVars' again."); }
				maxPerInputVars = readEqualsInteger();
			} else if (currentWord.equalsIgnoreCase("head")) {
				if (typedHeadLiteral != null) { throw new ParsingException("Have already read a head =" + typedHeadLiteral + " when processing a 'relevant' and have encountered another."); }
				typedHeadLiteral = readEqualsTypedLiteral();
			} else if (currentWord.equalsIgnoreCase("noAutoNegate")) { // Fine if this is read more than once.
				autoNegate = false;
			} else if (currentWord.equalsIgnoreCase("autoNegate"))   { // Fine if this is read more than once.
				autoNegate = true;
			}
			tokenRead = getNextToken();
        }
		if (strength != null && strength.isLessThanNeutral()) { autoNegate = false; }

		List<TypeSpec> typeSpecs    = new ArrayList<TypeSpec>(4);
		List<Term>     terms        = (typedHeadLiteral == null ? bodyTerms : typedHeadLiteral.getArguments());
		PredicateName  newPname     = (typedHeadLiteral == null ? stringHandler.getPredicateNameNumbered("anonymousAND_WI") : typedHeadLiteral.predicateName);
		if (typedHeadLiteral == null) {
			List<Variable> freeVars     = new ArrayList<Variable>(4);
			List<String>   freeVarNames = new ArrayList<String>(4);

			stringHandler.getTypedFreeVariablesAndUniquelyName(terms, null, freeVars, freeVarNames, typeSpecs, true);		// These will not maintain the World-State positions since the arguments names are probably not in the file being read.
			typedHeadLiteral = stringHandler.getLiteral(newPname, convertToListOfTerms(freeVars), freeVarNames).clearArgumentNamesInPlace(); // BUGGY if we want to keep argument names ...

			if (debugLevel > 1) { Utils.println("\n% line #" + tokenizer.lineno() + ", processRelevantAND: typedHeadLiteral = " + typedHeadLiteral + ", " + bodyTerms + "\n%    freeVars=" + freeVars + " specs=" + typeSpecs); }
		} else {
			typeSpecs = typedHeadLiteral.getTypeSpecs();
		}
		int   arity = typedHeadLiteral.numberArgs();
		Clause newC = stringHandler.getClause(typedHeadLiteral, true);

		newC.negLiterals = new ArrayList<Literal>(1);
		for (Term term : bodyTerms) {
			if        (term instanceof Function) {
				newC.negLiterals.add(( (Function) term).convertToLiteral(stringHandler));
			} else if (term instanceof StringConstant) { // Convert this to a zero-arity literal.
				newC.negLiterals.add( stringHandler.getLiteral( stringHandler.getPredicateName(( (StringConstant) term).getName())));
			} else { throw new Error("Cannot handle this term in processRelevantAND" + term); }
		}

		newPname.addInliner(arity);
		stringHandler.setRelevance(newPname, arity, strength);
		stringHandler.recordModeWithTypes(typedHeadLiteral, stringHandler.getConstantSignatureThisLong(arity), typeSpecs, max, maxPerInputVars);
		if (listOfSentences == null) { throw new ParsingException("Should not have an empty list!"); } // This holds the read-in clauses.  If reset here, the new list will be lost.
		listOfSentences.add(newC);
		stringHandler.resetAllVariables();
		if (debugLevel > 1) {
			Utils.println("\n% " + newC.toString(Integer.MAX_VALUE) + ". // Added to background knowledge (size = " + Utils.comma(listOfSentences) + ") by processRelevantAND.");
		}
		if (debugLevel > 1) {
			Utils.println("% inline:   " + newPname  + "/");
			Utils.println("% relevant: " + newPname  + "/" + arity + ", " + strength);
			Utils.print(  "% mode:     " + newPname  + "(");
			boolean addComma = false;
			for (TypeSpec ps : typeSpecs) { if (addComma) { Utils.print(", "); } else { addComma = true; } Utils.print(ps.toString()); }
			Utils.println(")");
		}
		if (autoNegate) {
			Literal nottypedHeadLiteral = createNegatedVersion(typedHeadLiteral);
			processRelevantNOT(listOfSentences, nottypedHeadLiteral, typedHeadLiteral, strength.getOneLowerStrengthAvoidingNegativeStrengths(), max, maxPerInputVars, false); // Prevent infinite loops.
		}
		return typedHeadLiteral;
	}
	private Literal processRelevantOR(Literal typedHeadLiteral, List<Sentence> listOfSentences) throws ParsingException, IOException {
        int        max              = Integer.MAX_VALUE;
        int        maxPerInputVars  = Integer.MAX_VALUE;
		boolean    autoNegate       = true;
        List<Term> bodyTerms        = processListOfTerms('(', false).getTerms();
		RelevanceStrength  strength = readRelevanceStrength();

		int tokenRead = (atEOL() ? 0 : getNextToken());
		while (!atEOL()) { // Have some optional arguments since not yet at EOL.
			String currentWord = tokenizer.reportCurrentToken();
			if (tokenRead == ',') {  } // OK if there are some commas separating the items.
			else if (currentWord.equalsIgnoreCase("max")) { // BUG: the user can't use 'max' nor 'maxPerInputVars' as target predicates.  TODO fix
				if (max < Integer.MAX_VALUE) { throw new ParsingException("Have already read max=" + max + " when processing a 'relevant' and have encountered 'max' again."); }
				max              = readEqualsInteger();
			} else if (currentWord.equalsIgnoreCase("maxPerInputVars")) {
				if (maxPerInputVars < Integer.MAX_VALUE) { throw new ParsingException("Have already read maxPerInputVars=" + max + " when processing a 'relevant' and have encountered 'maxPerInputVars' again."); }
				maxPerInputVars  = readEqualsInteger();
			} else if (currentWord.equalsIgnoreCase("head")) {
				if (typedHeadLiteral != null) { throw new ParsingException("Have already read a head =" + typedHeadLiteral + " when processing a 'relevant' and have encountered another."); }
				typedHeadLiteral = readEqualsTypedLiteral();
			} else if (currentWord.equalsIgnoreCase("noAutoNegate")) { // Fine if this is read more than once.
				autoNegate = false;
			} else if (currentWord.equalsIgnoreCase("autoNegate"))   { // Fine if this is read more than once.
				autoNegate = true;
			}
			tokenRead = getNextToken();
        }
		if (strength != null && strength.isLessThanNeutral()) { autoNegate = false; }

		boolean typedHeadLiteralWasNULL = (typedHeadLiteral == null);
		List<TypeSpec> typeSpecs    = new ArrayList<TypeSpec>(4);
        List<Term>     terms        = (typedHeadLiteralWasNULL ? bodyTerms : typedHeadLiteral.getArguments());
        PredicateName  newPname     = (typedHeadLiteralWasNULL? stringHandler.getPredicateNameNumbered("anonymousOR_WI") : typedHeadLiteral.predicateName);

        if (typedHeadLiteral == null) {
			List<Variable> freeVars     = new ArrayList<Variable>(4);
			List<String>   freeVarNames = new ArrayList<String>(4);

			stringHandler.getTypedFreeVariablesAndUniquelyName(terms, null, freeVars, freeVarNames, typeSpecs, true);		// These will not maintain the World-State positions since the arguments names are probably not in the file being read.
			typedHeadLiteral = stringHandler.getLiteral(newPname, convertToListOfTerms(freeVars), freeVarNames).clearArgumentNamesInPlace(); // BUGGY if we want to keep argument names ...

			if (debugLevel > 1) { Utils.println("\n% line #" + tokenizer.lineno() + ", processRelevantOR: typedHeadLiteral = " + typedHeadLiteral + ", " + bodyTerms + "\n%    freeVars=" + freeVars + " specs=" + typeSpecs); }
		} else {
			typeSpecs = typedHeadLiteral.getTypeSpecs();
		}
		int arity = typedHeadLiteral.numberArgs();

		// Create a P :- Q for each argument to the OR.  P is *not* an in-liner, due to the combinatorics involved.
		// If a term is a LIST such as [Q, R, S] then add P :- Q, R, S.
		// If a term is an AND(P, Q, R), treat the same as it being [Q, R, S].
		if (debugLevel > 1) { Utils.println(""); }
		for (Term term : bodyTerms) {
			Clause newC = stringHandler.getClause(typedHeadLiteral, true);
			newC.negLiterals = new ArrayList<Literal>(1);
			if        (Function.isaConsCell(term)) {
				List<Term> innerTerms = ((ConsCell) term).convertConsCellToList();
				for (Term inner : innerTerms) {
					newC.negLiterals.add(( (Function) inner).convertToLiteral(stringHandler));
				}
			} else if (term instanceof Function) {
				Function f = (Function) term;
				if (f.functionName == stringHandler.getFunctionName("AND")) {
					if (f.numberArgs() > 0) for (Term inner : f.getArguments()) {
						newC.negLiterals.add(( (Function) inner).convertToLiteral(stringHandler));
					}
				} else {
				newC.negLiterals.add(( (Function) term).convertToLiteral(stringHandler));
				}
			} else if (term instanceof StringConstant) { // Convert this to a zero-arity literal.
				newC.negLiterals.add( stringHandler.getLiteral( stringHandler.getPredicateName(( (StringConstant) term).getName())));
			} else { throw new Error("Cannot handle this term in processRelevantOR" + term); }
			if (listOfSentences == null) { throw new ParsingException("Should not have an empty list!"); }
			listOfSentences.add(newC); // This holds the read-in clauses.
			if (debugLevel > 1) {
				Utils.println("\n% " + newC.toString(Integer.MAX_VALUE) + ". // Added to background knowledge (size = " + Utils.comma(listOfSentences) + ") by processRelevantOR.");
			}
		}
		if (typedHeadLiteralWasNULL) { newPname.markAsSupportingPredicate(arity, false); } // This is NOT inlined, but it is supporting (i.e., it is not a clause-head that is in the BK; instead we generated it).  We need to keep disjuncts around in theories - flattening into clauses could otherwise lead to a combinatorial explosion.
		stringHandler.setRelevance(newPname, arity, strength);
		stringHandler.recordModeWithTypes(typedHeadLiteral, stringHandler.getConstantSignatureThisLong(arity), typeSpecs, max, maxPerInputVars);
		stringHandler.resetAllVariables();
		if (debugLevel > 1) {
			Utils.println( "% marked as a supporting literal: " + newPname + "/" + arity);
			Utils.println( "% relevant: " + newPname + "/" + arity + ", " + strength);
			Utils.print(   "% mode:     " + newPname + "(");
			boolean addComma = false;
			for (TypeSpec ps : typeSpecs) { if (addComma) { Utils.print(", "); } else { addComma = true; } Utils.print(ps.toString()); }
			Utils.println(")");
		}
		if (autoNegate) {
			Literal notTypedHeadLiteral = createNegatedVersion(typedHeadLiteral);
			processRelevantNOT(listOfSentences, notTypedHeadLiteral, typedHeadLiteral, strength.getOneLowerStrengthAvoidingNegativeStrengths(), max, maxPerInputVars, false); // Prevent infinite loops.
		}
		return typedHeadLiteral;
	}
	private Literal processRelevantNOT(Literal typedHeadLiteral, List<Sentence> listOfSentences) throws ParsingException, IOException {
        int        max              = Integer.MAX_VALUE;
        int        maxPerInputVars  = Integer.MAX_VALUE;
		boolean    autoNegate       = true;
		expectAndConsume('(', null);
		Literal innerLit = processLiteral(false);
		expectAndConsume(')', null);
		RelevanceStrength  strength = readRelevanceStrength();

		int tokenRead = (atEOL() ? 0 : getNextToken());
		while (!atEOL()) { // Have some optional arguments since not yet at EOL.
			String currentWord = tokenizer.reportCurrentToken();
			if (tokenRead == ',') {  } // OK if there are some commas separating the items.
			else if (currentWord.equalsIgnoreCase("max")) { // BUG: the user can't use 'max' nor 'maxPerInputVars' as target predicates.  TODO fix
				if (max < Integer.MAX_VALUE) { throw new ParsingException("Have already read max=" + max + " when processing a 'relevant' and have encountered 'max' again."); }
				max             = readEqualsInteger();
			} else if (currentWord.equalsIgnoreCase("maxPerInputVars")) {
				if (maxPerInputVars < Integer.MAX_VALUE) { throw new ParsingException("Have already read maxPerInputVars=" + max + " when processing a 'relevant' and have encountered 'maxPerInputVars' again."); }
				maxPerInputVars = readEqualsInteger();
			} else if (currentWord.equalsIgnoreCase("head")) {
				if (typedHeadLiteral != null) { throw new ParsingException("Have already read a head =" + typedHeadLiteral + " when processing a 'relevant' and have encountered another."); }
				typedHeadLiteral = readEqualsTypedLiteral();
			} else if (currentWord.equalsIgnoreCase("noAutoNegate")) { // Fine if this is read more than once.
				autoNegate = false;
			} else if (currentWord.equalsIgnoreCase("autoNegate"))   { // Fine if this is read more than once.
				autoNegate = true;
			} else { throw new Error("Cannot handle this in processRelevantNOT: " + currentWord); }
			tokenRead = getNextToken();
        }
		if (strength != null && strength.isLessThanNeutral()) { autoNegate = false; }
		return processRelevantNOT(listOfSentences, typedHeadLiteral, innerLit, strength, max, maxPerInputVars, autoNegate);
	}
	private Literal processRelevantNOT(List<Sentence> listOfSentences, Literal typedHeadLiteral, Literal innerLit, RelevanceStrength strength, int max, int maxPerInputVars, boolean createNegatedVersion) throws ParsingException, IOException {
		List<TypeSpec> typeSpecs         = new ArrayList<TypeSpec>(4);
		List<Term>     terms             = (typedHeadLiteral == null ? innerLit.getArguments() : typedHeadLiteral.getArguments());
		PredicateName  newPname          = (typedHeadLiteral == null ? stringHandler.getPredicateNameNumbered(will_notPred_prefix + innerLit.predicateName.name) : typedHeadLiteral.predicateName);

		if (typedHeadLiteral == null) {
			List<Variable> freeVars     = new ArrayList<Variable>(4);
			List<String>   freeVarNames = new ArrayList<String>(4);

			stringHandler.getTypedFreeVariablesAndUniquelyName(terms, null, freeVars, freeVarNames, typeSpecs, true);		// These will not maintain the World-State positions since the arguments names are probably not in the file being read.
			typedHeadLiteral = stringHandler.getLiteral(newPname, convertToListOfTerms(freeVars), freeVarNames).clearArgumentNamesInPlace(); // BUGGY if we want to keep argument names ...


			if (debugLevel > 1) { Utils.println("\n% line #" + tokenizer.lineno() + ": processRelevantNOT:  typedHeadLiteral = " + typedHeadLiteral + ", innerLit = " + innerLit + "\n%    freeVars=" + freeVars + " specs=" + typeSpecs); }
		} else {
			typeSpecs = typedHeadLiteral.getTypeSpecs();
		}
		int     arity = typedHeadLiteral.numberArgs();
		Clause  newC  = stringHandler.getClause(typedHeadLiteral, true);
		Literal notP  = stringHandler.wrapInNot(innerLit);

		newC.negLiterals = new ArrayList<Literal>(1);
		newC.negLiterals.add(notP);
		newPname.addInliner(arity);
		stringHandler.setRelevance(newPname, arity, strength);
		stringHandler.recordModeWithTypes(typedHeadLiteral, stringHandler.getConstantSignatureThisLong(arity), typeSpecs, max, maxPerInputVars);
		if (listOfSentences == null) { throw new ParsingException("Should not have an empty list!"); }
		listOfSentences.add(newC); // This holds the read-in clauses.
		if (debugLevel > 1) {
			Utils.println("\n% " + newC.toString(Integer.MAX_VALUE) + ". // Added to background knowledge (size = " + Utils.comma(listOfSentences) + ") by processRelevantNOT.");
		}
		stringHandler.resetAllVariables();
		if (debugLevel > 1) {
			Utils.println("% inline:   " + newPname + "/" + arity);
			Utils.println("% relevant: " + newPname + "/" + arity + ", " + strength);
			Utils.println("% mode:     " + newPname + "(" + newPname.getTypeList() + ")");
		}
		if (createNegatedVersion) { processRelevantLiteral(listOfSentences, innerLit, strength.getOneLowerStrengthAvoidingNegativeStrengths(), max, maxPerInputVars, false); } // Prevent infinite loops.
		return typedHeadLiteral;
	}

    private Literal processRelevantLiteral(List<Sentence> listOfSentences) throws ParsingException, IOException {
        int max = Integer.MAX_VALUE;
        int maxPerInputVars = Integer.MAX_VALUE;
        boolean autoNegate = true;
        Literal innerLit = processLiteral(true);    //Utils.println("%   processRelevantLiteral: innerLit = " + innerLit);
         //Utils.println("%   processRelevantLiteral: strength = " + strength);

        int tokenRead = (atEOL() ? 0 : getNextToken());
        String currentWord = tokenizer.reportCurrentToken();

        RelevanceStrength strength = readRelevanceStrength();
        while (!atEOL()) { // Have some optional arguments since not yet at EOL.
            currentWord = tokenizer.reportCurrentToken(); //Utils.println("%   processRelevantLiteral: currentWord = " + currentWord);
            if (tokenRead == ',') {
            } // OK if there are some commas separating the items.
            else if (currentWord.equalsIgnoreCase("max")) { // BUG: the user can't use 'max' nor 'maxPerInputVars' as target predicates.  TODO fix
                if (max < Integer.MAX_VALUE) {
                    throw new ParsingException("Have already read max=" + max + " when processing a mode and have encountered 'max' again.");
                }
                max = readEqualsInteger();
            }
            else if (currentWord.equalsIgnoreCase("maxPerInputVars")) {
                if (maxPerInputVars < Integer.MAX_VALUE) {
                    throw new ParsingException("Have already read maxPerInputVars=" + max + " when processing a mode and have encountered 'maxPerInputVars' again.");
                }
                maxPerInputVars = readEqualsInteger();
            }
            else if (currentWord.equalsIgnoreCase("noAutoNegate")) { // Fine if this is read more than once.
                autoNegate = false;
            }
            else if (currentWord.equalsIgnoreCase("autoNegate")) { // Fine if this is read more than once.
                autoNegate = true;
            }
            else {
                throw new Error("Cannot handle this in processRelevantLiteral: " + currentWord);
            }
            tokenRead = getNextToken();
        }
        if (strength != null && strength.isLessThanNeutral()) {
            autoNegate = false;
        }
        return processRelevantLiteral(listOfSentences, innerLit, strength, max, maxPerInputVars, autoNegate);


    }

	private Literal processRelevantLiteral(List<Sentence> listOfSentences, Literal innerLit, RelevanceStrength  strength, int max, int maxPerInputVars, boolean createNegatedVersion) throws ParsingException, IOException {
		int           arity = innerLit.numberArgs();
		PredicateName pName = innerLit.predicateName;

		stringHandler.setRelevance(pName, arity, strength);
		if (debugLevel > 1) { Utils.println("% relevant: " + pName + "/" + arity + ", " + strength); } // Utils.println("\n% line #" + tokenizer.lineno() + ": processRelevantLiteral: " + innerLit + "\n"); }

		if (createNegatedVersion) { processRelevantNOT(listOfSentences, null, innerLit, strength, max, maxPerInputVars, false); } // Prevent infinite loops.
		return innerLit;
	}
	private void processRelevantLiteralSpec(String predicateNameAsString) throws ParsingException, IOException {
		int               arity    = readInteger();
		RelevanceStrength strength = readRelevanceStrength();
		stringHandler.setRelevance(stringHandler.getPredicateName(predicateNameAsString), arity, strength);
		peekEOL(true); // These cannot have additional information since we don't have the arguments.
	}

    private void processLiteralAlias() throws ParsingException, IOException {
        Literal alias = processLiteral(true);

        expectAndConsumeToken("=>");

        Literal example = processLiteral(true);

        stringHandler.addLiteralAlias(alias, example);
    }

    /** Process a Relevant Clause statement.
     *
     * The relevantClause statement
     *
     * @param listOfSentences
     * @throws ParsingException
     * @throws IOException
     */
    private void processRelevantClause(List<Sentence> listOfSentences) throws ParsingException, IOException {

        Sentence relevantClause = null;

        Literal exampleLiteral;

        if ( checkAndConsumeToken("@") ) {
            exampleLiteral = processLiteral(true);
            exampleLiteral = stringHandler.lookupLiteralAlias(exampleLiteral);
        }
        else {
            exampleLiteral = processLiteral(true);
        }

        expectAndConsumeToken(":");

        if ( checkAndConsumeToken("[") ) {
            NamedTermList list = processListOfTerms('[', false);
            List<Literal> literals = convertTermsToLiterals(list.getTerms());

            relevantClause = stringHandler.getClause(literals, true);
        }
        else if(checkAndConsumeToken("(")) {
            NamedTermList list = processListOfTerms('(', false);
            List<Literal> literals = convertTermsToLiterals(list.getTerms());

            relevantClause = stringHandler.getClause(literals, true);
        }
        else {
            relevantClause = processLiteral(false);
        }

        expectAndConsumeToken(",");

        RelevanceStrength strength = readRelevanceStrength();

 //       System.out.println("Read Relevant Clause:");
//        System.out.println("  Example  = " + exampleLiteral + ".");
//        System.out.println("  Clause   = " + relevantClause + ".");
//        System.out.println("  Strength = " + strength + ".");

        Literal relevanceFact = stringHandler.getLiteral("relevant_clause", exampleLiteral.convertToFunction(stringHandler), stringHandler.getSentenceAsTerm(relevantClause, ""), stringHandler.getStringConstant(strength.name()));

        listOfSentences.add(relevanceFact);

    }

    private void processRelevantFeature(List<Sentence> listOfSentences) throws ParsingException, IOException {

        Literal exampleLiteral;

        if ( checkAndConsumeToken("@") ) {
            exampleLiteral = processLiteral(true);
            exampleLiteral = stringHandler.lookupLiteralAlias(exampleLiteral);
        }
        else {
            exampleLiteral = processLiteral(true);
        }

        //exampleLiteral = stringHandler.lookupLiteralAlias(exampleLiteral);

        expectAndConsumeToken(":");

        String predicateName = getNextString();
        expectAndConsumeToken("/");
        String arity = getNextString();

        expectAndConsumeToken(",");

        RelevanceStrength strength = readRelevanceStrength();

//        System.out.println("Read Relevant Feature:");
//        System.out.println("  Example  = " + exampleLiteral + ".");
//        System.out.println("  Feature  = " + predicateName + "/" + arity + ".");
//        System.out.println("  Strength = " + strength + ".");

        Literal relevanceFact = stringHandler.getLiteral("relevant_feature", exampleLiteral.convertToFunction(stringHandler), stringHandler.getStringConstant(predicateName + "/" + arity, false), stringHandler.getStringConstant(strength.name()));

        listOfSentences.add(relevanceFact);

    }

    private void processRelevantLiteralNew(List<Sentence> listOfSentences) throws ParsingException, IOException {

        Literal exampleLiteral;

        if ( checkAndConsumeToken("@") ) {
            exampleLiteral = processLiteral(true);
            exampleLiteral = stringHandler.lookupLiteralAlias(exampleLiteral);
        }
        else {
            exampleLiteral = processLiteral(true);
        }

        expectAndConsumeToken(":");

        Literal relevantLiteral = processLiteral(true);

        expectAndConsumeToken(",");

        RelevanceStrength strength = readRelevanceStrength();

        Literal relevanceFact = stringHandler.getLiteral("relevant_literal", exampleLiteral.convertToFunction(stringHandler), relevantLiteral.convertToFunction(stringHandler), stringHandler.getStringConstant(strength.name()));

        listOfSentences.add(relevanceFact);
    }

    private void processRelevantMode(List<Sentence> listOfSentences) throws ParsingException, IOException {

        Literal exampleLiteral;

        if ( checkAndConsumeToken("@") ) {
            exampleLiteral = processLiteral(true);
            exampleLiteral = stringHandler.lookupLiteralAlias(exampleLiteral);
        }
        else {
            exampleLiteral = processLiteral(true);
        }

        expectAndConsumeToken(":");

        Literal relevantLiteral = processLiteral(true);

        expectAndConsumeToken(",");

        RelevanceStrength strength = readRelevanceStrength();

        int maxModes = 3;
        if ( checkAndConsumeToken(",") ) {
            if ( checkAndConsumeToken("max")) {
                expectAndConsumeToken("=");
                maxModes = readInteger();
            }
        }

        Literal relevanceFact = stringHandler.getLiteral("relevant_mode", exampleLiteral.convertToFunction(stringHandler), relevantLiteral.convertToFunction(stringHandler), stringHandler.getStringConstant(strength.name()));

        listOfSentences.add(relevanceFact);
    }

    private void processNonOperational() throws IOException {
        PredicateNameAndArity pnaa = processPredicateNameAndArity();

        while( checkToken(".") == false && atEOL() == false) {
            checkAndConsumeToken(",");
            if ( checkAndConsumeToken("operational") ) {
                expectAndConsumeToken("=");
                PredicateName predicateName = processPredicateName();

                pnaa.getPredicateName().addOperationalExpansion(predicateName, pnaa.getArity());
            }
            else {
                throw new ParsingException("Error parsing nonOperational expression:  Unexpected toke '" + tokenizer.reportCurrentToken() +"'.");
            }
        }

    }

    private void processContainsCallables() throws IOException, ParsingException {
        PredicateNameAndArity pnaa = processPredicateNameAndArity();

        pnaa.setContainsCallable();
    }

    /** Returns true  if the next token is tokenToEval and consume it if it is.
     *
     * If the token doesn't match tokenToEval, the token isn't consumed.
     *
     * @param tokenToEval Token to look for.
     * @return True if next token = tokenToEval.  False otherwise.
     * @throws ParsingException
     * @throws IOException
     */
    private boolean checkAndConsumeToken(String tokenToEval) throws ParsingException, IOException {
        if (atEOL()) {
            return false;
        }

        int tokenRead = getNextToken();
        String currentWord = tokenizer.reportCurrentToken();

        if (currentWord.equals(tokenToEval)) {
            return true;
        }
        else {
            tokenizer.pushBack();
            return false;
        }
    }

    /** Returns true if the next token is tokenToEval but does not consume it.
     *
     *
     * @param tokenToEval Token to look for.
     * @return True if next token = tokenToEval.  False otherwise.
     * @throws ParsingException
     * @throws IOException
     */
    private boolean checkToken(String tokenToEval) throws ParsingException, IOException {
        if (atEOL()) {
            return false;
        }

        int tokenRead = getNextToken();
        String currentWord = tokenizer.reportCurrentToken();
        tokenizer.pushBack();

        if (currentWord.equals(tokenToEval)) {
            return true;
        }
        else {
            return false;
        }
    }

    /** Reads the next token,makes sure it is tokenToEval, and consumes it.
     *
     * @param tokenToEval Expected next token.
     * @throws ParsingException Thrown if the next token is not tokenToEval.
     * @throws IOException
     */
    private void expectAndConsumeToken(String tokenToEval) throws ParsingException, IOException {
        boolean done = false;
        while(done == false) {

        if ( atEOL()  ) throw new ParsingException("Unexpected end of file.  Expected '" + tokenToEval + "'." );

            int tokenRead = getNextToken();
            String currentWord = tokenizer.reportCurrentToken();

            if ( tokenToEval.startsWith(currentWord) == false) {
                throw new ParsingException("Unexpected token '" + currentWord + "'.  Expected '" + tokenToEval + "'." );
            }
            else if ( tokenToEval.length() != currentWord.length()) {
                tokenToEval = tokenToEval.substring(currentWord.length());
            }
            else {
                done = true;
            }
        }
    }


    private PredicateNameAndArity processPredicateNameAndArity() throws IOException {
        String predicateName = getPredicateOrFunctionName(tokenizer.nextToken());

        expectAndConsumeToken("/");

        int arity = (int)processNumber(tokenizer.nextToken());

        return new PredicateNameAndArity(stringHandler.getPredicateName(predicateName), arity);
    }

    private PredicateName processPredicateName() throws IOException {
        String predicateName = getPredicateOrFunctionName(tokenizer.nextToken());
        return stringHandler.getPredicateName(predicateName);
    }

	private Literal createNegatedVersion(Literal lit) {
		Literal result = lit.copy(false); // Do not want new variables here (or will need to match up to rest of clause).
		String candidateName = will_notPred_prefix + lit.predicateName.name;
		result.predicateName = stringHandler.getPredicateNameNumbered(candidateName); // Watch for name conflicts.
		if (!result.predicateName.name.equalsIgnoreCase(candidateName)) {
			Utils.warning("Needed to use '" + result.predicateName + "' because '" + candidateName + "' already existed.");
		}
		return result;
	}

	/**
	 * Process something like:  cost: p/2, 1.5;
	 * Such costs can be used when scoring clauses (default cost is 1.0).
	 * @throws ParsingException
	 */
	private void processCost(boolean isFinal) throws ParsingException, IOException {
		// Have already read the 'cost:"
		int tokenRead = checkForPredicateNamesThatAreCharacters(getNextToken());

		if (tokenRead == StreamTokenizer.TT_WORD) {
			String currentWord = tokenizer.sval();
			PredicateName pName = stringHandler.getPredicateName(currentWord);
			tokenRead = getNextToken();
			if (tokenRead != '/') { throw new ParsingException("Expecting a '/' (slash) in an 'cost' specification, but got: '" + reportLastItemRead() + "'."); }
			int arity = readInteger();

			checkAndConsume(','); // OK if there is a commas separating the items.

			tokenRead = getNextToken();
			double cost = processNumber(tokenRead);

			if (debugLevel > 1) { Utils.println("cost: " + pName + "/" + arity + ", " + cost); }
			pName.setCost(arity, cost, isFinal);
			return;
		}
		throw new ParsingException("Expecting the name of a predicate in a 'cost' but read: '" + reportLastItemRead() + "'.");
	}

	private void processDirective(String directiveName) throws ParsingException, IOException {
		// Have already read something like 'okIfUnknown:" (the colon isn't passed in).
		if (directiveName == null) { throw new ParsingException("Cannot pass in directiveName=null."); } // This is a programmer, rather than user, error.
		int tokenRead = checkForPredicateNamesThatAreCharacters(getNextToken());
		if (tokenRead == StreamTokenizer.TT_WORD) {
			String currentWord = tokenizer.sval();
			PredicateName pName = stringHandler.getPredicateName(currentWord);
			tokenRead = getNextToken();
			if (tokenRead != '/') { throw new ParsingException("Expecting a '/' (slash) in a '" + directiveName + "' specification, but got: '" + reportLastItemRead() + "'."); }
			if (checkAndConsume('#')) {
				if (debugLevel > 1) { Utils.println("Read that " + pName + " can be unknown for any number of arguments."); }
				if      (directiveName.equalsIgnoreCase("okIfUnknown"))                    { pName.setCanBeAbsent(-1); } // -1 means "any arity"
				else if (directiveName.equalsIgnoreCase("dontComplainAboutMultipleTypes")) { pName.setDontComplainAboutMultipleTypes(-1); }
				else { throw new ParsingException("Cannot process directiveName=" + directiveName+ "."); } // This is a programmer, rather than user, error.
			}
			else {
				int arity = readInteger();
				if (debugLevel > 1) { Utils.println("Read that " + pName + "/" + arity + " can be unknown."); }
				if (directiveName.equalsIgnoreCase("okIfUnknown"))                         { pName.setCanBeAbsent(arity); }
				else if (directiveName.equalsIgnoreCase("dontComplainAboutMultipleTypes")) { pName.setDontComplainAboutMultipleTypes(arity); }
				else { throw new ParsingException("Cannot process directiveName=" + directiveName+ "."); } // This is a programmer, rather than user, error.
			}
			peekEOL(true);
			return;
		}
		throw new ParsingException("Expecting the name of a predicate in a '" + directiveName + "' but read: '" + reportLastItemRead() + "'.");
	}

	/**
         * Process the specification of a Horn ('definite' actually) clause that
         * should be precomputed. For example: precompute: p(x) :- q(x, y), r(y).
         *
         * @param index
         * @throws ParsingException
         */
	private void processPrecompute(int index) throws ParsingException, IOException {
		String fileNameToUse;
		int tokenRead = getNextToken();
		String currentWord = tokenizer.reportCurrentToken();
		
		boolean usingDefaultName = false;
		if ("fileName".equalsIgnoreCase(currentWord)) {
			tokenRead = getNextToken();			
			if (tokenRead != '=') { throw new ParsingException("Expecting an '=' but got: " + reportLastItemRead() + "."); }
			tokenRead = getNextToken();
			boolean quoted = atQuotedString(tokenRead);

			if (tokenRead == StreamTokenizer.TT_WORD || quoted) {
				fileNameToUse = (quoted ? tokenizer.svalQuoted() : tokenizer.sval());
				if (!quoted && checkAndConsume('.')) { // See if there is an extension.
					int lineNumber = tokenizer.lineno();
					tokenRead = getNextToken(false); // How do we distinguish if there is an '.' as a EOL or if it is a delimiter in a file name?  Use the line number as a hack?
					if (tokenRead == StreamTokenizer.TT_EOF || lineNumber != tokenizer.lineno()) {	 // Done.
						throw new ParsingException("Expecting the file name of a file in which to place the precomputed results, but reached EOF.");
					}
					if (tokenRead != StreamTokenizer.TT_WORD) {
						tokenizer.pushBack(2); // The period is apparently an (logical) EOL since something that isn't text follows.
					} else { fileNameToUse += "." + tokenizer.sval(); }
				}
			} else {
				throw new ParsingException("Expecting the file name of a file in which to place the precomputed results, but read:\n '" + reportLastItemRead() + "'.");
			}
			checkAndConsume(','); // Allow an optional comma.
		} else {
			tokenizer.pushBack(1);
			fileNameToUse = "precomputed" + (index > 0 ? index : "");
			usingDefaultName = true;
		}
		
		Sentence sentenceToPrecompute = processFOPC_sentence(0);
		if (sentencesToPrecompute == null) { initializeSentencesToPrecompute(); }
		sentencesToPrecompute[index].add(sentenceToPrecompute);
		setFileNameForSentencesToPrecompute(index, fileNameToUse, usingDefaultName);
		if (debugLevel > 1) { Utils.println("% precompute" + (index > 0 ? index : "") + ": " + sentenceToPrecompute + "\n%  Will be written to: " + fileNameToUse); }
	}

	@SuppressWarnings("unchecked")
	private void initializeSentencesToPrecompute() {
		sentencesToPrecompute = (List<Sentence>[]) new List<?>[getNumberOfPrecomputeFiles()];
		sentencesToPrecomputeFileNameToUse = new String[getNumberOfPrecomputeFiles()];
		for (int i = 0; i < getNumberOfPrecomputeFiles(); i++) { sentencesToPrecompute[i] = new ArrayList<Sentence>(4); sentencesToPrecomputeFileNameToUse[i] = null; }
	}

	/**
	 *  prune: prunableLiteral,    // If a literal that unifies with 'ifPresentLiteral' is in already in a clause being learned,
	 *         ifPresentLiteral,   // do not add something that also unifies with 'prunableLiteral' - the commas and the final '.' (or ';') are optional.
	 *         [warnIf(N)]         // The optional third argument says to complain if there are N or more existing rules whose head unifies with 'ifPresentLiteral' since this pruning is based on the assumption that less than N such rules exist (i.e., the 'precompute:' facility assumes N=1).
	 *
	 * @throws ParsingException
	 */
	private void processPrune(boolean isaVariant, int truthValue) throws ParsingException, IOException {  // TruthValue: -1 means 'prune because false', 1 means because true, and 0 means unknown.
		Literal prunableLiteral  = processLiteral(false);
		String commaOne = " ";
		if (checkAndConsume(',')) { commaOne = ", "; } // Commas are optional.
		if (peekEOL(false)) { // Have something like "prune: f(x,x)."
			if (isaVariant) { throw new ParsingException("Cannot have items of the form: isaVariant: f(x)."); }
			prunableLiteral.predicateName.recordPrune(prunableLiteral,  null, -1, truthValue);
			return;
		}
		Literal ifPresentLiteral = processLiteral(false);
		if (isaVariant) {
			stringHandler.needPruner = true;
			prunableLiteral.predicateName.recordPrune(    prunableLiteral,  ifPresentLiteral, 1, truthValue);
			ifPresentLiteral.predicateName.recordPrune(   ifPresentLiteral, prunableLiteral,  1, truthValue);
			prunableLiteral.predicateName.recordVariants( prunableLiteral,  ifPresentLiteral, stringHandler);
			ifPresentLiteral.predicateName.recordVariants(ifPresentLiteral, prunableLiteral,  stringHandler);
		} else {
			String commaTwo = " ";
			if (checkAndConsume(',')) { commaTwo = ", "; } // Commas are optional.
			if (!commaTwo.equalsIgnoreCase(" ") || !peekEOL(true)) {
				Literal warnLiteral = processLiteral(false);
				if (warnLiteral != null && warnLiteral.predicateName == stringHandler.getPredicateName("warnIf") && warnLiteral.numberArgs() == 1) {
					  // Utils.println("%   TODO   Process 'prune: " + prunableLiteral + commaOne + ifPresentLiteral + commaTwo + warnLiteral + "'.");
					  Term term = warnLiteral.getArgument(0);
					  if (term instanceof NumericConstant) {
						  int n = ((NumericConstant) term).value.intValue(); // Use the integer value regardless (enough thrown exceptions already ...).
						  stringHandler.needPruner = true;
						  prunableLiteral.predicateName.recordPrune(prunableLiteral, ifPresentLiteral, n, truthValue);
					  }
					  else { throw new ParsingException("Read '" + warnLiteral + "' after 'prune: " + prunableLiteral + commaOne + ifPresentLiteral + commaTwo + "' and was expecting that the argument to 'warnIf(N)' be a number."); }
				}
				else { throw new ParsingException("Read '" + warnLiteral + "' after 'prune: " + prunableLiteral + commaOne + ifPresentLiteral + commaTwo + "' and was expecting 'warnIf(N)'."); }
				peekEOL(true);
			}
			else {
				stringHandler.needPruner = true;
				prunableLiteral.predicateName.recordPrune(prunableLiteral, ifPresentLiteral, Integer.MAX_VALUE, truthValue);
			}
		}
	}

	@SuppressWarnings("fallthrough")
	private Sentence processWeight(int followingChar) throws ParsingException, IOException {
		boolean openParens = false;
		Sentence sentence;
		switch (followingChar) {
			case '(':
			case '{':
			case '[':
				openParens = true;
			case ':':
			case '=':
				double   wgt      = readWeight();
				if (openParens) {
					int nextToken = getNextToken();
					if (nextToken != ')' && nextToken != '}' && nextToken != ']') { // If the parenthesis isn't closed, assume of the form: '(wgt FOPC)'
						checkAndConsume(',');  // A comma after the number is optional.
						sentence = processFOPC_sentence(1);
					}
					else {
						checkAndConsume(',');
						sentence = processFOPC_sentence(0);
					}
				}
				else {
					    checkAndConsume(',');
					    sentence = processFOPC_sentence(0);
				}
				sentence.setWeightOnSentence(wgt);
				return sentence;
			default: throw new ParsingException("After 'weight' or 'wgt' expected one of {':', '=', '(', '{'} but read: '" + reportLastItemRead() + "'.");
		}
	}

	private double readWeight() throws ParsingException, IOException {
		int tokenRead = getNextToken();
		double result = processNumber(tokenRead);
		if (Utils.isaNumber(result)) { // If here, cannot read as an integer (nor as a double).
			return result;
		}
		throw new ParsingException("Was trying to read a number but failed on: '" + reportLastItemRead() + "'.");
	}

	private boolean atInfinity() {
		String currentWord = tokenizer.reportCurrentToken();
		boolean result = (currentWord.equalsIgnoreCase("inf") || currentWord.equalsIgnoreCase("infinity"));
				
		if (result && checkAndConsume('(')) { // Allow inf() to be a predicate.
			if (debugLevel > 1 && result) { Utils.println("pushing back the infinity because an open paren is next."); }
			tokenizer.pushBack();
			return false;
		}
		return result;
	}

	private double processNumber(int tokenRead) throws ParsingException, IOException {
		if (debugLevel > 1) { Utils.println("processNumber: " + reportLastItemRead()  + "  [tokenRead = " + tokenRead + ", " + StreamTokenizer.TT_WORD + "]"); } 
		int countOfBackupsNeeded = 0;
		int negate               = 1;
		if (tokenRead == '@') {  // A leading @ indicates the value needs to be looked up in the list of set parameters.
			tokenRead       = getNextToken();
			String wordRead = tokenizer.sval();
			String setting  = stringHandler.getParameterSetting(wordRead);
			if (setting     == null) { throw new ParsingException(" Read '@" + wordRead + "', but '" + wordRead + "' has not been set."); }
			Double setToDouble = Double.parseDouble(setting);
			if (setToDouble == null) { throw new ParsingException(" Read '@" + wordRead + "', but '" + wordRead + "' has been set to '" + setting + "', rather than a number."); }
			return setToDouble;
		} else if (tokenRead == '-')  { // Have a minus sign.
			negate    = -1; if (debugLevel > -1) { Utils.println("processNumber: have a '-'"); } // xxx
			countOfBackupsNeeded++;
			tokenRead = getNextToken();
			if (atInfinity()) { return Double.NEGATIVE_INFINITY; }
		} else if (tokenRead == '+')  { // Allow a plus sign.
			if (debugLevel > 1) { Utils.println("processNumber: have a '+'"); }
			countOfBackupsNeeded++;
			tokenRead = getNextToken();
			if (atInfinity()) { return Double.POSITIVE_INFINITY; }
		}

		if (tokenizer.ttype() != StreamTokenizer.TT_WORD) {
			if (debugLevel > 1) { Utils.println("processNumber: do not have a number"); }
			tokenizer.pushBack(countOfBackupsNeeded); // Return to where the processNumber() started.
			return Double.NaN;
		}

		String wordRead = tokenizer.sval();
		if (atInfinity()) { return Double.POSITIVE_INFINITY; }
		Long integerConstant = null;
        char firstCharacter = wordRead.charAt(0);
        if ( firstCharacter >= '0' && firstCharacter <= '9') {
            try {  // See if the word read can be viewed as an integer.
                integerConstant = Long.valueOf(wordRead);  // Notice: due to bug mentioned above, we need to handle decimal points ourselves.
                countOfBackupsNeeded = 0; // If integer read w/o problem, then the reads above were fine.
                if (checkAndConsume('.')) {
                    countOfBackupsNeeded++; // For the decimal point.
                    countOfBackupsNeeded++;
                    int nextToken = getNextToken(); // If so, look at the next word.
                    if (nextToken != StreamTokenizer.TT_WORD) { throw new ParsingException("Period is not decimal point."); }
                    String wordRead2 = tokenizer.sval();
                    try {
                        String wordRead3 = "";
                        char lastChar  = wordRead2.charAt(wordRead2.length() - 1);
                        if (lastChar == 'e' || lastChar == 'E') { // If last character is 'e' or 'E' then maybe have scientific notation.
                            countOfBackupsNeeded++;
                            nextToken = getNextToken();
                            switch (nextToken) {
                                case '+':
                                    countOfBackupsNeeded++;
                                    nextToken = getNextToken();
                                    if (nextToken != StreamTokenizer.TT_WORD) { tokenizer.pushBack(countOfBackupsNeeded); throw new ParsingException("Period is not decimal point."); }
                                    wordRead3 = "+" + tokenizer.sval(); break; // Could leave out the "+" but leave it in since the user did ...
                                case '-':
                                    countOfBackupsNeeded++;
                                    nextToken = getNextToken();
                                    if (nextToken != StreamTokenizer.TT_WORD) { tokenizer.pushBack(countOfBackupsNeeded); throw new ParsingException("Period is not decimal point."); }
                                    wordRead3 = "-" + tokenizer.sval(); break;
                                default: throw new NumberFormatException(); // If of the form '2e3' will read all in one fell swoop, so only need to deal with '+' or '-' being "token breakers."
                            }
                        }
                        String doubleAsString = wordRead + "." + wordRead2 + wordRead3;
                        return negate * Double.parseDouble(doubleAsString);
                    }
                    catch (NumberFormatException e) {
                        tokenizer.pushBack(countOfBackupsNeeded); // Push back the word after the decimal point and return the decimal point.
                        return negate * integerConstant; // Then simply return the integer read.
                    }
                }
                return negate * integerConstant;
            }
            catch (NumberFormatException e) { // If here, cannot read as an integer (nor as a double).
                tokenizer.pushBack(countOfBackupsNeeded); // Return to where the processNumber() started.
                return Double.NaN;
            }
            catch (IOException e) { // Tried to read a '.' as a decimal point, whereas it is an EOL followed by an EOF.
                if (e.getMessage().startsWith("Unexpected EOF")) {
                    tokenizer.pushBack(countOfBackupsNeeded); // Push back the EOF.
                    return negate * integerConstant;
                }
                throw new ParsingException("Unexpectedly reached an I/O exception: " + e.getMessage());
            }
            catch (Exception e) { // Tried to read a '.' as a decimal point, whereas it is an EOL.
                if (e.getMessage().startsWith("Period is not decimal point")) {
                    tokenizer.pushBack(countOfBackupsNeeded); // Push back the decimal point, which is an EOL here.  Needed to read PAST the decimal point to make this decision, so need to return TWO tokens here.
                    return negate * integerConstant;
                }
                throw new ParsingException("Unexpected exception dealing with a period: " + e.getMessage());
            }
        }
		tokenizer.pushBack(countOfBackupsNeeded); // Return to where the processNumber() started.
		return Double.NaN;
	}

	private Set<String> loadedLibraries = new HashSet<String>(4);
	public List<Sentence> loadAllLibraries() throws ParsingException {
		String[] knownLibraries = { "arithmeticInLogic", "comparisonInLogic", "differentInLogic", "listsInLogic" };

		boolean hold_cleanFunctionAndPredicateNames = stringHandler.cleanFunctionAndPredicateNames;
		stringHandler.cleanFunctionAndPredicateNames = false;
		Utils.println(PARSER_VERBOSE_LIBRARY_LOADING, "% LoadAllLibraries() called.  Currently loaded libraries: " + Utils.limitLengthOfPrintedList(loadedLibraries, 25));
		List<Sentence> results = null;
		for (String library : knownLibraries) if (!loadedLibraries.contains(library)) {
			if (results == null) { results = new ArrayList<Sentence>(4); }
			try {
				List<Sentence> allLibrarySentences = loadThisFile(true, library, false);
				if (allLibrarySentences != null) { results.addAll(allLibrarySentences); }
			} catch (Exception e) {
				Utils.reportStackTrace(e);
				throw new ParsingException("Problem encountered reading built-in library: '" + library + "'.");
			}
		}
		stringHandler.cleanFunctionAndPredicateNames = hold_cleanFunctionAndPredicateNames;
		return results;
	}

	private Set<String> loadedBasicModes = new HashSet<String>(4);
	public List<Sentence> loadAllBasicModes() throws ParsingException {
		String[] knownBasicModes = { "modes_arithmeticInLogic", "modes_comparisonInLogic", "modes_differentInLogic", "modes_listsInLogic" };

		boolean hold_cleanFunctionAndPredicateNames = stringHandler.cleanFunctionAndPredicateNames;
		stringHandler.cleanFunctionAndPredicateNames = false;
		Utils.println(PARSER_VERBOSE_MODE_LOADING, "% LoadAllModes() called.  Currently loaded modes: " + Utils.limitLengthOfPrintedList(loadedBasicModes, 25));
		List<Sentence> results = null;
		for (String library : knownBasicModes) if (!loadedBasicModes.contains(library)) {
			if (results == null) { results = new ArrayList<Sentence>(4); }
			try {
				List<Sentence> allLibrarySentences = loadThisFile(true, library, false);
				if (allLibrarySentences != null) { results.addAll(allLibrarySentences); }
			} catch (Exception e) {
				Utils.reportStackTrace(e);
				throw new ParsingException("Problem encountered reading built-in library: '" + library + "'.");
			}
		}
		stringHandler.cleanFunctionAndPredicateNames = hold_cleanFunctionAndPredicateNames;
		return results;
	}

	private List<Sentence> loadThisLibrary(FileParser newParser, String libName) throws ParsingException, IOException {
		if (loadedLibraries.contains(libName)) { return null; } // Already loaded.
		List<Sentence> result = null;
		loadedLibraries.add(libName);  // TODO - should we store URLs instead?
		URL libraryURL = getClass().getResource("/edu/wisc/cs/will/FOPC_MLN_ILP_Parser/" + libName + ".fopcLibrary");
		if (libraryURL == null) { throw new ParsingException("Unknown library: " + libName); }
		InputStream inStream  = new NamedInputStream(new BufferedInputStream(libraryURL.openStream()), libName + ".fopcLibrary");
		if (!dontPrintUnlessImportant) { Utils.println(PARSER_VERBOSE_LIBRARY_LOADING, "% Reading library '" + libName + "'."); } //Utils.waitHere("libs: " + loadedLibraries);
		result = newParser.readFOPCstream(null, inStream);
		inStream.close();
		return result;
	}

	/**
         * Parse the file named after this 'import:' directive. For example:
         * import: text. The EOL ('.' or ';') at the end is optional.
         *
         * @return A list of sentences, the content of the imported file.
         * @throws ParsingException
         */
	private List<Sentence> processAnotherFile(boolean isaLibraryFile, boolean complainIfFileDoesNotExist) throws ParsingException, IOException {
		// Have already read the "import:" or "importLibrary:"
		int     nextToken = getNextToken();
		boolean quoted    = atQuotedString(nextToken);
		if (nextToken == StreamTokenizer.TT_WORD || quoted) {
			String newFileName = (quoted ? tokenizer.svalQuoted() : tokenizer.sval());
			if (!quoted && checkAndConsume('.')) { // See if there is an extension.
				int lineNumber = tokenizer.lineno();
				nextToken = getNextToken(true); // How do we distinguish if there is an '.' as a EOL or if it is a delimiter in a file name?  Use the line number as a hack?
				if (nextToken != StreamTokenizer.TT_EOF) { // If EOF, all done.
					if (lineNumber != tokenizer.lineno()) {
						tokenizer.pushBack(); // The period is apparently an (logical) EOL since something that isn't text follows.  Pushback that something.
					} else { newFileName += "." + tokenizer.sval(); }
				}
			}
						
			if (!dontPrintUnlessImportant) { Utils.println(PARSER_VERBOSE_FILE_INCLUDES, "% ProcessAnotherFile: directoryName = " + directoryName + "\n%   fileName = " + newFileName); }			
			
			if (newFileName.charAt(0) == '@') { newFileName = stringHandler.getParameterSetting(newFileName.substring(1)); }
			newFileName = Utils.replaceWildCards(
					       newFileName.replace("IMPORT_VAR1", Utils.removeAnyOuterQuotes(stringHandler.import_assignmentToTempVar1)));
			newFileName =  newFileName.replace("IMPORT_VAR2", Utils.removeAnyOuterQuotes(stringHandler.import_assignmentToTempVar2));
			newFileName =  newFileName.replace("IMPORT_VAR3", Utils.removeAnyOuterQuotes(stringHandler.import_assignmentToTempVar3));
			newFileName =  newFileName.replace("FACTS",       Utils.removeAnyOuterQuotes(stringHandler.FACTS));
			newFileName =  newFileName.replace("PRECOMP",     Utils.removeAnyOuterQuotes(stringHandler.PRECOMP));
			newFileName =  newFileName.replace("SWD",         Utils.removeAnyOuterQuotes(stringHandler.SWD));
			newFileName =  newFileName.replace("TASK",        Utils.removeAnyOuterQuotes(stringHandler.TASK));
			
			if (!isaLibraryFile && !newFileName.contains(".")) { newFileName += stringHandler.precompute_file_postfix; } //only add extension _after_ doing substitutions
			
			List<Sentence> results = loadThisFile(isaLibraryFile, newFileName, !complainIfFileDoesNotExist);
			if (!dontPrintUnlessImportant && (directoryName != null || fileName != null)) { Utils.println(MessageType.PARSER_VERBOSE_FILE_INCLUDES,"\n% Returning to reading: dir = " + directoryName + ", file = " + fileName + "\n"); }
			return results;
		}
		throw new ParsingException("Expecting the file name of a file to import, but read: '" + reportLastItemRead() + "'.");
	}
	
	public void checkForDefinedImportAndPrecomputeVars(String parameterName) {	// Simply check them all.  TODO - clean up.	
		// Precomputes  NOTE: all the parameters checked here must contain "precompute" or "import" or they wont be reached.
		String vStr;
		vStr = stringHandler.getParameterSetting("precomputePrefix");
		if (vStr != null) {                       stringHandler.precompute_file_prefix  = vStr; }
		vStr = stringHandler.getParameterSetting("precomputePostfix");
		if (vStr != null) {                       stringHandler.precompute_file_postfix = vStr; }
		vStr = stringHandler.getParameterSetting("numberOf_precomputes"); // Need this to match: contains("precompute")
		if (vStr != null) {                       setNumberOfPrecomputeFiles(Integer.parseInt(vStr)); }
		vStr = stringHandler.getParameterSetting("precomputeVar1"); // Will replace instances of PRECOMPUTE_VAR1 in files names for precompute outputs.
		if (vStr != null) {                       stringHandler.precompute_assignmentToTempVar1 = Matcher.quoteReplacement(vStr); }
		vStr = stringHandler.getParameterSetting("precomputeVar2");
		if (vStr != null) {                       stringHandler.precompute_assignmentToTempVar2 = Matcher.quoteReplacement(vStr); }
		vStr = stringHandler.getParameterSetting("precomputeVar3");
		if (vStr != null) {                       stringHandler.precompute_assignmentToTempVar3 = Matcher.quoteReplacement(vStr); }	

		// Imports
		vStr = stringHandler.getParameterSetting("importPrefix");
		if (vStr != null) {                       stringHandler.import_file_prefix  = vStr; }
		vStr = stringHandler.getParameterSetting("importPostfix");
		if (vStr != null) {                       stringHandler.import_file_postfix = vStr; }
		vStr = stringHandler.getParameterSetting("importVar1"); // Will replace instances of IMPORT_VAR1 in files names for imported files.
		if (vStr != null) {                       stringHandler.import_assignmentToTempVar1 = Matcher.quoteReplacement(vStr); }
		vStr = stringHandler.getParameterSetting("importVar2");
		if (vStr != null) {                       stringHandler.import_assignmentToTempVar2 = Matcher.quoteReplacement(vStr); }
		vStr = stringHandler.getParameterSetting("importVar3");
		if (vStr != null) {                       stringHandler.import_assignmentToTempVar3 = Matcher.quoteReplacement(vStr); }
		
	}

	public List<Sentence> loadThisFile(boolean isaLibraryFile, String newFileNameRaw, Boolean okIfFileDoesntExist) throws ParsingException, IOException {
		String   newFileName = Utils.replaceWildCards(newFileNameRaw);
		FileParser newParser = new FileParser(stringHandler); // Needs to use the same string handler.
		newParser.dontPrintUnlessImportant = dontPrintUnlessImportant;
		if (loadedLibraries != null) { newParser.loadedLibraries.addAll(loadedLibraries); } // Need to know what was already loaded.
        if ( isaLibraryFile ) {
            if ( Utils.isMessageTypeEnabled(PARSER_VERBOSE_LIBRARY_LOADING) || stringHandler.haveLoadedThisFile(newFileName, false) == false ) {
            	if (!dontPrintUnlessImportant) { Utils.println("% Load library file '" + newFileName + "'."); }
            }
        }
        else {
            Utils.println(PARSER_VERBOSE_MODE_LOADING, "% Load '" + newFileName + "'.");
        }
		//if (tokenizer != null) { peekEOL(true); }
		//Utils.println("DEBUGGING: dir = " + directoryName);
		List<Sentence> result = null;
		if (isaLibraryFile) {
			// Don't load a file more than once.
			if (stringHandler.haveLoadedThisFile(newFileName, true)) {
				if (debugLevel > 1) { Utils.println(PARSER_VERBOSE_LIBRARY_LOADING, "Have already loaded " + newFileName + "."); }
				return null;
			}
			result = loadThisLibrary(newParser, newFileName);
		} else {
			String file2load = Utils.createFileNameString(directoryName, newFileName);
			if (stringHandler.haveLoadedThisFile(file2load, true)) {
				if (debugLevel > 1) { Utils.println(PARSER_VERBOSE_FILE_INCLUDES, "Have already loaded " + file2load + "."); }
				return null;
			}
			if (!dontPrintUnlessImportant) { Utils.println(PARSER_VERBOSE_FILE_INCLUDES, "% loadThisFile: directoryName = " + directoryName + ", newFileName = " + newFileName + ", file2load = " + file2load); }
			result = newParser.readFOPCfile(file2load, okIfFileDoesntExist);
		}
		if (newParser.sentencesToPrecompute != null) {
			if (sentencesToPrecompute == null) { initializeSentencesToPrecompute(); }
			for (int i = 0; i < getNumberOfPrecomputeFiles(); i++) {
				List<Sentence> sents = newParser.getSentencesToPrecompute(i);
			//	Utils.println("% precompute_assignmentToTempVar1 = " + stringHandler.precompute_assignmentToTempVar1);
			//	Utils.println("% precompute_assignmentToTempVar2 = " + stringHandler.precompute_assignmentToTempVar2);
			//	Utils.println("% precompute_assignmentToTempVar3 = " + stringHandler.precompute_assignmentToTempVar3);
				if (Utils.getSizeSafely(sents) > 0) { 
					sentencesToPrecompute[i].addAll(sents);
					String newName = newParser.getFileNameForSentencesToPrecompute(i);
					Utils.println("  loadThisFile: i=" + i + " newName=" + newName + " sents=" + sents);
					if (newName == null) { Utils.waitHere(" newName = null"); }
					setFileNameForSentencesToPrecompute(i, newName, newName.startsWith("precomputed"));
				}
			}
		}
		if (Utils.getSizeSafely(newParser.literalsToThreshold) > 0) {
			if (literalsToThreshold == null) { literalsToThreshold = new HashSet<LiteralToThreshold>(4 + newParser.literalsToThreshold.size()); }
			literalsToThreshold.addAll(newParser.literalsToThreshold);
		}
		if (Utils.getSizeSafely(newParser.loadedLibraries) > 0) {
			if (loadedLibraries == null) { loadedLibraries = new HashSet<String>(4 + newParser.loadedLibraries.size()); }
			if (!dontPrintUnlessImportant) { Utils.println(PARSER_VERBOSE_LIBRARY_LOADING, "% Importing '" + newFileName + "' also loaded these libraries: " + newParser.loadedLibraries); }
			loadedLibraries.addAll(newParser.loadedLibraries);
		}

		if (!dontPrintUnlessImportant) { Utils.println(PARSER_VERBOSE_MODE_LOADING, "% Have loaded '" + newFileName + "'."); }
		return result;
	}

	// Read two strings and store.
	private void processSetParameter() throws ParsingException, IOException {
		int    tokenRead = getNextToken();
		String parameterName   = getPossiblyQuotedString(tokenRead, true);

		//Utils.println("string1 = " + string1);
		checkAndConsume('=');
		tokenRead             = getNextToken();
		double resultAsNumber = processNumber(tokenRead);
		if (Utils.isaNumber(resultAsNumber)) {
			//Utils.println("string2 = " + resultAsNumber);
			if (Math.floor(resultAsNumber) == resultAsNumber) { // See if really an integer.
				stringHandler.recordSetParameter(parameterName, Integer.toString((int) resultAsNumber), fileName, tokenizer.lineno());
			} else {
				stringHandler.recordSetParameter(parameterName, Double.toString(       resultAsNumber), fileName, tokenizer.lineno());
			}
		} else {
			String parameterValue = getPossiblyQuotedString(tokenRead, true);
			//Utils.println("string2 = " + string2);
			stringHandler.recordSetParameter(parameterName, parameterValue, fileName, tokenizer.lineno());

			// Handle parser strings here.
			if        (parameterName.equalsIgnoreCase("parsingWithNamedArguments")) {
				parsingWithNamedArguments = Boolean.valueOf(parameterValue);
			} else if (parameterName.equalsIgnoreCase("maxWarnings")) {
				maxWarnings               = Integer.valueOf(parameterValue);
			} else if (parameterName.equalsIgnoreCase("variablesStartWithQuestionMarks")) {
				if (Boolean.valueOf(parameterValue)) { stringHandler.setVariablesStartWithQuestionMarks(); }
				else                                 { stringHandler.usingPrologNotation(); }
			} else if (parameterName.equalsIgnoreCase("stringsAreCaseSensitive")) {
				stringHandler.setStringsAreCaseSensitive(Boolean.valueOf(parameterValue));
			}
            else if (parameterName.equals("duplicateRuleAction")) {
                VariantClauseAction action = VariantClauseAction.fromString(parameterValue);
                if (action == null) {
                    Utils.warning("Illegal value for parameter " + parameterName + ".  Must be one of " + Arrays.toString(VariantClauseAction.values()));
                }
                else {
                    stringHandler.variantRuleHandling = action;
                }
            }
            else if (parameterName.equals("duplicateFactAction")) {
                VariantClauseAction action = VariantClauseAction.fromString(parameterValue);
                if (action == null) {
                    Utils.warning("Illegal value for parameter " + parameterName + ".  Must be one of " + Arrays.toString(VariantClauseAction.values()));
                }
                else {
                    stringHandler.variantFactHandling = action;
                }
            }
		}
		peekEOL(true);
		if (parameterName.contains("precompute") || parameterName.contains("import")) { checkForDefinedImportAndPrecomputeVars(parameterName); }
	}

	/**
         * Process an 'typeA isa typeB.' The 'isa' is optional. The EOL ('.' or ';') also is optional.
         *
         * @throws ParsingException
         */
	private void processISA() throws ParsingException, IOException {
		int    tokenRead = getNextToken();
		String beforeIsa = getPossiblyQuotedString(tokenRead, true);

		tokenRead = getNextToken();
		String afterIsa = null;
		if (tokenRead != StreamTokenizer.TT_WORD) { Utils.error("Expecting 'isa' or the name of a type, but got: '" + reportLastItemRead() + "'.  beforeIsa=" + beforeIsa); }
		if (tokenizer.sval().equalsIgnoreCase("isa")) {  // If the optional isa is present, suck it up.
			tokenRead = getNextToken();
			if (tokenRead != StreamTokenizer.TT_WORD) { Utils.error("Expecting the name of a type, but got: " + reportLastItemRead() + "."); }
		}
		afterIsa = tokenizer.sval();
		peekEOL(true); // Suck up an optional EOL.

		Term childAsConstant  = stringHandler.getVariableOrConstant(beforeIsa);
		if (!(childAsConstant instanceof Constant))  { throw new ParsingException("Items in ISA's must be constants.  You provided: >> " + beforeIsa + " << isa " + afterIsa); }
		//if (!(parent instanceof StringConstant)) { throw new ParsingException("Items in ISA's must be (string) constants.  You provided: " + child + " isa >> " + parent + " <<"); }
		Type child  = stringHandler.isaHandler.getIsaType(beforeIsa);
		Type parent = stringHandler.isaHandler.getIsaType(afterIsa);

		stringHandler.isaHandler.addISA(child, parent);
		if (debugLevel > 0) { Utils.println("Read this ISA: " + beforeIsa + " isa " + afterIsa + "."); }
		if (++isaCounter % 10000 == 0) { Utils.println("%     Read ISA #" + Utils.comma(isaCounter) + ": " + beforeIsa + " isa " + afterIsa + "."); }
	}

	/**
         * Process the specification of the range of a type, e.g. 'teenage = 13,
         * ..., 19.' and 'size = {small, medium, large};' Braces are optional.
         * The EOL ('.' or ';') is optional IF the braces are present. Note that
         * DOUBLES currently cannot be types (if they were to be allowed, would
         * need to require {}'s so the EOL use of ' could be differentiated from
         * a decimal point.
         *
         * @throws ParsingException
         */
	private void processTypeRange() throws ParsingException, IOException {  // TODO handle doubles here but only if in braces.
		int typeNameCode = getNextToken();
		if (typeNameCode != StreamTokenizer.TT_WORD) { Utils.error("Expecting the name of a type, but got: " + reportLastItemRead() + "."); }
		String typeName = tokenizer.sval();
		int tokenRead = getNextToken();
		if (tokenRead != '=') { Utils.error("Expecting '=' but got: " + reportLastItemRead() + "."); }
		boolean needClosingBrace  = false;
		boolean containsDotDotDot = false;
		List<Constant> constants = new ArrayList<Constant>(4);
		tokenRead = getNextToken();
		if (tokenRead == '{') { needClosingBrace = true; tokenRead = getNextToken(); }

		while (tokenRead != '.' && tokenRead != ';' && tokenRead != '}') {
			String constantAsString = tokenizer.sval();
			if (isAllDigits(constantAsString)) {
				constants.add(stringHandler.getNumericConstant(Integer.parseInt(constantAsString)));
			}
			else {
				constants.add(stringHandler.getStringConstant(constantAsString));
			}
			checkForComma(false, true, true, "processing a type range");
			tokenRead = getNextToken();
			if (tokenRead == '.') { // See if this is '...'
				if (checkAndConsume('.') && checkAndConsume('.')) {
					if (constants.isEmpty() || !(constants.get(constants.size() - 1) instanceof NumericConstant)) {
						throw new ParsingException("The '...' shorthand needs to follow an integer.  You provided: '" + constants.get(constants.size() - 1) + "'.");
					}
					constants.add(stringHandler.getStringConstant("...")); // Note: multiple '...'s are possible, and they can go "uphill" (e.g., "1, ..., 10") or "down hill" (e.g., "10, ..., 1") - however this code doesn't check for overall sequences that are monotonic, so "1, ..., 10, 90, ..., 11" is valid (thouhg maybe it shoudl not be?).
					containsDotDotDot = true;
					if (!checkAndConsume(',')) { throw new ParsingException("Expecting a comma after '...' in the specification of a range."); }
					tokenRead = getNextToken();
				}
			}
		}
		if (needClosingBrace) {
			if (tokenRead != '}') { throw new ParsingException("Since an open brace ('{') was read, expecting a closing one in the specification of a type range."); }
			peekEOL(true); // Suck up an optional EOL.
		}

    	if (debugLevel > 0) { Utils.println("Read the type specification: " + typeName + " = " + constants); }
		if (containsDotDotDot) {
			List<Constant> expandedConstants = new ArrayList<Constant>(2 * constants.size());
			int previous = Integer.MIN_VALUE;
			int size     = constants.size();
			for (int i = 0; i < size; i++) {
				Constant c = constants.get(i);
				if (c instanceof NumericConstant) {
					previous = ((NumericConstant) c).value.intValue();
					expandedConstants.add(c); // Duplicates are checked elsewhere - don't want to drop them here since that might mess up the use of '...' - e.g., "1, 2, 10, 15, ... 10".
				}
				else if (c instanceof StringConstant && ((StringConstant) c).equals(stringHandler.getStringConstant("..."))) { // getName().equalsIgnoreCase("...")) {
					if (i == size - 1) { throw new ParsingException("The '...' in a range must be followed by a number."); }
					Constant nextConstant = constants.get(i + 1);
					if (!(nextConstant instanceof NumericConstant))  { throw new ParsingException("The '...' in a range must be followed by an integer.  You provided: '" + nextConstant + "'."); }
					int next = ((NumericConstant) nextConstant).value.intValue();

					if (Math.abs(next - previous) > 2000) { throw new ParsingException("Do you really want to expand from " + previous + " to " + next + "?  If so, you'll need to edit and recompile processTypeRange()."); }
					if (next >= previous) {
						for (int k = previous + 1; k < next; k++) {
							expandedConstants.add(stringHandler.getNumericConstant(k));
						}
					}
					else {
						for (int k = previous - 1; k > next; k--) {
							expandedConstants.add(stringHandler.getNumericConstant(k));
						}
					}
				}
				else { throw new ParsingException("When '...' is present, all types must be number.  You provided: '" + c + "'."); }
			}
			if (debugLevel > 2) { Utils.println("  The expands to: " + typeName + " = " + expandedConstants); }
			stringHandler.recordPossibleTypes(typeName, expandedConstants);
		}
		else {
			stringHandler.recordPossibleTypes(typeName, constants);
		}
	}

	/** Process a mode specification.  There needs to be an EOL at the end ('.' or ';') due to the optional arguments.
	 *  If the optional arguments are used, they can be separated by commas, but this isn't necessary.
	 *
	 *     mode:       typed_literal           // This states the types of the arguments in this literal.  Types are + (an 'input' variable; MUST be present earlier in the clause), - (an 'output' variable; need not already be present in the clause), and # (a constant; need not already be present).    A variable can be followed by '!k' or $k' - the former means "this predicate will be true for EXACTLY k possible values for this argument, where the latter is similar but for "AT MOST K."
	 *  			   [target=pred/numbArgs]  // Optionally [not yet implemented] can say that the above mode only applies when learning this target.  A sample is 'parentOf/2' (the literal whose predicate name is 'parentOf' and which has two arguments).
	 *  			   [max=#]                 // Optionally say that typed_literal can appear in a learned clauses at most # (some integer) times.
	 *  			   [maxPerInputVars=#]     // Optionally indicate that PER SETTING to the 'input' (i.e. '+') variables, can occur at most this many times (an idea taken from Aleph).
	 */
	private void processMode(List<Sentence> listOfSentences, boolean thisIsaNoMode) throws ParsingException, IOException {  // TODO if token not a known optional argument could pushback() w/o needing an EOL, but be more restrictive for now.
		Literal       typedHeadLiteral = processLiteral(true);
		int           tokenRead    = getNextToken();
		PredicateName targetPred   = null;
		int           arity        = -1; // '-1' means not specified.
		int           max          = Integer.MAX_VALUE;
		int        maxPerInputVars = Integer.MAX_VALUE;

		while (!atEOL()) { // Have some optional arguments since not yet at EOL.
			String currentWord = tokenizer.reportCurrentToken();
			if (tokenRead == ',') {  } // OK if there are some commas separating the items.
			else if (currentWord.equalsIgnoreCase("max")) { // BUG: the user can't use 'max' nor 'maxPerInputVars' as target predicates.  TODO fix
				if (max < Integer.MAX_VALUE) { throw new ParsingException("Have already read max=" + max + " when processing a mode and have encountered 'max' again."); }
				max             = readEqualsInteger();
			}
			else if (currentWord.equalsIgnoreCase("maxPerInputVars")) {
				if (maxPerInputVars < Integer.MAX_VALUE) { throw new ParsingException("Have already read maxPerInputVars=" + max + " when processing a mode and have encountered 'maxPerInputVars' again."); }
				maxPerInputVars = readEqualsInteger();
			}
			else if (currentWord.equalsIgnoreCase("target")) {
				Utils.warning("The use of the 'target' option in the specification of modes has not yet been implemented.  So this mode will apply to all targets.");
				if (targetPred != null) { throw new ParsingException("Have already read targetPred=" + targetPred + " and have now read '" + currentWord + " when processing a mode."); }
				tokenRead    = getNextToken();
				if (tokenRead != '=') { throw new ParsingException("Expecting to read '=' (after 'target'), but instead read: '" + reportLastItemRead() + "'."); }
				currentWord = getNextString();
				targetPred = stringHandler.getPredicateName(currentWord);
				tokenRead = getNextToken();
				if (tokenRead != '/') { throw new ParsingException("Expecting a '/' (slash) in a mode specification but got: '" + reportLastItemRead() + "'."); }
				arity = readInteger();
			}
			else {
				throw new ParsingException("Parsing a mode - " + typedHeadLiteral + " - and instead of reading 'target=' or 'max=' or 'maxPerInputVars=', unexpectedly read: '" + reportLastItemRead() + "'.");
			}
			tokenRead = getNextToken();
		}

		if (typedHeadLiteral.getArguments() != null) {
			for (Term term : typedHeadLiteral.getArguments()) {
				if (term instanceof Function) {
					//processTypesInFunction((Function) term); // Seems these are properly marked with their types.
					continue;
				}
				if (term.getTypeSpec() != null) { continue; }
				throw new ParsingException("All arguments in mode specifications must be typed.  There is no type for '" + term + "' in '" + typedHeadLiteral + "'.");
			}
		}
		stringHandler.recordMode(typedHeadLiteral, max, maxPerInputVars, thisIsaNoMode);
		

        listOfSentences.add(stringHandler.getClause(stringHandler.getLiteral("mode", typedHeadLiteral.convertToFunction(stringHandler)), true));

		if (debugLevel > 1) {
			Utils.print("READ " + (thisIsaNoMode ? "noMode" : "mode") + ": " + typedHeadLiteral);
			if (targetPred != null)   { Utils.print(" target=" + targetPred + "/" + arity); }
			if (max             < Integer.MAX_VALUE) { Utils.print(" max=" + max); }
			if (maxPerInputVars < Integer.MAX_VALUE) { Utils.print(" maxPerInputVars=" + maxPerInputVars); }
			Utils.println(".");
		}
		// Do NOT skipToEOL() here since that is what ended the while loop.
	}

 	        //Function By Navdeep Kaur
 		// This function obtains and then sets the randomwalk constraints for each predicate. 
 		private void processRandomWalks(List<Sentence> listOfSentences)throws ParsingException, IOException {
 			
 			int tokenRead = checkForPredicateNamesThatAreCharacters(getNextToken());
 			String        currentWord = tokenizer.reportCurrentToken();
 				
 			PredicateName predicate = stringHandler.getPredicateName(currentWord);
 			
 			System.out.print("\nSetting the randomwalkconstraint for '" + predicate +"':");
 			tokenRead = getNextToken();
 
 			if (tokenRead != '=') { throw new ParsingException("Expecting a '=' (equal to) in a randomwalkconstraint specification for '" + predicate + "', but got: '" + reportLastItemRead() + "'."); }
 			tokenRead = getNextToken();
 			if(tokenRead =='.')
 				predicate.setRandomWalkFlag();
 			
 			while(tokenRead != '.')
 			{	if(tokenRead==','){	tokenRead = getNextToken();	continue;}
 				else{
 					String  currentConstraint = tokenizer.reportCurrentToken();
 					predicate.addRandomWalkConstraint(currentConstraint);
 					System.out.print(" 	"+currentConstraint);
 				}
 				if (debugLevel > 1) {
 					Utils.println("%   READ randomwalkconstraint: " + predicate + "/"  + ".");
 				}
 				tokenRead = getNextToken();
 			}
 		
 			peekEOL(true); // Suck up an optional EOL.
 			if(!predicate.getNoTwinValue())
 			{
 				List<PredicateSpec> myArgs =predicate.getTypeList();
 				
 				if(myArgs.size()>1){ Utils.error("There Should be only one predicate with name = '"+predicate);	}
 				else{
 					
 					List<TypeSpec> spec = (myArgs.get(0)).getTypeSpecList();
 								
 					if( spec.size()>2){Utils.error("Grounding Random Walks for binary predicates only.");}
 													
 					FunctionName fName = stringHandler.getFunctionName("_"+currentWord);
 					List<Term> terms = new ArrayList<Term>();
 					List<String> names = null;
 					TypeSpec typespec = null;
 							
 					Term Arg0 = stringHandler.getAnonymousTerm(spec.get(1));
 					Term Arg1 = stringHandler.getAnonymousTerm(spec.get(0));
 					
 					terms.add(Arg0);
 					terms.add(Arg1);
 					
 					Term possibleTerm = stringHandler.getFunction(fName, terms, names, typespec);
 					Literal typedHeadLiteral = convertTermToLiteral(possibleTerm);
 					
 					if (typedHeadLiteral.getArguments() != null) {
 						for (Term term : typedHeadLiteral.getArguments()) {
 							if (term instanceof Function) {
 								continue;
 							}
 							if (term.getTypeSpec() != null) { continue; }
 							throw new ParsingException("All arguments in mode specifications must be typed.  There is no type for '" + term + "' in '" + typedHeadLiteral + "'.");
 						}
 					}
 					stringHandler.recordMode(typedHeadLiteral, Integer.MAX_VALUE, Integer.MAX_VALUE, false);
 					
 					listOfSentences.add(stringHandler.getClause(stringHandler.getLiteral("mode", typedHeadLiteral.convertToFunction(stringHandler)), true));
 					
 					//List<Term>   sign = (myArgs.get(0)).getSignature();
 					//PredicateNameAndArity PName = stringHandler.getPredicate("_"+currentWord,2);
 					//System.out.println(terms);
 					
 					//List<Term> newsign = new ArrayList<Term>();
 					//List<TypeSpec> newspec = new ArrayList<TypeSpec>();
 					
 					//newsign.add(0, sign.get(1)); newsign.add(1, sign.get(0)); //Swapping signature
 					//newspec.add(0, spec.get(1)); newspec.add(1, spec.get(0)); //Swapping specification
 									
 					//System.out.println(((spec.get(1)).getType()).typeName);
 					//System.out.println(spec.get(1).mode);
 					//stringHandler.recordModeWithTypes(PName, newsign, newspec, Integer.MAX_VALUE, Integer.MAX_VALUE, true);
 					
 				}
 			}
 		}
 	

	private void processConstrains() throws ParsingException, IOException {
		int tokenRead = checkForPredicateNamesThatAreCharacters(getNextToken());
		String        currentWord = tokenizer.reportCurrentToken();
		PredicateName predicate = stringHandler.getPredicateName(currentWord);
		tokenRead = getNextToken();

		if (tokenRead != '/') { throw new ParsingException("Expecting a '/' (slash) in a constrains specification for '" + predicate + "', but got: '" + reportLastItemRead() + "'."); }
		int arity = readInteger();

		tokenRead = getNextToken();
		if (tokenRead == ',') { tokenRead = getNextToken(); } // OK if there are some commas separating the items.
		currentWord = tokenizer.reportCurrentToken();
		if (!currentWord.equalsIgnoreCase("arg")) { throw new ParsingException("Expecting to read: 'arg' but instead read '" + reportLastItemRead() + "'."); }
		tokenRead    = getNextToken();
		if (tokenRead != '=') { throw new ParsingException("Expecting to read '=' (after 'arg'), but instead read: '" + reportLastItemRead() + "'."); }
		int position = readInteger();
		if (position < 1 || position > arity) { throw new ParsingException("Expecting to read an integer between 1 and " + arity + ", but instead read '" + position + "."); }
		tokenRead    = getNextToken();
		if (tokenRead == ',') { tokenRead = getNextToken(); }
		Type type = stringHandler.isaHandler.getIsaType(tokenizer.reportCurrentToken());
		boolean pruneIfNoEffect = false;
		if (!atEOL()) {
			tokenRead    = getNextToken();
			if (tokenRead == ',') { tokenRead = getNextToken(); }
			currentWord = tokenizer.reportCurrentToken();
			if (!currentWord.equalsIgnoreCase("pruneIfNoEffect")) { throw new ParsingException("Expecting to read: 'arg' but instead read '" + reportLastItemRead() + "'."); }
			pruneIfNoEffect = true;
		}
		predicate.addConstrainsArgumentType(arity, position, type, pruneIfNoEffect);
		if (debugLevel > 1) {
			Utils.println("%   READ constrains: " + predicate + "/" + arity + " at arg #" + position + " to type '" + type + "'." + (pruneIfNoEffect ? "  If the pruning has no impact, prune this literal.": ""));
		}
		peekEOL(true); // Suck up an optional EOL.
	}

	@SuppressWarnings("unused")
	private void processTypesInFunction(Function f) {
		if (f.numberArgs() < 1) { return; }
		for (Term arg : f.getArguments()) {
			if (arg instanceof Function) {
				processTypesInFunction((Function) arg);
			} else {
				Utils.println(" arg = " + arg + " type=" + arg.getTypeSpec());
			}
		}
	}

	/** Process a specification of a determinate literal.
	 *
	 *   Eg, determinate: p/3 arg=2 type=integer.
	 *
	 * When all other arguments are fixed, the specified arg's is deterministic and of this type.
	 *
	 */
	private void processDeterminate() throws ParsingException, IOException {
		int tokenRead = checkForPredicateNamesThatAreCharacters(getNextToken());
		String        currentWord = tokenizer.reportCurrentToken();
		PredicateName predicate = stringHandler.getPredicateName(currentWord);
		tokenRead = getNextToken();

		if (tokenRead != '/') { throw new ParsingException("Expecting a '/' (slash) in a determinate specification for '" + predicate + "', but got: '" + reportLastItemRead() + "'."); }
		int arity = readInteger();

        expectAndConsumeToken(",");
        expectAndConsumeToken("arg");
        expectAndConsumeToken("=");
        int position = readInteger();

		if (position < 1 || position > arity) { throw new ParsingException("Expecting to read an integer between 1 and " + arity + ", but instead read '" + position + "."); }

		tokenRead = getNextToken();

        Type type = null;

        if ( checkAndConsumeToken("," ) ) {
            expectAndConsumeToken("type");
            expectAndConsumeToken("=");

            String typeAsString = getNextString();
            type = stringHandler.isaHandler.getIsaType(typeAsString);
        }
		predicate.setDeterminateInfo(arity, position, type);
        
		if (debugLevel > 1) {
			Utils.println("%   READ determinate: " + predicate+ "/" + arity + " at arg #" + position + " with type = '" + type + "'.");
		}
		peekEOL(true); // Suck up an optional EOL.
	}

	private void processFunctionAsPred(FunctionAsPredType prefix) throws ParsingException, IOException {
		int tokenRead = checkForPredicateNamesThatAreCharacters(getNextToken());
		String        currentWord = tokenizer.reportCurrentToken();
		PredicateName predicate = stringHandler.getPredicateName(currentWord);
		tokenRead = getNextToken();

		if (tokenRead != '/') { throw new ParsingException("Expecting a '/' (slash) in a " + prefix + "FunctionAsPred specification for '" + predicate + "', but got: '" + reportLastItemRead() + "'."); }
		int arity = readInteger();

		tokenRead = getNextToken();
		if (tokenRead == ',') { tokenRead = getNextToken(); } // OK if there are some commas separating the items.
		currentWord = tokenizer.reportCurrentToken();
		if (!currentWord.equalsIgnoreCase("arg")) { Utils.println("Expecting to read: 'arg' but instead read '" + reportLastItemRead() + "'."); }
		tokenRead    = getNextToken();
		if (tokenRead != '=') { throw new ParsingException("Expecting to read '=' (after 'arg'), but instead read: '"  + reportLastItemRead() + "'."); }
		int position = readInteger();
		if (position < 1 || position > arity) { throw new ParsingException("Expecting to read an integer between 1 and " + arity + ", but instead read '" + position + "."); }

		predicate.addFunctionAsPred(prefix, arity, position);
		if (debugLevel > 1) {
			Utils.println("%   READ " + prefix + "FunctionAsPred: " + predicate+ "/" + arity + " at arg #" + position + "'.");
		}
		peekEOL(true); // Suck up an optional EOL.
	}

	private void processBridger() throws ParsingException, IOException {
		int tokenRead = checkForPredicateNamesThatAreCharacters(getNextToken());
		String        currentWord = tokenizer.reportCurrentToken();
		PredicateName predicate = stringHandler.getPredicateName(currentWord);
		tokenRead = getNextToken();

		if (tokenRead != '/') { throw new ParsingException("Expecting a '/' (slash) in a bridger specification for '" + predicate + "', but got: '" + reportLastItemRead() + "'."); }
		int arity = readInteger();

		predicate.addBridger(arity);
		if (debugLevel > 1) {
			Utils.println("%   READ bridger: " + predicate + "/" + arity + ".");
		}
		peekEOL(true); // Suck up an optional EOL.
	}

	private void processTemporary() throws ParsingException, IOException {
		int tokenRead = checkForPredicateNamesThatAreCharacters(getNextToken());
		String        currentWord = tokenizer.reportCurrentToken();
		PredicateName predicate = stringHandler.getPredicateName(currentWord);
		tokenRead = getNextToken();

		if (tokenRead != '/') { throw new ParsingException("Expecting a '/' (slash) in a temporary specification for '" + predicate + "', but got: '" + reportLastItemRead() + "'."); }
		int arity = readInteger();

		predicate.addTemporary(arity);
		if (debugLevel > 1) {
			Utils.println("%   READ temporary: " + predicate + "/" + arity + ".");
		}
		peekEOL(true); // Suck up an optional EOL.
	}

	private void processInline() throws ParsingException, IOException {
		int           tokenRead   = checkForPredicateNamesThatAreCharacters(getNextToken());
		String        currentWord = tokenizer.reportCurrentToken();
		PredicateName predicate   = stringHandler.getPredicateName(currentWord);
		tokenRead = getNextToken();

		if (tokenRead != '/') { throw new ParsingException("Expecting a '/' (slash) in an inline specification for '" + predicate + "', but got: '" + reportLastItemRead() + "'."); }
		int arity = readInteger();

		predicate.addInliner(arity);
		if (debugLevel > 1) {
			Utils.println("%   READ inline: " + predicate + "/" + arity + ".");
		}
		peekEOL(true); // Suck up an optional EOL.
	}

	private void processFilter() throws ParsingException, IOException {
		int           tokenRead   =	checkForPredicateNamesThatAreCharacters(getNextToken());
		String        currentWord = tokenizer.reportCurrentToken();
		PredicateName predicate   = stringHandler.getPredicateName(currentWord);
		tokenRead = getNextToken();

		predicate.addFilter();
		if (debugLevel > 1) {
			Utils.println("%   READ filter: " + predicate + ".  tokenRead = " + tokenRead);
		}
		peekEOL(true); // Suck up an optional EOL.
	}

	private void processQueryPred() throws ParsingException, IOException {
		int           tokenRead   = checkForPredicateNamesThatAreCharacters(getNextToken());
		String        currentWord = tokenizer.reportCurrentToken();
		PredicateName predicate   = stringHandler.getPredicateName(currentWord);
		tokenRead = getNextToken();

		if (tokenRead != '/') { throw new ParsingException("Expecting a '/' (slash) in a query-predicate specification for '" + predicate + "', but got: '" + reportLastItemRead() + "'."); }
		int arity = readInteger();

		predicate.addQueryPred(arity);
		if (debugLevel > 1) {
			Utils.println("%   READ query predicate: " + predicate + "/" + arity + ".");
		}
		stringHandler.addQueryPredicate(predicate, arity);
		peekEOL(true); // Suck up an optional EOL.
	}

	private void processHiddenPred() throws ParsingException, IOException {
		int tokenRead = checkForPredicateNamesThatAreCharacters(getNextToken());
		String        currentWord = tokenizer.reportCurrentToken();
		PredicateName predicate = stringHandler.getPredicateName(currentWord);
		tokenRead = getNextToken();

		if (tokenRead != '/') { throw new ParsingException("Expecting a '/' (slash) in a hidden-predicate specification for '" + predicate + "', but got: '" + reportLastItemRead() + "'."); }
		int arity = readInteger();

		predicate.addHiddenPred(arity);
		if (debugLevel > 1) {
			Utils.println("%   READ hidden predicate: " + predicate+ "/" + arity + ".");
		}
		stringHandler.addHiddenPredicate(predicate, arity);
		peekEOL(true); // Suck up an optional EOL.
	}

	private void processThreshold()  throws ParsingException, IOException {
		Literal typedHeadLiteral = processLiteral(true);
		String  currentWord  = tokenizer.reportCurrentToken();
		int     tokenRead    = getNextToken();
		int     maxCuts      = -1;
		boolean createTiles  = false;
		boolean firstArgIsExampleID = false;

		tokenRead = getNextToken();
		if (tokenRead == ',') { tokenRead = getNextToken(); } // OK if there are some commas separating the items.
		currentWord = tokenizer.reportCurrentToken();
		if (!currentWord.equalsIgnoreCase("arg")) { Utils.println("Expecting to read: 'arg' but instead read '" + reportLastItemRead() + "'."); }
		tokenRead    = getNextToken();
		if (tokenRead != '=') { throw new ParsingException("Expecting to read '=' (after 'arg'), but instead read: '" + reportLastItemRead() + "'."); }
		int position = readInteger();
		if (position < 1 || position > typedHeadLiteral.numberArgs()) { throw new ParsingException("Expecting to read an integer between 1 and " + typedHeadLiteral.numberArgs() + ", but instead read '" + position + "."); }

		while (!atEOL()) { // Have some optional arguments since not yet at EOL. {
			tokenRead   = getNextToken();
			currentWord = tokenizer.reportCurrentToken();
			if (tokenRead == ',' || atEOL()) {  } // OK if there are some commas separating the items.
			else if (currentWord.equalsIgnoreCase("maxCuts")) {
				tokenRead = getNextToken();
				if (tokenRead != '=') { throw new ParsingException("Expecting to read '=' (after 'maxCuts'), but instead read: '" + reportLastItemRead() + "'."); }
				maxCuts = readInteger();
				if (maxCuts < 2) { throw new ParsingException("Expecting to read an integer great than 1, but instead read '" + maxCuts + "."); }
			}
			else if (currentWord.equalsIgnoreCase("createTiles")) {
				createTiles = true;
			}
			else if (currentWord.equalsIgnoreCase("firstArgIsExampleID")) {
				firstArgIsExampleID = true;
			}
			else { throw new ParsingException("Expecting to read 'maxCuts' or 'createTiles' or 'firstArgIsExampleID,' but instead read: '" + reportLastItemRead() + "'."); }

		}
		skipToEOL();
        if (literalsToThreshold == null) {
            literalsToThreshold = new HashSet<LiteralToThreshold>(4);
        }
        literalsToThreshold.add(stringHandler.getLiteralToThreshold(typedHeadLiteral.predicateName, typedHeadLiteral.getArguments(), position, maxCuts, createTiles, firstArgIsExampleID));
        if (debugLevel > 1) {
            Utils.println("%   READ threshold: " + typedHeadLiteral + " at arg #" + position + " with maxCuts = '" + maxCuts + "', createTiles='" + createTiles + "', and firstArgIsExampleID='" + firstArgIsExampleID + "'.");
        }

	}

	private int getNextToken() throws IOException {
		return getNextToken(false);
	}

    //private long getCount = 0;
	private int getNextToken(boolean okIfEOF) throws IOException {
		int tokenRead = tokenizer.nextToken();

		if (tokenRead == StreamTokenizer.TT_EOF && !okIfEOF) { throw new IOException("Unexpected EOF: " + fileName); }

//        System.out.print(tokenizer.reportCurrentToken());
//        if ( getCount++ % 100 == 0) System.out.println();
		return tokenRead;
	}

	/**
         * Read the next token and return it as a string. If the next token is
         * not a string, throw an exception.
         *
         * @return The next string in the tokenizer's input stream.
         * @throws ParsingException
         */
	private String getNextString() throws ParsingException, IOException {
		int tokenRead = getNextToken();
		if (tokenRead != StreamTokenizer.TT_WORD) { throw new ParsingException("Expected to read a token, but read: '" + reportLastItemRead() + "'."); }
		return tokenizer.sval();
	}

	private int readEqualsInteger() throws ParsingException, IOException {
		int tokenRead = getNextToken();
		if (tokenRead != '=') { throw new ParsingException("Expecting an '=' but got: " + reportLastItemRead() + "."); }
		return readInteger();
	}

	private Literal readEqualsTypedLiteral() throws ParsingException, IOException {
		int tokenRead = getNextToken();
		if (tokenRead != '=') { throw new ParsingException("Expecting an '=' but got: " + reportLastItemRead() + "."); }
		return processLiteral(true);
	}

	private int readInteger() throws ParsingException, IOException {
		int   tokenRead = getNextToken();
		boolean negated = false;
		if (tokenRead == '-') {
			negated   = true;
			tokenRead = getNextToken();
		}
		if (tokenRead == '@') {  // A leading # indicates the value needs to be looked up in the list of set parameters.
			tokenRead       = getNextToken();
			String wordRead = tokenizer.sval();
			String setting  = stringHandler.getParameterSetting(wordRead);
			if (setting      == null) { Utils.error(" Read '@" + wordRead + "', but '" + wordRead + "' has not been set."); }
			Integer setToInteger = Integer.parseInt(setting);
			if (setToInteger == null) { Utils.error(" Read '@" + wordRead + "', but '" + wordRead + "' has been set to '" + setting + "', rather than an integer."); }
			return setToInteger;
		}
		if (tokenRead != StreamTokenizer.TT_WORD || !isAllDigits(tokenizer.sval())) {
			String lastItem = reportLastItemRead();
			tokenizer.pushBack();
			if (negated) { tokenizer.pushBack(); } // Get back to state when readInteger() called in case the caller wants to field the exception.
			throw new ParsingException("Expecting an integer but got: '" + lastItem + "'.");
		}
		int value = Integer.parseInt(tokenizer.sval());
		if (negated) { return -value; }
		return value;
	}

	/**
     * See if this character is the next one in the stream. If not, throw an
     * exception using this provided message (if the message = null,
     * generate one instead).
     *
     * @param charValue
     * @param exceptionMsg
     * @throws ParsingException
     */
	private void expectAndConsume(char charValue, String exceptionMsg) throws ParsingException, IOException {
		int tokenRead = getNextToken();
		if (tokenRead == (int)charValue) { return; }
		if (exceptionMsg == null) { throw new ParsingException("Expecting the character '" + charValue + "' but read '" + reportLastItemRead() + "'."); }
		throw new ParsingException(exceptionMsg);
	}

	/** See if this character is the next one in the stream. If so, "chew it
     * up" and return 'true.' Otherwise push it back and return 'false.'
     *
     * @param charValue
     * @return Whether the given character is the next one in the stream.
     * @throws ParsingException
     */
	private boolean checkAndConsume(char charValue) {
		int tokenRead;
		try {
			tokenRead = getNextToken();
		}
		catch (IOException e) {
			return false; // If at EOF, no need to throw an exception.  Just say nothing to peek at.  TODO - make sure this cant lead to an infinite loop of peek's.
		}
		if (debugLevel > 2) { Utils.println("  peeking at: '" + reportLastItemRead() + "' vs. '" + charValue + "'."); }
		if (tokenRead == (int)charValue) { return true; }
		tokenizer.pushBack();
		return false;
	}

	/**
         * See if the current token is EOL ('.' or ';').
         *
         * @return Whether the current token in the tokenizer is an end-of-line
         *         marker.
         */
	private boolean atEOL() {
		return (tokenizer.ttype() == '.' || tokenizer.ttype() == ';');
	}

	/**
         * See if next token is an EOL character ('.' or ';').
         *
         * @return Whether the next token in the tokenizer is an end-of-line marker.
         * @throws ParsingException
         */
	private boolean peekEOL(boolean okIfEOF) throws ParsingException, IOException {
		int token = tokenizer.nextToken(); // Suck up the EOL if it is next.
		if (!okIfEOF && token == StreamTokenizer.TT_EOF) { throw new IOException("Unexpected EOF."); }
		if (token == '.' || token == ';') { return true; }
		tokenizer.pushBack();
		return false;
	}

	/**
         * Expecting a comma, say in a list of arguments, but can also "peek"
         * for other tokens that close the list.
         *
         * @param rightParenOk
         * @param rightBraceOK
         * @param okEOL
         * @param partOfErroMsg
         * @throws ParsingException
         */
	private void checkForComma(boolean rightParenOK, boolean rightBraceOK, boolean okEOL, String partOfErrorMsg) throws ParsingException, IOException {
		if (checkAndConsume(',')) { return; }
		if (rightParenOK && checkAndConsume(')')) { tokenizer.pushBack(); return; }
		if (rightBraceOK && checkAndConsume('}')) { tokenizer.pushBack(); return; }
		if (rightBraceOK && checkAndConsume(']')) { tokenizer.pushBack(); return; }
		if (okEOL        && peekEOL(true))     {                       return; }
		getNextToken();
		throw new ParsingException("Was looking for a comma"
							+ (rightParenOK ? " or a right parenthesis"           : "")
							+ (rightBraceOK ? " or a right brace or bracket"      : "")
							+ (okEOL        ? " or an EOL character ('.' or ';')" : "")
							+ " when " + partOfErrorMsg + ", but read: '" + reportLastItemRead() + "'.");
	}

	private boolean isAllDigits(String integerString) {
		// 'parseInt' gets called twice since this is only a boolean, but no big deal to read integer strings twice.
		try { Integer.parseInt(integerString); return true;  }
		catch (NumberFormatException e)     {  return false; }
	}

	private String reportLastItemRead() {
		int tokenRead = tokenizer.ttype();
		if (tokenRead == StreamTokenizer.TT_EOF)  { return "EOF"; }
		if (tokenRead == StreamTokenizer.TT_WORD) { return tokenizer.sval(); }
		return String.valueOf((char) tokenRead);  // Want the character not its integer representation.
	}

	private boolean isaPossibleTermName(int tokenRead) {
		switch (tokenRead) {
			case '+':                     return (tokenizer.prevToken() == '\\');
			case '\\':                    return true; // Might be \+().
			case '-':                     return true; // Added by JWS Jan 2010.
			case StreamTokenizer.TT_WORD: return true;
			default:                      return false;
		}
	}

    private boolean checkForOperator() throws ParsingException, IOException {
        return checkToken("-") || checkToken("*") || checkToken("/") || checkToken("+");
    }

	private String getPredicateOrFunctionName() throws ParsingException {
		return getPredicateOrFunctionName(tokenizer.ttype());
	}
	private String getPredicateOrFunctionName(int tokenRead) throws ParsingException {
		switch (tokenRead) {  // If changed, check out checkForPredicateNamesThatAreCharacters (for cases where a single-char string is returned).
			case StreamTokenizer.TT_WORD:                   return tokenizer.sval();
		//	case ':':  if (tokenizer.prevToken() == '-')  { return ":-"; } // Support ':-' as a predicate.
			case '-':                                       return "-";
			case '+':  if (tokenizer.prevToken() == '\\') { return "\\+"; }
					   return "+";
			case '=':  if (tokenizer.prevToken() == '\\') {
							if (checkAndConsume('='))     { return "\\=="; }
					   }
					   break;
			case '\\': if (checkAndConsume('+'))          { return "\\+";  }
			  		   if (checkAndConsume('='))  {
							if (checkAndConsume('='))     { return "\\=="; }
							                                return "\\=";
			 		   }
		}
		throw new ParsingException("Expecting a predicate name but read: '" + reportLastItemRead() + "'.");
	}

    private String checkAndConsumeArgumentName() throws IOException {

        String possibleName = null;

        int token = getNextToken();
        if ( token == StreamTokenizer.TT_WORD) {
            possibleName = tokenizer.reportCurrentToken();
            if ( checkAndConsumeToken("=") ) {
                return possibleName;
            }
        }
        tokenizer.pushBack();

        return null;
    }

	private Literal processLiteral(boolean argumentsMustBeTyped) throws ParsingException, IOException {
		int tokenRead        = getNextToken();
		int leftParenCounter = 0;
		while (tokenRead == '(' || tokenRead == '{' || tokenRead == '[') {
			leftParenCounter++;
			tokenRead = getNextToken();
		}

		tokenRead = checkForPredicateNamesThatAreCharacters(tokenRead);
		Term possibleTerm     = processRestOfTerm(tokenRead, false); // WHY????? argumentsMustBeTyped);
		tokenRead             = getNextToken(true);

		if (tokenRead == StreamTokenizer.TT_EOF) { return convertTermToLiteral(possibleTerm); }
		String peekAtNextWord = isInfixTokenPredicate(tokenRead);
		Literal inFixLiteral  = null;
		if (peekAtNextWord != null) { // Handle 'is' and <, >, >=, <=, ==, etc.
			inFixLiteral = processInfixLiteral(possibleTerm, peekAtNextWord, argumentsMustBeTyped);
			tokenRead    = getNextToken(); // Needed for the check for left parentheses.
		}
		while (leftParenCounter > 0) { // Suck up any closing parentheses.
			if (tokenRead != ')' && tokenRead != '}' && tokenRead != ']') { throw new ParsingException("Expecting " + leftParenCounter + " more right parentheses, but read: '" + tokenizer.reportCurrentToken() + "'."); }
			leftParenCounter--;
			tokenRead = getNextToken(true); // Always read one too many, then push back below.
		}
		if (tokenRead != StreamTokenizer.TT_EOF) { tokenizer.pushBack(); }
		if (inFixLiteral != null) { return inFixLiteral; }
		return convertTermToLiteral(possibleTerm);
	}

//    /** Reads a (positive) literal from the stream.
//     *
//     * The literal is a formula consisting of a predicate symbol and it's terms:
//     *
//     * Literal =>
//     *      (
//     *          <IDENTIFIER>
//     *
//     *          [
//     *              <LEFTPARAN> listOfTerms() <RIGHTPARAN>
//     *          |
//     *              infixOperator() term()
//     *          ]
//     *      )
//     *   |
//     *      <VARIABLE> infixOperator() term()
//     *
//     *
//     *
//     * A look-ahead of 1 is required to disambiguate between Infix and Non-infix symbols.
//     *
//     * @param argumentsMustBeTyped
//     * @return
//     * @throws ParsingException
//     * @throws IOException
//     */
//    private boolean processLiteralTAW(ReturnValue<Literal> literal, boolean argumentsMustBeTyped) throws ParsingException, IOException {
//
//        ReturnValue<String> predicateName;
//
//        if ( processIdentifierTAW(predicateName)) {
//
//        }
//
//    private boolean processPredicateSymbolTAW(ReturnValue<String> string) {
//        String name = getPredicateOrFunctionName();
//        List<Term> terms = null;
//
//    }

    /** Reads a list of Terms from the stream.
     *
     * Assumes that the initial '(' has already been read and that the terminating ')' will be
     * consumed.
     * 
     * @param argumentsMustBeTyped
     * @return
     * @throws ParsingException
     * @throws IOException
     */
    private NamedTermList processListOfTerms(char openingBracket, boolean argumentsMustBeTyped) throws ParsingException, IOException {

        List<Term> terms = new ArrayList<Term>();
        List<String> names = null;

        Term t;
        String name;

        boolean done = false;

        String closingBracketChar = Character.toString(getClosingBracket(openingBracket));

        // We check immediate for a closing bracket to
        // support literals written as:  x() although
        // this is illegal in prolog.
        if (checkAndConsumeToken(closingBracketChar)) {
            done = true;
        }

        while (!done) {
            // Look for a name?
            name = checkAndConsumeArgumentName();
            t = processTerm(argumentsMustBeTyped);

            terms.add(t);

            if (names != null || name != null) {
                if (names == null) {
                    names = new ArrayList<String>();
                }
                // Have to add even the null names just
                // in case they are necessary.
                names.add(name);
            }

            if (checkAndConsumeToken(closingBracketChar)) {
                done = true;
            }
            else if ( checkToken(",") == false) {
                getNextToken();
                throw new ParsingException("Unexpected token '" + tokenizer.reportCurrentToken() + "'.  Expected ',' or '" + closingBracketChar + "'." );
            }
            else {
                expectAndConsumeToken(",");
            }
        }

        return new NamedTermList(terms, names);
    }

    /** Reads a list of Terms from the stream.
     *
     * Assumes that the initial '(' has already been read and that the terminating ')' will be
     * consumed.
     *
     * @param argumentsMustBeTyped
     * @return
     * @throws ParsingException
     * @throws IOException
     */
    private ConsCell processConsCellList(boolean argumentsMustBeTyped) throws ParsingException, IOException {

        ConsCell head = null;
        ConsCell tail = null;

        Term t;
        String name;

        boolean done = false;

        // We check immediate for a closing bracket to
        // support literals written as:  x() although
        // this is illegal in prolog.
        if (checkAndConsumeToken("]")) {
            head = stringHandler.getNil();
            done = true;
        }

        while (!done) {
            // Look for a name?
            name = checkAndConsumeArgumentName();
            t = processTerm(argumentsMustBeTyped);

            ConsCell cell = stringHandler.getConsCell(t, stringHandler.getNil(), null);
            if ( head == null ) {
                head = cell;
                tail = head;
            }
            else {
                tail.setCdr(cell);
                tail = cell;
            }

            if (checkAndConsumeToken("]")) {
                done = true;
            }
            else if ( checkAndConsumeToken("|") ) {
                name = checkAndConsumeArgumentName();
                t = processTerm(argumentsMustBeTyped);
                tail.setCdr(t);

                expectAndConsumeToken("]");

                done = true;
            }
            else if ( checkToken(",") == false) {
                getNextToken();
                throw new ParsingException("Unexpected token '" + tokenizer.reportCurrentToken() + "'.  Expected ',', '|', or ']'." );
            }
            else {
                expectAndConsumeToken(",");
            }
        }

        return head;
    }

    private char getClosingBracket(char openingBracketChar) {
        switch (openingBracketChar) {
                case '(':
                    return ')';
                case '{':
                    return '}';
                case '[':
                    return ']';
            default:
                return 0;
            }
    }

	/**
         * Read a list of terms. If argumentsMustBeTyped=true, these arguments
         * must be typed (e.g., human:John).
         *
         * @param argumentsMustBeTyped
         * @return A list of terms.
         * @throws ParsingException
         */
//	private NamedTermList processListOfTerms(boolean argumentsMustBeTyped) throws ParsingException, IOException {
//		// Have read the open parenthesis before this is called.
//		List<Term> args             = new ArrayList<Term>(2);
//		int        tokenRead        = getNextToken();
//		int        leftParenCounter = 0;
//		Term       term;
//		String        argumentName  = null; // Used with parsingWithNamedArguments.
//		List<String>       argNames = (parsingWithNamedArguments ? new ArrayList<String>(2) : null);
//		if (debugLevel > 2) { Utils.println("% entering processListOfTerms (PLT)"); }
//		while (leftParenCounter > 0 || (tokenRead != ')' && tokenRead != '}') && tokenRead != ']') { // Continue until closing parenthesis found.
//			term = null;
//			switch (tokenRead) {
//				case '[':
//                    term = processList(argumentsMustBeTyped, 1, false);
//                    break;
//				case '(':
//				case '{': leftParenCounter++; break;
//				case ')':
//				case '}': leftParenCounter--; break;
//				default:  argumentName = reportLastItemRead(); // Hold on to the current item, in case an equal sign follows.
//						  boolean needToProcessListOfTerms = false; // TODO logic seems overly complex, so clean up
//						  boolean closeWithRightParen      = false;
//
//                          if (parsingWithNamedArguments && peekThisChar('=')) { // TODO don't need this parsingWithNamedArguments flag, but keep around for a bit (8/26/08).
//					    	  if (debugLevel > 2) { Utils.println("% PLT found argumentName=" + argumentName); }
//					    	  if      (peekThisChar('[')) { needToProcessListOfTerms = true; }
//					    	  else if (peekThisChar('(')) { needToProcessListOfTerms = true; closeWithRightParen = true; } // Allow '()' to wrap LISTs in named arguments.
//					    	  else {  tokenRead = getNextToken(); }
//						  } else {
//							  if (parsingWithNamedArguments && debugLevel > 2) { Utils.println("% PLT: A equal sign was not found, so unset argumentName"); }
//							  argumentName = null;  // A equal sign was not found, so unset.
//                          }
//
//                          if ( needToProcessListOfTerms ) {
//                              term = processList(argumentsMustBeTyped, 1, closeWithRightParen);
//                          }
//                          else {
//                              term = processRestOfTerm(tokenRead, argumentsMustBeTyped);
//                          }
//
//                          if (peekIfAtInfixMathSymbol()) {
//							  tokenizer.pushBack();
//							  if (debugLevel > 2) { Utils.println("% PLT processMathExpression: " + term); }
//					    	  term = processMathExpression(term, argumentsMustBeTyped, false);
//						  }
//						  // replaced 5/09 by JWS with a better method:
//						  //if (argumentName != null) {
//						  // replaced 5/09 by JWS with a better method: term = stringHandler.assignTermName(term, argumentName);
//						  //  if (debugLevel > 2) { Utils.println("   named arg: " + argumentName + "=" + term); }
//						  //}
//			}
//			if (leftParenCounter < 0)              { throw new ParsingException("Have too many left parentheses."); }
//			if (args != null && args.size() > 100) { throw new ParsingException("Have read 100 arguments for a term.  Maybe a closing parenthesis is missing?"); }
//			if (term != null) {
//				args.add(term);
//				if (parsingWithNamedArguments) {
//					if (argNames == null) { argNames = new ArrayList<String>(args.size()); }
//					argNames.add(argumentName);
//				}
//				checkForComma(true, true, false, "processing a list of terms");
//			}
//			tokenRead = getNextToken();
//		}
//		if (parsingWithNamedArguments && Utils.getSizeSafely(args) > 1) {
//			if (debugLevel > 2) { Utils.println("% processListOfTerms: preparing to handle lists,\n%  args  = " + args + "\n%  names = " + argNames); }
//			// Because the silly IL language has a weird way of dealing with lists, 'correct' for that here.
//			// Specifically, instead of
//			//		p(a=1, b=[1,2,3], c=true)
//			// IL has
//			//	    p(a=1, b=1,2,3, c=true)
//			// So look for some unnamed args, and merge unto a CONS list.
//
//			// First see if any 'unnamed' arguments.
//			int foundUnnamed = 0;
//			int foundNamed   = 0;
//			int numbArgs = Utils.getSizeSafely(args);
//			for (int i = 0; i < numbArgs; i++) {
//				if (argNames.get(i) == null) { foundUnnamed++; } else { foundNamed++; }
//				if (debugLevel > 3) { Utils.println("   i = " + i + " name[i] = '" + argNames.get(i) + "' foundUnnamed = " + foundUnnamed + " foundNamed = " + foundNamed); }
//			}
//			if (foundUnnamed > 0 && foundNamed < 1) { // All in one unnamed list.
//				List<Term>   newArgs  = new ArrayList<Term>(  numbArgs / 2);
//				List<String> newNames = new ArrayList<String>(1);
//				newNames.add("anonymous");
//				newArgs.add(ConsCell.convertListToConsCell(stringHandler, args));
//				if (debugLevel > 2) { Utils.println("% Resetting (v1) NamedTermList:\n%  args  = " + args + " -> " + newArgs +"\n%  names = " + argNames + " -> " + newNames); }
//				args     = newArgs;
//				argNames = newNames;
//				//Utils.waitHere("Why no names???");
//			}
//			if (foundUnnamed > 0 && foundNamed > 0) { // In no unnamed, then fine as is (i.e., no need to create lists).
//				List<Term>   newArgs  = new ArrayList<Term>(  numbArgs - foundUnnamed);
//				List<Term>   holder   = new ArrayList<Term>(             foundUnnamed); // This will hold list items.
//				List<String> newNames = new ArrayList<String>(numbArgs - foundUnnamed);
//
//				boolean insideList = (argNames.get(0) == null); // See if starting in a list.
//				if (insideList) { newNames.add("anonymousList"); } // If so, give it a name.
//				for (int i = 0; i < numbArgs; i++) {
//					if (insideList) {
//						if (argNames.get(i) != null) {
//							if (debugLevel > 2) { Utils.println("%  List has ended at i=" + (i - 1)); }
//							insideList = false;
//							ConsCell cc = ConsCell.convertListToConsCell(stringHandler, holder);
//							newArgs.add(cc);
//							holder.clear();
//						} else { // Otherwise just collect items.
//							if (debugLevel > 2) { Utils.println("%  List continuing at i=" + i + " add item=" + args.get(i)); }
//							holder.add(args.get(i));
//						}
//					}
//					if (!insideList) { // NOT in a list.  Do NOT make an else-if since if the last list ended, we need to still process item i.
//						if (argNames.get(i) == null) {
//							Utils.waitHere("This should not happen due to peeking ahead.");
//						} else if ((i + 1) < numbArgs && argNames.get(i + 1) == null) { // Starting a list.
//							if (debugLevel > 2) { Utils.println("%  List starting at i=" + i + "  name=" + argNames.get(i) + " firstItem=" + args.get(i)); }
//							insideList = true;
//							holder.add(args.get(i)); // Hold on to the values, which will be put in a list.
//							newNames.add(argNames.get(i)); // Grab the name now.
//						} else { // Not in a list, so simply collect.
//							if (debugLevel > 2) { Utils.println("%  Non-list at i=" + i + "  name=" + argNames.get(i) + " value=" + args.get(i)); }
//							newArgs.add(args.get(i));
//							newNames.add(argNames.get(i));
//						}
//					}
//				}
//				if (insideList) {
//					if (debugLevel > 2) { Utils.println("% Still in a list when the arguments ended.  holder=" + holder); }
//					newArgs.add(ConsCell.convertListToConsCell(stringHandler, holder));
//				}
//				if (debugLevel > 2) { Utils.println("% Resetting (v2) NamedTermList:  args  = " + args + " -> " + newArgs +"\n  names = " + argNames + " -> " + newNames); }
//				args     = newArgs;
//				argNames = newNames;
//			}
//		}
//		if (debugLevel > 2) { Utils.println("% Returning a NamedTermList:\n%  args  = " + args + "\n%  names = " + argNames); }
//		return new NamedTermList(args, argNames);
//	}

	/**
         * Is the current token an indicator of a type specification? E.g., see TypeSpec.isaModeSpec for the full list.
         *
         * @return Whether the current token is a type specification.
         * @throws IOException
         */
	private boolean atTypeSpec() throws IOException {
		int tokenRead = tokenizer.ttype();
		if (tokenRead == '+' || tokenRead == '-') {
			if (tokenizer.prevToken() == '\\') { return false; } // Currently at the ISO standard, but semi-weirdly named, predicate '\+'.
			// If '+' or '-' need to see if the next item is a string of digits.
			int nextToken  = getNextToken();
			if (nextToken == StreamTokenizer.TT_WORD && isAllDigits(tokenizer.sval())) {  // This '+' or '-' is a sign in front of some digits.
				tokenizer.pushBack();
				return false;
			}
			if (nextToken == StreamTokenizer.TT_WORD && atInfinity()) { // Have +inf or -inf, which is not a type spec for type 'inf'.
				tokenizer.pushBack();
				return false;
			}
			tokenizer.pushBack();
			return true;
		}
		return TypeSpec.isaModeSpec((char) tokenRead);
	}

	private TypeSpec getTypeSpec(int tokenRead, StreamTokenizerJWS tokenizer) throws ParsingException, IOException {
		char modeAsChar = (char)tokenRead;
		int nextTokenRead = getNextToken();
		if (nextTokenRead != StreamTokenizer.TT_WORD) { throw new ParsingException("Expecting a type in a typed term (e.g., 'human' in '+human:John'), but instead got: '" + reportLastItemRead() + "'."); }
		return new TypeSpec(modeAsChar, tokenizer.sval(), stringHandler);
	}

	// At one time this was being considered for sharing as a utility, which is why it is a static.
	// But HandleFOPCstrings.getNumericConstant handles converting to int's when appropriate.
	protected static NumericConstant convertToNumericConstant(HandleFOPCstrings stringHandler, TypeSpec typeSpec, double value) {
		return stringHandler.getNumericConstant(typeSpec, value);
	}

	   // Terms can be wrapped in parentheses.
    private Term processTerm(boolean argumentsMustBeTyped) throws ParsingException, IOException {
        int tokenRead = getNextToken();
        switch (tokenRead) {
            case '(': // Handle parentheses.
                NamedTermList terms = processListOfTerms('(', argumentsMustBeTyped);
                List<Literal> literals = new ArrayList<Literal>();
                for (Term term : terms.getTerms()) {
                    literals.add(term.asLiteral());
                }
                return stringHandler.getSentenceAsTerm(stringHandler.getClause(literals, null), "");
            case '{':
                return processTerm(argumentsMustBeTyped, 1);
            case '[': // Process a list.
                return processConsCellList(argumentsMustBeTyped);
            case '\\': // Could be \+().
            case '\'':
            case '"':
            case '-':
            case '+':
            case '=':
            case '#': // Have to include the possible type specs here...
            case '&': // Have to include the possible type specs here...
            case '*': // Have to include the possible type specs here...
            case '^': // Have to include the possible type specs here...
            case ':': // Have to include the possible type specs here...
            case '$': // Have to include the possible type specs here...
            case '@': // Have to include the possible type specs here...
            case '`': // Have to include the possible type specs here...
            case '>': // Have to include the possible type specs here...
            case StreamTokenizer.TT_WORD:
                Term result = processRestOfTerm(tokenRead, argumentsMustBeTyped);
                if ( checkForOperator() ) {
                    result = processMathExpression(result, argumentsMustBeTyped, false);
                }
                return result;
            default:
            	if (TypeSpec.isaModeSpec((char) tokenRead)) { // TODO - clean up so this code isn't duplicated with the lines immediately above.
                    result = processRestOfTerm(tokenRead, argumentsMustBeTyped);
                    if ( checkForOperator() ) {
                        result = processMathExpression(result, argumentsMustBeTyped, false);
                    }
                    return result;            		
            	}
                throw new ParsingException("Reading a term and expected a left parenthesis, a minus or plus sign (etc), or a token, but instead read: '" + reportLastItemRead() + "'.");
        }
    }

	private Term processTerm(Term termSoFar, boolean argumentsMustBeTyped, int leftParensCount) throws ParsingException, IOException {
		if (leftParensCount < 0) { throw new ParsingException("Have too many right parentheses after " + termSoFar); }
		int tokenRead = getNextToken();
		switch (tokenRead) {
			case '(':
			case '{':
			case '[':
				return processTerm(termSoFar, argumentsMustBeTyped, (leftParensCount + 1));
			case ')':
			case '}':
			case ']':
				if (leftParensCount == 0) { return termSoFar; }
				return processTerm(termSoFar, argumentsMustBeTyped, (leftParensCount - 1));
			case StreamTokenizer.TT_WORD:
			default: throw new ParsingException("Expecting a parentheses, but read unexpected character: '" + reportLastItemRead() + "'.");
		}
	}

	private Term processTerm(boolean argumentsMustBeTyped, int leftParensCount) throws ParsingException, IOException {
		if (leftParensCount < 0) { throw new ParsingException("Have too many right parentheses."); }
		int tokenRead = getNextToken();
		switch (tokenRead) {
			case '(':
			case '{':
				return processTerm(argumentsMustBeTyped, (leftParensCount + 1));
			case '\\': // Could be \+().
			case StreamTokenizer.TT_WORD:
				Term result = processRestOfTerm(tokenRead, argumentsMustBeTyped);
				if (leftParensCount == 0) { return result; }
				return processTerm(result, argumentsMustBeTyped, leftParensCount);
			default: throw new ParsingException("Expecting a literal, but read unexpected character: '" + reportLastItemRead() + "'.");
		}
	}

	/**
	 * A typeSpec can be followed with a !k or $k.  The former means the predicate "wrapping" this argument is true for EXACTLY k settings of this argument.  The latter is similar, except it the predicate is true for AT MOST k settings.
	 *
	 * @param typeSpec
	 * @throws ParsingException
	 */
	private void checkForLimitOnNumberOfTrueSettings(TypeSpec typeSpec) throws ParsingException, IOException {
		if (typeSpec == null) { return; }
		if (checkAndConsume('!')) {
			try {
				int counter = readInteger();
				if (counter <= 0) { throw new ParsingException("Expecting to read a positive integer here, but read: " + counter); }
				typeSpec.truthCounts = counter;
			}
			catch (Exception e) {
				typeSpec.truthCounts = 1; // k=1 can be left implicit.
			}
		}
		else if (checkAndConsume('$')) {
			try {
				int counter = readInteger();
				if (counter <= 0) { throw new ParsingException("Expecting to read a positive integer here, but read: " + counter); }
				typeSpec.truthCounts = -counter;
			}
			catch (Exception e) {
				typeSpec.truthCounts = -1; // k=1 can be left implicit.
			}
		}
	}

	/**
         * Read the REST of a term. The first token read is provided. If
         * argumentsMustBeTyped=true, any arguments must be typed (e.g.,
         * human:John).
         *
         * @param tokenRead
         * @param argumentsMustBeTyped
         * @return A term, parsed in its entirety.
         * @throws ParsingException
         */
	private Term processRestOfTerm(int tokenRead, boolean argumentsMustBeTyped) throws ParsingException, IOException {
		return processRestOfTerm(tokenRead, argumentsMustBeTyped, false);
	}
	private Term processRestOfTerm(int tokenRead, boolean argumentsMustBeTyped, boolean calledFromInsideMathExpression) throws ParsingException, IOException {
		int      negate    = 1;
		TypeSpec typeSpec  = null;
		boolean  skippedOverPlusSign = false;

		if (debugLevel > 1) { Utils.println("PRT: processRestOfTerm: '" + reportLastItemRead() + "'."); }
		if (argumentsMustBeTyped || atTypeSpec()) { // Also look for OPTIONAL typed terms.
			typeSpec  = getTypeSpec(tokenRead, tokenizer);
			if (!checkAndConsume(':')) { // Just a type specification here, so done with the term.
				Term result = stringHandler.getAnonymousTerm(typeSpec);
				checkForLimitOnNumberOfTrueSettings(typeSpec);
				return result;
			}
			tokenRead = getNextToken();
		}
		if (atInfinity()) { return convertToNumericConstant(stringHandler, typeSpec, Double.POSITIVE_INFINITY); }
		if (atQuotedString(tokenRead)) {
			// Keep reading until end of string.
			/*
			Utils.println("atQuotedString: " + tokenizer.svalQuoted());
			String stringBody = tokenizer.svalQuoted();
			int new_tokenRead = getNextToken();
			while (new_tokenRead != tokenRead) {
				Utils.println("next token: " + tokenizer.reportCurrentToken());
				stringBody += tokenizer.reportCurrentToken();
				new_tokenRead = getNextToken();
			}
			*/
			Term sc = null;
			if (convertQuotedAllDigitStringsToNumericConstants) {
				sc = stringHandler.getStringConstantButCheckIfNumber(typeSpec, (char)tokenRead + tokenizer.svalQuoted() + (char)tokenRead, !stringHandler.keepQuoteMarks);
			} else {
				sc = stringHandler.getStringConstant(typeSpec, (char)tokenRead + tokenizer.svalQuoted() + (char)tokenRead, !stringHandler.keepQuoteMarks);
			}
		//	Term sc = stringHandler.getStringConstant(typeSpec, (char)tokenRead + stringBody + (char)tokenRead, !stringHandler.keepQuoteMarks);
			//Utils.waitHere(" keepQuoteMarks = " + stringHandler.keepQuoteMarks + ", sc = " + sc);
			return sc;
		}

		if (tokenRead == '-')  { // Have a minus sign.  Since this is a logical expression, can only be negating a number.
			negate    = -1;
			tokenRead = getNextToken();
			if (atInfinity()) { return convertToNumericConstant(stringHandler, typeSpec, Double.NEGATIVE_INFINITY); }
		}
		if (tokenRead == '+' && tokenizer.prevToken() != '\\') {  // Just a plus sign that can be ignored (note: we confirmed it isn't the built-in "\+" predicate).
			tokenRead = getNextToken();
			if (atInfinity()) { return convertToNumericConstant(stringHandler, typeSpec, Double.POSITIVE_INFINITY); }
			skippedOverPlusSign = true; // TODO Might want to loop over these, so -- (i.e., double negations) could be handled ...
		}
		if (!isaPossibleTermName(tokenRead)) { throw new ParsingException("Expecting a term or literal name but read: '" + reportLastItemRead() + "'."); }

		// See if the next word read can be viewed as an integer or double.
		if (debugLevel > 1) { Utils.println("process rest of term: have tokenRead = " + tokenRead); }
		double resultAsNumber = processNumber(tokenRead);
		if (Utils.isaNumber(resultAsNumber)) {
			return convertToNumericConstant(stringHandler, typeSpec, negate * resultAsNumber);
		}
		String wordRead = getPredicateOrFunctionName(tokenRead);
		if (negate == -1)        { throw new ParsingException("Read an unexpected '-' when parsing a term."); }
		if (skippedOverPlusSign) { throw new ParsingException("Read an unexpected '+' when parsing a term."); }
		if (checkAndConsume('(')) { // See if this is a function.
			FunctionName fName = stringHandler.getFunctionName(wordRead);
			List<Term>   arguments;
			List<String> names = null;
			// ONCE is really more of a connective than a predicate, but since it is the only prefix-based connective, treat it here.
			if (wordRead.equalsIgnoreCase("once")) { // A once() needs to have an argument that is an FOPC clause.
				Sentence sent = processFOPC_sentence(1); // No need to require once()'s that only have one argument, which was a common source of errors in Prolog anyway.
				Clause clause = convertSimpleConjunctIntoClause(sent, fName);
				arguments     = new ArrayList<Term>(  1);
				arguments.add(stringHandler.getSentenceAsTerm(clause, "once"));
				//names         = new ArrayList<String>(1);
				//names.add("onceArg");
			} else if (wordRead.equalsIgnoreCase("call")) {
				Term termForCall = processTerm(argumentsMustBeTyped); // This can be a variable here, but at evaluation time it needs to be a function, which will be converted to a literal and evaluated.
				if (!checkAndConsume(')') && !checkAndConsume('}') && !checkAndConsume(']')) { throw new ParsingException("Expecting a right parenthesis to close this " + wordRead + "()."); }
				arguments     = new ArrayList<Term>(  1);
				arguments.add(termForCall);
				//names         = new ArrayList<String>(1);
				//names.add("callArg");
			} else if (wordRead.equalsIgnoreCase("findAll") || wordRead.equalsIgnoreCase("all")   ||
				       wordRead.equalsIgnoreCase("bagOf")   || wordRead.equalsIgnoreCase("setOf")) { // A findAll(), etc. needs to have an SECOND argument that is an FOPC clause.
				Term termForFindall     = processTerm(argumentsMustBeTyped);
				if (!checkAndConsume(',')) { throw new ParsingException("Expecting a comma after '" + termForFindall + "' in a " + wordRead + "()."); }
				Sentence sentenceForFindAll = processFOPC_sentence(0, true);
				if (!checkAndConsume(',')) { throw new ParsingException("Expecting a comma after '" + termForFindall + "' and '" + sentenceForFindAll + "' in a " + wordRead + "()."); }
				Term listForFindAll     = processTerm(argumentsMustBeTyped);
				if (!checkAndConsume(')') && !checkAndConsume('}') && !checkAndConsume(']')) { throw new ParsingException("Expecting a right parenthesis to close this " + wordRead + "()."); }
				Sentence implicitImplication = stringHandler.getConnectedSentence(sentenceForFindAll, stringHandler.getConnectiveName("->"), stringHandler.getTermAsLiteral(termForFindall)); //stringHandler.getLiteral(stringHandler.getPredicateName("implictHead")));
				List<Clause> clauses = implicitImplication.convertToClausalForm();
				if (clauses.size() != 1) { throw new ParsingException("The body of a findAll(), etc. needs to be a simple clause.  You provided: " + sentenceForFindAll); }
				Clause clause = clauses.get(0);
				if (clause.posLiterals == null) { Utils.error("Renamed posList = null in " + implicitImplication + " and " + clause); }
				TermAsLiteral renamedHead =  (TermAsLiteral) clause.posLiterals.get(0);
				if (renamedHead == null) { Utils.error("Renamed head = null in " + implicitImplication + " and " + clause); }
				//Utils.println("Renamed head = '" + renamedHead + "' in '" + implicitImplication + "' and '" + clause + "' stringHandler = " + stringHandler + ".");
				Term termForFindall2 = renamedHead.term; // Need to get this so variable renaming is consistent.
				if (!clause.isDefiniteClause()) { throw new ParsingException("The body of a findAll(), etc. needs to be a conjunction ('and') of literals.  You provided: " + sentenceForFindAll); }
				clause.posLiterals = null; // No need to keep the "implictHeadForFindAll" around.  The resolution theorem prover "knows" it is implicitly there.
				arguments = new ArrayList<Term>(  3);
				arguments.add(termForFindall2);
				arguments.add(stringHandler.getSentenceAsTerm(clause, wordRead));
				arguments.add(listForFindAll);
				//names     = new ArrayList<String>(3);
				//names.add(wordRead);
				//names.add("body");
				//names.add("collector");
				/*
				Utils.println(" termForFindall     = " + termForFindall);
				Utils.println(" termForFindall2    = " + termForFindall2);
				Utils.println(" sentenceForFindAll = " + sentenceForFindAll);
				Utils.println(" listForFindAll     = " + listForFindAll);
				Utils.println(" clauses            = " + clauses);
				*/
			}
			else if (wordRead.equalsIgnoreCase("countProofs") || wordRead.equalsIgnoreCase("countUniqueBindings")) { // A countProofs() needs to have an FIRST argument that is an FOPC clause.
					Sentence sentenceForCounter = processFOPC_sentence(0, true);
					if (!checkAndConsume(',')) { throw new ParsingException("Expecting a comma '" + sentenceForCounter + "' in a " + wordRead + "()."); }
					Term listForCounter     = processTerm(argumentsMustBeTyped);
					if (!checkAndConsume(')') && !checkAndConsume('}') && !checkAndConsume(']')) { throw new ParsingException("Expecting a right parenthesis to close this " + wordRead + "().  Recall countProofs(clause, N) and countUniqueBindingsclause, N) only have two arguments."); }
					Sentence implicitImplication = stringHandler.getConnectedSentence(sentenceForCounter, stringHandler.getConnectiveName("->"), stringHandler.getLiteral(stringHandler.getPredicateName("implictHead")));
					List<Clause> clauses = implicitImplication.convertToClausalForm();
					if (clauses.size() != 1) { throw new ParsingException("The body of a countProofs() or countUniqueBindings() needs to be a simple clause.  You provided: " + sentenceForCounter); }
					Clause clause = clauses.get(0);
					if (!clause.isDefiniteClause()) { throw new ParsingException("The body of a Counter(), etc. needs to be a conjunction ('and') of literals.  You provided: " + sentenceForCounter); }
					clause.posLiterals = null; // No need to keep the "implictHeadForCounter" around.  The resolution theorem prover "knows" it is implicitly there.
					arguments = new ArrayList<Term>(2);
					//names     = new ArrayList<String>(3);
					arguments.add(stringHandler.getSentenceAsTerm(clause, wordRead));
					arguments.add(listForCounter);
					//names.add(wordRead);
					//names.add("body");
					//names.add("counter");
			}
			else {
				 NamedTermList namedTermList = processListOfTerms('(', argumentsMustBeTyped); // This should suck up the closing parenthesis.
				 arguments = namedTermList.getTerms();
				 names     = namedTermList.getNames();
			}
			checkForLimitOnNumberOfTrueSettings(typeSpec); // Look for a training !k or $k.
			return stringHandler.getFunction(fName, arguments, names, typeSpec);
		}
		else if (!calledFromInsideMathExpression && peekIfAtInfixMathSymbol()) {
			tokenizer.pushBack();
			Term initialTerm = stringHandler.getVariableOrConstant(typeSpec, wordRead);
			Term mathExpression = processMathExpression(initialTerm, argumentsMustBeTyped, false);
			checkForLimitOnNumberOfTrueSettings(typeSpec);
			return mathExpression;
		}
		checkForLimitOnNumberOfTrueSettings(typeSpec);
		return stringHandler.getVariableOrConstant(typeSpec, wordRead);  // If the next character isn't an open parenthesis, then have a constant or a variable.
	}

	private boolean peekAheadForConnective() throws IOException {
		int tokenRead = getNextToken();
		String  currentWord  = tokenizer.reportCurrentToken();
		boolean result = ConnectiveName.isaConnective(currentWord);
		tokenizer.pushBack();
		return result;
	}

	private boolean peekIfAtInfixMathSymbol() throws IOException {
		int tokenRead = getNextToken();
		switch (tokenRead) {
			case '+':
			case '-':
			case '*':
			case '/': return true;
		}
		tokenizer.pushBack();
		return false;
	}

	private Clause convertSimpleConjunctIntoClause(Sentence sent, AllOfFOPC caller) throws ParsingException, IOException {
		Sentence implicitImplication = stringHandler.getConnectedSentence(sent, stringHandler.getConnectiveName("->"), stringHandler.getLiteral(stringHandler.getPredicateName("implictHead")));
		List<Clause> clauses = implicitImplication.convertToClausalForm();
		return convertlistOfSentencesIntoClause(clauses, sent, caller);
	}
	private Clause convertlistOfSentencesIntoClause(List<Clause> clauses, Sentence sent, AllOfFOPC caller) throws ParsingException, IOException {
		if (clauses.size() != 1) { throw new ParsingException("The body of a '" + caller + "' needs to be a simple clause.  You provided: " + sent); }
		Clause clause = clauses.get(0);
		      if (!clause.isDefiniteClause()) {
            throw new ParsingException("The body of a '" + caller + "' needs to be a conjunction ('and') of literals.  You provided: " + sent);
        }
        clause.posLiterals = null; // No need to keep the "implictHead" around.  The resolution theorem prover "knows" it is implicitly there.
		return clause;
	}

	/*
	 * 	[]                      = nil
	 *  [TermA]                 = consCell(TermA, nil);
	 *  [TermA | TermB]         = consCell(TermA, TermB)
	 *  [TermA, TermB]          = consCell(TermA, consCell(TermB, nil))
	 *  [TermA, TermB | Term C] = consCell(TermA, consCell(TermB, TermC))
	 *
	 */
	private ConsCell processList(boolean argumentsMustBeTyped, int leftParensCount, boolean closeWithRightParen) throws ParsingException, IOException {
		// When called, one or more OPENs of list (i.e., '[') have been encountered.
		// Utils.println("In processList: leftParensCount=" + leftParensCount);
		if (leftParensCount < 0) { throw new ParsingException("Have too many closing ]'s in a list."); }
		int tokenRead = getNextToken();
		switch (tokenRead) {
			case '[': // Need to process a new list, then cons it on the front of the rest of the list.
				ConsCell firstPart = processList(argumentsMustBeTyped, 1, false);
				Term    secondPart = processInsideConsCell(argumentsMustBeTyped, leftParensCount, false);
				return stringHandler.getConsCell(firstPart, secondPart, null);
			case ']': // Can "pop" the stack.
				if (tokenRead == ']' && closeWithRightParen) { throw new ParsingException("Expecting a ')', but read: '" + reportLastItemRead() + "'."); }
				if (leftParensCount == 1) { return stringHandler.getNil(); }
				return processList(argumentsMustBeTyped, (leftParensCount - 1), closeWithRightParen);
		    default:
				try { // Read the first term.
					Term  first = processRestOfTerm(tokenRead, argumentsMustBeTyped);
					// Read the rest of this list.
					Term  rest  = processInsideConsCell(argumentsMustBeTyped, 1, closeWithRightParen);
					// Make a cons cell.
					ConsCell firstCons;
                    if (rest == null) {
                        firstCons = stringHandler.getConsCell(first, null);
                    }
                    else {
                        firstCons = stringHandler.getConsCell(first, rest, null);
                    }
					if (leftParensCount == 1) { return firstCons; } // If only one level deep, done.
					// If not done, process the rest and cons the first item on the front.
					Term term = processInsideConsCell(argumentsMustBeTyped, (leftParensCount - 1), closeWithRightParen);
					return stringHandler.getConsCell(firstCons, term,  null);
                } catch (ParsingException e) {
                    throw e;
				} catch (Exception e) {
					throw new ParsingException("Expecting a term or a '[' or a ']', but read: '" + reportLastItemRead() + "'\nand received this exception: " + e);
				}
		}
	}

	/**
         * p([ [a], [[[b]]], [c | d] ]). Have read the first item in a cons
         * cell, e.g., 'a' in '[a, ...]' or in '[a | b]' or in '[a]'
         *
         * @param argumentsMustBeTyped
         * @param leftParensCount
         * @return TODO The second half of the cons cell?
         * @throws ParsingException
         */
	private Term processInsideConsCell(boolean argumentsMustBeTyped, int leftParensCount, boolean closeWithRightParen) throws ParsingException, IOException {
		int tokenRead = getNextToken();
		// Utils.println("processInsideConsCell:" + reportLastItemRead());
		switch (tokenRead) {
			case ',':
				return processList(argumentsMustBeTyped, leftParensCount, closeWithRightParen);
			case '|':
				Term term = processTerm(argumentsMustBeTyped);
				// Need to suck up the closing bracket.  Complain if not found.
				if (!checkAndConsume(']')) {
					throw new ParsingException("Expecting a ']' after a '| term' in a list, but read: '" + reportLastItemRead() + "'.");
				}
				if (leftParensCount == 1) { return term; }
				Term rest = processInsideConsCell(argumentsMustBeTyped, (leftParensCount - 1), closeWithRightParen);
				return stringHandler.getConsCell(term, rest, null);
		//	case ')':
		//	case '}':
		//		if (!closeWithRightParen) { throw new ParsingException("Processing inside a list and expecting a '|', ',' or ']', but read: '" + reportLastItemRead() + "'."); }
			case ']':
				if (tokenRead == ']' && closeWithRightParen) { throw new ParsingException("Expecting a ')', but read: '" + reportLastItemRead() + "'."); }
				if (leftParensCount == 1) { return stringHandler.getNil(); }
				return processInsideConsCell(argumentsMustBeTyped, (leftParensCount - 1), closeWithRightParen);
			default: throw new ParsingException("Processing inside a list and expecting a '|', ',' or ']', but read: '" + reportLastItemRead() + "'.");
		}
	}

	private boolean atQuotedString(int token) {
		return token == '"' || (FileParser.allowSingleQuotes && token == '\'');
	}

	/**
	 * If reading a string, possibly quoted, return it.  If not a string, complain if requested; otherwise return null.
	 *
	 * @param tokenRead
	 * @param complainIfNotString
	 * @return The parsed string.
	 * @throws ParsingException
	 */
	private String getPossiblyQuotedString (int tokenRead, boolean complainIfNotString) throws ParsingException, IOException {
		if (atQuotedString(tokenRead)) {
			return (char)tokenRead + tokenizer.svalQuoted() + (char)tokenRead;
		}
		try {
			Double result = processNumber(tokenRead);
			if (!result.isNaN()) { return Double.toString(result); }
		} catch (Exception e) {
		}

		if (tokenRead != StreamTokenizer.TT_WORD) {
			if (complainIfNotString) { throw new ParsingException("Expecting the name of a type, but got: " + reportLastItemRead() + "."); }
			return null;
		}
		return tokenizer.sval();
	}

	/**
	 * Default to not complaining if not currently at a string.
	 *
	 * @param tokenRead
	 * @return The parsed string.
	 */
	@SuppressWarnings("unused")
	private String getPossiblyQuotedString (int tokenRead) throws ParsingException, IOException {
		return getPossiblyQuotedString(tokenRead, false);
	}

	/**
         * Read the variables of a quantifier. If only one, it need not be
         * wrapped in parentheses.
         *
         * @return A list of variables.
         * @throws ParsingException
         */
	private List<Variable> readListOfVariables() throws ParsingException, IOException {
		int tokenRead = getNextToken();
		switch (tokenRead) {
			case '(':
			case '{':
			case '[':
                List<Term>    terms = processListOfTerms((char)tokenRead, false).getTerms();
                List<Variable> vars = new ArrayList<Variable>(terms.size());
                for (Term t : terms) {
                    if (t instanceof Variable) { vars.add((Variable) t); }
                    else { throw new ParsingException("Expecting a list of VARIABLEs, but read this non-variable: '" + t + "' in " + terms + "."); }
                }
                return vars;
			case StreamTokenizer.TT_WORD: // Allow ONE variable to appear w/o parentheses.
				Term term = stringHandler.getVariableOrConstant(tokenizer.sval(), true); // These are NEW variables since they are those of a quantifier.
				// Utils.println("string = " + tokenizer.sval() + " and term = " + term);
				if (term instanceof Variable) {
					List<Variable> result = new ArrayList<Variable>(1);
					result.add((Variable) term);
					return result;
				}
				throw new ParsingException("Expecting a variable (for a quantifier), but read: '" + term + "'.");
			default:
                throw new ParsingException("Expecting a variable or a left parenthesis, but read: '" + reportLastItemRead() + "'.");
		}
	}

	// Note that NOT is also handled here.
    private ConnectiveName processPossibleConnective(int tokenRead) throws ParsingException, IOException {
    	switch (tokenRead) {
			case StreamTokenizer.TT_WORD:
				String candidate = tokenizer.sval();
				if (ConnectiveName.isaConnective(candidate)) {
					if (false && "v".equalsIgnoreCase(candidate) && checkAndConsume('(')) { // TODO - see if there is a space after the 'v' ... Allow 'v' (or 'V') to be a single-character predicate name.
						tokenizer.pushBack();
						return null;
					}
					if (ignoreThisConnective(false, candidate)) { return null; }
					return stringHandler.getConnectiveName(candidate);
				}
				return null;
			case '^':
			case '&':
			case ',':
			case '~': if (treatAND_OR_NOTasRegularNames) { return null; }
					  return stringHandler.getConnectiveName(String.valueOf((char)tokenRead));
			case '-':
				tokenRead = getNextToken();
				if (tokenRead == '>') { return stringHandler.getConnectiveName("->"); }
				tokenizer.pushBack();
				return null;
				//throw new ParsingException("Expecting the connective '->' but read: '-" + reportLastItemRead() + "'.");
			case '=':
				tokenRead = getNextToken();
				if (tokenRead == '>') { return stringHandler.getConnectiveName("=>"); }
				tokenizer.pushBack();
				return null;
				//throw new ParsingException("Expecting the connective '=>' but read: '-" + reportLastItemRead() + "'.");
			case ':':
				tokenRead = getNextToken();
				if (tokenRead == '=') { return stringHandler.getConnectiveName(":="); }
				if (tokenRead == '-') { return stringHandler.getConnectiveName(":-"); }
				tokenizer.pushBack();
				return null;
				//throw new ParsingException("Expecting the connective ':-' or ':=' but read: ':" + reportLastItemRead() + "'.");
			case '<':
				tokenRead      = getNextToken();
				if (tokenRead != '-' && tokenRead != '=') {
					tokenizer.pushBack();
					return null;
				}
				int tokenRead2 = getNextToken();
				if (tokenRead == '-' && tokenRead2 == '>') { return stringHandler.getConnectiveName("<->"); }
				if (tokenRead == '=' && tokenRead2 == '>') { return stringHandler.getConnectiveName("<=>"); }
				tokenizer.pushBack();
				tokenizer.pushBack();
				return null;
				// throw new ParsingException("Expecting the connective '<->' or '<=>' but read: ':" + tmp + reportLastItemRead() + "'.");
			case '\\':
				tokenRead = getNextToken();
				if (tokenRead == '+') { return stringHandler.getConnectiveName("\\+"); }
				tokenizer.pushBack();
				return null;
			default: return null;
		}
	}

	/**
	 * Read an FOPC sentence.
	 *
	 */
    private Sentence processFOPC_sentence(int insideLeftParenCount) throws ParsingException, IOException {
    	return  processFOPC_sentence(insideLeftParenCount, false);
    }
	private Sentence processFOPC_sentence(int insideLeftParenCount, boolean commaEndsSentence) throws ParsingException, IOException {
		List<AllOfFOPC> accumulator = new ArrayList<AllOfFOPC>(4);
		boolean         lookingForConnective = false;
		while (true) { // PFS = processFOPC_sentence
			int tokenRead = getNextToken();
			if (commaEndsSentence && insideLeftParenCount == 0 && tokenRead == ',') { // Sometimes want to read ONE argument as a sentence - e.g., the 2nd argument to findAll.
				Sentence resultComma = convertAccumulatorToFOPC(accumulator);
				if (debugLevel > 2) { Utils.println("PFS: Return @comma result: '" + resultComma + "' (with insideLeftParenCount=" + insideLeftParenCount + ")\n"); }
				tokenizer.pushBack();
				return resultComma;
			}
			if (debugLevel > 1) { Utils.println("PFS: process FOPC: '" + reportLastItemRead() + "' (with insideLeftParenCount=" + insideLeftParenCount + ")"); }
			ConnectiveName connective = processPossibleConnective(tokenRead);
			if (connective != null) { // OK to have NOT or '~' be the first item and OK to have any number of NOT's in a row.
            	if (debugLevel > 2) { Utils.println("PFS: read connective: " + connective); }
    			if (!lookingForConnective && accumulator.size() > 0 && !ConnectiveName.isaNOT(connective.name)) { throw new ParsingException("Encountered two logical connectives in a row: '" + accumulator.get(accumulator.size() - 1) + "' and '" + connective + "'."); }
            	if (accumulator.isEmpty() && !ConnectiveName.isaNOT(connective.name)) {  throw new ParsingException("Encountered '" + connective + "' as the FIRST connective."); }
            	accumulator.add(connective);
    			lookingForConnective = false;
            }
            else {
            	// First see if dealing with an in-fix predicate.
            	String peekAtNextWord = isInfixTokenPredicate(tokenRead);
            	if (peekAtNextWord != null) {
            		AllOfFOPC lastItemAdded = accumulator.get(accumulator.size() - 1);
            		accumulator.remove(accumulator.size() - 1);
            		if (lastItemAdded instanceof TermAsSentence) {
            			Sentence sInFix = processInfixLiteral(((TermAsSentence) lastItemAdded).term, peekAtNextWord);
            			accumulator.add(sInFix);
    				}
            		else { throw new ParsingException("Cannot handle '" + peekAtNextWord + "' after '" + lastItemAdded + "'."); }
            	}
            	else {
            		switch (tokenRead) {
            			case '(':
            			case '{':
            			case '[':
            				Sentence resultLeftParens = processFOPC_sentence(insideLeftParenCount + 1); // Parse up to the closing right parenthesis.
							accumulator.add(resultLeftParens);
							break;
            			case ')':
            			case '}':
            			case ']':
            				if (insideLeftParenCount == 0) {
            					tokenizer.pushBack(); // Push this back.  This right parenthesis closes an outer call.
            				}
            				Sentence resultLeftParen = convertAccumulatorToFOPC(accumulator);
            				if (debugLevel > 2) { Utils.println("PFS: Return @rightParen result: '" + resultLeftParen + "' (with insideLeftParenCount=" + insideLeftParenCount + ")\n"); }
            				return resultLeftParen;
            			case '.':
            			case ';':
            				tokenizer.pushBack(); // Push this back.  It might be used to close several quantifiers.  If doing a top-level call, that call can such this up.
            				Sentence resultEOL =  convertAccumulatorToFOPC(accumulator);
            				if (debugLevel > 2) { Utils.println("PFS: Return @EOL result: '" + resultEOL + "' (with insideLeftParenCount=" + insideLeftParenCount + ")\n"); }
            				return resultEOL;
            			case '!': // Prolog's 'cut'.
            				PredicateName pName = stringHandler.standardPredicateNames.cut;
            				Literal lit = stringHandler.getLiteral(pName);
            				accumulator.add(lit);
            				break;
            			case '+': // Could have something like '+5 < y'
            			case '-': // Or, more likely, '-5 < y'  Or this could be a "bare" weight on a sentence.
            				//Term firstTerm = processRestOfTerm(tokenRead, false);
            				//TermAsSentence termAsSent = new TermAsSentence(firstTerm);
            				//accumulator.add(termAsSent);
            				//break;
            			case '\\': // Might be \+().
            			case StreamTokenizer.TT_WORD:
            				Sentence s = processFOPC_sentenceFromThisToken(insideLeftParenCount);
            				accumulator.add(s);
            				break;
            			case ':':
            				throw new ParsingException("Unexpectedly read ':'.  The previous token might be a misspelling of a keyword.  Have accumulated these tokens: " + accumulator);
            			default:
                            throw new ParsingException("Expecting a part of an FOPC sentence, but read the unexpected character: '" + reportLastItemRead() + "'.");
            		}
            		if (lookingForConnective) { throw new ParsingException("Encountered two FOPC sentences in a row: '" + accumulator.get(accumulator.size() - 2) + "' and '" + accumulator.get(accumulator.size() - 1) + "'."); }
            	}
            	lookingForConnective = true;
            }
            if (debugLevel > 2) { Utils.println("PFS: FOPC-sentence accumulator: " + accumulator + " (insideLeftParenCount=" + insideLeftParenCount + ")" ); }
		}
	}

	private Sentence processFOPC_sentenceFromThisToken(int insideLeftParenCount) throws ParsingException, IOException {
		String currentWord = getPredicateOrFunctionName(); // This will only be called if reading a string (which might be representing a number).
		if (debugLevel > 1) { Utils.println("PFStoken: process FOPC from: '" + currentWord + "' (with insideLeftParenCount=" + insideLeftParenCount + ")"); }
		// Quantifiers are scoped to go to the next EOL unless parenthesis limit the scope.
		if (currentWord.equalsIgnoreCase("ForAll")) {
			List<Variable> variables = readListOfVariables();
			Sentence       body; // We'll end this either when parentheses are matched or EOL is hit.
			if (checkAndConsume('(') || checkAndConsume('{')) {
				body = processFOPC_sentence(0); // We'll end this when a right parenthesis is encountered.
				if (!checkAndConsume(')') && !checkAndConsume('}') && !checkAndConsume(']')) { throw new ParsingException("Expecting to find a right parenthesis closing: '" + currentWord + " " + variables + " " + body + "'."); }
			}
			else {
				body = processFOPC_sentence(0);
			}
			UniversalSentence uSent = stringHandler.getUniversalSentence(variables, body);
			stringHandler.unstackTheseVariables(variables);
			if (debugLevel > 2) { Utils.println("PFStoken: Return @ForAll result: '" + uSent + "' (with insideLeftParenCount=" + insideLeftParenCount + ")\n"); }
			return uSent;
		}
		else if (currentWord.equalsIgnoreCase("ThereExists") || currentWord.equalsIgnoreCase("Exists") || currentWord.equalsIgnoreCase("Exist")) { // Note: 'Exist' allowed since that is what Alchemy uses.
			List<Variable> variables = readListOfVariables();
			Sentence       body;
			if (checkAndConsume('(') || checkAndConsume('{')) {
				body = processFOPC_sentence(0); // We'll end this when a right parenthesis is encountered.
				if (!checkAndConsume(')') && !checkAndConsume('}') && !checkAndConsume(']')) { throw new ParsingException("Expecting to find a right parenthesis closing: '" + currentWord + " " + variables + " " + body + "'."); }
			}
			else {
				body = processFOPC_sentence(0);
			}
			ExistentialSentence eSent = stringHandler.getExistentialSentence(variables, body);
			stringHandler.unstackTheseVariables(variables);
			if (debugLevel > 2) { Utils.println("PFStoken: Return @Exists result: '" + eSent + "' (with insideLeftParenCount=" + insideLeftParenCount + ")\n"); }
			return eSent;
		}
        else {
            // See if this is an in-fix literal.
            Term possibleTerm = processRestOfTerm(tokenizer.ttype(), false);
            int tokenRead = getNextToken();
            String peekAtNextWord = isInfixTokenPredicate(tokenRead);
            if (peekAtNextWord != null) { // Handle 'is' and { <, >, >=, <=, == }.
                return processInfixLiteral(possibleTerm, peekAtNextWord);
            }
            tokenizer.pushBack(); // Undo the getNextToken() that checked for an infix predicate.

            if (possibleTerm instanceof NumericConstant) { // If reading a number and not in an in-fix (e.g., '5 <= 6') then interpret as a weighted sentence.
                if (debugLevel > 2) { Utils.println("PFStoken: Processing this number: " + possibleTerm); }
                Sentence sent;
                if (insideLeftParenCount > 0) {
                    if (insideLeftParenCount > 1) { throw new ParsingException("Possibly too many left parentheses before a weight."); }
                    if (checkAndConsume(')') || checkAndConsume('}') || checkAndConsume(']')) { // The parentheses wrap the number.
                        checkAndConsume(','); // Allow an optional comma after the number.
                        sent = processFOPC_sentence(0);
                    } else {
                        checkAndConsume(','); // Allow an optional comma after the number.
                        sent = processFOPC_sentence(insideLeftParenCount); // The parentheses wrap something like this: '(weight FOPC)'
                    }
                } else {
                       checkAndConsume(','); // Allow an optional comma after the number.
                       sent = processFOPC_sentence(0); // No parentheses involved.
                }
                sent.setWeightOnSentence(((NumericConstant) possibleTerm).value.doubleValue());
                return sent;
            } else {
                return convertTermToLiteral(possibleTerm);
            }
        }
	}

	private Literal convertTermToLiteral(Term term) throws ParsingException, IOException {
		if (term instanceof Function) {
			PredicateName pName = stringHandler.getPredicateName(((Function) term).functionName.name);
			Function      f     = (Function) term;
			return stringHandler.getLiteral(pName, f.getArguments(), f.getArgumentNames());
		}
        else if (term instanceof StringConstant) {  // This is an argument-less predicate.
			PredicateName pName = stringHandler.getPredicateName(((StringConstant) term).getName());
			return stringHandler.getLiteral(pName);
		}
        else if (term instanceof Variable) {  // This is an argument-less predicate.
			PredicateName pName = stringHandler.standardPredicateNames.implicit_call;
			return stringHandler.getLiteral(pName, Collections.singletonList(term));
		}
        else if ( term instanceof LiteralAsTerm ) {
            LiteralAsTerm lat = (LiteralAsTerm)term;
            return lat.itemBeingWrapped;
        }
		throw new ParsingException("Encountered '" + term + "' (" + term.getClass() + "), but was expecting a LITERAL");
	}


	private List<Term> convertToListOfTerms(Collection<Variable> collection) {
		if (collection == null) { return null; }
		List<Term> results = new ArrayList<Term>(collection.size());
		for (Variable var : collection) { results.add(var); }
		return results;
	}


    private List<Literal> convertTermsToLiterals(List<Term> terms) throws ParsingException, IOException {
        List<Literal> literals = new ArrayList<Literal>(terms.size());
        for (int i = 0; i < terms.size(); i++) {
            literals.add( convertTermToLiteral(terms.get(i)));
        }
        return literals;
    }

	// A simplistic way to get around the use of '-' as a 'dash.'
	public String convertDashToUnderscore(String str) {
		if (str == null || str.length() < 3) { return str; }
		boolean foundDashToUnderscore = false;
		boolean haveSeenLetter        = false;
		StringBuilder result = new StringBuilder(str.length());
		char a = ' ';
		char b = str.charAt(0);
		char c = str.charAt(1);
		result.append(b); // If the first char is a '-' it is ok (i.e., it must be a minus sign).
		for (int i = 1; i < str.length() - 1; i++) {
			if (Character.isLetter(a) && !haveSeenLetter) { haveSeenLetter = true; }
			a = b;
			b = c;
			c = str.charAt(i + 1);
			// A '-' is OK after an equals sign, after white space (bug if space is escaped?), or between two digits that have not been proceeded by a letter.
			if (b != '-' || a == '=' || Character.isWhitespace(a) || (!haveSeenLetter && !foundDashToUnderscore && Character.isDigit(a) && Character.isDigit(c))) {
				result.append(b);    // if (b == '-') Utils.println("--KEEP-->"   + a + b + c);
			} else if (b == '-' && i > 1 && Character.isDigit(str.charAt(i - 2)) && (a == 'E' || a == 'e') && Character.isDigit(c)) {
				result.append(b); // Assume this is a minus sign in scientific notation.
			} else {
				if (!foundDashToUnderscore) { foundDashToUnderscore = true; }
				result.append('_');	 //               Utils.println("--CHANGE-->" + a + b + c);
			}
			if (b == '=' || (a != '\\' && Character.isWhitespace(b))) {
				foundDashToUnderscore = false;  // Reset if '=' or whitespace found.  Also handle an overriding backslash before the whitespace.
				haveSeenLetter        = false;
			}
		}
		result.append(str.charAt(str.length() - 1));
		//Utils.println("ORIGINAL");
		//Utils.println(str);
		//Utils.println("CONVERTED");
		//Utils.println(result.toString());
		return result.toString();
	}

    private class ReturnValue<T> {
        T value;
    }

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		args = Utils.chopCommentFromArgs(args);
		Utils.createDribbleFile("dribble" + Utils.defaultFileExtensionWithPeriod);
		HandleFOPCstrings stringHandler = new HandleFOPCstrings();
		FileParser        parser        = new FileParser(stringHandler);

		parser.readFOPCfile("debugParser" + Utils.defaultFileExtensionWithPeriod);
		Utils.waitHere();

		stringHandler.useStdLogicNotation();

		//List<Sentence> sentences = parser.readFOPCfile(args[0] + Utils.defaultFileExtensionWithPeriod);
		//List<Sentence> sentences = parser.readFOPCstream("(A v B v C) ^ (D v E v F) ^ (G v H) => Concept;");
	//	List<Sentence> sentences = parser.readFOPCstream("P1 v P2 v ... v Pn v NOT(N1 v N2 v Nm)  => Concept;");
	//	List<Sentence> sentences = parser.readFOPCstream("((P1 v P2 v Pn) and NOT(N1 v N2 v Nm))  => Concept;");
	//	List<Sentence> sentences = parser.readFOPCstream("((P1 v P2 v Pn) and Not_N1 and Not_N2 and Not_Nm)  => Concept;");
		// Eight combinations of: {combine with AND or OR} x {negate or not} x {predict concept or negation of concept}
		List<Sentence> sentences1 = parser.readFOPCstream("(    P1 ^     P2 ^     P3)  =>     Concept;");
		List<Sentence> sentences2 = parser.readFOPCstream("(    P1 ^     P2 ^     P3)  => not Concept;");
		List<Sentence> sentences3 = parser.readFOPCstream("(not P1 ^ not P2 ^ not P3)  =>     Concept;");
		List<Sentence> sentences4 = parser.readFOPCstream("(not P1 ^ not P2 ^ not P3)  => not Concept;");
		List<Sentence> sentences5 = parser.readFOPCstream("(    P1 v     P2 v     P3)  =>     Concept;");
		List<Sentence> sentences6 = parser.readFOPCstream("(    P1 v     P2 v     P3)  => not Concept;");
		List<Sentence> sentences7 = parser.readFOPCstream("(not P1 v not P2 v not P3)  =>     Concept;");
		List<Sentence> sentences8 = parser.readFOPCstream("(not P1 v not P2 v not P3)  => not Concept;");
		// Might want to edit: public  static final int defaultNumberOfLiteralsPerRowInPrintouts = 1;
		for (Sentence sentence : sentences1) {
			Utils.println("\nFROM:\n  " + sentence.toPrettyString() + ";\n TO:");
			for (Clause c : sentence.convertToClausalForm()) {
				Utils.println("  " + c.toPrettyString(Integer.MAX_VALUE) + ";");
			}
		}
		for (Sentence sentence : sentences2) {
			Utils.println("\nFROM:\n  " + sentence.toPrettyString() + ";\n TO:");
			for (Clause c : sentence.convertToClausalForm()) {
				Utils.println("  " + c.toPrettyString(Integer.MAX_VALUE) + ";");
			}
		}
		for (Sentence sentence : sentences3) {
			Utils.println("\nFROM:\n  " + sentence.toPrettyString() + ";\n TO:");
			for (Clause c : sentence.convertToClausalForm()) {
				Utils.println("  " + c.toPrettyString(Integer.MAX_VALUE) + ";");
			}
		}
		for (Sentence sentence : sentences4) {
			Utils.println("\nFROM:\n  " + sentence.toPrettyString() + ";\n TO:");
			for (Clause c : sentence.convertToClausalForm()) {
				Utils.println("  " + c.toPrettyString(Integer.MAX_VALUE) + ";");
			}
		}
		for (Sentence sentence : sentences5) {
			Utils.println("\nFROM:\n  " + sentence.toPrettyString() + ";\n TO:");
			for (Clause c : sentence.convertToClausalForm()) {
				Utils.println("  " + c.toPrettyString(Integer.MAX_VALUE) + ";");
			}
		}
		for (Sentence sentence : sentences6) {
			Utils.println("\nFROM:\n  " + sentence.toPrettyString() + ";\n TO:");
			for (Clause c : sentence.convertToClausalForm()) {
				Utils.println("  " + c.toPrettyString(Integer.MAX_VALUE) + ";");
			}
		}
		for (Sentence sentence : sentences7) {
			Utils.println("\nFROM:\n  " + sentence.toPrettyString() + ";\n TO:");
			for (Clause c : sentence.convertToClausalForm()) {
				Utils.println("  " + c.toPrettyString(Integer.MAX_VALUE) + ";");
			}
		}
		for (Sentence sentence : sentences8) {
			Utils.println("\nFROM:\n  " + sentence.toPrettyString() + ";\n TO:");
			for (Clause c : sentence.convertToClausalForm()) {
				Utils.println("  " + c.toPrettyString(Integer.MAX_VALUE) + ";");
			}
		}

		/*
		Utils.println("\nRead these sentences:\n");
		if (sentences != null) for (Sentence s : sentences) {
			Utils.println("  "   + s + ".");
			Utils.println("    " + Clause.toPrettyStringlistOfSentences("     ", s.convertToClausalForm()) + ".\n");
		}

		StringConstant constant = (StringConstant) stringHandler.getVariableOrConstant("dog");
		List<Type> types = stringHandler.getTypesOfConstant(constant, false);
		if (types == null) {
			types = new ArrayList<Type>(1);
			types.add(stringHandler.getIsaType(constant.getName()));
		}
		List<Constant> allInstances = new ArrayList<Constant>(16);
		for (Type type : types) {
			List<Constant> results = stringHandler.getAllInstances(type);
			if (results != null) { allInstances.addAll(results); }
		}
		Utils.println("\n\ngetAllInstances(" + constant + "/" + types + ") = " + allInstances);
		*/
	}
	/**
	 * @param numberOfPrecomputeFiles the numberOfPrecomputeFiles to set
	 */
	public void setNumberOfPrecomputeFiles(int numberOfPrecomputeFiles) {
		this.numberOfPrecomputeFiles = numberOfPrecomputeFiles;
	}
	/**
	 * @return the numberOfPrecomputeFiles
	 */
	public int getNumberOfPrecomputeFiles() {
		return numberOfPrecomputeFiles;
	}
}
