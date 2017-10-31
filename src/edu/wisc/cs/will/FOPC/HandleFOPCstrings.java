/**
 *
 */
package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.ILP.ClauseOptimiser;
import edu.wisc.cs.will.ResThmProver.VariantClauseAction;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import static edu.wisc.cs.will.ResThmProver.VariantClauseAction.*;

import edu.wisc.cs.will.Utils.Utils;
import java.util.Arrays;
import static edu.wisc.cs.will.Utils.MessageType.*;

/**
 * @author shavlik
 *
 * The class handles converting from strings to instances.
 * It also handles the 'isa' hierarchy (hetrarchy, really) of types and the specification of ranges of variables.
 *
 */
public final class HandleFOPCstrings implements CallbackRegister {

    public final StandardPredicateNames standardPredicateNames;

	protected final static int debugLevel   =   0; // Used to control output from this project (0 = no output, 1=some, 2=much, 3=all).
	protected              int warningCount =   1;
	protected final static int maxWarnings  = 100;
	public                 int exceptionCount     =   1; // These should be used when something is caught, and we don't want to print
	public    final static int exceptionCountMax  = 100; // the warning an excessive number of times.

	private         static int countOfStringHandlers = 0;
	
	public  int     prologCounter = 0, prologCounterB = 0, prologCounterC = 0, prologCounterD = 0, prologCounterE = 0; // These are special variables accessible by setCounter/1 and incrCounter/2 and incrCounter/3 from Prolog.  Meant for advanced use only.

	public  boolean dontPrintUnlessImportant = false;

	private boolean ignoreCaseOfStringsOtherThanFirstChar = false; // If this is ever set, strange bugs can occur.
	public  boolean cleanFunctionAndPredicateNames        = false; // Check for hyphens and spaces.  DO NOT SET UNTIL AFTER LIBRARIES ARE LOADED.
	public  boolean keepQuoteMarks                        = false; // Set to true if quote marks on string constants should be preserved.  NOTE: if true, then strings with quote marks will NOT be cleaned regardless of any other setting.
	private boolean defaultValue_cleanStringConstants     = true;  // If false, will not clean and will always wrap in quote marks EVEN IF NO QUOTES ORIGINALLY.
	public  boolean alwaysUseParensForInfixFunctions      = false; // Useful for debugging the parser, and possibly for safely writing out expressions.

	public boolean printTypedStrings     = false; // If set to true, then Terms will have their types printed.
	public boolean printVariableCounters = false; // If set to true, then variables will have their counters printed.

	public String  precompute_file_prefix = ""; // Allow overriding of these.
	public String  precompute_file_postfix = ".txt";
	public String  precompute_assignmentToTempVar1 = "UNASSIGNED_precompute_assignmentToTempVar1";
	public String  precompute_assignmentToTempVar2 = "UNASSIGNED_precompute_assignmentToTempVar2";
	public String  precompute_assignmentToTempVar3 = "UNASSIGNED_precompute_assignmentToTempVar3";

	public String  import_file_prefix  = ""; // Allow overriding of these.
	public String  import_file_postfix = ".txt";
	public String  import_assignmentToTempVar1 = "UNASSIGNED_import_assignmentToTempVar1";
	public String  import_assignmentToTempVar2 = "UNASSIGNED_import_assignmentToTempVar2";
	public String  import_assignmentToTempVar3 = "UNASSIGNED_import_assignmentToTempVar3";
	public String  FACTS   = "FACTS_UNASSIGNED";  // The MachineReading project uses these, for BOTH import and precompute.
	public String  PRECOMP = "PRECOMP_UNASSIGNED";
	public String  SWD     = "SWD_UNASSIGNED";    // SWD = ScratchWorkingDir (do NOT use SCRATCH because we already use MYSCRATCHDIR).
	public String  TASK    = "TASK_UNASSIGNED";

	public int     numberOfLiteralsPerRowInPrintouts = Clause.defaultNumberOfLiteralsPerRowInPrintouts; // Store this here once, rather than in every clause.
	public int     numberOfTermsPerRowInPrintouts            = 4; // Actually only if this is 1 does it matter (used for debugging).
	public int     numberOfTermsPerRowInPrintoutsForLiterals = 4; // The Literal class will use the MIN of this and the above.
	
	public int     starModeMap = TypeSpec.plusMode; // '*' modes are defined via this (this allows a program to change modes within a run).

	// These constants indicate where in Literals 'special' terms are located.
	// A non-negative value V means this special term is in position V (counting starts at zero).
	// A negative value W means this special term is in position "#args - W" (so '-1' means LAST arg).
	// Indicating an argument out of range means 'ignore' (TODO - check that code works this way).
	public    int locationOfWorldArg         =  0;
    public    int locationOfStateArg         = -1;
    public    int locationOfNumericOutputArg = -2;

    public    IsaHetrarchy                isaHandler;
	public    DoBuiltInMath               mathHandler;
	public    DoBuiltInListProcessing     listHandler;
	private   List<PredicateNameAndArity> knownModes; // Hold all the predicates with known modes.
	private   List<PredicateNameAndArity> disallowedModes;
	public    boolean                     needPruner = false;



	public    enum VarIndicator { questionMarks, lowercase, uppercase }
	private        VarIndicator           variableIndicator = null; // Usually when read inside a file the former setting is reverted to once file reading is over.  But if null when file reading starts, that setting persists after the file is closed (ie., the first setting defines the default).
	private        VarIndicator           defaultVariableIndicator = VarIndicator.uppercase; // This will be set very early by the constructor since it needs to create some strings and needs to choose a notation (but after that it is again set to null).
	// NOTE: if variableIndicator=lowercase, then standard FOPC notation is used when printing.  Otherwise Prolog notation is used.  TODO - allow a separate variable to decide how to print?

	public    boolean                     prettyPrintClauses     = true;
	public    boolean                     printArgumentNames     = false;
    public    boolean                     duplicateCostWarningEnabled = true;
    //public    boolean                     verbose                = true;
	protected Map<String,PredicateName>   predicateNameHash; // These map a given string to one and only one instance.
	protected Map<String,FunctionName>    functionNameHash;
	protected Map<String,ConnectiveName>  connectiveNameHash;
	protected Map<String,Stack<Variable>> variableHash;
	protected Set<String>                 variableNamesSeen;
	protected Set<String>                 internalVariableNamesSeen; // The internally generated names.  Need to keep separate so can be removed when needed.
	protected Stack<Map<String,Stack<Variable>>> stackOfVariableHashes;
	protected Map<String,StringConstant>  stringConstantHash;
	protected Map<String,NumericConstant> numericConstantHash;

	private   Map<FunctionName,  Integer> precedenceTableForOperators;
	private   Map<ConnectiveName,Integer> precedenceTableForConnectives;
	public    Map<Term,List<Type>>    constantToTypesMap;       // A given constant can have multiple types.  Record them here.  TODO 'wrap' this variable?
	private   RecordHandler               recordHandler;
	private   ConsCell                    nil;                      // The nil used for lists.
    private   Literal                     nilAsLiteral;             // Just so we can convert back to the nil if we treat nil as a literal at some point.
	private   List<Term>                  listNIL;                  // NIL in a list.
	private   Set<Term>                   setNIL;                   // NIL in a set.
	protected Map<Type,Set<Term>>     knownConstantsOfThisType; // Collection all constants of a given type.  Use a hash map for efficiency.
	private   long varCounter             = 0; // Used to create new variable names that start with 'a', 'b', 'c', etc.
	private   long var2Counter            = 0; // Used for variables names that start with any other string (and prepends 'v_' or 'V_' to them to avoid name clashes).
	private   long overallCounter         = 0;
	private   int  countOfSkolemFunctions = 0;

	private boolean              predicatesHaveCosts = false; // Set if ANY predicate has a cost.  If so, the SUM of costs is used instead of length() to score a clause.
	private Set<RelevantLiteral> relevantLiterals    = null;  // Collect statements about which predicateName/arity's have an associated relevance statement.

	public    Constant  trueIndicator, falseIndicator;
	public    Literal   trueLiteral,   falseLiteral, cutLiteral;
	public    Clause    trueClause,    falseClause;


	// Invented predicates should have the following suffix.
	// This is useful if one is creating multiple theories, one can reset this for every theory
	// to make sure that the invented predicates have unique names.
	public String inventedPredicateNameSuffix = "";

	// Be very careful if you want to change these!
	private boolean useStrictEqualsForLiterals  = false; // If 'true,' only say literals are equal if they are '=='.
	private boolean useStrictEqualsForClauses   = false; // If 'true,' only say clauses  are equal if they are '=='.
	private boolean useStrictEqualsForFunctions = false; // Ditto for functions.
	public  boolean useFastHashCodeForLiterals  = true;
	public  boolean useFastHashCodeForClauses   = true;

    private Map<String,Integer> nameCounter    = new HashMap<String,Integer>(4);  // Unique name counter for anonymous names...

	private   static Map<String,Integer> precedenceTableForOperators_static   = null; // To avoid the need to pass around a stringHandler, there is also a static version that uses String.equals instead of '=='.
	private   static Map<String,Integer> precedenceTableForConnectives_static = null;
	private   static String alphabet = "abcdefghijkmnpqrstuvwxyz"; // 'l' and 'o' dropped since they are confusing (look like '1' and '0').
    public static final String[] alphabet2 = {
        "A","B","C","D","E","F","G","H","I","J","K", // "O" left out since it looks like a zero.   (Cap "L" looks OK.)
        "L","M","N","P","Q","R","S","T","U","W","X","Y","Z" }; // I DROPPED "V" since it means "OR"
    public static final int alphabet2Size = alphabet2.length;

	// Collect user-defined predicates.  These have priority over built-ins if there is a name collision (hence users can overwrite existing ones if they wish).
	private Map<PredicateName,Map<Integer,UserDefinedLiteral>> userAddedProcDefinedPredicates = null;
    private UserDefinedLiteralCache userDefinedLiteralCache = null; // Cache for user defined literals.

    private Set<String> filesLoaded = new HashSet<String>(8);

    // This group records information used by the MLN code.
	private List<PredicateName> queryPredicates;
	private List<Integer>       queryPredArities;
	private List<PredicateName> hiddenPredicates;
	private List<Integer>       hiddenPredArities;
    protected ClauseOptimiser   clauseOptimizer;


    public boolean underscoredAnonymousVariables = false;

    public PredicateNameAndArityFilter spyEntries = new PredicateNameAndArityFilter(this);

    /** Clausebase handling for facts added to the clausebase. */
    public VariantClauseAction variantFactHandling = WARN_AND_REMOVE_VARIANTS;

    /** Clausebase handling for facts added to the clausebase. */
    public VariantClauseAction variantRuleHandling = WARN_AND_REMOVE_VARIANTS;

    private Map<Literal, Literal> literalAliases = new HashMap<Literal, Literal>();

	public HandleFOPCstrings() {
		this(false);
	}
	public HandleFOPCstrings(VarIndicator variableIndicator) {
		this();
		setVariableIndicator(variableIndicator);
	}
	public HandleFOPCstrings(VarIndicator variableIndicator, boolean okToBeSecondStringHandler) {
		this(okToBeSecondStringHandler);
		setVariableIndicator(variableIndicator);
	}
	public HandleFOPCstrings(boolean okToBeSecondStringHandler) {
		if (!okToBeSecondStringHandler) { Utils.println(STRING_HANDLER_CREATION, "\n% Creating string handler #" + Utils.comma(++countOfStringHandlers) + ".\n"); }
		if (countOfStringHandlers > 1)  { Utils.warning(STRING_HANDLER_CREATION, "Do you really want to make string handler #" + Utils.comma(countOfStringHandlers) + "?"); }
		boolean hold = cleanFunctionAndPredicateNames;
		cleanFunctionAndPredicateNames = false;

		knownConstantsOfThisType = new HashMap<Type,Set<Term>>(4);
		knownModes          = new ArrayList<PredicateNameAndArity>(16);
		disallowedModes     = new ArrayList<PredicateNameAndArity>(4);
		predicateNameHash   = new HashMap<String,PredicateName>(64);
		functionNameHash    = new HashMap<String,FunctionName>(16);
		connectiveNameHash  = new HashMap<String,ConnectiveName>(16);
		variableHash        = new HashMap<String,Stack<Variable>>(1024);  // Need some cleanup (garbage collection) mechanism ..  TODO
		variableNamesSeen         = new HashSet<String>(1024);
		internalVariableNamesSeen = new HashSet<String>(1024);
		stackOfVariableHashes     = new Stack<Map<String,Stack<Variable>>>();
		stringConstantHash  = new HashMap<String,StringConstant>(32);
		numericConstantHash = new HashMap<String,NumericConstant>(32);
		constantToTypesMap  = new HashMap<Term,List<Type>>(256); // Likely to be a lot of these, and of not, the testbed is a small one and space unimportant


        standardPredicateNames = new StandardPredicateNames(this);

        recordHandler       = new RecordHandler();
		isaHandler          = new IsaHetrarchy(this);
		mathHandler         = new DoBuiltInMath(this);
		listHandler         = new DoBuiltInListProcessing(this);
		mathHandler.listHandler = listHandler;
		listHandler.mathHandler = mathHandler;
		trueIndicator       = this.getStringConstant("true");
		falseIndicator      = this.getStringConstant("false");
		trueLiteral         = this.getLiteral(standardPredicateNames.trueName);
		falseLiteral        = this.getLiteral(standardPredicateNames.falseName);
		cutLiteral          = this.getLiteral(standardPredicateNames.cut);
		trueClause          = this.getClause(trueLiteral,  true);
		falseClause         = this.getClause(falseLiteral, false);
		precedenceTableForOperators   = new HashMap<FunctionName,  Integer>( 8);
		precedenceTableForConnectives = new HashMap<ConnectiveName,Integer>(24);
		initPrecedences(precedenceTableForOperators, precedenceTableForConnectives);
		if (precedenceTableForOperators_static == null) {
			precedenceTableForOperators_static   = new HashMap<String,Integer>( 8);
			precedenceTableForConnectives_static = new HashMap<String,Integer>(24);
			initPrecedences_static(precedenceTableForOperators_static, precedenceTableForConnectives_static);
		}

		// Initialize some parameters used in libraries.
		recordSetParameter("relevance0", "POSSIBLE_ANSWER",   "built-in default", -1); // Probably a bad choice to number with LOWER being better ...
		recordSetParameter("relevance1", "STRONGLY_RELEVANT", "built-in default", -1);
		recordSetParameter("relevance2", "WEAKLY_RELEVANT",   "built-in default", -1);
		recordSetParameter("relevance3", "NEUTRAL",           "built-in default", -1);
		recordSetParameter("mixAndMatchAdviceLiterals", "WEAKLY_RELEVANT",    "built-in default", -1);
		recordSetParameter("atOrAboveTargetArguments", "IRRELEVANT",          "built-in default", -1);
		recordSetParameter("belowTargetArguments",     "WEAKLY_RELEVANT",     "built-in default", -1);
		recordSetParameter("typeInRelevance2",         "ISA_OBSERVED_FEATURE","built-in default", -1);
		recordSetParameter("typeInRelevance1",         "STRONGLY_RELEVANT",   "built-in default", -1);
		recordSetParameter("typeInRelevance0",         "POSSIBLE_ANSWER",     "built-in default", -1);
		recordSetParameter("typeInRelevance",          "POSSIBLE_ANSWER",     "built-in default", -1); // TODO - this is in some megatest files for IL; can deleted once those are updated.
		recordSetParameter("modeMax1",     "1", "built-in default", -1);
		recordSetParameter("modeMax2",     "2", "built-in default", -1);
		recordSetParameter("modeMax3",     "3", "built-in default", -1);
		recordSetParameter("modeMax4",     "4", "built-in default", -1);
		recordSetParameter("modeMax5",     "5", "built-in default", -1);
		recordSetParameter("modeMaxInf", "100", "built-in default", -1); // Currently (6/09) not used in the libraries, but that might change.
		recordSetParameter("thresholdsMax1",     "10", "built-in default", -1);
		recordSetParameter("thresholdsMax2",    "100", "built-in default", -1);
		recordSetParameter("thresholdsMax3",   "1000", "built-in default", -1);
		recordSetParameter("thresholdsMax4",  "10000", "built-in default", -1);
		recordSetParameter("thresholdsMax5", "100000", "built-in default", -1);
		cleanFunctionAndPredicateNames = hold;

		setVariableIndicator(null); // Wait for the first user file to set things, and keep that as the default.
	}

	public void reportStats() {
		Utils.println("% Some stats about the string handler:");
		Utils.println("%  overall variable counter    = " + Utils.comma(overallCounter));
		Utils.println("%  varCounter                  = " + Utils.comma(varCounter));
		Utils.println("%  var2Counter                 = " + Utils.comma(var2Counter));
		Utils.println("%  |variableNamesSeen|         = " + Utils.comma(variableNamesSeen)         + "  " + Utils.limitLengthOfPrintedList(variableNamesSeen,         100));
		Utils.println("%  |internalVariableNamesSeen| = " + Utils.comma(internalVariableNamesSeen) + "  " + Utils.limitLengthOfPrintedList(internalVariableNamesSeen, 100));
		Utils.println("%  |numericConstantHash|       = " + Utils.comma(numericConstantHash));
		Utils.println("%  |nameCounter|               = " + Utils.comma(nameCounter));
		Utils.println("%  |variableHash|              = " + Utils.comma(variableHash));
		Utils.println("%  |stackOfVariableHashes|     = " + Utils.comma(stackOfVariableHashes));
		long total = 0;
		if (variableHash != null) for (String str : variableHash.keySet()) { total += Utils.getSizeSafely(variableHash.get(str)); }
		Utils.println("%  |variableHash| total        = " + Utils.comma(total));
	}

	public int getArgumentPosition(int argLocationIndicator, int numberOfArgs) {
		if (argLocationIndicator >= 0) {
			if (argLocationIndicator >= numberOfArgs) { Utils.error("Cannot have argLocationIndicator >= numberOfArgs"); }
			return argLocationIndicator;
		}
		if (numberOfArgs + argLocationIndicator < 0)  { Utils.error("Cannot have -argLocationIndicator > numberOfArgs"); }
		return numberOfArgs + argLocationIndicator;
	}

	private void initPrecedences(Map<FunctionName,  Integer> precedenceTableForOperators,
								 Map<ConnectiveName,Integer> precedenceTableForConnectives) {
		precedenceTableForOperators.put(getFunctionName("+"),   500); // These precedence numbers are those of YAP Prolog.
		precedenceTableForOperators.put(getFunctionName("-"),   500);
		precedenceTableForOperators.put(getFunctionName("*"),   400);
		precedenceTableForOperators.put(getFunctionName("/"),   400);
		precedenceTableForOperators.put(getFunctionName("mod"), 300);
		precedenceTableForOperators.put(getFunctionName("**"),  200); // This is exponentation.
		precedenceTableForOperators.put(getFunctionName("=:="),1200); // Use these in case equality predicates get reified.
		precedenceTableForOperators.put(getFunctionName("=="), 1200);
		precedenceTableForOperators.put(getFunctionName("="),  1200);
        precedenceTableForOperators.put(getFunctionName("is"), 1200);

		// precedenceTableForPredicates.put(standardPredicateNames.is, 700);  700 for all except 300 for mod, so don't bother recording.

		precedenceTableForConnectives.put(getConnectiveName("not"),         900);
		precedenceTableForConnectives.put(getConnectiveName("LogicalNot"),  900);
		precedenceTableForConnectives.put(getConnectiveName("~"),           900);
		precedenceTableForConnectives.put(getConnectiveName("\\+"),         900);
		precedenceTableForConnectives.put(getConnectiveName("LogicalAnd"), 1000);
		precedenceTableForConnectives.put(getConnectiveName("and"),        1000);
		precedenceTableForConnectives.put(getConnectiveName("^"),          1000);
		precedenceTableForConnectives.put(getConnectiveName("&"),          1000);
		precedenceTableForConnectives.put(getConnectiveName(","),          1000);
		precedenceTableForConnectives.put(getConnectiveName("or"),         1100);
		precedenceTableForConnectives.put(getConnectiveName("LogicalOr"),  1100);
		precedenceTableForConnectives.put(getConnectiveName("v"),          1100);
		precedenceTableForConnectives.put(getConnectiveName("else"),       1100); // Used in (P then Q else R).
		precedenceTableForConnectives.put(getConnectiveName("then"),       1150); // CURRENTLY THIS IS TREATED AS A LITERAL AFTER PARSING.  This is ISO Prolog's '->' (and if-then-else construct).
		precedenceTableForConnectives.put(getConnectiveName("implies"),    1200); //   Note: 'then' has precedence of 1050 in YAP, but we want it to be higher than ELSE.
		precedenceTableForConnectives.put(getConnectiveName("=>"),         1200);
		precedenceTableForConnectives.put(getConnectiveName("->"),         1200);
		precedenceTableForConnectives.put(getConnectiveName(":-"),         1200);
		precedenceTableForConnectives.put(getConnectiveName(":="),         1200);
		precedenceTableForConnectives.put(getConnectiveName("if"),         1200);
		precedenceTableForConnectives.put(getConnectiveName(":="),         1200);
		precedenceTableForConnectives.put(getConnectiveName("equivalent"), 1200);
		precedenceTableForConnectives.put(getConnectiveName("<=>"),        1200);
		precedenceTableForConnectives.put(getConnectiveName("<->"),        1200); // Also ForAll and Exists have precedence of 1500.

	} // TODO clean up so don't need TWO copies of all these strings ...
	private static void initPrecedences_static(Map<String,Integer> precedenceTableForOperators, Map<String,Integer> precedenceTableForConnectives) {
		precedenceTableForOperators.put("+",   500); // These precedence numbers are those of YAP Prolog.
		precedenceTableForOperators.put("-",   500);
		precedenceTableForOperators.put("*",   400);
		precedenceTableForOperators.put("/",   400);
		precedenceTableForOperators.put("mod", 300); // All names here need to be lowercase.  TODO should create a method that does that, so mistakes here aren't a problem.
		precedenceTableForOperators.put("**",  200);
		precedenceTableForOperators.put("=:=",1200); // Use these in case equality predicates get reified.
		precedenceTableForOperators.put("==", 1200);
		precedenceTableForOperators.put("=",  1200);

		precedenceTableForConnectives.put("not",         900); // All names here also need to be lowercase.
		precedenceTableForConnectives.put("logicalnot",  900);
		precedenceTableForConnectives.put("~",           900);
		precedenceTableForConnectives.put("\\+",         900);
		precedenceTableForConnectives.put("and",        1000);
		precedenceTableForConnectives.put("logicaland", 1000);
		precedenceTableForConnectives.put("^",          1000);
		precedenceTableForConnectives.put("&",          1000);
		precedenceTableForConnectives.put(",",          1000);
		precedenceTableForConnectives.put("or",         1100);
		precedenceTableForConnectives.put("logicalor",  1100);
		precedenceTableForConnectives.put("v",          1100);
		precedenceTableForConnectives.put("else",       1100); // Used in (P then Q else R).
		precedenceTableForConnectives.put("then",       1150); // CURRENTLY THIS IS TREATED AS A LITERAL AFTER PARSING.  This is ISO Prolog's '->' (and if-then-else construct).
		precedenceTableForConnectives.put("implies",    1200);
		precedenceTableForConnectives.put("=>",         1200);
		precedenceTableForConnectives.put("->",         1200);
		precedenceTableForConnectives.put(":-",         1200);
		precedenceTableForConnectives.put(":=",         1200);
		precedenceTableForConnectives.put("if",         1200);
		precedenceTableForConnectives.put("equivalent", 1200);
		precedenceTableForConnectives.put("<=>",        1200);
		precedenceTableForConnectives.put("<->",        1200);	 // Also ForAll and Exists have precedence of 1500.
	}

    public        int getOperatorPrecedence(String operator) {
        return getOperatorPrecedence(getFunctionName(operator));
    }
	public        int getOperatorPrecedence(FunctionName fName) {
		Integer result = precedenceTableForOperators.get(fName);
		if (result == null) { Utils.error("No precedence is known for this operator: " + fName); }
		return result;
	}
	public static int getOperatorPrecedence_static(String fName) {
		Integer result = precedenceTableForOperators_static.get(fName);
		return result == null ? 1300 : result;
	}

	public        int getLiteralPrecedence(PredicateName pName) { // All of the in-fix literals have the same precedence.
		if (pName == standardPredicateNames.then) { return 1050;  } // Except for THEN, which becomes a literal after parsing.
		return 700;
	}
	public static int getLiteralPrecedence_static(PredicateName pName) { // All of the in-fix literals have the same precedence.
		if (pName.name.equalsIgnoreCase("then")) { return 1050; }        // Except for THEN, which becomes a literal after parsing.
		return 700;
	}

	public        int getConnectivePrecedence(ConnectiveName cName) {
		Integer result = precedenceTableForConnectives.get(cName);
		if (result == null) { Utils.error("No precedence is known for this connective: " + cName); }
		return result;
	}
	public static int getConnectivePrecedence_static(ConnectiveName cName) {
		Integer result = precedenceTableForConnectives_static.get(cName.name.toLowerCase());
		if (result == null) { Utils.error("No precedence is known for this connective: " + cName); }
		return result;
	}

	public boolean isVariableIndicatorSet() {  return variableIndicator != null; } // This allows us to know that the first setting in a file should become the chosen setting even after that file is closed.
	public void    usePrologNotation()     { if (!usingPrologNotation())   { if (!dontPrintUnlessImportant) Utils.println(STRING_HANDLER_VARIABLE_INDICATOR, "\n% Switching to Prolog notation for variables; previous setting = "         + variableIndicator); } setVariableIndicator(VarIndicator.uppercase); }
	public void    useStdLogicNotation()   { if (!usingStdLogicNotation()) { if (!dontPrintUnlessImportant) Utils.println(STRING_HANDLER_VARIABLE_INDICATOR, "\n% Switching to standard-logic notation for variables; previous setting = " + variableIndicator); } setVariableIndicator(VarIndicator.lowercase);	 }
	public boolean usingPrologNotation()   { if (getVariableIndicator() == null) { setVariableIndicator(defaultVariableIndicator); } return variableIndicator == VarIndicator.uppercase; }
	public boolean usingStdLogicNotation() { if (getVariableIndicator() == null) { setVariableIndicator(defaultVariableIndicator); } return variableIndicator == VarIndicator.lowercase; }


	// TODO - note that useStdLogicNotation still impacts how FOPC sentences are printed even if variablesStartWithQuestionMarks=true.  NEED TO CLEAN UP.
	public Boolean answerTo_printUsingStdLogicNotation = null; // CAN SET THIS TO OVERRIDE.
	public boolean printUsingStdLogicNotation() {
		if (answerTo_printUsingStdLogicNotation != null) { return answerTo_printUsingStdLogicNotation; }
		return usingStdLogicNotation();
	}

	public void setVariablesStartWithQuestionMarks() {
		if (!doVariablesStartWithQuestionMarks()) {
			if (!dontPrintUnlessImportant) Utils.println(STRING_HANDLER_VARIABLE_INDICATOR, "\n% Switching to using a leading '?' to denote a variable; previous setting = " + variableIndicator);
		}
		setVariableIndicator(VarIndicator.questionMarks);
	}
	public boolean doVariablesStartWithQuestionMarks() {
		if (getVariableIndicator() == null) { setVariableIndicator(defaultVariableIndicator); }
		return variableIndicator == VarIndicator.questionMarks;
	}

	public void setVariableIndicator(VarIndicator varIndicator) {
		setVariableIndicator(varIndicator, true);
	}
	public void setVariableIndicator(VarIndicator varIndicator, boolean reportChange) {
		if (variableIndicator == varIndicator) { return; }
		if (!dontPrintUnlessImportant && reportChange) Utils.println(STRING_HANDLER_VARIABLE_INDICATOR, (varIndicator == null ? "\n% Unset'ing VarIndicator." : "\n% Switching to VarIndicator = " + varIndicator + "."));
		variableIndicator = varIndicator;
	}

	public VarIndicator getVariableIndicator() {
		if (variableIndicator == null) { setVariableIndicator(defaultVariableIndicator); }
		return variableIndicator;
	}

	public VarIndicator getVariableIndicatorNoSideEffects() {
		return variableIndicator;
	}

	public String getStringToIndicateCurrentVariableNotation() {
		if (doVariablesStartWithQuestionMarks()) { return "useLeadingQuestionMarkVariables: true.\n";  }
		else if (usingStdLogicNotation())        { return "useStdLogicNotation: true.\n";  }
		else                                     { return "usePrologVariables: true.\n";   }
	}

	public String getShortStringToIndicateCurrentVariableNotation() {
		if (doVariablesStartWithQuestionMarks()) { return "useLeadingQuestionMarkVariables";  }
		else if (usingStdLogicNotation())        { return "useStdLogicNotation:";  }
		else                                     { return "usePrologVariables";   }
	}

	////////////////////////////////////////////////////////////////////////////////
	// This next group deals with creating instances from FOPC.  By passing everything
	// through this class, we can prevent incorrect new calls to those where 'canonical' instances are needed (e.g., PredicateName, Variable, Constant, etc).
	// Also, we can later aim to make some/all of these canonical as well, should that make sense.
	////////////////////////////////////////////////////////////////////////////////

    public Clause getClause() {
		return new Clause(this, null, null);
	}
	public Clause getClause(List<Literal> posLiterals, List<Literal> negLiterals) {
		return new Clause(this, posLiterals, negLiterals);
	}
	public Clause getClause(List<Literal> posLiterals, List<Literal> negLiterals, String extraLabel) {
		return new Clause(this, posLiterals, negLiterals, extraLabel);
	}
	public Clause getClause(Literal posLiteral, Literal negLiteral, String extraLabel) {
		List<Literal> posLiterals = new ArrayList<Literal>(1);
		List<Literal> negLiterals = new ArrayList<Literal>(1);
		if ( posLiteral != null ) posLiterals.add(posLiteral);
		if ( negLiteral != null ) negLiterals.add(negLiteral);
		return new Clause(this, posLiterals, negLiterals, extraLabel);
	}
	public Clause getClause(Literal posLiteral, Literal negLiteral) {
		return getClause(posLiteral, negLiteral, null);
	}
	public Clause getClause(List<Literal> literals, boolean literalsAreAllPos) {
		return new Clause(this, literals, literalsAreAllPos);	// NOTE: if literalsAreAllPos=false THEN IT IS ASSUMED ALL LITERALS ARE NEGATIVE.
	}
	public Clause getClause(Literal literal, boolean literalIsPos) {
		return new Clause(this, literal, literalIsPos);
	}
	public Clause getClause(Literal literal, boolean literalIsPos, String extraLabel) {
		return new Clause(this, literal, literalIsPos, extraLabel);
	}

	public ConnectedSentence getConnectedSentence(ConnectiveName connective, Sentence B) {
		return new ConnectedSentence(this, connective, B);
	}
	public ConnectedSentence getConnectedSentence(Sentence A, ConnectiveName connective, Sentence B) {
		return new ConnectedSentence(this, A, connective, B);
	}
    public Sentence getConnectedSentence(List<? extends Sentence> sentences, ConnectiveName connective) {
        Sentence sentence = sentences.get(0);
        for (int i = 1; i < sentences.size(); i++) {
            sentence = getConnectedSentence(sentence, connective, sentences.get(i));
        }
        return sentence;
    }

	public ConsCell getConsCell() {
		return new ConsCell(this);
	}
	public ConsCell getConsCell(FunctionName functionName, TypeSpec typeSpec) {
		return new ConsCell(this, functionName, typeSpec);
	}
	public ConsCell getConsCell(Term firstTerm, TypeSpec typeSpec) {
		return new ConsCell(this, firstTerm, typeSpec);
	}
	public ConsCell getConsCell(Term firstTerm, Term restTerm, TypeSpec typeSpec) {
		return new ConsCell(this, firstTerm, restTerm, typeSpec);
	}
	public ConsCell getConsCell(FunctionName functionName, List<Term> arguments, List<String> argumentNames, TypeSpec typeSpec) {
		return new ConsCell(this, functionName, arguments, argumentNames, typeSpec);
	}
	public ConsCell getConsCell(Function f) {
		return new ConsCell(this, f.functionName, f.getArguments(), f.getArgumentNames(), f.getTypeSpec());
	}
    public ConsCell getConsCellFromList(List<Term> items) {

        ConsCell head = null;
        
        ConsCell tail = null;

        if ( items == null || items.isEmpty() ) {
            head = null;

        }
        else {
            for (Term term : items) {
                ConsCell newCell = getConsCell(term, null);
                if ( head == null) {
                    head = newCell;
                }
                else {
                    tail.setCdr(newCell);
                }
                tail = newCell;
            }
        }

        return head;
    }

	public ExistentialSentence getExistentialSentence(Collection<Variable> variables, Sentence body) {
		return new ExistentialSentence(this, variables, body);
	}

    public Function getFunction(String functionName, List<Term> arguments, TypeSpec typeSpec) {
		return new Function(this, getFunctionName(functionName), arguments, typeSpec);
	}

	public Function getFunction(FunctionName functionName, List<Term> arguments, TypeSpec typeSpec) {
		return new Function(this, functionName, arguments, typeSpec);
	}

	public Function getFunction(FunctionName functionName, Term argument, TypeSpec typeSpec) {
		List<Term> arguments = new ArrayList<Term>(1);
		arguments.add(argument);
		return new Function(this, functionName, arguments, typeSpec);
	}
	public Function getFunction(FunctionName functionName, TypeSpec typeSpec) {
		return new Function(this, functionName, typeSpec);
	}
	public Function getFunction(FunctionName functionName, List<Term> arguments, List<String> argumentNames, TypeSpec typeSpec) {
        if ( functionName.name.equalsIgnoreCase("consCell")) {
            return new ConsCell(this, functionName, arguments, argumentNames, typeSpec);
        }
        else {
            return new Function(this, functionName, arguments, argumentNames, typeSpec);
        }
	}

    public Function getFunction(Function existingFunction, List<Term> newArguments) {

        int newArgsSize = newArguments == null ? 0 : newArguments.size();

        if ((existingFunction.getArity() > 0 && newArguments == null) || (existingFunction.getArity() != newArgsSize)) {
            throw new IllegalArgumentException("newArguments.size() must match arity of " + existingFunction);
        }

        Function newFunction;
        if ( existingFunction == getNil() ) {
            newFunction =  getNil();
        }
        else if(existingFunction instanceof ConsCell) {
            newFunction = getConsCell(existingFunction.functionName, newArguments, existingFunction.getArgumentNames(), existingFunction.getTypeSpec());
        }
        else {
            newFunction = getFunction(existingFunction.functionName, newArguments, existingFunction.getArgumentNames(), existingFunction.getTypeSpec());
        }

        return newFunction;
    }

    public Function getFunction(FunctionName functionName, Term ... arguments) {
        return getFunction(functionName, Arrays.asList(arguments), null);
    }
    public Function getFunction(String functionName, Term ... arguments) {
        return getFunction(functionName, Arrays.asList(arguments), null);
    }

    public Function getFunction(String functionName, List<Term> arguments) {
        return getFunction( getFunctionName(functionName), arguments, null);
   }
	public ListAsTerm getListAsTerm(List<Term> objects) {
		return new ListAsTerm(this, objects);
	}
	public ListAsTerm getListAsTerm(List<Term> objects, boolean processItemsInList) {
		return new ListAsTerm(this, objects, processItemsInList);
	}

	public ListAsSentence getListAsSentence(List<Sentence> objects) {
		return new ListAsSentence(this, objects);
	}
	public ListAsSentence getListAsSentence(List<Sentence> objects, boolean processItemsInList) {
		return new ListAsSentence(this, objects, processItemsInList); // Needs coding if processItemsInList=true.
	}

	public Literal getLiteral() {
		return new Literal(this);
	}
	public Literal getLiteral(PredicateName pred) {
		return new Literal(this, pred);
	}
	public Literal getLiteral(PredicateName pred, List<Term> arguments) {
		return new Literal(this, pred, arguments);
	}
	public Literal getLiteral(PredicateName pred, List<Term> arguments, List<String> argumentNames) {
		return new Literal(this, pred, arguments, argumentNames);
	}
	public Literal getLiteral(String pred, List<Term> arguments, List<String> argumentNames) {
		return new Literal(this, getPredicateName(pred), arguments, argumentNames);
	}
	public Literal getLiteral(PredicateName pred, Term argument) {
		return new Literal(this, pred, argument);
	}
    public Literal getLiteral(Literal existingLiteral, List<Term> newArguments) {
        int newArgCount = newArguments == null ? 0 : newArguments.size();
        if ((existingLiteral.getArity() > 0 && newArguments == null) || (existingLiteral.getArity() != newArgCount)) {
            throw new IllegalArgumentException("newArguments.size() must match arity of " + existingLiteral);
        }

        Literal newLiteral = getLiteral(existingLiteral.predicateName, newArguments, existingLiteral.getArgumentNames());
        return newLiteral;
    }
    public Literal getLiteral(PredicateName pred, Term... arguments) {
        if (arguments == null) {
            return getLiteral(pred);
        }
        else {
            List<Term> terms = Arrays.asList(arguments);
            return getLiteral(pred, terms);
        }
    }
    public Literal getLiteral(String predicateName, Term... arguments) {
        PredicateName pn = getPredicateName(predicateName);
        if (arguments == null) {
            return getLiteral(pn);
        }
        else {
            List<Term> terms = Arrays.asList(arguments);
            return getLiteral(pn, terms);
        }
    }

    public Literal getLiteral(String predicateName, List<Term> terms) {
        PredicateName pn = getPredicateName(predicateName);
        return getLiteral(pn, terms);
    }

	public Sentence getTermAsSentence(Term term) {
		return new TermAsSentence(this, term);
	}

	public Literal getTermAsLiteral(Term term) {
		return new TermAsLiteral(this, term);
	}

	public ConstructedLiteral getConstructedLiteral(PredicateName pred, AllOfFOPC constructor) {
		return new ConstructedLiteral(this, pred, constructor);
	}
	public ConstructedLiteral getConstructedLiteral(PredicateName pred, List<Term> arguments, AllOfFOPC constructor) {
		return new ConstructedLiteral(this, pred, arguments, constructor);
	}
	public ConstructedLiteral getConstructedLiteral(PredicateName pred, Term argument, AllOfFOPC constructor) {
		return new ConstructedLiteral(this, pred, argument, constructor);
	}

	public LiteralToThreshold getLiteralToThreshold(PredicateName predicateName, List<Term> arguments, int position) {
		return new LiteralToThreshold(this, predicateName, arguments, position);
	}
	public LiteralToThreshold getLiteralToThreshold(PredicateName predicateName, List<Term> arguments, int position, int maxCuts, boolean createTiles, boolean firstArgIsExampleID) {
		return new LiteralToThreshold(this, predicateName, arguments, position, maxCuts, createTiles, firstArgIsExampleID);
	}

	public LiteralAsTerm getLiteralAsTerm(Literal itemBeingWrapped) {
		return new LiteralAsTerm(this, itemBeingWrapped);
	}

	public ObjectAsTerm getObjectAsTerm(Object item) {
		return new ObjectAsTerm(this, item, true);
	}
	public ObjectAsTerm getObjectAsTerm(Object item, boolean warnIfWrappingTerm) {
		return new ObjectAsTerm(this, item, warnIfWrappingTerm);
	}

	//public Sentence getSentence() { // Can't do this one, since it is ABSTRACT.
	//	return new Sentence(this);
	//}

	public SentenceAsTerm getSentenceAsTerm(Sentence s, String wrapper) {
		return new SentenceAsTerm(this, s, wrapper);
	}

	public UniversalSentence getUniversalSentence(Collection<Variable> variables, Sentence body) {
		return new UniversalSentence(this, variables, body);
	}


	public Literal wrapInNot(Function f) {
		return wrapInNot(f.convertToLiteral(this));
	}
	public Literal wrapInNot(Literal innerLit) {
		PredicateName notPname = standardPredicateNames.negationByFailure;

		// Process into the required structure for negation-by-failure.
		List<Literal>  innerLitInList = new ArrayList<Literal>(1);
		innerLitInList.add(innerLit);
		Clause clauseInsideNot = getClause(null, innerLitInList) ;
		List<Term> notArgs = new ArrayList<Term>(2);
		notArgs.add(getSentenceAsTerm(clauseInsideNot, "not"));
		return getLiteral(notPname, notArgs);
	}

    /** Returns the NegationByFailure of clauseInsideNot.
     *
     * Note: For proper logical sense, the clause within
     * the negation should have positive literals, not negated
     * literals.
     *
     * \+(P) is defined as:
     *
     * \+(P) :- P, !, fail.
     * \+(P).
     *
     * This is logically equivalent to:
     *
     * \+(P) OR ~P OR ~! OR ~fail.  Here ~ is true negation.
     *
     * Consider ~Q as the contents of \+:
     *
     * \+(~Q). Expanding the first clause of definition of +\(~Q), we get:
     *
     * \+(~Q) :- ~Q, !, fail.
     *
     * Equivalent to:
     *
     * \+(~Q) OR ~(~Q)), ~!, ~fail.
     *
     * equivalent to:
     *
     * \+(~Q) OR Q OR ~! OR ~fail.
     *
     * However, this is not a definite clause, so that implies
     * that the literal inside a negation by failure,
     * can not be a negated literal.
     *
     * Plus, the parser will parse \+( A,B,C ) such
     * that A,B,C will be a SentenceAsTerm as a positive
     * literal.
     *
     * If the contentsOfNegationByFailure clause is a set of negative literals,
     * the clause will be adjusted to be a set of positive literals.
     *
     * @param contentsOfNegationByFailure Contents to put inside the negation-by-failure.  Clause
     * should contain either all positive literals or all negative literals.
     * @return a Literal with predicate name of \+ and arity 1, whose argument is a
     * clause with all positive literals obtained from contentsOfNegationByFailure.
     */
    public Literal getNegationByFailure(Clause contentsOfNegationByFailure) {

        Literal result = null;

//        if (isNegationByFailure(clauseInsideNot)) {
//            result = getNegationByFailureContents(clauseInsideNot);
//        }
//        else {

        if ( contentsOfNegationByFailure.getPosLiteralCount() != 0 && contentsOfNegationByFailure.getNegLiteralCount() != 0 ) {
            Utils.error("Negation-by-failure content clause contains both positive and negative literals!");
        }

        List<Literal> negatedLiterals;
        if (contentsOfNegationByFailure.getPosLiteralCount() > 0) {
            negatedLiterals = contentsOfNegationByFailure.getPositiveLiterals();
        }
        else {
            negatedLiterals = contentsOfNegationByFailure.getNegativeLiterals();
        }

        if ( negatedLiterals.isEmpty() ) {
            // Empty clauseInside creates a \+(true).  We
            // could replace with fail, but I want to maintain
            // the negation structure.
            StringConstant trueConstant = getStringConstant("true");
            result = getLiteral(standardPredicateNames.negationByFailure, trueConstant);
        }
        else if(negatedLiterals.size() == 1) {
            Function insideFunction = negatedLiterals.get(0).convertToFunction(this);
            result = getLiteral(standardPredicateNames.negationByFailure, insideFunction);
        }
        else {
            //Clause negatedClause = getClause(negatedLiterals, true);
            //SentenceAsTerm contents = getSentenceAsTerm(negatedClause, "negationByFailure");
            List<Term> terms = new ArrayList<Term>(negatedLiterals.size());
            for (Literal literal : negatedLiterals) {
                terms.add(literal.asFunction());
            }

            result = getLiteral(standardPredicateNames.negationByFailure, terms);
        }

        return result;
    }

    /** Returns the contents of a negation-by-failure as a clause with all positive literals.
     *
     * Per the discussion in getNegativeByFailure, the clause within a negation-by-failure should
     * contain positive literals only.  As such, getNegationByFailureContents always returns
     * a clause with positive literals.  If the actual content clause contains negative literals,
     * it will be rewritten to contain positive literals.
     *
     * @param negationByFailure A clause with a single literal (either positive or negative) with predicate name of \+ and arity 1.
     * @return Contents of a negation-by-failure as a clause with all positive literals
     */
    public Clause getNegationByFailureContents(Clause negationByFailure) {
        if ( negationByFailure.getPosLiteralCount() == 0 && negationByFailure.getNegLiteralCount() == 1 && negationByFailure.getNegLiteral(0).predicateName == standardPredicateNames.negationByFailure) {
            return getNegationByFailureContents(negationByFailure.getNegLiteral(0));
        }
        else if ( negationByFailure.getPosLiteralCount() == 1 && negationByFailure.getNegLiteralCount() == 0 && negationByFailure.getPosLiteral(0).predicateName == standardPredicateNames.negationByFailure) {
            return getNegationByFailureContents(negationByFailure.getPosLiteral(0));
        }
        else  {
            Utils.error("getNegationContets expect a clause with no positive lits and one neg lit with pname \\+.");
            return null;
        }
    }

    /** Returns the contents of a negation-by-failure as a clause with all positive literals.
     *
     * Per the discussion in getNegativeByFailure, the clause within a negation-by-failure should
     * contain positive literals only.  As such, getNegationByFailureContents always returns
     * a clause with positive literals.  If the actual content clause contains negative literals,
     * it will be rewritten to contain positive literals.
     *
     * @param negationByFailure A literal with predicate name of \+ and arity 1.
     * @return Contents of a negation-by-failure as a clause with all positive literals
     */
    public Clause getNegationByFailureContents(LiteralOrFunction negationByFailure) {

        Clause result = null;

        if ( negationByFailure.getPredicateName() == standardPredicateNames.negationByFailure ) {

            if ( negationByFailure.getArity() == 1 ) {

                Term arg = negationByFailure.getArguments().get(0);
                Clause clause = arg.asClause();
                if ( clause == null ) {
                    Utils.error("Negated literal to have single argument of type Function or SentenceAsTerm.  Literal: " + negationByFailure + ".");
                }

                if ( clause.getPosLiteralCount() != 0 && clause.getNegLiteralCount() != 0 ) {
                    Utils.error("Negation-by-failure content clause contains both positive and negative literals!");
                }

                if ( clause.getNegLiteralCount() != 0 ) {
                    clause = getClause(clause.getNegativeLiterals(), true);
                }

                result = clause;
            }
            else {
                // We have multiple arguments to the negation-by-failure.
                // Thus the terms become the literals to the clause.
                List<Literal> lits = new ArrayList<Literal>();
                for (Term literal : negationByFailure.getArguments()) {
                    lits.add(literal.asLiteral());
                }

                result = getClause(lits, null);
            }
        }
        else {
            Utils.error("Literal " + negationByFailure + " was not a negationByFailure.");
            return null;
        }

        return result;
    }

    public Clause getNegationByFailureContents(Literal negationByFailure) {
        return getNegationByFailureContents((LiteralOrFunction)negationByFailure);
    }

    /** Returns whether the positiveNegationByFailure clause is a negation-by-failure.
     *
     * A clause is a negation-by-failure if it is either a single positive literal or a
     * single negative literal and that literal has a predicate name of \+ and arity 1.
     *
     * @param possibleNegationByFailure Clause to evaluate.
     * @return True if clause is either a single positive literal or a
     * single negative literal and that literal has a predicate name of \+ and arity 1.
     */
    public boolean isNegationByFailure(Sentence possibleNegationByFailure) {


        if ( possibleNegationByFailure instanceof Clause ) {
            Clause possibleNegationByFailureClause = (Clause) possibleNegationByFailure;

            Literal possibleNegationByFailureLiteral = null;

            if ( possibleNegationByFailureClause.getPosLiteralCount() == 0 && possibleNegationByFailureClause.getNegLiteralCount() == 1) {
                possibleNegationByFailureLiteral = possibleNegationByFailureClause.getNegLiteral(0);
            }
            else if ( possibleNegationByFailureClause.getPosLiteralCount() == 1 && possibleNegationByFailureClause.getNegLiteralCount() == 0 ) {
                possibleNegationByFailureLiteral = possibleNegationByFailureClause.getPosLiteral(0);
            }

            return isNegationByFailure((LiteralOrFunction)possibleNegationByFailureLiteral);
        }
        else if ( possibleNegationByFailure instanceof Literal ) {
            return isNegationByFailure((LiteralOrFunction)possibleNegationByFailure);
        }

        return false;

    }

    /** Returns whether the possibleNegationByFailure literal is a negation-by-failure.
     *
     * A literal is a negation-by-failure if it has a predicate name of \+ and arity 1.
     *
     * @param possibleNegationByFailure literal to evaluate.
     * @return True if literal has a predicate name of \+ and arity 1.
     */
    public boolean isNegationByFailure(LiteralOrFunction possibleNegationByFailure) {
        return (possibleNegationByFailure != null && possibleNegationByFailure.getPredicateName() == standardPredicateNames.negationByFailure);
    }

    public boolean isNegationByFailure(Literal possibleNegationByFailure) {
        return isNegationByFailure((LiteralOrFunction)possibleNegationByFailure);
    }

	/**
	 * Call the math or list handler to simplify an expression.
	 * @param expression
	 * @return The numeric result of computing the given expression.
	 */
	public Term simplify(Term expression) {
		if (listHandler.canHandle(expression)) {
			return listHandler.simplify(expression);
		}
		if (mathHandler.canHandle(expression)) {
			return mathHandler.simplify(expression);
		}
	//	Utils.error("Do not know how to simplify:\n  " + expression);
		return expression;  // Sometimes plain-old items will appear (e.g., an integer) that don't need simplification.
	}

	public void resetVarCounters() {
		// int n = 2; // Will start with this many aa's
		varCounter  = 0; //(int) Math.pow(24.0, n - 1.0); // Assumes that the head has fewer that 24 variables (since the variables in the target are 'a', 'b', etc.).
		var2Counter = 0; // Not used for the head (i.e., target), so can reset to 0.
		internalVariableNamesSeen.clear();
		resetAllVariables();
	}

	public void recordMode(Literal typedLiteral) {
		recordMode(typedLiteral, Integer.MAX_VALUE, Integer.MAX_VALUE, false);
	}
	public void recordMode(Literal typedLiteral, int maxOccurrences, int maxPerInputVars, boolean thisIsaNoMode) {
		List<TypeSpec> types = new ArrayList<TypeSpec>(Utils.getSizeSafely(typedLiteral.getArguments()));
		getTypeList(typedLiteral.getArguments(), types);
		List<Term> signature = getSignature(typedLiteral.getArguments());
		//Utils.println("\n% recordModeWithTypes: " + typedLiteral + "  args=" + typedLiteral.getArguments() + " sig=" + signature + " types=" + types);
		if (thisIsaNoMode) {
			disableModeWithTypes(typedLiteral, signature, types, maxOccurrences, maxPerInputVars, true);
		} else {
			recordModeWithTypes(typedLiteral, signature, types, maxOccurrences, maxPerInputVars, true);
		}
	}
	public void recordModeWithTypes(Literal typedLiteral, List<Term> signature, List<TypeSpec> types, int maxOccurrences, int maxPerInputVars) {
		recordModeWithTypes(typedLiteral, signature, types, maxOccurrences, maxPerInputVars, false);
	}
	public void recordModeWithTypes(Literal typedLiteral, List<Term> signature, List<TypeSpec> types, int maxOccurrences, int maxPerInputVars, boolean okIfDuplicate) {
        if (typedLiteral != null ) recordModeWithTypes(typedLiteral.getPredicateNameAndArity(), signature, types, maxOccurrences, maxPerInputVars, okIfDuplicate);
	}
	public void recordModeWithTypes(PredicateNameAndArity predicate, List<Term> signature, List<TypeSpec> types, int maxOccurrences, int maxPerInputVars, boolean okIfDuplicate) {
        if ( predicate != null ) {
            recordPredicatesWithKnownModes(predicate);
            predicate.getPredicateName().recordMode(signature, types, maxOccurrences, maxPerInputVars, okIfDuplicate);
        }
	}
	public void disableModeWithTypes(Literal typedLiteral, List<Term> signature, List<TypeSpec> types, int maxOccurrences, int maxPerInputVars, boolean okIfDuplicate) {
        if (typedLiteral != null ) disableModeWithTypes(typedLiteral.getPredicateNameAndArity(), signature, types, maxOccurrences, maxPerInputVars, okIfDuplicate);
	}
	public void disableModeWithTypes(PredicateNameAndArity predicate, List<Term> signature, List<TypeSpec> types, int maxOccurrences, int maxPerInputVars, boolean okIfDuplicate) {
        if ( predicate != null ) {
            recordPredicatesWithDisabledModes(predicate);
            predicate.getPredicateName().disableMode(signature, types, maxOccurrences, maxPerInputVars, okIfDuplicate);
        }
	}

	////////////////////////  TODO clean up the typeSpec stuff ////////////////////////////////////////////////

	// Collect the argument types in the order they appear in a traversal of the literal's arguments ('types' are only at LEAVES).
	// TODO: but seems functions also need to be typed for proper operation ...
	public void getTypeList(List<Term> arguments, List<TypeSpec> typeSpecs) {
		getTypeList(arguments, typeSpecs, false);
	}
	public void getTypeList(List<Term> arguments, List<TypeSpec> typeSpecs, boolean skipConstants) {
		for (Term spec : arguments) {
			if (skipConstants && spec instanceof Constant) { continue; }
			if (spec.typeSpec != null) { typeSpecs.add(spec.typeSpec); } // NOTE: we do NOT want to skip duplicates!
			else if (spec instanceof Function) {
				getTypeList(((Function) spec).getArguments(), typeSpecs);
			} else { Utils.error("Need all these arguments to be typed: " + arguments + " typeSpecs = " + typeSpecs); }
		}
	}

	// Collect free variables and their types.  Only need to type a variable the first time mentioned,
	// though OK to do so more than once (but subsequent types must be consistent).
	// UNLIKE THE ABOVE, HERE WE WANT TO REMOVE DUPLICATES.
	// If onlyKeepPlusVariables=true, do not collect variables that are of type '-' and the like.
	public void getTypedFreeVariables(                               List<Term> arguments, List<String> argNames, List<Variable> freeVars, List<String> freeVarNames, List<TypeSpec> typeSpecs, boolean onlyKeepPlusOrMinusVariables) {
		getTypedFreeVariables(null, arguments, argNames, freeVars, freeVarNames, typeSpecs, onlyKeepPlusOrMinusVariables);
	}
	public void getTypedFreeVariables(Variable keepThisVarIfPresent, List<Term> arguments, List<String> argNames, List<Variable> freeVars, List<String> freeVarNames, List<TypeSpec> typeSpecs, boolean onlyKeepPlusOrMinusVariables) {
		if (arguments != null) for (int i = 0; i < arguments.size(); i++) {
			Term spec = arguments.get(i);
			if (spec instanceof Constant) {
				continue;
			} else if (spec == null) {
				Utils.warning("getTypedFreeVariables: have spec = null for argument " + (i + 1) + " in: " + arguments);
			} else if (spec.typeSpec != null) {
				if (spec instanceof Variable && freeVars.contains(spec)) { // It can be OK to have a repeat since sometimes this is called successively on the same literal or function.
					 // if (debugLevel > 1) { Utils.println("%  getTypedFreeVariables: already have typeSpec '" + spec.typeSpec + "' of '" + spec + "' in " + typeSpecs); }
				}
				else if (spec == keepThisVarIfPresent || !onlyKeepPlusOrMinusVariables || spec.typeSpec.isPlusOrMinus() || spec.typeSpec.isNotYetSet()) { // If requested, only want the '+' and '-' (and their isVariant) variables.
					Variable specAsVar = (Variable) spec;
					if (!freeVars.contains(specAsVar)) {
						typeSpecs.add(spec.typeSpec);
						freeVars.add(specAsVar);
						freeVarNames.add(argNames == null ? "unnamed" : argNames.get(i));
					}
				} else if (debugLevel > 1) { Utils.println("%  getTypedFreeVariables: typeSpec '" + spec.typeSpec + "' of '" + spec + "' is not a plusorMinus or unset var."); }
			} else if (spec instanceof Variable && freeVars.contains(spec)) {
				if (debugLevel > 1) { Utils.println("%  getTypedFreeVariables: already have variable '" + spec + "' in " + freeVars); }
				continue;
			} else if (spec instanceof Function) {
				getTypedFreeVariables(keepThisVarIfPresent, ((Function) spec).getArguments(), ((Function) spec).getArgumentNames(), freeVars, freeVarNames, typeSpecs, onlyKeepPlusOrMinusVariables);
			} else { Utils.error("Need all these arguments to be typed: " + spec + "  all info: " + arguments + "  freeVars = " + freeVars + "  typeSpecs = " + typeSpecs); }
		}
	}
	public void getTypedFreeVariablesAndUniquelyName(                               List<Term> arguments, List<String> argNames, List<Variable> freeVars, List<String> freeVarNames, List<TypeSpec> typeSpecs, boolean onlyKeepPlusOrMinusVariables) {
		getTypedFreeVariablesAndUniquelyName(null, arguments, argNames, freeVars, freeVarNames, typeSpecs, onlyKeepPlusOrMinusVariables);
	}
	public void getTypedFreeVariablesAndUniquelyName(Variable keepThisVarIfPresent, List<Term> arguments, List<String> argNames, List<Variable> freeVars, List<String> freeVarNames, List<TypeSpec> typeSpecs, boolean onlyKeepPlusOrMinusVariables) {
		getTypedFreeVariables(keepThisVarIfPresent, arguments, argNames, freeVars, freeVarNames, typeSpecs, onlyKeepPlusOrMinusVariables);
		if (freeVarNames == null) { return; }
		// Since these names are going to be the field names for a new literal, need unique names for them.
		List<String> freeVarNamesNew = numberTheseArguments(freeVarNames);
		freeVarNames.clear();
		freeVarNames.addAll(freeVarNamesNew);
	}

	public List<String> numberTheseArguments(List<String> argNames) {
		if (argNames == null) { return null; }
		List<String> results = new ArrayList<String>(argNames.size());
		for (int i = 1; i <= argNames.size(); i++) {
			String oldName = argNames.get(i - 1);
			if (oldName.equals(NamedTerm.worldNameField)     ||
			    oldName.equals(NamedTerm.returnedValueField) ||
			    oldName.equals(NamedTerm.stateNameField)) {
				results.add(oldName);
			} else {
				results.add("arg" + i);
			}
		}
		return results;
	}

	////////////////////////////////////////////////////////////////////////

	private StringConstant  stringConstantMarker  = null;
	private NumericConstant numericConstantMarker = null;
	private Variable        variableMarker        = null;
	private ConsCell        listMarker            = null;
	public List<Term> getSignature(List<Term> arguments) {
		return getSignature(arguments, false);
	}
	public List<Term> getSignature(List<Term> arguments, boolean useConstantMarkerForVars) { // JWS (7/10) this boolean might just be a temporary hack.
		if (Utils.getSizeSafely(arguments) < 1) { return null; }
		if (stringConstantMarker == null) {
			stringConstantMarker  = getStringConstant("Const");
			numericConstantMarker = getNumericConstant(0);
			variableMarker        = getExternalVariable("Var"); // Need be an external variable, but seems ok to do so.
			listMarker            = getNil();
		}
		List<Term> result = new ArrayList<Term>(Utils.getSizeSafely(arguments));
		for (Term arg : arguments) {
			if      (arg instanceof StringConstant)  { result.add(stringConstantMarker);  }
			if      (arg instanceof NumericConstant) { result.add(numericConstantMarker); }
			else if (arg instanceof Variable) {        result.add(useConstantMarkerForVars ? stringConstantMarker : variableMarker);        }
			else if (arg instanceof ConsCell) {        result.add(listMarker);            } // We won't try to deal with the WHAT is in the list (and if we do, we'll need to make sure that matchingSignatures matches [] to anything.
			else if (arg instanceof Function) {
				Function f           = (Function) arg;
				Function functionSig = getFunction(f.functionName, getSignature(f.getArguments()), f.getTypeSpec());
				result.add(functionSig);
			}
		}
		return result;
	}
	// TODO - this was added as a patch.  The signature stuff needs to be cleaned up.
	public List<Term> getConstantSignatureThisLong(int i) {
		if (i < 1) { return null; }
		if (stringConstantMarker == null) {
			stringConstantMarker  = getStringConstant("Const");
			numericConstantMarker = getNumericConstant(0);
			variableMarker        = getExternalVariable("Var");
		}
		List<Term> results = new ArrayList<Term>(i);
		for (int j = 0; j < i; j++) {
			results.add(stringConstantMarker);
		}
		return results;
	}

	// Keep track of the predicates for which modes are known.  For simplicity, use a list since later will want to walk through it and speed is not crucial here.
	public void recordPredicatesWithKnownModes(PredicateNameAndArity predicateName) {
		if ( knownModes.contains(predicateName) == false ) {
            knownModes.add(predicateName);
        }
	}
	
	// Keep track of the predicates for which modes are disabled.
	public void recordPredicatesWithDisabledModes(PredicateNameAndArity predicateName) {
		if ( disallowedModes.contains(predicateName) == false ) {
			disallowedModes.add(predicateName);
        }
	}

    public void removePredicateWithKnownModes(PredicateNameAndArity predicateName) {
		knownModes.remove(predicateName);
	}

	public ConsCell getNil() {
		if (nil == null) { nil = this.getConsCell(); } // The empty cons cell is 'nil'
		return nil;
	}

    public Literal getNilAsLiteral() {
        if (nilAsLiteral == null ) {
            nilAsLiteral = getLiteral( getPredicateName("[]") );
        }
        return nilAsLiteral;
    }

	public List<Term> getListNil() {
		if (nil == null) { nil = this.getConsCell(); } // The list containing the empty cons cell.
		if (listNIL == null) { listNIL = new ArrayList<Term>(1); listNIL.add(nil); }
		return listNIL;
	}
	public Set<Term> getSetNil() {
		if (nil == null) { nil = this.getConsCell(); } // The list containing the empty cons cell.
		if (setNIL == null) { setNIL = new HashSet<Term>(4); setNIL.add(nil); }
		return setNIL;
	}


	private String standardize(String str, boolean cleanString, boolean hadQuotesOriginally) {
		if (!cleanString) { return str; }
		if (ignoreCaseOfStringsOtherThanFirstChar && !hadQuotesOriginally) { return str.toLowerCase(); }
		return str;
	}
	private String standardize(String str, boolean hadQuotesOriginally) {
		if (ignoreCaseOfStringsOtherThanFirstChar && !hadQuotesOriginally) { return str.toLowerCase(); }
		return str;
	}
	private String standardize(String str) {
		return standardize(str, false);
	}

	public boolean knownPredicateName(String nameRaw) {
		String name    = cleanString(nameRaw);
		String stdName = standardize(name); // Hash case-independently.
		PredicateName hashedValue = predicateNameHash.get(stdName);

		return (hashedValue != null);
	}

	public PredicateName getPredicateName(String nameRaw) {
		return getPredicateName(nameRaw, cleanFunctionAndPredicateNames);
	}

    public PredicateName getPredicateName(String nameRaw, boolean cleanName) {
		String name    = (cleanName ? cleanString(nameRaw) : nameRaw);
		String stdName = standardize(name); // Hash case-independently.
		PredicateName hashedValue = predicateNameHash.get(stdName);

		if (hashedValue != null) { return hashedValue; }

		PredicateName result = new PredicateName(name, this); // Store using the first version seen.
		predicateNameHash.put(stdName, result);
        if ( stdName.equals(name) == false ) {
            // TAW: This is a bit of a hack to add both the standardized name
            // TAW: and the non-standard, but cleaned name to the predicateNameHash.
            // TAW: This resolves an issue that occurs when the ignoreCaseOfStringsOtherThanFirstChar
            // TAW: is changed after some of the build-in predicate names have been retrieved.
            predicateNameHash.put(name, result);
        }
		return result;
	}

    public PredicateNameAndArity getPredicate(String name, int arity) {
        return new PredicateNameAndArity(getPredicateName(name), arity);
    }

    public PredicateNameAndArity getPredicate(PredicateName pName, int arity) {
        return new PredicateNameAndArity(pName, arity);
    }

	private int getNextNameCounter(String name) {
		Integer lookup = nameCounter.get(name);

		if (lookup == null) { // The pName has an implicit '0' the first time it is created.
			nameCounter.put(name, 1); // If there was a name conflict, then subsequent times we need to add to the counter.
			return 1;
		}
		nameCounter.put(name, lookup + 1);
		return lookup + 1;
	}

    public PredicateName getPredicateNameNumbered(String predicateName) {
        String originalPredicateName = predicateName;
    	while (knownPredicateName(predicateName)) {
    		// Keep trying until a unique name is produced.  Want to only add counters to the ORGINAL name.
            predicateName = originalPredicateName + getNextNameCounter(originalPredicateName);
    	}
    	PredicateName pName = getPredicateName(predicateName);
    	pName.addTemporary(-1);
    	return pName;
    }

   /** Looks up the predicate name in the cache.  If it exists, it returns the cached version.  In not, it adds the predicateName to the cache.
    *
    * This is used to look up PredicateNames when we are de-serializing.  We attempt to maintain
    * some information if possible about the predicateName.  However, in most cases, the predicateNames
    * will already be instantiated and we will probably lose the serialized predicateName information anyway.
    *
    * @param pName
    * @return
    */
    protected PredicateName getPredicateName(PredicateName pName) {
		String name    = pName.name; // cleanString(pName.name); // should already be cleaned..
        String stdName = standardize(name); // Hash case-independently.
        PredicateName hashedValue = predicateNameHash.get(stdName);

        if (hashedValue != null) { return hashedValue; }

		PredicateName result = new PredicateName(name, this); // Store using the first version seen.
		predicateNameHash.put(stdName, result);
        return result;
    }

	public FunctionName getFunctionName(String nameRaw) {
		String name    = (cleanFunctionAndPredicateNames ? cleanString(nameRaw) : nameRaw);
		String stdName = standardize(name); // Hash case-independently.
		FunctionName hashedValue = functionNameHash.get(stdName);

		if (hashedValue != null) { return hashedValue; }

		FunctionName result = new FunctionName(name); // Store using the first version seen.
		functionNameHash.put(stdName, result);
		return result;
	}

	public ConnectiveName getConnectiveName(String name) {
		// Do not call this since some dashes can appear here: cleanString(nameRaw);
		String stdName = standardize(name); // Hash case-independently.
		ConnectiveName hashedValue = connectiveNameHash.get(stdName);

		if (hashedValue != null) { return hashedValue; }

		ConnectiveName result = new ConnectiveName(name); // Store using the first version seen.
		connectiveNameHash.put(stdName, result);
		return result;
	}

	// These are used when a mode only specifies the type and doesn't also include any Terms.  E.g., 'mode: p(+human)'   instead of     'mode: p(+human:x)'
	public Constant getAnonymousTerm(TypeSpec spec)  {
		return new StringConstant(this, null, false, doVariablesStartWithQuestionMarks(), usingStdLogicNotation(), spec);
	}

	public Term getVariableOrConstant(TypeSpec spec, String name) {
		return getVariableOrConstant(spec, name, false); // The default is to NOT create new variables.
	}
	public Term getVariableOrConstant(TypeSpec spec, String name, boolean createNewVariable) {
		//Utils.println("getVariableOrConstant/3: " + name);
		if (isaConstantType(name)) { return getStringConstant(spec, name); } else { return getExternalVariable(spec, name, createNewVariable); }
	}

	public Term getVariableOrConstant(String name) {
		return getVariableOrConstant(name, false);
	}
	public Term getVariableOrConstant(String name, boolean createNewVariable) {
		//Utils.println("getVariableOrConstant/2: " + name);
		String typeIfNumber = isaNumericConstant(name);

		if (typeIfNumber == null) {
			if (isaConstantType(name))  { return getStringConstant(name); }
			return getExternalVariable(name, createNewVariable);
		}
		if (typeIfNumber.equals("integer")) { return getNumericConstant(Integer.parseInt(   name)); }  // Getting numbers here should be rare.
		if (typeIfNumber.equals("double"))  { return getNumericConstant( Double.parseDouble(name)); }
		Utils.error("Cannot interpret this variable or constant: '" + name + "'.");
		return null;
	}

	public String isaNumericConstant(String name) {
		if (name == null || name.length() < 1) { return null; }
		switch (name.charAt(0)) {
			case '-':
			case '+':
			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':
			case '8':
			case '9':
				 if (name.contains(".")) {
					 try { Double.parseDouble(name); return "double"; }
					 catch (NumberFormatException e) { Utils.error("This looks to be a double but could not parse it: '" + name + "'."); }
				 }
				 try { Integer.parseInt(name); return "integer"; }
				 catch (NumberFormatException e) { Utils.error("This looks to be an integer but could not parse it: '" + name + "'."); }

		}
		return null;
	}

	// Should this be interpreted as a Constant (or a Variable)?
	public boolean isaConstantType(String name) {
		if (name == null || name.length() < 1) { return false; } // Only variables can be nameless.
		Character char0 = name.charAt(0);
		if (char0 == '_') { return false; } // Underscore always indicates variable ala' YAP.
		if (doVariablesStartWithQuestionMarks()) { return char0 != '?'; }
		if (name.equals("")) { return true; }
		// Ellipsis in range: is considered a constant
		if (name.equals("...")) { return true; }
		switch (char0) {
			case '"':
			case '\'':  // Quoted strings are always constants.
			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':
			case '8':
			case '9': return true;  // Assume this is a number.  TODO confirm by parsing a number?
			case '_': return false; // Underscore always indicates variable ala' YAP.  Now checked above, but leave here regardless.
		}
		boolean startsWithLowerCase = Character.isLowerCase(name.charAt(0));

		if (usingStdLogicNotation()) { return !startsWithLowerCase; }
		return startsWithLowerCase;
	}

	private Map<String,Integer> mapForGetUniqueStringConstant = new HashMap<String,Integer>(4);
	public StringConstant getUniqueStringConstant(String string) {
		Integer lookup = mapForGetUniqueStringConstant.get(string);
		if (lookup == null) {
			lookup = 0;
		}
		boolean cleanString = true;
		while (true) {
			lookup++;
			mapForGetUniqueStringConstant.put(string, lookup);
			String combo  = ((string.charAt(0) == '"' || (FileParser.allowSingleQuotes && string.charAt(0) == '\'')) 
								? string.charAt(0) + string.substring(1, string.length() - 1) + lookup + string.charAt(0) // Put inside any quotes.
							    :  string + lookup);								
			String newStr = standardize(combo, cleanString);
			if (stringConstantHash.get(newStr) == null) {
				return getStringConstant(newStr, cleanString); // Assume caller adds an underscore if necessary.  If user calls sufficiently often something like getUniqueStringConstant(str1) and getUniqueStringConstant(str), a name collision can occur.
			}
			if (lookup > 123456) { Utils.error("getUniqueStringConstant: string =" + string); }
		}
	}
	public StringConstant getUnCleanedStringConstant(String name) { // This means we'll keep quote marks here (and so wont match to unquoted version) - so use carefully!
		return getStringConstant(null, name, false);
	}
	public StringConstant getStringConstant(String name) {
		return getStringConstant(null, name);
	}
    public StringConstant getStringConstant(String name, boolean cleanString) {
		return getStringConstant(null, name, cleanString);
	}
	public StringConstant getStringConstant(TypeSpec spec, String name) {
		return getStringConstant(spec, name, defaultValue_cleanStringConstants);
	}
	public StringConstant getStringConstant(TypeSpec spec, String name, boolean cleanString) {
		return getStringConstant(spec, (doVariablesStartWithQuestionMarks() || !cleanString ? name : Utils.setFirstCharToRequestedCase(name, usingStdLogicNotation())), cleanString, true);
	}
	public StringConstant getStringConstant(TypeSpec spec, String nameRaw, boolean cleanString, boolean complainIfWrongCase) {
		if (cleanString && !isaConstantType(nameRaw)) {
			if (complainIfWrongCase) { Utils.error("Since variableIndicator = " + variableIndicator  + ", '" + nameRaw + "' is not a constant."); }
			return null; // The caller can handler the error (e.g., the parser might want to report the line number).
		}

		boolean hadQuotesOriginally = false;
		// Handle quote marks.
		if (nameRaw != null && nameRaw.length() > 0 && (nameRaw.charAt(0) == '"' || (FileParser.allowSingleQuotes && nameRaw.charAt(0) == '\''))) { // Treat x, 'x', 'X', "x", and "X" as the same (assuming that lowercaseMeansVariable=false; otherwise the 'bare' x should be X; also ignoreCaseOfStringsOtherThanFirstChar=false means case does matter).
			Character lastChar = nameRaw.charAt(nameRaw.length() - 1);
			if (lastChar != '"' && (!FileParser.allowSingleQuotes || lastChar != '\'')) { 
				Utils.warning("\nSeems maybe there should be a quote mark at the end of\n  " + nameRaw + "\nbut read '" + lastChar + "'.");
			//	nameRaw = nameRaw.replace("\"", "\\\""); // Escape any quote marks in this string.  TODO - should we see if they are ALREADY escaped?
			} else {
				nameRaw = nameRaw.substring(1, nameRaw.length() - 1); // Drop the first and last characters (i.e., the quote marks).
				hadQuotesOriginally = true;
			}
			//Utils.println("*** INNER NAME FOR [" + name + "] is [" + hashName.toLowerCase() + "].");
		} // else { Utils.println("***** No quotes in " + name + "."); }

		String name = (cleanString ? cleanString(nameRaw, hadQuotesOriginally) : nameRaw);
		if (name == null)      { name = "nullString";  }
//		if (name.length() < 1) { name = "emptyString"; } // Changed by JWS 5/11.

		String         stdName     = standardize(name, cleanString, hadQuotesOriginally); // Hash case-independently.
		StringConstant hashedValue = stringConstantHash.get(stdName);
		if (hashedValue != null) {
			if (spec != null) { hashedValue.setTypeSpec(spec); }
			return hashedValue;
		}

		// NOTE: "!clean" below had been "!clean|| hadQuotesOriginally
		StringConstant result = new StringConstant(this, name, !cleanString, doVariablesStartWithQuestionMarks(), usingStdLogicNotation(), spec); // Use the first name encountered.
		stringConstantHash.put(stdName, result);
		return result;
	}
	public Constant getStringConstantButCheckIfNumber(TypeSpec spec, String name, boolean cleanString) {
		Number viewNameAsNumber = isaQuotedNumber(name);
		if (viewNameAsNumber != null) { 
			return getNumericConstant(spec, viewNameAsNumber.doubleValue()); // Other code (chooseStringForDouble) checks to see if this is really an integer.
		}
		return getStringConstant(spec, name, cleanString);
	}
	
	private Number isaQuotedNumber(String name) {
		if (name == null) { return null; }
		if (name.charAt(0) != '"'  || (name.charAt(name.length() - 1) != '"')) { return null; }
		
		if (!Character.isDigit(name.charAt(1))) { return null; }
		
		String innerStr = name.substring(1, name.length() - 1);
		try { 
			return Integer.parseInt(innerStr);
		} catch (NumberFormatException e1) {
			try {
				return Double.parseDouble(innerStr);
			} catch (NumberFormatException e2) {
				return null;
			}
		}
	}

	/* THIS CODE IS NO LONGER USED SINCE THE SAME TERM CAN HAVE MULTIPLE NAMES - JWS, 5/09
	// This is used for terms of the form:  p(x=1, y=2).  Ie, the termNames are the 'x' and the 'y' in this example.
	// NOTE: for now, this code is written all in one method, rather than via object-oriented style.
	// If named arguments get more use, this should be cleaned up.  TODO
	public Term assignTermName(Term term, String termName) {
		if (term     == null) { Utils.error("Cannot have term=null here."); }
		if (termName == null) { Utils.error("Cannot have termName=null here."); }
		if (termName.equalsIgnoreCase(term.argumentName)) { return term; } // Already properly named.
		if (term instanceof Variable) {
			Variable       var       = (Variable) term;
			String         varName   = var.name;
			String         stdName   = (termName + "=" + varName).toLowerCase();
			Stack<Variable> hashedStackOfValues = variableHash.get(stdName);
			if (hashedStackOfValues != null && !hashedStackOfValues.empty()) {
				Variable result = hashedStackOfValues.peek();  // Return the top of the stack.
				if (result == null) { Utils.error("This should never happen."); }
				if (result.argumentName == null) {
					result.argumentName = termName;
				}
				else if (!result.argumentName.equalsIgnoreCase(termName)) {
					Utils.error("This variable is already named: '" + result.argumentName + "' so cannot name to '" + termName + "'.  Variable: " + term);
				}
				if (result.getTypeSpec() != term.getTypeSpec()) {
					Utils.error("These type spec's should match '" + term.getTypeSpec() + "' and '" + result.getTypeSpec() + "'.");
				}
				return result;
			}

			Variable        result = new Variable(this, varName, overallCounter++, term.getTypeSpec());
			Stack<Variable> stack  = new Stack<Variable>();
			stack.push(result);
			variableHash.put(stdName, stack);  // TODO - will these unify?  and if not, are constants also buggy????
			variableNamesSeen.add(stdName);
			// Utils.println(" add variable (version 2) " + stdName);
			result.argumentName = termName;
			return result;
		}
		if (term instanceof StringConstant) {
			String         constName   = ((StringConstant) term).name;
			String         stdName     = (termName + "=" + constName). toLowerCase(); // Hash case-independently.
			StringConstant hashedValue = stringConstantHash.get(stdName);
			if (hashedValue != null) {
				if (hashedValue.argumentName == null) {
					Utils.error("Should have an argument name: '" + hashedValue + "'.");
					// hashedValue.argumentName = termName;
				}
				else if (!hashedValue.argumentName.equalsIgnoreCase(termName)) {
					Utils.error("This string constant is already named: '" + hashedValue.argumentName + "' so cannot name to '" + termName + "'.  Constant: " + term);
				}
				return hashedValue;
			}

			StringConstant result = new StringConstant(this, constName, doVariablesStartWithQuestionMarks(), lowercaseMeansVariable, term.getTypeSpec());
			stringConstantHash.put(stdName, result);
			result.argumentName = termName;
			return result;
		}
		if (term instanceof NumericConstant) {
			NumericConstant numConst = (NumericConstant) term;
			String stdName = (termName + "=" + numConst.getName()).toLowerCase(); // Hash case-independently.
			NumericConstant hashedValue = numericConstantHash.get(stdName);

			if (hashedValue != null) {
				if (hashedValue.argumentName == null) {
					Utils.error("Should have an argument name: '" + hashedValue + "'.");
					//hashedValue.argumentName = termName;
				}
				else if (!hashedValue.argumentName.equalsIgnoreCase(termName)) {
					Utils.error("This numeric constant is already named: '" + hashedValue.argumentName + "' so cannot name to '" + termName + "'.  Constant: " + term);
				}
				return hashedValue;
			}

			NumericConstant result = new NumericConstant(this, numConst.value, numConst.getType(), numConst.getTypeSpec());
			numericConstantHash.put(stdName, result);
			result.argumentName = termName;
			return result;
		}
		if (Function.isaConsCell(term)) { // In order to get lists to pretty-print nicely, need to handle this specially.
			ConsCell termAsCons   = (ConsCell) term;
			String   functName = termAsCons.functionName.name;
			// Not necessary to put the '=' here, since function instances aren't checked via '==' anyway.	Instead, just copy.
			ConsCell newConsCell = getConsCell(getFunctionName(functName), termAsCons.getTypeSpec());
			newConsCell.getArguments() = termAsCons.getArguments();
			newConsCell.argumentName = termName;
			return newConsCell;
		}
		if (term instanceof Function) {
			Function termAsF   = (Function) term;
			String   functName = termAsF.functionName.name;
			// Not necessary to put the '=' here, since function instances aren't checked via '==' anyway.	Instead, just copy.
			Function newFunction = getFunction(getFunctionName(functName), termAsF.getArguments(), termAsF.getTypeSpec());
			newFunction.argumentName = termName;
			return newFunction;
		}
		Utils.error("Unknown type of term: '" + term + "'.");
		return null;
	}

	public Term unassignTermName(Term term) {
		if (term.argumentName == null) { return term; } // Already  unnamed.
		if (term instanceof NumericConstant) {
			NumericConstant numConst = (NumericConstant) term;
			String stdName = numConst.getName().toLowerCase(); // Hash case-independently.
			NumericConstant hashedValue = numericConstantHash.get(stdName);

			if (hashedValue != null) {
				if (hashedValue.argumentName != null) {
					Utils.error("This numeric constant has a name: '" + hashedValue.argumentName + "', so cannot be unnamed.  StdName='" + stdName + "'.\n hashedValue='" + hashedValue + "'  hashMap=" + numericConstantHash);
				}
				return hashedValue;
			}

			NumericConstant result = new NumericConstant(this, numConst.value, numConst.getType(), numConst.getTypeSpec());
			numericConstantHash.put(stdName, result);
			result.argumentName = null;
			return result;
		}
		if (term instanceof StringConstant) {
			String         constName   = ((StringConstant) term).name;
			String         stdName     = constName.toLowerCase(); // Hash case-independently.
			StringConstant hashedValue = stringConstantHash.get(stdName);
			if (hashedValue != null) {
				if (hashedValue.argumentName != null) {
					Utils.error("This string constant has a name: '" + hashedValue.argumentName + "', so cannot be unnamed.");
				}
				return hashedValue;
			}

			StringConstant result = new StringConstant(this, constName, doVariablesStartWithQuestionMarks(), lowercaseMeansVariable, term.getTypeSpec());
			stringConstantHash.put(stdName, result);
			result.argumentName = null;
			return result;
		}
		if (term instanceof Variable) {
			Variable       var       = (Variable) term;
			String         varName   = var.name;
			String         stdName   = varName.toLowerCase();
			Stack<Variable> hashedStackOfValues = variableHash.get(stdName);
			if (hashedStackOfValues != null && !hashedStackOfValues.empty()) {
				Variable result = hashedStackOfValues.peek();  // Return the top of the stack.
				if (result == null) { Utils.error("This should never happen."); }
				if (result.argumentName != null) {
					Utils.error("This variable has a name: '" + result.argumentName + "', so cannot be unnamed.");
				}
				if (result.getTypeSpec() != term.getTypeSpec()) {
					Utils.error("These type spec's should match '" + term.getTypeSpec() + "' and '" + result.getTypeSpec() + "'.");
				}
				return result;
			}

			Variable        result = new Variable(this, varName, overallCounter++, term.getTypeSpec());
			Stack<Variable> stack  = new Stack<Variable>();
			stack.push(result);
			variableHash.put(stdName, stack); //  Utils.println(" add variable (version 3) " + stdName);
			variableNamesSeen.add(stdName);
			result.argumentName = null;
			return result;
		}
		if (Function.isaConsCell(term)) { // See explanation above for why ConsCell needs to be treated specially.
			ConsCell termAsCons   = (ConsCell) term;
			String   functName    = termAsCons.functionName.name;
			ConsCell newConsCell  = getConsCell(getFunctionName(functName), termAsCons.getTypeSpec());
			newConsCell.getArguments() = termAsCons.getArguments();
			newConsCell.argumentName = null;
			return newConsCell;
		}
		if (term instanceof Function) {
			Function    termAsF  = (Function) term;
			String    functName  = termAsF.functionName.name;
			Function newFunction = getFunction(getFunctionName(functName), termAsF.getArguments(), termAsF.getTypeSpec());
			newFunction.argumentName = null;
			return newFunction;
		}
		Utils.error("Unknown term type: '" + term + "'.");
		return null;
	}
	*/


	public boolean needsToBeQuoted(String name) {
		if (name == null || name.length() < 1) { return false; }
		if (doVariablesStartWithQuestionMarks()) { return false; } // WAS:  name.charAt(0) == '?'; }
		if (name.length() == 0) { return true; }
		if ((usingStdLogicNotation() && Character.isLowerCase(name.charAt(0))) || // Need to quote to override current variable-versus-constant 'rule.'
		    (usingPrologNotation()   && Character.isUpperCase(name.charAt(0)))) { return true; }

		char[] characters = name.toCharArray();
		for (int i = 0; i < name.length(); i++) {
			if (!Character.isLetterOrDigit(characters[i])) { return true; }

		}
		return false;

	}

	protected int chooseStringForDouble(double value) { // NOTE: need to extend to handle long's. TODO
		int valueAsInt = (int) value;

		if (Utils.diffDoubles(value, valueAsInt)) { // The integer value is sufficiently different than the double, so use the double.
		//	Utils.println("  diff: " + valueAsInt + " and " + value);
			return NumericConstant.isaDouble;
		}
	//	Utils.println("  same: " + valueAsInt + " and " + value);
		return     NumericConstant.isaInteger;
	}

	// Uniquely store numbers (which will waste memory if lots of numbers ...).  Notice that matching will be as exact as the string rep, which seems reasonable.
	// It is silly to duplicate this code just due to the type of the number, but clean up later.  TODO
	public NumericConstant getNumericConstant(int value) {
		return getNumericConstant(null, value);
	}
	public NumericConstant getNumericConstant(long value) {
		return getNumericConstant(null, value);
	}
	public NumericConstant getNumericConstant(TypeSpec spec, int value) {
		return getNumericConstant(spec, value, NumericConstant.isaInteger, Integer.toString(value)); // So '1' and '1.0' match, convert everything to a double.
	}
	public NumericConstant getNumericConstant(TypeSpec spec, long value) {
		return getNumericConstant(spec, value, NumericConstant.isaLong,       Long.toString(value));
	}
	public NumericConstant getNumericConstant(double value) {
		return getNumericConstant(null, value);
	}
	public NumericConstant getNumericConstant(TypeSpec spec, double value) {
		int ncType = chooseStringForDouble(value);
		return getNumericConstant(spec, value, ncType, (ncType == NumericConstant.isaInteger ? Integer.toString((int) value) : Double.toString(value)));
	}
	public NumericConstant getNumericConstant(float value) {
		return getNumericConstant(null, value);
	}
	public NumericConstant getNumericConstant(TypeSpec spec, float value) {
		return getNumericConstant(spec, (double) value);
	}
	private NumericConstant getNumericConstant(TypeSpec spec, Number value, int type, String stringVersion) {
		String stdName = standardize(stringVersion); // Hash case-independently, even if a number (could use scientific notation).
		NumericConstant hashedValue = numericConstantHash.get(stdName);

		if (hashedValue != null) {
			if (spec != null) { hashedValue.setTypeSpec(spec); }
			return hashedValue; }

		NumericConstant result = new NumericConstant(this, value, type, spec);
		numericConstantHash.put(stdName, result);
		return result;
	}

	////////////////////// Type Ranges ////////////////////

	public void recordPossibleTypes(String categoryRaw, List<? extends Term>possibleValues) {
		String category       = cleanString(categoryRaw);
		String stdName        = standardize(category); // Hash case-independently.
		Type   categoryAsType = isaHandler.getIsaType(stdName);

		Set<Term> oldValue = getKnownConstantsOfThisType().get(categoryAsType);
		if (oldValue != null) { Utils.error("Have already specified a list of possible values for " + categoryAsType
												+ ".  The old values: " + oldValue + " and the new: " + possibleValues + "."); }

		// Confirm no duplicates in this list.  This is O(n^2) but these lists shouldn't be too long ...
		int dups = 0;
		Set<Term> duplicated = null;
		for (Term c : possibleValues) if (duplicated == null || !duplicated.contains(c)) {
			// The above confirms there were no previous constants of this type, but still need to check that none of these constants are of some other type.
			// if (constantToTypesMap.containsKey(c)) { Utils.error("Constant '" + c + "' is already marked as being of types = '" + constantToTypesMap.containsKey(c) + "', so cannot also set it to type=" + categoryAsType  + "."); }
			int count = 0;
			for (Term d : possibleValues) if (c.equals(d)) { count++; }
			if (count > 1) {
				if (duplicated == null) { duplicated = new HashSet<Term>(4); }
				duplicated.add(c);
				Utils.println("  Warning: multiple copies (" + count + ") of '" + c + "' in types for " + category + " = " + possibleValues + ".  Discarding the duplicates.");
				dups += count;
			}
		}
		List<Term> cleanedPossibleValues = (dups > 0 ? null : new ArrayList<Term>(possibleValues));
		if (dups > 0) {
			cleanedPossibleValues = new ArrayList<Term>(possibleValues.size() - dups);
			for (Term c : possibleValues) if (!duplicated.contains(c)) {
				if (c == null) { Utils.error("This should not happen: " + possibleValues); }
				cleanedPossibleValues.add(c);
			}

			// Now need to add ONE copy of all the duplicated items.  TODO - this loses order, so if that matters, add the FIRST duplicate and mark in a 2nd hashMap.
			for (Iterator<Term> cIter = duplicated.iterator(); cIter.hasNext(); ) {
			     cleanedPossibleValues.add(cIter.next());
			}
		}
		for (Term c : cleanedPossibleValues) { addNewConstantOfThisType(c, categoryAsType);	}
	}

	/**
	 * Retrieves the constants of the given type. Inheritance is not
	 * considered when looking at the types, so the types are exact.
	 *
	 * @param type
	 *                The type of the constants you want to retrieve.
	 * @return The constants of exactly the given type, as a hash map of
	 *         something.
	 */
	public Set<Term> getConstantsOfExactlyThisType(Type type) {
	    return getKnownConstantsOfThisType().get(type);
	}

	/**
	 * Retrieves the constants of the given type. Inheritance is not
	 * considered when looking at the types, so the types are exact.
	 *
     * @param type
     * @return The constants of exactly the given type as a list, or null if
	 *         there are no such constants.  A FRESH list is returned.
	 */
	public Set<Term> getConstantsOfExactlyThisTypeAsList(Type type) { // TODO if this is too slow, keep a HashSet AND a list version (i.e., the usual time-space tradeoff).
	    Set<Term> types = getKnownConstantsOfThisType().get(type);
	    if (types == null) { return null; }
	    Set<Term> result =  new HashSet<Term>(4);
	    result.addAll(types);
	    return result;
	}

	public void addNewConstantOfThisType(Term constant, Type type) {
		addNewConstantOfThisType(constant, type, true);
	}
	public void addNewConstantOfThisType(Term constant, Type type, boolean callAddISA) {
		if (debugLevel > 2) { Utils.println("addNewConstantOfThisType to isaHetrarchy: " + constant + " type=" + type); }
		//if (type.typeName.equals("Phase") || type.typeName.equals("Position") ) {Utils.println("addNewConstantOfThisType to isaHetrarchy: " + constant + " type=" + type); }
		Type constantAsType = isaHandler.getIsaType(constant);
		isaHandler.addISA(constantAsType, type);
		Set<Term> existingConstantsOfThisType = getConstantsOfExactlyThisType(type);

		if (existingConstantsOfThisType == null) { // Create this if needed.
			existingConstantsOfThisType = new HashSet<Term>(32);
			getKnownConstantsOfThisType().put(type, existingConstantsOfThisType);
		}
		if (existingConstantsOfThisType.contains(constant)) { return; } // Already in the map.
		existingConstantsOfThisType.add(constant);
		setTypeOfConstant(constant, type, callAddISA); // Avoid a circularity.
	}

	public void addConstantToISA(Term childAsStringConstant, Type childType, Type parentType) {
		isaHandler.addISA(childType, parentType);
		addNewConstantOfThisType(childAsStringConstant, parentType, false);
	}

	public List<Type> getTypesOfConstant(Term constant, boolean complainIfNull) {
		List<Type> result = constantToTypesMap.get(constant);
		if (result == null && complainIfNull) { Utils.error("Cannot find type(s) of '" + constant + "' in " + constantToTypesMap); }
		return result;
	}

	public void setTypeOfConstant(Term constant, Type type, boolean callAddIsa) {
		List<Type> oldTypes = getTypesOfConstant(constant, false);

		if (oldTypes != null && !oldTypes.contains(type)) {
			oldTypes.add(type);
		}
		if (oldTypes == null) {
			List<Type> types = new ArrayList<Type>(1);
			types.add(type);
			constantToTypesMap.put(constant, types);
		}
		if (callAddIsa) { isaHandler.addISA(constant, type); } // Keep the ISA hetrarchy and the information about constants consistent.  Also, avoid a circularity (wouldn't be an infinite loop due to other checking, but nevertheless would waste some cycles).
	}

	////////////////////// Variables ////////////////////

	public void pushVariableHash() { // Utils.println(" pushVariableHash");
		if (variableHash == null) { Utils.error("variableHash should not be null!"); }
		stackOfVariableHashes.push(variableHash);
		variableHash = new HashMap<String,Stack<Variable>>(16); // Assume these are small, since used for renaming, etc.
	}
	public void popVariableHash() { // Utils.println(" popVariableHash");
		if (stackOfVariableHashes != null) { variableHash = stackOfVariableHashes.pop(); } // Revert to previous.
		else { Utils.error("stackOfVariableHashes should not be null!"); }
	}

	public Variable pushVariable(TypeSpec spec, String name) {
		checkForValidVariableName(name);
		if (name != null && name.length() > 0 && name.charAt(0) == '_') { return new Variable(this, name, overallCounter++, spec); } // Ala' YAP Prolog, variables that start with underscores are always unique.
		Stack<Variable> varStack = variableHash.get(name);
		if (varStack != null) {
			Variable variable = new Variable(this, name, overallCounter++, spec);
			varStack.push(variable);
			return variable;
		}
		return getExternalVariable(spec, name);
	}

	private void checkForValidVariableName(String name) {
		if (name == null || name.length() < 1) { return; }
		if (name.charAt(0) == '_') { return; } // Allow strings starting with an underscore to be variable names ala' YAP.
		if (doVariablesStartWithQuestionMarks()) {
			if (name.charAt(0) !='?') { Utils.error("Variables need to start with a '?' but you provided: " + name); }
		} else if (usingStdLogicNotation() && Character.isUpperCase(name.charAt(0))) {
			Utils.error("Variables need to start with a lower-case letter but you provided: " + name);
		} else if (usingPrologNotation()   && Character.isLowerCase(name.charAt(0))) {
			Utils.error("Variables need to start with an upper-case letter but you provided: " + name);
		}
	}

	public void  popVariable(String name) {
		Stack<Variable> varStack = variableHash.get(name);
		if (varStack != null) { varStack.pop(); }
	}

	/*
	 * Rename all the variables in this sentence starting at 'A'.
	 */
	public Sentence renameAllVariables(Sentence s) {
		Collection<Variable> vars = s.collectAllVariables();
		if (Utils.getSizeSafely(vars) < 1) { return s; }
		BindingList bl = renameAllVariables(vars, s);
		Sentence newS = s.applyTheta(bl.theta);
		if (debugLevel > 10) { Utils.println("% renameAllVariables: bl = " + bl); Utils.waitHere("newS = " + newS); }
		return newS;
	}

	public BindingList renameAllVariables(Collection<Variable> vars, AllOfFOPC owner) { // If owner != null, variables that only appear once are renamed to "_";
		if (vars == null) { return null; }
		BindingList bl = new BindingList();
		resetVarCounters();
		if (debugLevel > 2) { Utils.println("% renameAllVariables: starting at counter=" + varCounter); }
		for (Variable var : vars) {
			Variable v = (countVarOccurrencesInFOPC(var, owner) == 1 ? getExternalVariable(var.getTypeSpec(), "_", true) :  getNewGeneratedVariable(true));
			if (debugLevel > 2) { Utils.println("%  var = " + var.getName() + ":" + var.counter + "  v=" + v + " + varCounter=" + varCounter); }
			bl.addBinding(var, v);
		}
		resetVarCounters();
		return bl;
	}

	public int countVarOccurrencesInFOPC(Variable v, AllOfFOPC fopc) {
		if (fopc == null || v == null) { return 0; }
		return fopc.countVarOccurrencesInFOPC(v);
	}

	public void reportVarsInFOPC(Sentence s) {
		Collection<Variable> vars = s.collectAllVariables();
		Utils.println("% Variables in: " + s);
		for (Variable var : vars) { Utils.print(" " + var.getName() + ":" + var.counter); }
		Utils.println("");
	}

	public void reportVarsInFOPC(Term t) {
		Collection<Variable> vars = t.collectAllVariables();
		Utils.println("% Variables in: " + t);
		for (Variable var : vars) { Utils.print(" " + var.getName() + ":" + var.counter); }
		Utils.println("");
	}
	///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	// This is used to keep track of the parent of a variable when it arises from copying.  Currently only Variable.copy() adds to it.
	// It is used when in a hack for the WisconsinRelevanceInterpreter and should not be used elsewhere.
	// The same map is used here as in Binding so applyTheta can be used to reverse these copies where doing so is needed.
	public Map<Variable,Term> parentVarMap = new HashMap<Variable,Term>(4);
	private boolean recordParentVariables = false;
	public void recordParentVariable(Variable newVar, Variable oldVar) {
		if (recordParentVariables) { parentVarMap.put(newVar, oldVar); }
	}
	public Term getParentVariable(Variable var) {
		return parentVarMap.get(var);
	}
	public void turnOnParentVarMap() {
		parentVarMap.clear();
		recordParentVariables = true;
	}
	public void turnOffParentVarMap() {
		parentVarMap.clear();
		recordParentVariables = false;
	}
	///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	public String getVariablePrefix() {
		if (doVariablesStartWithQuestionMarks()) { return "?"; }
		return "";
	}

	public String convertToVarString(String name) {
		if (doVariablesStartWithQuestionMarks()) {
			if (name != null && name.charAt(0) == '?') { return name; }
			return "?" + name;
		}
		return Utils.setFirstCharToRequestedCase(name, usingPrologNotation());
	}
	public Variable getExternalVariable(String name) {
		return getExternalVariable(name, false);
	}
	public Variable getExternalVariable(String name, boolean createNewVariable) {
	//	if (isaConstantType(name)) {  CONVERT AS NEEDED
	//		if (doVariablesStartWithQuestionMarks()) { Utils.error("Since variablesStartWithQuestionMarks=" + doVariablesStartWithQuestionMarks() + ", '" + name + "' cannot be the name of a variable."); }
	//		Utils.error("Since lowercaseMeansVariable=" + lowercaseMeansVariable + ", '" + name + "' cannot be the name of a variable.");
	//	}
		return getExternalVariable(null, convertToVarString(name), createNewVariable);
	}
	public Variable getExternalVariable(TypeSpec spec, String name, boolean createNewVariable) {
		if (createNewVariable || (name != null && name.length() > 0 && name.charAt(0) == '_')) { return pushVariable(spec, name); } // A variable of the form '_' is always a NEW variable.
		return getExternalVariable(spec, name);
	}
	private Variable getExternalVariable(TypeSpec spec, String name) {
		Variable variable = help_getVariable(spec, name, false);
		if (name == null) { Utils.waitHere("getVariable: name=null"); }
//		if ( name != null ) variableNamesSeen.add(name);
        variableNamesSeen.add(name);
		return variable;
	}
    public Variable getExternalVariable(String type, String postfix, long counter) {
		if (doVariablesStartWithQuestionMarks()) {
			String newType = (type.charAt(0) == '?' ? type : "?" + type);
			return getExternalVariable(null, newType + postfix + "_" + counter);  // These could be GENERATED vars if we knew there were no name clashes when printed out and read back in.
		}
		String VtoUse = (usingStdLogicNotation() ? "v" : "V");
		return getExternalVariable(null, VtoUse + (++var2Counter) +  "_" + type + postfix);
	}

    public Variable getTypedExternalVariable(String type, char modeAsChar, long counter) {
		if (doVariablesStartWithQuestionMarks()) {
			String newType = (type.charAt(0) == '?' ? type : "?" + type);
			return getExternalVariable(new TypeSpec(modeAsChar, type, this), newType + "_" + counter);
		}
		String VtoUse = (usingStdLogicNotation() ? "v" : "V");
		return getExternalVariable(new TypeSpec(modeAsChar, type, this), VtoUse + counter +  "_" + type);
	}

	public Variable getGeneratedVariable(String name, boolean createNewVariable) {
	//	if (isaConstantType(name)) {
	//		if (doVariablesStartWithQuestionMarks()) { Utils.error("Since variablesStartWithQuestionMarks=" + doVariablesStartWithQuestionMarks() + ", '" + name + "' cannot be the name of a variable."); }
	//		Utils.error("Since lowercaseMeansVariable=" + lowercaseMeansVariable + ", '" + name + "' cannot be the name of a variable.");
	//	}
		return getGeneratedVariable(null, convertToVarString(name), createNewVariable);
	}
	public Variable getGeneratedVariable(TypeSpec spec, String name, boolean createNewVariable) {
		if (createNewVariable || (name != null && name.length() > 0 && name.charAt(0) == '_')) { return pushVariable(spec, name); } // A variable of the form '_' is always a NEW variable.
		return getGeneratedVariable(spec, name);
	}
	private Variable getGeneratedVariable(TypeSpec spec, String name) {
		Variable var = help_getVariable(spec, name, true);
		if (name == null) { Utils.waitHere("getGeneratedVariable: name=null"); }
		internalVariableNamesSeen.add(name);
		return var;
	}

	public Variable getNewUnamedVariable() {
		return new Variable(this, null, overallCounter++, null, true); // These do not need to be hashed.
	}
	public Variable getNewNamedGeneratedVariable() {
		return getNewGeneratedVariable(false);
	}

	private Variable help_getVariable(TypeSpec spec, String name, boolean generatedVar) {
		Stack<Variable> hashedStackOfValues = variableHash.get(name); // TODO - could have one hash for each type of variable, but seems ok to merge.

		if (hashedStackOfValues != null && !hashedStackOfValues.empty()) {
			Variable var = hashedStackOfValues.peek();  // Return the top of the stack.
			if (spec != null) { var.setTypeSpec(spec); }
			return var;
		}
		checkForValidVariableName(name);

		Variable        variable = new Variable(this, name, overallCounter++, spec, generatedVar);
		Stack<Variable> stack    = new Stack<Variable>();
		stack.push(variable);
//        if (name != null) {
            variableHash.put(name, stack);  // Utils.println(" add variable " + name);
//        }
        return variable;
	}

	public void stackTheseVariables(Collection<Variable> variables) { // This is used when entering the scope of a ForAll or Exists.
		for (Variable var : variables) { pushVariable(var.typeSpec, var.getName()); }
	}

	public void unstackTheseVariables(Collection<Variable> variables) { // This is used when exiting the scope of a ForAll or Exists.
		for (Variable var : variables) { popVariable(var.getName()); }
	}

	// Clear the stack of variables "in view" - so all new variable strings will get fresh instances.
	public void resetAllVariables() { // Utils.println(" clear variable hash");
		if (variableHash == null) { return; }
		else                      { variableHash.clear(); }
	}

	private Variable getNewGeneratedVariable(boolean dontcheck_variableNamesSeen) { // Note: 'a-z' not the same as dealing with base 10 and '0-9' since the allowed string 'aa' is different from 'a' whereas '00' is an illegal digit string.
		while (true) { // NOTE: if alphabet.length != 24, all those calc's will be off, though should be ok if there are MORE than 24 chars - in that case, we'd just skip some combo's.
			int firstChar    = (int) (varCounter % 24); // Remember that 'l' and 'o' are dropped.
			String nameToUse = alphabet.substring(firstChar, firstChar+1);
			if      (varCounter <  24) {

			}
			else if (varCounter >=     24 && varCounter <      576) {
				int secondChar  = (int) (varCounter /    24); // Once we've gone from 'a' to 'z', go to 'aa' to 'az' to 'zz' then from 'aaa' to 'aaz' to 'zzz' (and maybe one or more cycles), after which go to 'aN' where N indicates the number of repeats.
				nameToUse = alphabet.substring(secondChar-1, secondChar) + nameToUse;
			}
			else if (varCounter >=    576 && varCounter <    13824) {
				int secondChar = (int) ((varCounter /     24) % 24);
				int thirdChar  = (int) ( varCounter /    576);
				nameToUse =   alphabet.substring(thirdChar-1, thirdChar)
							+ alphabet.substring(secondChar,  secondChar+1) + nameToUse;
			}
			else if (varCounter >=  13824 && varCounter <  331776) {
				int secondChar = (int) ((varCounter /     24) % 24);
				int thirdChar  = (int) ((varCounter /    576) % 24);
				int fourthChar = (int) ( varCounter /  13824);
				nameToUse =   alphabet.substring(fourthChar-1, fourthChar)
							+ alphabet.substring(thirdChar,    thirdChar+1)
							+ alphabet.substring(secondChar,   secondChar+1) + nameToUse;
			}
			else if (varCounter >= 331776 && varCounter < 7962624) {
				int secondChar = (int) ((varCounter /     24) % 24);
				int thirdChar  = (int) ((varCounter /    576) % 24);
				int fourthChar = (int) ((varCounter /  13824) % 24);
				int fifthChar  = (int) ( varCounter / 331776);
				nameToUse =   alphabet.substring(fifthChar-1, fifthChar)
							+ alphabet.substring(fourthChar,  fourthChar+1)
							+ alphabet.substring(thirdChar,   thirdChar+1)
							+ alphabet.substring(secondChar,  secondChar+1) + nameToUse;
			}
			else if (varCounter >= 7962624 && varCounter < 191102976) {
				int secondChar = (int) ((varCounter  /      24)) % 24;
				int thirdChar  = (int) ((varCounter  /     576)) % 24;
				int fourthChar = (int) ((varCounter  /   13824)) % 24;
				int fifthChar  = (int) ((varCounter  /  331776)) % 24;
				int sixthChar  = (int) ( varCounter  / 7962624);
				nameToUse =   alphabet.substring(sixthChar-1, sixthChar)
							+ alphabet.substring(fifthChar,   fifthChar+1)
							+ alphabet.substring(fourthChar,  thirdChar+1)
							+ alphabet.substring(thirdChar,   thirdChar+1)
							+ alphabet.substring(secondChar,  secondChar+1) + nameToUse;
			}
			else { nameToUse += varCounter; }
			String properCase = convertToVarString(nameToUse);
			varCounter++;
			//Utils.println("Got new var (counter=" + varCounter + " mod=" + (varCounter % 24) + "): " + properCase + ", name=" + nameToUse + ", firstChar=" + firstChar);
			if (dontcheck_variableNamesSeen || !variableNamesSeen.contains(properCase)) { // Make sure no inadvertant name collisions.  TODO - could also use this to filter out bad four-letter words (but I'd rather not type up such a list ...).
				// Utils.warning("% This variable already exists: " + properCase + "  varCounter = " + Utils.comma(varCounter));
				return getGeneratedVariable(null, properCase);
			}
		}
	}
	/*  Trevor (or whoever): these might be needed in the Student.  See me on how to replace after I cleaned up some things in here.
	public Variable getNewVariable(String type) {	MAYBE CHANGE "Variable" TO "V2var" in these names?
		return getNewVariable(type, "");
	}
	public Variable getNewVariable(String type, String postfix) {
		return getNewVariable(type, postfix, ++var2Counter);
	}
	public Variable getNewVariable(String type, String postfix, long counter) {
		if (doVariablesStartWithQuestionMarks()) {
			String newType = (type.charAt(0) == '?' ? type : "?" + type);
			return getExternalVariable(null, newType + postfix + "_" + counter);  // These could be GENERATED vars if we knew there were no name clashes when printed out and read back in.
		}
		String VtoUse = (lowercaseMeansVariable ? "v" : "V");
		return getExternalVariable(null, VtoUse + (++var2Counter) +  "_" + type + postfix);
	}

	public Variable getNewTypedVariable(String type, char modeAsChar) {
		return getNewTypedVariable(type, modeAsChar, ++var2Counter);
	}
	public Variable getNewTypedVariable(String type, char modeAsChar, long counter) {
		if (doVariablesStartWithQuestionMarks()) {
			String newType = (type.charAt(0) == '?' ? type : "?" + type);
			return getExternalVariable(new TypeSpec(modeAsChar, type, this), newType + "_" + counter);
		}
		String VtoUse = (lowercaseMeansVariable ? "v" : "V");
		return getExternalVariable(new TypeSpec(modeAsChar, type, this), VtoUse + counter +  "_" + type);
	}
	*/


	public Term createNewSkolem(List<Variable> outerUniversalVars, TypeSpec typeSpec) {
		if (outerUniversalVars == null) {
			if (doVariablesStartWithQuestionMarks()) { return getStringConstant(typeSpec, "?skolem" + countOfSkolemFunctions++); }
			return getStringConstant(typeSpec, (usingStdLogicNotation() ? "Skolem" : "skolem") + countOfSkolemFunctions++);  // If no arguments, only need a constant.
		}
		FunctionName fName = getFunctionName("skolem" + countOfSkolemFunctions++);
		fName.isaSkolem = true;
		List<Term> arguments = new ArrayList<Term>(outerUniversalVars.size());
		arguments.addAll(outerUniversalVars);
		Function result = this.getFunction(fName, arguments, null);
		result.typeSpec = typeSpec;
		return result;
	}

	protected RecordHandler getRecordHandler() {
		return recordHandler;
	}

	public boolean allArgumentsConstant(Literal lit) {
		return help_allArgumentsConstant(lit.getArguments());
	}
	public boolean help_allArgumentsConstant(List<Term> items) {
		if (items == null) { return true; }
		for (Term term : items) {
			if (  term instanceof Function)  {
				if (!help_allArgumentsConstant(((Function) term).getArguments())) { return false; }
			}
			else if (!(term instanceof Constant)) { return false; }
		}
		return true;
	}

	// NOTE: this method has the SIDE EFFECT of adding 'lit' to 'hashedFactsByAllArgs' if not already in there, AND all the lit's arguments are constants.
	public boolean existingVariableFreeLiteral(Literal lit, Map<PredicateName,Map<List<Term>,List<Literal>>> hashedFactsByAllArgs) { // NOTE: this does NOT handle cases with variables.
		List<Term> args = lit.getArguments();
		int numbArgs = lit.numberArgs();
		if (!allArgumentsConstant(lit)) {
			return false;  // Need ALL arguments to be constants to use this hash.
		}
		List<Term> argsAsConstants = (numbArgs == 0 ? null : new ArrayList<Term>(numbArgs));
		if (args != null) for (Term term : args) {
			if (term == null) { Utils.error("Have arg=null in '" + lit); }
			argsAsConstants.add(term);
		}
		Map<List<Term>,List<Literal>> entry = hashedFactsByAllArgs.get(lit.predicateName);

		if (entry == null) { // New entry.
			entry = new HashMap<List<Term>,List<Literal>>(4);
			hashedFactsByAllArgs.put(lit.predicateName, entry);
		}
		List<Literal> listOfLiterals = entry.get(argsAsConstants);
		if (listOfLiterals == null) {
			listOfLiterals = new ArrayList<Literal>(4);
			entry.put(argsAsConstants, listOfLiterals);
		}
		else {
			// Utils.println("DUP: " + lit + " in " + entry);
			return true;
		}
		listOfLiterals.add(lit);
		return false;
	}

	public void setPredicatesHaveCosts(boolean value) {
		predicatesHaveCosts = value;
	}
	public boolean getPredicatesHaveCosts() {
		return predicatesHaveCosts;
	}

	public void setRelevance(PredicateName name, int arity, RelevanceStrength strength) {
		RelevantLiteral newStatement = new RelevantLiteral(name, arity, strength);

		if (relevantLiterals == null) { relevantLiterals = new HashSet<RelevantLiteral>(4); }
		relevantLiterals.add(newStatement);

		name.setRelevance(arity, strength);
	}
	public double convertRelevanceStrengthToCost(RelevanceStrength strength) {
		String hasBeenSet = getParameterSetting(strength.toString()); // See if overridden.
		if (hasBeenSet != null) { Double.parseDouble(hasBeenSet); }
		return strength.defaultCost();
	}
	public Set<RelevantLiteral> getCollectionOfRelevantLiterals() {
		return relevantLiterals;
	}

	private Map<String,SetParamInfo> hashOfSetParameters = new HashMap<String,SetParamInfo>(4);
	// If doing joint inference, one target would be evidence for other predicate
	// So it may have more than one mode for target. This prevents the error check.
	public boolean dontComplainIfMoreThanOneTargetModes = false;
	// Record that a 'setParameter' appeared in a file.  Store so that it can be accessed later.
	// NOTE: Later additions override older ones without warning.
	public void recordSetParameter(String paramName, String paramValue) {
		recordSetParameter(paramName, paramValue, "set by call in code", -1);
	}
	public void recordSetParameter(String paramName, String paramValue, String fileName, int lineno) {
		/*
		SetParamInfo lookup = hashOfSetParameters.get(paramName);
		if (lookup != null) {
			if (lookup.parameterValue.equals(paramValue)) { return; }
			Utils.error("Have already set '" + paramName + "' to " + lookup.parameterValue + " and now asking to set it to " + paramValue);
		}
		*/
		//Utils.waitHere(paramName);
		hashOfSetParameters.put(paramName, new SetParamInfo(paramName, paramValue, fileName, lineno));
	}
	public String getParameterSetting(String paramName) {
		SetParamInfo lookup = hashOfSetParameters.get(paramName);
		if (lookup == null) { return null; }
		return lookup.parameterValue;
	}

    public String getInventedPredicateNameSuffix() {
        if ( inventedPredicateNameSuffix == null ) {
            inventedPredicateNameSuffix = getParameterSetting("inventedPredicateNameSuffix");
        }

        if ( inventedPredicateNameSuffix == null ) {
            return "";
        }
        else {
            return inventedPredicateNameSuffix;
        }
    }

    public void setInventedPredicateNameSuffix(String inventedPredicateNameSuffix) {
        this.inventedPredicateNameSuffix = inventedPredicateNameSuffix;
    }

	public void complainAboutBadSetting(String paramName, String msgs) {
		SetParamInfo lookup = hashOfSetParameters.get(paramName);

		if (lookup == null) { Utils.error("Should not complain about parameter name that wasn't stored: '" + paramName + "'."); }
		Utils.error("Parameter '" + paramName + " was set to an illegal value: '" + lookup.parameterValue +
					" (line " + Utils.comma(lookup.lineNumber) + " of file '" + lookup.fileName + "'.");
	}


	public void addQueryPredicate(PredicateName predicate, int arity) {
		if (queryPredicates == null) {
			queryPredicates  = new ArrayList<PredicateName>(1);
			queryPredArities = new ArrayList<Integer>(1);
		}
		queryPredicates.add(predicate);
		queryPredArities.add(arity);
	}
	public void addHiddenPredicate(PredicateName predicate, int arity) {
		if (hiddenPredicates == null) {
			hiddenPredicates  = new ArrayList<PredicateName>(1);
			hiddenPredArities = new ArrayList<Integer>(1);
		}
		hiddenPredicates.add(predicate);
		hiddenPredArities.add(arity);
	}
	public List<PredicateName> getQueryPredicates()   { return queryPredicates;   }
	public List<Integer>       getQueryPredArities()  { return queryPredArities;  }
	public List<PredicateName> getHiddenPredicates()  { return hiddenPredicates;  }
	public List<Integer>       getHiddenPredArities() { return hiddenPredArities; }

    public Type getType(String type) {

        return isaHandler.getIsaType(type);
    }

	public void addUserProvidedProcDefinedPred(PredicateName pName, int arity, UserDefinedLiteral userLit) throws IllegalStateException {
		//Utils.waitHere("New user-defined literal: " + pName + "/" + arity + "   " + userLit);
		if (userLit == null) { return; }
		if (userAddedProcDefinedPredicates == null) { userAddedProcDefinedPredicates = new HashMap<PredicateName,Map<Integer,UserDefinedLiteral>>(4); }

		Map<Integer,UserDefinedLiteral> lookup1 = userAddedProcDefinedPredicates.get(pName);
		if (lookup1 == null) {
			lookup1 = new HashMap<Integer,UserDefinedLiteral>(4);
			userAddedProcDefinedPredicates.put(pName, lookup1);
		}
		UserDefinedLiteral lookup2 = lookup1.get(arity);
		if (lookup2 == null) {
			lookup1.put(arity, userLit);
		} else if (lookup2 != userLit) {
			throw new IllegalStateException("Already have '" + pName + "/" + arity + "' bound to user-defined '" + lookup2 + "' and cannot assign to '" + userLit + "'.");
		}
	}

	public UserDefinedLiteral getUserDefinedLiteral(PredicateName pName, int arity) {
    	if (userAddedProcDefinedPredicates == null) { return null; }
    	Map<Integer,UserDefinedLiteral> lookup1 = userAddedProcDefinedPredicates.get(pName);
		if (lookup1 == null) { return null; }
		//Utils.waitHere("Lookup user-defined literal: " + pName + "/" + arity + " and found " + lookup1.get(arity));
		return lookup1.get(arity);
	}

    @Override
    public void registerCallback(String name, UserDefinedLiteral literalDefinition) throws IllegalStateException {
        PredicateName predicateName = getPredicateName(name);
        addUserProvidedProcDefinedPred(predicateName, literalDefinition.getArity(), literalDefinition);
    }

    public UserDefinedLiteralCache getUserDefinedLiteralCache() {
        if ( userDefinedLiteralCache == null ) {
            userDefinedLiteralCache = new UserDefinedLiteralCache();
        }
        return userDefinedLiteralCache;
    }

	public boolean haveLoadedThisFile(String fileName, boolean recordLoaded) {
		if (filesLoaded.contains(fileName)) { return true; }
		if (recordLoaded) { filesLoaded.add(fileName); }
		return false;
	}

	public String createSafeStringConstantForWILL(String string) {
		return Utils.createSafeStringConstantForWILL(string, this);
	}

	public String createSafeStringVariableForWILL(String string) {
		return Utils.createSafeStringVariableForWILL(string, this);
	}

	public boolean usingStrictEqualsForLiterals() {
		return useStrictEqualsForLiterals;
	}
	public boolean usingStrictEqualsForFunctions() {
		return useStrictEqualsForFunctions;
	}
	public boolean usingStrictEqualsForClauses() {
		return useStrictEqualsForClauses;
	}
	public void setUseStrictEqualsForLiterals(boolean value) {
		useStrictEqualsForLiterals = value;
	}
	public void setUseStrictEqualsForFunctions(boolean value) {
		useStrictEqualsForFunctions = value;
	}
	public void setUseStrictEqualsForClauses(boolean value) {
		useStrictEqualsForClauses = value;
	}

	public List<Variable> getThisManyVars(int count, boolean dontcheck_variableNamesSeen) {
		if (count < 1) { return null; }
		List<Variable> results = new ArrayList<Variable>(count);
		resetVarCounters();
		for (int i = 0; i < count; i++) {
			results.add(getNewGeneratedVariable(dontcheck_variableNamesSeen));
		}
		resetVarCounters();
		return results;
	}

    public  ClauseOptimiser getClauseOptimizer() {
        if ( clauseOptimizer == null ) {
            clauseOptimizer = new ClauseOptimiser(this);
        }
        return clauseOptimizer;
    }

    public Clause getOptimizedClause(Clause clause) {
        return getClauseOptimizer().rewriteWithCuts(clause);
    }

    protected String cleanString(String str) {
    	return cleanString(str, false);
    }
    protected String cleanString(String str, boolean hadQuotesOriginally) {
    	return Utils.cleanString(str, this, hadQuotesOriginally);
    }

    public PredicateNameAndArityFilter getSpyEntries() {
        return spyEntries;
    }


    /** Sets both the variant fact and variant rule handling to action.
     *
     * @param action the new VariantClauseAction action.
     */
    public void setVarientClauseHandling(VariantClauseAction action) {
        this.variantFactHandling = action;
        this.variantRuleHandling = action;
    }

    public StringConstant getAlphabeticalVariableName(int variableIndex) {
        StringBuilder stringBuilder = new StringBuilder();

        while (true) {
            int mod = variableIndex % alphabet2Size;
            stringBuilder.append(alphabet2[mod]);
            variableIndex -= mod;
            if (variableIndex == 0) {
                break;
            }
            variableIndex /= alphabet2Size;
        }


        String anonymousName = null;

        if (doVariablesStartWithQuestionMarks()) {
            anonymousName = "?" + stringBuilder.toString();
        }
        else if (usingStdLogicNotation()) {
            anonymousName = stringBuilder.toString().toLowerCase();
        }
        else {
            anonymousName = stringBuilder.toString();
        }

        return getStringConstant(null, anonymousName, false);
    }

	public static void main(String[] args)  {
		args = Utils.chopCommentFromArgs(args);
		HandleFOPCstrings stringHandler = new HandleFOPCstrings(VarIndicator.uppercase);

		Utils.println("cleanString:                                " + Utils.cleanString("world1Ex2neg", null));
		Utils.println("createSafeStringConstantForWILL(lowerCase): " + Utils.createSafeStringConstantForWILL("world1Ex2neg", stringHandler));
		stringHandler.useStdLogicNotation();
		Utils.println("createSafeStringConstantForWILL(upperCase): " + Utils.createSafeStringConstantForWILL("world1Ex2neg", stringHandler));
		Utils.waitHere();

	}

    /**
     * @return the knownModes
     */
    public List<PredicateNameAndArity> getKnownModes() {
        return knownModes;
    }

    /**
     * @param knownModes the knownModes to set
     */
    public void setKnownModes(List<PredicateNameAndArity> knownModes) {
        this.knownModes = knownModes;
    }

    public void addKnownMode(PredicateNameAndArity predicateName) {
        if ( knownModes == null ) {
            knownModes = new ArrayList<PredicateNameAndArity>();
        }

        if ( knownModes.contains(predicateName) == false ) {
            knownModes.add(predicateName);
        }
    }

    public void removeKnownMode(PredicateNameAndArity predicateName) {
        if ( knownModes != null ) {
            knownModes.remove(predicateName);
        }
    }

    public void addLiteralAlias(Literal alias, Literal literal) {
       literalAliases.put(alias, literal);
    }

    public Literal lookupLiteralAlias(Literal alias) {
        Literal literal = literalAliases.get(alias);
        if ( literal == null ) {
            throw new IllegalArgumentException("Unable to find Literal for alias of " + alias + ".");
        }
        return literal;
    }


    public void setStarMode(int value) {
        starModeMap = value;
    }
	public int     getStarMode()          { return starModeMap; }
	public String  getStarModeString()    { return TypeSpec.getModeString(starModeMap); }

//    public void    setStarModeMap(int value) {        starModeMap = value; }
//	public int     getStarModeMap()          { return starModeMap; }
//	public String  getStarModeString()    { return TypeSpec.getModeString(starModeMap); }

    class SetParamInfo {
        protected String parameterName; // Don't really need to store this, but might as well for completeness.
        protected String parameterValue;
        protected String fileName;
        protected int    lineNumber;

        protected SetParamInfo(String parameterName, String parameterValue, String fileName, int lineNumber) {
            this.parameterName  = parameterName;
            this.parameterValue = parameterValue;
            this.fileName       = fileName;
            this.lineNumber     = lineNumber;
        }
    }

	public void setStringsAreCaseSensitive(boolean matchingShouldBeCaseSensitive) {
		if (ignoreCaseOfStringsOtherThanFirstChar != !matchingShouldBeCaseSensitive && !dontPrintUnlessImportant) { Utils.println(STRING_HANDLER_VARIABLE_INDICATOR, "% Changing setStringsAreCaseSensitive to " + matchingShouldBeCaseSensitive + "."); }
		ignoreCaseOfStringsOtherThanFirstChar = !matchingShouldBeCaseSensitive;
	}
	public boolean getStringsAreCaseSensitive() {
		return !ignoreCaseOfStringsOtherThanFirstChar;
	}

	public String getStringToIndicateStringCaseSensitivity() {
		return "setParam: stringsAreCaseSensitive = " + !ignoreCaseOfStringsOtherThanFirstChar + ".\n";
	}
	/**
	 * @return the knownConstantsOfThisType
	 */
	public Map<Type,Set<Term>> getKnownConstantsOfThisType() {
		return knownConstantsOfThisType;
	}


}


