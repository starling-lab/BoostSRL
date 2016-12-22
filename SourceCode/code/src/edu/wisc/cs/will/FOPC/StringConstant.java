/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.FOPC.visitors.TermVisitor;
import edu.wisc.cs.will.Utils.Utils;
import java.io.ObjectStreamException;
import java.io.Serializable;

/**
 * @author shavlik
 *
 */
@SuppressWarnings("serial")
public class StringConstant extends Constant implements Serializable {
    private String name = null;
    
    public static boolean debugMe = false;
    
    public static boolean addBackSlashes = true;

    private boolean alwaysUseDoubleQuotes = false;
//	private boolean variablesStartWithQuestionMarks_valueAtCreationTime; // Save space and use time.
//	private boolean lowercaseMeansVariable_valueAtCreationTime;

    public static long instancesCreated = 0;
    
    protected StringConstant() {
    	instancesCreated++;
    	checkIfQuoteMarksNeeded();  // 'name' not set, so don't need this, but keep it in case we later change the code.
    }

    protected StringConstant(HandleFOPCstrings stringHandler, String name, boolean alwaysUseDoubleQuotes, boolean variablesStartWithQuestionMarks, boolean lowercaseMeansVariable, TypeSpec typeSpec) {
    	this();
    	this.name = name; // DON'T CALL THESE DIRECTLY.  GO VIA HandleFOPCstrings.
        while (name != null && name.length() > 1 && name.charAt(0) == '"' && name.charAt(name.length() - 1) == '"' ) { 
        	name = name.substring(1, name.length() - 1);  // We'll add these back on if needed.
        }
        this.stringHandler = stringHandler;
        this.setTypeSpec(typeSpec);
        //	variablesStartWithQuestionMarks_valueAtCreationTime = variablesStartWithQuestionMarks;  TODO - if these are ever turned back on, use the VarIndicator enum
        //	lowercaseMeansVariable_valueAtCreationTime          = lowercaseMeansVariable;
        if (name != null && name.equalsIgnoreCase("-inf")) {
            Utils.error("Where did this come from? ");
        }
        this.alwaysUseDoubleQuotes = alwaysUseDoubleQuotes;
        if (!alwaysUseDoubleQuotes) { checkIfQuoteMarksNeeded(); }
    }

    public boolean freeVariablesAfterSubstitution(BindingList theta) {
        return false;
    }

    public String toTypedString() {
        String end = (typeSpec != null ? typeSpec.getCountString() : "");
        if (name == null) {
            return typeSpec.getModeString() + typeSpec.isaType.typeName + end;
        } // Sometimes anonymous string constants are used (e.g., to pass around typeSpec's).
        String nameToUse = getName();
        return (typeSpec != null ? typeSpec.getModeString() + typeSpec.isaType.typeName + ":" + nameToUse + end : nameToUse + end);
    }
    
    private void checkIfQuoteMarksNeeded() { 
    	alwaysUseDoubleQuotes     = false;
    	boolean containsNonNumber = false;
        if (name != null) for (int i = 0; i < name.length(); i++) {
        	char chr = name.charAt(i);
        	if (!(Character.isLetterOrDigit(chr) || (i > 0 && chr == '_'))) {// Should we quote if the FIRST char is a digit?
        		alwaysUseDoubleQuotes = true; // CHECK IF CHAR IS ONE THAT FileParser's tokenizer does not handle.
        		break; 
        	} else if (chr >= '\u00AA' && chr <= '\u00FF') { // SOME THINGS WERE SLIPPING THROUGH (eg, Beioncé), SO DO THIS      DONT DO THIS BOTH HERE AND IN StreamTokenizeTAW (though not harmful - would just add more quote marks than are necessary).
        		alwaysUseDoubleQuotes = true;
        		break;
        	}
        	if (!containsNonNumber && Character.isLetter(chr)) { containsNonNumber = true; }
        } 
        if (!containsNonNumber) { alwaysUseDoubleQuotes = true; } // If something was a string of numbers, we want it quoted (for later parsing as a StringConstant rather than as a NumericConstant).
    }

    public String getName() {
    //	if (AllOfFOPC.printUsingAlchemyNotation) { // Alchemy uses CAPS for constants and cannot handle quote marks (or at least Tuffy cannot).
    //		if (alwaysUseDoubleQuotes) { Utils.waitHere("Have alwaysUseDoubleQuotes=true and printUsingAlchemyNotation=true for: " + name); }
    //		if (name.charAt(0) == '"' || name.charAt(0) == '\'') {
    //			return Utils.cleanString(name.substring(1, name.length() - 1), stringHandler); // Drop the quote marks and change spaces to underscores?
    //		}
    //		String newName = Utils.setFirstCharToRequestedCase(name, true);
    //		return newName;
    //	}
    	String safeName = makeSureNameIsSafe(name);
    	if (debugMe) {
    		Utils.println("    name: " + name);
    		Utils.println("safeName: " + safeName);
    		Utils.println("safeName.charAt(0):    " + safeName.charAt(0));
    		Utils.println("alwaysUseDoubleQuotes: " + alwaysUseDoubleQuotes);
    		Utils.println("isaConstantType:       " + stringHandler.isaConstantType(name));
    	}
    	if (safeName == null) { Utils.error("Have a StringConstant with an unbound name."); }
    	if (safeName.isEmpty()) { return "\"\""; } // Need something here so the string can be 'seen' (e.g., parsed back in).
    //	if (safeName.charAt(0) == '"' || safeName.charAt(0) == '\'') { return safeName; }  // TODO - do we want to support SINGLE quoted strings?
    	if (safeName.length() >  1 && safeName.charAt(0) == '"' && safeName.charAt(safeName.length() - 1) == '"') { return safeName; } // Already quoted.
    	if (safeName.length() == 1 && safeName.charAt(0) == '"')  { return '"' + '\\' + safeName + '"'; }
    	if (safeName.length() == 1 && safeName.charAt(0) == '\'') { return '"' +        safeName + '"'; } // This line might not be needed.
        return (stringHandler.isaConstantType(name)
                ? (alwaysUseDoubleQuotes ? '"' + safeName + '"' : safeName)
                : '"' + safeName + '"'); // Need to override by quoting.  Note that if safeName started with quote marks, it would have been caught above.
    }

    /** Returns the name without any quoting or escaping of characters.
     *
     * Sometime we need the name of a StringConstant without the quoting
     * and escaping of characters.  This is necessary when we are going to
     * do custom printing (aka the PrettyPrinter) or when we want to do
     * processing of the name prior to quoting.
     *
     * @return
     */
    public String getBareName() {
        return name;
    }
    
    // In this case, if there are quotes we want them to be escaped since the calling code will wrap the results in quote marks.  TODO - clean up
    public static String makeSureNameIsSafeAsTerm(String name) {
    	if (name != null && name.equals("\"")) { return "\\\""; }
    	String name2 = makeSureNameIsSafe(name);

		if (name2 != null && name2.length() > 0) {
	    	boolean startsWithQuote = false, endsWithQuote = false;
	    	if (name.charAt(0)                 == '"') { startsWithQuote = true; }
	    	if (name.charAt(name.length() - 1) == '"') {   endsWithQuote = true; }
	    	
	    	if (startsWithQuote && endsWithQuote) {
	    		name2 = "\\" + name2.substring(0, name.length() - 1) + "\\\""; // Need to pull out the last quote mark to insert the escape.
	    	    Utils.println("% Quotes in text: " + name + "\n   " + StringConstant.makeSureNameIsSafe(name) + "\n   " + name2); 
	    	}	    	
		}
		return name2;
    }
    
    public static String makeSureNameIsSafe(String name) {
    	if (name == null || !addBackSlashes) { return name; }
    	if (name.isEmpty()) { return name; }
    	
    	StringBuilder    result = new StringBuilder(name.length());
    	boolean startsWithQuote = false, endsWithQuote = false;
    	if (name.charAt(0)                 == '"') { startsWithQuote = true; }
    	if (name.charAt(name.length() - 1) == '"') {   endsWithQuote = true; }    	
    	
    	if (startsWithQuote && endsWithQuote) { result.append('"');  }
    	else if (startsWithQuote)             { result.append('\\').append('"'); } // Seems more readable than using :  result.append("\\\"");

		//char prevChr = 0;
		boolean nextCharEscaped = false;
    	for (int i = (startsWithQuote ? 1 : 0); i < name.length() - (endsWithQuote ? 1 : 0); i++) {
    		char chr = name.charAt(i);
    		// For quotes
    		if (chr == '"') {
    			// If prev character wasn't \, escape it
    			if (!nextCharEscaped) {
    				result.append('\\');
    			} 
    		} 
    		if (chr != '"' && chr != '\\') {
    			// A character apart from " was escaped=> add an extra slash
    			// Handle's cases such as \n, \t
    			if (nextCharEscaped) {
    				result.append('\\');
    			}
    		}
    		//System.out.println(nextCharEscaped+":"+chr);
    		// For slash
    		if (chr =='\\') {

    			// If there is a slash before, already escaped but the next character is not
    			if (nextCharEscaped) {
    				nextCharEscaped = false;
    			} else { // The next character is escaped by this slash
    				nextCharEscaped = true;
    			}
    		} else {
    			// Set this to false for any other character
    			nextCharEscaped = false;
    		}
    		
    		/*if (chr == '"' || chr == '\\') { // No need to escape single quotes in strings BUT DO NEED OUTER QUOTES || chr == '\'') { 
    			if (prevChr != '\\') { result.append('\\'); } // See if already escaped.  Buggy if earlier chars were '\\' - i.e., an escaped backslash. TODO - to fix, maybe need a counter of consecutive backslashes, and if odd, then no need to add one?
    		}*/
    		//prevChr = chr;
    		result.append(chr);
    	}
    	// The string may end with a slash.
    	if (nextCharEscaped) { result.append('\\'); }
    	
    	if (startsWithQuote && endsWithQuote) { result.append('"');  }
    	else if (endsWithQuote)               { result.append('\\').append('"'); }

    //	if (name.contains("Big Ben")) { Utils.println("\nname = " + name + "  lastChar: " + Character.toString(name.charAt(name.length() - 1)) + "\nstartsWithQuote = " + startsWithQuote + "\n  endsWithQuote = " + endsWithQuote + "\n  " + result);	}
    	return result.toString();
    }

    public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
        return toString(precedenceOfCaller, bindingList);
    }

    public String toString(int precedenceOfCaller, BindingList bindingList) {
        if (stringHandler.printTypedStrings) {
            return toTypedString();
        }
        String prefix = "";
        // if (!stringHandler.isaConstantType(name)) { Utils.error("When read in '" + name + "' was a constant, but now it would be a constant.") ; }
        if (name == null) {
            if (typeSpec == null) {
                Utils.error("Have a stringConstant with name=null and typeSpec=null");
            }
            return prefix + typeSpec.getModeString() + typeSpec.isaType.typeName + typeSpec.getCountString();  // Sometimes anonymous string constants are used (e.g., to pass around typeSpec's).
        }
        if (name == null) {
            return prefix;
        } // Probably should report an error.
        if (stringHandler.doVariablesStartWithQuestionMarks()) {
            if (!alwaysUseDoubleQuotes && name.charAt(0) == '?') {
                Utils.error("How did a variable get into a constant? " + getName());
            }
            return prefix + getName();
        }
        return prefix + getName();
    }

    public Clause asClause() {
        return stringHandler.getClause(stringHandler.getLiteral( stringHandler.getPredicateName(name)), true);
    }
    @Override
    public Sentence asSentence() {
        return stringHandler.getLiteral(stringHandler.getPredicateName(name));
    }

    @Override
    public Literal asLiteral() {
        return stringHandler.getLiteral( stringHandler.getPredicateName(name));
    }


    public Function asFunction() {
        return stringHandler.getFunction( name);
    }

    
    @Override
    public BindingList isEquivalentUptoVariableRenaming(Term that, BindingList bindings) {
        if (that instanceof StringConstant == false) {
            return null;
        }

        StringConstant stringConstant = (StringConstant) that;

        if (this.name.equals(stringConstant.name) == false) {
            return null;
        }

        return bindings;
    }

    /*
    // OLD method: String nameToUse = (!stringHandler.isaConstantType(name) ? Utils.changeCaseFirstChar(name) : name);
    if (variablesStartWithQuestionMarks_valueAtCreationTime) { // Still the same.
    if (stringHandler. doVariablesStartWithQuestionMarks() == variablesStartWithQuestionMarks_valueAtCreationTime) {
    return prefix + name;
    }
    if (( stringHandler.lowercaseMeansVariable && Character.isLowerCase(name.charAt(0))) || // Need to quote to override current variable-versus-constant 'rule.'
    (!stringHandler.lowercaseMeansVariable && Character.isUpperCase(name.charAt(0)))) {
    return prefix + ((name.charAt(0) == '\'') ? name : '\'' + name + '\'');  // The quotes should be stripped off during parsing, but still check here for safety.
    }
    return prefix + name;

    } else {
    return prefix + (stringHandler.lowercaseMeansVariable == lowercaseMeansVariable_valueAtCreationTime // Still the same.
    ? name
    : ((name.charAt(0) == '\'') ? name // Already quoted.  See above comment about the parser stripping quotes.
    : '\'' + name + '\'')); // Need to override by quoting.
    }
    }
     */
    /** Replace with the cached version from stringHandler.
     *
     * @return
     * @throws ObjectStreamException
     */
    private Object readResolve() throws ObjectStreamException {
        return stringHandler.getStringConstant(typeSpec, name, true);
    }

    @Override
    public <Return, Data> Return accept(TermVisitor<Return, Data> visitor, Data data) {
        return visitor.visitStringConstant(this, data);
    }
}
