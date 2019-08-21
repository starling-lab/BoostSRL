/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import java.io.IOException;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.Utils.Utils;

/**
 * @author shavlik
 * 
 * The material in this class is used in ILP and MLNs, though it can play a role in other logical-reasoning systems.
 *
 */
@SuppressWarnings("serial")
public class TypeSpec extends AllOfFOPC implements Serializable, Cloneable { // IMPORTANT NOTE: if adding more symbols here, also edit atTypeSpec() in the parser.

    public final static int unspecifiedMode = -1; // For use when modes aren't needed.
	public final static int modeNotYetSet = 0; // Mark that this mode will be set later, when more information is available.
	public final static int plusMode      = 1; // An 'input' argument (should be bound when the predicate or function containing this is called).
	public final static int onceMode      = 2; // An 'input' argument that appears exactly ONCE in the clause SO FAR (can be reused later).
	public final static int minusMode     = 3; // An 'output' argument - need not be bound.
	public final static int novelMode     = 4; // An 'output' argument that is a NEW variable.
	public final static int constantMode  = 5; // An argument that should be a constant (i.e., not a variable).
	public final static int thisValueMode = 6; // This SPECIFIC constant should fill this argument slot.
	public final static int equalMode     = 7; // This variable must also appear in the body of a clause for that clause to be acceptable (otherwise, same as '+').
	public final static int minusOrConstantMode =  8; // Means BOTH '-' and '#'.
	public final static int plusOrConstantMode  =  9; // Means BOTH '+' and '#'.
	public final static int novelOrConstantMode = 10; // Means BOTH '^' and '#' (currently this one has no single-character name - TODO).
	public final static int starMode            = 11; // Look up the mode in the stringHandler.
	public final static int notHeadVarMode  	= 12; // The variable shouldn't be in the head of the clause.

    public Integer mode;    // One of the above, which are used to describe how this argument is to be used.
	public Type    isaType; // Can be "human," "book," etc.  Type hierarchies are user-provided.
	public int     truthCounts = 0; // Specifies how often this predicate will be true.
							       // If truthCounts =  0 then any number is possible.
								   // If truthCounts =  K and K > 0, then for EXACTLY K of the possibly values for this argument will the predicate be true.
								   // If truthCounts = -K and K > 0, then for AT MOST K possible values will this predicate be true.
	transient protected HandleFOPCstrings stringHandler = null;

	public TypeSpec(String modeAsString, String typeAsString, HandleFOPCstrings stringHandler) {
		this(modeAsString,
			 stringHandler.isaHandler.getIsaType(stringHandler.createSafeStringConstantForWILL(typeAsString)), 
			 stringHandler);		
	}
	public TypeSpec(String modeAsString, Type isaType, HandleFOPCstrings stringHandler) {
		this.stringHandler = stringHandler;
		if      (isaSynonymForPlus(         modeAsString)) { mode = plusMode;      }
		else if (isaSynonymForOnce(         modeAsString)) { mode = onceMode;      }
		else if (isaSynonymForMinus(        modeAsString)) { mode = minusMode;     }
		else if (isaSynonymForNovel(        modeAsString)) { mode = novelMode;     }
		else if (isaSynonymForConstant(     modeAsString)) { mode = constantMode;  }
		else if (isaSynonymForThisConstant( modeAsString)) { mode = thisValueMode; }
		else if (isaSynonymForEqual(        modeAsString)) { mode = equalMode;     }
		else if (isaSynonymForStar(         modeAsString)) { mode = starMode;      }
		else if (isaSynonymForMinusConstant(modeAsString)) { mode = minusOrConstantMode; }
		else if (isaSynonymForPlusConstant( modeAsString)) { mode = plusOrConstantMode;  }
		else if (isaSynonymForNovelConstant(modeAsString)) { mode = novelOrConstantMode; }
		else if (isaSynonymForUnspecified(  modeAsString)) { mode = unspecifiedMode;     }
		else if (isaSynonymForNotHeadVar(    modeAsString)) { mode = notHeadVarMode;     }
		else if (isaSynonymForNotYetSet(    modeAsString)) { mode = modeNotYetSet;     }
		else { Utils.error("Unknown mode string: '" + modeAsString + "'"); }
		this.isaType = isaType;
	}
	public TypeSpec(char modeAsChar, String typeAsString, HandleFOPCstrings stringHandler) {
		this.stringHandler = stringHandler;
		if      (modeAsChar == '+') { mode = plusMode;      } // If additions to this, be sure to add to isaModeSpec().
		else if (modeAsChar == '$') { mode = onceMode;      }
		else if (modeAsChar == '-') { mode = minusMode;     }
		else if (modeAsChar == '^') { mode = novelMode;     }
		else if (modeAsChar == '#') { mode = constantMode;  }
		else if (modeAsChar == '@') { mode = thisValueMode; }
		else if (modeAsChar == '*') { mode = starMode;      }
		else if (modeAsChar == '=') { mode = equalMode;     }
		else if (modeAsChar == '&') { mode = minusOrConstantMode; }
		else if (modeAsChar == ':') { mode = plusOrConstantMode;  }
		else if (modeAsChar == '`') { mode = notHeadVarMode;  }
		else if (modeAsChar == '>') { mode = modeNotYetSet;  }
		// novelOrConstantMode
		else if (modeAsChar == ' ') { mode = unspecifiedMode;     }
		else { Utils.error("Unknown mode character: '" + modeAsChar + "'"); }
		isaType = stringHandler.isaHandler.getIsaType(typeAsString);  // TODO should confirm that this is a known type
	}	
	public static boolean isaModeSpec(char c) { // Also look at FileParser.processTerm
		return c == '+' || c == '$' || c == '-' || c == '^' || c == '#' || c == '@' || c == '*' || c == '=' || c == '&' || c == ':' || c == '>'|| c == '`';
	}
	public TypeSpec(Type isaType, HandleFOPCstrings stringHandler) {
		this.stringHandler = stringHandler;
		this.mode          = unspecifiedMode;
		this.isaType       = isaType;
	}	
	public TypeSpec(int modeAsInt, Type isaType, HandleFOPCstrings stringHandler) {
		this.stringHandler = stringHandler;
		this.mode          = modeAsInt;
		this.isaType       = isaType;
	}
	

	public void setMode(int mode) {
		this.mode = mode;
	}	
	public void setType(String typeAsString) {
		this.isaType = new Type(typeAsString, stringHandler);
	}	

	public void setToMinusModeUnlessAlreadyHigher() {
		 mode = returnMoreRestrictiveMode(minusMode);
	}
	
	public Type returnMoreRestrictiveType(Type otherType) {
		if (isaType == otherType)                             { return isaType;   }
		if (stringHandler.isaHandler.isa(isaType, otherType)) { return isaType;   }
		if (stringHandler.isaHandler.isa(otherType, isaType)) { return otherType; }
		return null; // This indicates neither is ISA the other.
	}
	
	public int returnMoreRestrictiveMode(int otherMode) { // This ordering is a best guess ...
		if (mode      == equalMode)     { return mode;      }
		if (otherMode == equalMode)     { return otherMode; }
		if (mode      == thisValueMode) { return mode;      }
		if (otherMode == thisValueMode) { return otherMode; }
		if (mode      == onceMode)      { return mode;      }
		if (otherMode == onceMode)      { return otherMode; }
		if (mode      == plusOrConstantMode)  { return mode;      }
		if (otherMode == plusOrConstantMode)  { return otherMode; }
		if (mode      == plusMode)      { return mode;      }
		if (otherMode == plusMode)      { return otherMode; }
		if (mode      == novelMode)     { return mode;      }
		if (otherMode == novelMode)     { return otherMode; }
		if (mode      == minusMode)     { return mode;      }
		if (otherMode == minusMode)     { return otherMode; }
		if (mode      == notHeadVarMode)     { return mode;      }
		if (otherMode == notHeadVarMode)     { return otherMode; }
		if (mode      == starMode)      { return mode;      }
		if (otherMode == starMode)      { return otherMode; }
		if (mode      == minusOrConstantMode) { return mode;      }
		if (otherMode == minusOrConstantMode) { return otherMode; }
		if (mode      == unspecifiedMode)     { return otherMode; }
		return mode;
	}
	
	/**
         * Collect those type specifications that are for INPUT arguments. For
         * the other arguments, use 'null' (this way two different
         * specifications such as '(+human,-human,+dog)' and
         * '(-human,+human,-dog)' will be differentiated).
         * 
         * @param fullTypeSpec
         * @return A list of the argument types for the given predicate specification.
         */
	public static List<Type> getListOfInputArgumentTypes(PredicateSpec fullTypeSpec) {
		List<Type> inputArgumentTypes = new ArrayList<Type>(1);
		for (TypeSpec spec : fullTypeSpec.getTypeSpecList()) {
			if (spec.mustBeBound()) { inputArgumentTypes.add(spec.isaType); } else { inputArgumentTypes.add(null); }
		}
		return inputArgumentTypes;
	}	
	
    @Override
	public int hashCode() { // Need to have equal objects produce the same hash code.
		final int prime = 31;
		int result = 1;
		result = prime * result + mode;
		result = prime * result + ((isaType == null) ? 0 : isaType.hashCode());
		return result;
	}	
    @Override
	public boolean equals(Object obj) {
		if (!(obj instanceof TypeSpec)) { return false; }
		TypeSpec typeSpec = (TypeSpec) obj;
		return (mode == typeSpec.mode && isaType == typeSpec.isaType);
	}
	
	private boolean isaSynonymForPlus(String str) {
		return (str.equalsIgnoreCase("+") || str.equalsIgnoreCase("plus"));
	}	
	private boolean isaSynonymForOnce(String str) {
		return (str.equalsIgnoreCase("$") || str.equalsIgnoreCase("once"));
	}
	private boolean isaSynonymForMinus(String str) {
		return (str.equalsIgnoreCase("-") || str.equalsIgnoreCase("minus"));
	}
	private boolean isaSynonymForNovel(String str) {
		return (str.equalsIgnoreCase("^") || str.equalsIgnoreCase("novel"));
	}
	private boolean isaSynonymForConstant(String str) {
		return (str.equalsIgnoreCase("#") || str.equalsIgnoreCase("constant") || str.equalsIgnoreCase("const"));
	}
	private boolean isaSynonymForThisConstant(String str) {
		return (str.equalsIgnoreCase("@") || str.equalsIgnoreCase("at"));
	}
	private boolean isaSynonymForEqual(String str) {
		return (str.equalsIgnoreCase("=") || str.equalsIgnoreCase("equal") || str.equalsIgnoreCase("equals"));
	}
	private boolean isaSynonymForMinusConstant(String str) {
		return (str.equalsIgnoreCase(":") || str.equalsIgnoreCase("minusConstant") || str.equalsIgnoreCase("minConst"));
	}
	private boolean isaSynonymForPlusConstant(String str) {
		return (str.equalsIgnoreCase("&") || str.equalsIgnoreCase("plusConstant") || str.equalsIgnoreCase("plusConst"));
	}
	private boolean isaSynonymForNovelConstant(String str) {
		return (                             str.equalsIgnoreCase("novelConstant") || str.equalsIgnoreCase("novelConst"));
	}
	
	private boolean isaSynonymForNotHeadVar(String str) {
		return (str.equalsIgnoreCase("`") || str.equalsIgnoreCase("notHeadVar"));
	}
	private boolean isaSynonymForStar(String str) {
		return (str.equalsIgnoreCase("*") || str.equalsIgnoreCase("star"));
	}
	private boolean isaSynonymForUnspecified(String str) {
		return (str.equalsIgnoreCase(" ") || str.equalsIgnoreCase(""));
	}
	private boolean isaSynonymForNotYetSet(String str) {
		return (str.equalsIgnoreCase(">") || str.equalsIgnoreCase("unknown"));
	}
	
	public boolean isaStarMode() {
		return mode == starMode;
	}
	
	public boolean isPlusOrMinus() { // A rather odd special case.  We don't want to count 'star' (nor '^' ?) here.
		int modeToUse = mode;
		return mustBeBound() ||  modeToUse == minusMode; //  || modeToUse == novelMode;
	}
	
	public boolean mustBeBound() {
		int modeToUse = mode;
		if (mode == starMode) { modeToUse = stringHandler.getStarMode(); }
		return modeToUse == plusMode || modeToUse == equalMode || modeToUse == onceMode;
	}
	
	public boolean canBeBound() { // I don't think this means much (plus it should be double checked). 
		int modeToUse = mode;
		if (mode == starMode) { modeToUse = stringHandler.getStarMode(); }
		return modeToUse != novelMode && modeToUse != starMode;
	}
	
	public boolean mustBeBoundAndAppearOnlyOnce() {
		int modeToUse = mode;
		if (mode == starMode) { modeToUse = stringHandler.getStarMode(); }
		return modeToUse == onceMode;
	}
	
	public boolean canBeNewVariable() {
		int modeToUse = mode;
		if (mode == starMode) { modeToUse = stringHandler.getStarMode(); }
		return modeToUse == minusMode || modeToUse == minusOrConstantMode || mustBeNewVariable();
	}
	
	public boolean mustBeNewVariable() {
		int modeToUse = mode;
		if (mode == starMode) { modeToUse = stringHandler.getStarMode(); }
		return modeToUse == novelMode || modeToUse == novelOrConstantMode; // This might be buggy - it might not allow Constant to be used?  Depends on how the inner loop's child-generator handles this.
	}
	
	public boolean mustBeThisValue()	{
		int modeToUse = mode;
		if (mode == starMode) { modeToUse = stringHandler.getStarMode(); }
		return modeToUse == thisValueMode;
	}
	
	public boolean mustBeConstant()	{
		int modeToUse = mode;
		if (mode == starMode) { modeToUse = stringHandler.getStarMode(); }
		return modeToUse == constantMode;
	}
	
	
	public boolean mustNotBeHeadVar()	{
		int modeToUse = mode;
		if (mode == starMode) { modeToUse = stringHandler.getStarMode(); }
		return modeToUse == notHeadVarMode;
	}
	
	public boolean canBeConstant()	{
		int modeToUse = mode;
		if (mode == starMode) { modeToUse = stringHandler.getStarMode(); }
		return modeToUse == constantMode || modeToUse == minusOrConstantMode || modeToUse == plusOrConstantMode || modeToUse == novelOrConstantMode;
	}
	
	public boolean mustBeInBody()	{
		int modeToUse = mode;
		if (mode == starMode) { modeToUse = stringHandler.getStarMode(); }
		return modeToUse == equalMode;
	}
	
	public        String getModeString() {
		return getModeString(mode);
	}
	public static String getModeString(int modeToUse) {
		switch (modeToUse) {
			case plusMode:      return "+";
			case onceMode:      return "$";
			case minusMode:     return "-";
			case novelMode:     return "^";
			case constantMode:  return "#";
			case thisValueMode: return "@";
			case equalMode:     return "=";
			case starMode:      return "*";
			case minusOrConstantMode: return "&";
			case plusOrConstantMode:  return "%";
			case notHeadVarMode:  	  return "`";
			case novelOrConstantMode: return "novelConst";  // TODO
			case unspecifiedMode:     return "";
			case modeNotYetSet:       return ">";
			default: Utils.error("Unknown mode type code: '" + modeToUse + "'");
					 return null;
		}		
	}
	
	public String getCountString() {
		if (truthCounts ==  0) { return "";  }
		if (truthCounts ==  1) { return "!"; }
		if (truthCounts == -1) { return "$"; }
		if (truthCounts >   1) { return "!" + truthCounts; }
		return                          "$" + truthCounts;
	}
	
	public boolean hasUnspecifiedMode() {
		return mode == unspecifiedMode; 
	}
	public boolean isNotYetSet() {
		return mode == modeNotYetSet;
	}
	
    @Override
	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return getModeString() + isaType;
	}
    @Override
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return getModeString() + isaType;
	}
	@Override
	public TypeSpec applyTheta(Map<Variable, Term> bindings) {
		return this;
	}
	
	public TypeSpec copy(boolean recursiveCopy) {
		return clone();
	}

    public Type getType() {
        return isaType;
    }

    private void readObject(java.io.ObjectInputStream in) throws IOException, ClassNotFoundException {
        if ( in instanceof FOPCInputStream == false ) {
            throw new IllegalArgumentException(getClass().getCanonicalName() + ".readObject() input stream must support FOPCObjectInputStream interface");
        }

        in.defaultReadObject();

        FOPCInputStream fOPCInputStream = (FOPCInputStream) in;

        this.stringHandler = fOPCInputStream.getStringHandler();
    }
    
	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return 0;
	}

    public TypeSpec copy() {
        return clone();
    }

    

    protected TypeSpec clone() {
        try {
            return (TypeSpec) super.clone();
        } catch (CloneNotSupportedException ex) {
            return null;
        }
    }
}
