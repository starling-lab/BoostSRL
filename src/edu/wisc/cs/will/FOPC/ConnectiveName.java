package edu.wisc.cs.will.FOPC;

import java.io.IOException;
import java.io.ObjectStreamException;
import java.io.Serializable;
import java.util.Map;

import edu.wisc.cs.will.Utils.Utils;

/**
 * @author shavlik
 *
 *  All functions with the same name map to the same instance. 
 */
@SuppressWarnings("serial")
public class ConnectiveName extends AllOfFOPC implements Serializable { // If items are added here, add them to HandleFOPCstrings as well.
	
    private final static String ANDalt0        = "AND";
	private final static String ANDalt1        = "^";
	private final static String ANDalt2        = "&"; // TODO - also allow && and ||?
	private final static String ANDalt3        = ",";
	private final static String ORalt0         = "OR";
	private final static String ORalt1         = "v";
	private final static String ORalt2         = "|";
//	private final static String ORalt2         = ";"; // No longer used since this is also accepted as an end-of-sentence indicator.
	private final static String ORalt3         = "ELSE";
	private final static String NOTalt0        = "NOT";
	private final static String NOTalt1        = "~";
	private final static String NOTalt2        = "\\+";
//	private final static String NOTalt3        = "!"; // Reserve this as Prolog's 'cut' symbol.
	private final static String IMPLIESalt0    = "=>";
	private final static String IMPLIESalt1    = "->";
	private final static String IMPLIESalt2    = "IMPLIES";
	private final static String IMPLIESalt3    = ":-"; // This is what Prolog uses.  THESE NEED TO BE IN isaBackwardsIMPLIES().
	private final static String IMPLIESalt4    = ":="; // And allow these two variants.
	private final static String IMPLIESalt5    = "IF";
	private final static String EQUIVALENTalt0 = "<=>";
	private final static String EQUIVALENTalt1 = "<->";
	private final static String EQUIVALENTalt2 = "EQUIVALENT";
	private final static String SPECIAL        = "THEN";
	
	private final static String LogicalAND     = "LogicalAnd";
	private final static String LogicalOR      = "LogicalOr";
	private final static String LogicalNOT     = "LogicalNot";

    public final static ConnectiveName AND     = new ConnectiveName(ANDalt0);
    public final static ConnectiveName OR      = new ConnectiveName(ORalt0);
    public final static ConnectiveName NOT     = new ConnectiveName(NOTalt0);
    public final static ConnectiveName IMPLIES = new ConnectiveName(IMPLIESalt0);
    public final static ConnectiveName EQUIVALENT = new ConnectiveName(EQUIVALENTalt0);
	
	public String name;
	
	/**
	 * 
	 */
	protected ConnectiveName(String name) { // This is protected because getConnectiveName(String name) should be used instead.
		this.name = name;
	}
	/**
    *
    * @param str
    * @return
    * @deprecated 
    */
	public static String standardizeConnective(String str) { // No longer used.
		if (isaAND(str)) { return "AND"; }
		if (isaOR( str)) { return "OR";  }
		if (isaNOT(str)) { return "NOT"; }
		if (isaIMPLIES(   str)) { return  "->"; }
		if (isaEQUIVALENT(str)) { return "<->"; }
		return str;
	}
	public static boolean isaAND(String str) {
		return (   str.equalsIgnoreCase(ConnectiveName.ANDalt0) || str.equalsIgnoreCase(ConnectiveName.ANDalt1) || str.equalsIgnoreCase(ConnectiveName.ANDalt2) || str.equalsIgnoreCase(ConnectiveName.ANDalt3) || str.equalsIgnoreCase(ConnectiveName.LogicalAND));
	}
	public static boolean isaOR(String str) {
		return (   str.equalsIgnoreCase(ConnectiveName.ORalt0)  || str.equalsIgnoreCase(ConnectiveName.ORalt1)  || str.equalsIgnoreCase(ConnectiveName.ORalt2)  ||  str.equalsIgnoreCase(ConnectiveName.ORalt3) || str.equalsIgnoreCase(ConnectiveName.LogicalOR));
	}
	public static boolean isaNOT(String str) {
		return (   str.equalsIgnoreCase(ConnectiveName.NOTalt0) || str.equalsIgnoreCase(ConnectiveName.NOTalt1) || str.equalsIgnoreCase(ConnectiveName.NOTalt2) || str.equalsIgnoreCase(ConnectiveName.LogicalNOT));
	}
	public static boolean isaIMPLIES(String str) {
		return (   str.equalsIgnoreCase(ConnectiveName.IMPLIESalt0)    || str.equalsIgnoreCase(ConnectiveName.IMPLIESalt1)    || str.equalsIgnoreCase(ConnectiveName.IMPLIESalt2)
				|| str.equalsIgnoreCase(ConnectiveName.IMPLIESalt3)|| str.equalsIgnoreCase(ConnectiveName.IMPLIESalt4)    || str.equalsIgnoreCase(ConnectiveName.IMPLIESalt5));
	}
	public static boolean isaBackwardsIMPLIES(String str) {
		return (   str.equalsIgnoreCase(":-") || str.equalsIgnoreCase("if") || str.equalsIgnoreCase(":="));
	}
	public static boolean isaEQUIVALENT(String str) {
		return (   str.equalsIgnoreCase(ConnectiveName.EQUIVALENTalt0) || str.equalsIgnoreCase(ConnectiveName.EQUIVALENTalt1) || str.equalsIgnoreCase(ConnectiveName.EQUIVALENTalt2));
	}
	public static boolean isaSPECIAL(String str) {
		return (   str.equalsIgnoreCase(ConnectiveName.SPECIAL) );
	}
	
	public static boolean sameConnective(ConnectiveName a, ConnectiveName b) {
        if ( a.name.equals(b.name) ) return true;
		if (isaAND(       a.name)) { return isaAND(       b.name); }
		if (isaOR(        a.name)) { return isaOR(        b.name); }
		if (isaNOT(       a.name)) { return isaNOT(       b.name); }
		if (isaIMPLIES(   a.name)) { return isaIMPLIES(   b.name); }
		if (isaEQUIVALENT(a.name)) { return isaEQUIVALENT(b.name); }
		if (isaSPECIAL(   a.name)) { return isaSPECIAL(   b.name); }
		Utils.error("Unknown connectives: << '" + a + "' << and '" + b + "'");
		return false;
	}

    public boolean isSameConnective(ConnectiveName that) {
        return sameConnective(this, that);
    }
	
	public static boolean isaConnective(String str) {
		return ( isaAND(str) || isaOR(str) || isaNOT(str) || isaIMPLIES(str) || isaEQUIVALENT(str) || isaSPECIAL(str) );
	}

	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return name;
	}
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return name;
	}

    /** Substitutes the ConnectiveName with a SerializableConnectiveName while Serializing.
     *
     * @return
     * @throws java.io.ObjectStreamException
     */
    private Object writeReplace() throws ObjectStreamException {
        return new SerializableConnectiveName(name);
    }
    
    public static boolean isTextualConnective(String str) {
    	return  "v".equalsIgnoreCase(str) ||
    		   "if".equalsIgnoreCase(str) ||
    		   "or".equalsIgnoreCase(str) ||
    		  "and".equalsIgnoreCase(str) ||
   		    //"not".equalsIgnoreCase(str) ||
   		     "else".equalsIgnoreCase(str) ||
   		     "then".equalsIgnoreCase(str) ||
   		  "implies".equalsIgnoreCase(str) ||
   	   "equivalent".equalsIgnoreCase(str);
    }

    /** This is a little hack to allow the Type to be canonicalized by the string handler.
     *
     * We want to use readResolve to canonicalize the Type object.  However, when we
     * run readResolve, we don't have the InputStream.  No inputStream, no string handler.
     * So, we serialize this little stub class which has a variable to temporarily hold
     * the string handler.
     *
     * This call will then use the readResolve method to fix up the stream.
     */
    protected static class SerializableConnectiveName implements Serializable {

        String name;

        transient public HandleFOPCstrings stringHandler;

        public SerializableConnectiveName(String name) {
            this.name = name;
        }

        /** Methods for reading a Object cached to disk.
         *
         * @param in
         * @throws java.io.IOException
         * @throws java.lang.ClassNotFoundException
         */
        private void readObject(java.io.ObjectInputStream in) throws IOException, ClassNotFoundException {
            if (in instanceof FOPCInputStream == false) {
                throw new IllegalArgumentException(ConnectiveName.class.getName() + ".readObject input stream must support FOPCObjectInputStream interface");
            }

            in.defaultReadObject();

            FOPCInputStream fOPCInputStream = (FOPCInputStream) in;

            this.stringHandler = fOPCInputStream.getStringHandler();
        }

        public Object readResolve() throws ObjectStreamException {
            // Canonicalize the object via the string handler...
            return stringHandler.getConnectiveName(name);
        }
    }

	@Override
	public ConnectiveName applyTheta(Map<Variable,Term> bindings) {
		return this;
	}
	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return 0;
	}

}