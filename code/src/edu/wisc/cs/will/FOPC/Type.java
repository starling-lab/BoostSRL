/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import java.io.IOException;
import java.io.ObjectStreamException;
import java.io.Serializable;
import java.util.Map;

/**
 * @author shavlik
 * 
 * The material in this class is used in ILP and MLNs, though it can play a role in other logical-reasoning systems.
 *
 */
@SuppressWarnings("serial")
public class Type extends AllOfFOPC implements Serializable {
	public String typeName;
    public HandleFOPCstrings stringHandler;

	/**
	 * 
	 */
    protected Type(String typeName, HandleFOPCstrings stringHandler) {
        this.typeName = typeName;
        this.stringHandler = stringHandler;
    }

	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return typeName;
	}
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return typeName;
	}
    
    public boolean isa(Type parentType) {
        return stringHandler.isaHandler.isa(this, parentType);
    }

    public boolean isa(String parentType) {
        return stringHandler.isaHandler.isa(this, parentType);
    }

   /** Substitutes the Type with a SerializableType while Serializing.
    *
    * @return
    * @throws java.io.ObjectStreamException
    */
   private Object writeReplace() throws ObjectStreamException {
       return new SerializableType(typeName);
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
    protected static class SerializableType implements Serializable {

        String typeName;
        transient public HandleFOPCstrings stringHandler;

        public SerializableType(String type) {
            this.typeName = type;
        }

        /** Methods for reading a Object cached to disk.
         *
         * @param in
         * @throws java.io.IOException
         * @throws java.lang.ClassNotFoundException
         */
        private void readObject(java.io.ObjectInputStream in) throws IOException, ClassNotFoundException {
            if (in instanceof FOPCInputStream == false) {
                throw new IllegalArgumentException(getClass().getCanonicalName() + ".readObject input stream must support FOPCObjectInputStream interface");
            }

            in.defaultReadObject();

            FOPCInputStream fOPCInputStream = (FOPCInputStream) in;

            this.stringHandler = fOPCInputStream.getStringHandler();
        }

        public Object readResolve() throws ObjectStreamException {
            // Canonicalize the object via the string handler...
            return stringHandler.isaHandler.getIsaType(typeName);
        }

    }

	@Override
	public Type applyTheta(Map<Variable, Term> bindings) {
		return this;
	}

	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return 0;
	}
}
