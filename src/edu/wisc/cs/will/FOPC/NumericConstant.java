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
public class NumericConstant extends Constant implements Serializable {

    public Number value;

    private int type;

    public static final int isaInteger = 0;

    public static final int isaDouble = 1;

    public static final int isaFloat = 2; // Not used, but leave in case this changes.

    public static final int isaLong = 3;

    public static long instancesCreated = 0;
    
    protected NumericConstant() {
    	instancesCreated++;
    }
    /**
     *
     */
    // DON'T CALL THESE DIRECTLY.  GO VIA HandleFOPCstrings.
    protected NumericConstant(HandleFOPCstrings stringHandler, Number value, int type, TypeSpec typeSpec) {
    	this();
        this.stringHandler = stringHandler;
        this.value = value;
        this.setType(type);
        this.setTypeSpec(typeSpec);
    }

    @Override
    public String getName() {
        switch (getType()) {
            case isaInteger:
                return Integer.toString(value.intValue());
            case isaLong:
                return Long.toString(value.longValue());
            case isaDouble:
                return Double.toString(value.doubleValue());
            case isaFloat:
                return Float.toString(value.floatValue());
            default:
                Utils.error("Have a numeric constant whose type is undefined: " + this);
                return null;
        }
    }

    public void setType(int type) {
        this.type = type;
    }

    public int getType() {
        return type;
    }

    public boolean isaInteger() {
        return getType() == isaInteger;
    }

    public boolean isaLong() {
        return getType() == isaLong;
    }

    public boolean isaDouble() {
        return getType() == isaDouble;
    }

    public boolean isaFloat() {
        return getType() == isaFloat;
    }

    @Override
    public BindingList isEquivalentUptoVariableRenaming(Term that, BindingList bindings) {
        if (that instanceof NumericConstant == false) {
            return null;
        }

        NumericConstant numericConstant = (NumericConstant) that;

        return (value.equals(numericConstant.value) ? bindings : null);
    }

    @Override
    public boolean freeVariablesAfterSubstitution(BindingList theta) {
        return false;
    }

    public String toTypedString() {
        String end = (typeSpec != null ? typeSpec.getCountString() : "");
        return (typeSpec != null ? typeSpec.getModeString() + typeSpec.isaType.typeName + ":" + value + end : value.toString() + end);
    }

    @Override
    public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
        return toString(precedenceOfCaller, bindingList);
    }

    @Override
    public String toString(int precedenceOfCaller, BindingList bindingList) {
        if (stringHandler.printTypedStrings) {
            return toTypedString();
        }
        return getName();
    }

    /** Replace with the cached version from stringHandler.
     *
     * @return
     * @throws ObjectStreamException
     */
    private Object readResolve() throws ObjectStreamException {
        if (type == isaInteger) {
            return stringHandler.getNumericConstant(typeSpec, value.intValue());
        }
        else if (type == isaDouble) {
            return stringHandler.getNumericConstant(typeSpec, value.doubleValue());
        }
        else if (type == isaFloat) {
            return stringHandler.getNumericConstant(typeSpec, value.floatValue());
        }
        else if (type == isaLong) {
            return stringHandler.getNumericConstant(typeSpec, value.longValue());
        }
        else {
            throw new ObjectStreamException("Unknown NumberConstant type encountered: " + type) {
            };
        }
    }

    @Override
    public <Return, Data> Return accept(TermVisitor<Return, Data> visitor, Data data) {
        return visitor.visitNumericConstant(this, data);
    }

	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		return 0;
	}
}
