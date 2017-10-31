/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC;

/**
 *
 * @author twalker
 */
public class TermToBooleanTypeConverter implements TermToJavaTypeConverter<Boolean> {

    public static final TermToBooleanTypeConverter converter = new TermToBooleanTypeConverter();
    
    private TermToBooleanTypeConverter() {
        
    }

    public Class<Boolean> getJavaType() {
        return Boolean.class;
    }

    public Boolean convertFromTerm(Term term) throws UnsupportedOperationException {
        if ( term.isGrounded() == false ) return null;

        String s = term.toString();

        if ( s.equalsIgnoreCase("true") ) {
            return true;
        }
        else if ( s.equalsIgnoreCase("false")) {
            return false;
        }

        return null;
    }

    public Term convertToTerm(Boolean value, HandleFOPCstrings stringHandler) throws UnsupportedOperationException {
        return value ? stringHandler.trueIndicator : stringHandler.falseIndicator;
    }
}
