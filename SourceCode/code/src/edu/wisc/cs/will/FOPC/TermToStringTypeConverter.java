/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC;

/**
 *
 * @author twalker
 */
public class TermToStringTypeConverter implements TermToJavaTypeConverter<String> {

    public static final TermToStringTypeConverter converter = new TermToStringTypeConverter();

    private TermToStringTypeConverter() {

    }
    
    public Class<String> getJavaType() {
        return String.class;
    }

    public String convertFromTerm(Term term) throws UnsupportedOperationException {
        if ( term.isGrounded() == false ) return null;
        return term.toString();
    }

    public Term convertToTerm(String string, HandleFOPCstrings stringHandler) throws UnsupportedOperationException {
        return stringHandler.getStringConstant(string);
    }

}
