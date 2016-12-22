/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC;

/**
 *
 * @author twalker
 */
public class TermToIntegerTypeConverter implements TermToJavaTypeConverter<Integer> {

    public static final TermToIntegerTypeConverter converter = new TermToIntegerTypeConverter();
    
    private TermToIntegerTypeConverter() {
        
    }

    public Class<Integer> getJavaType() {
        return Integer.class;
    }

    public Integer convertFromTerm(Term term) throws UnsupportedOperationException {
        try {
            return Integer.parseInt( term.toString() );
        }
        catch(NumberFormatException nfe) {

        }

        return null;
    }

    public Term convertToTerm(Integer integer, HandleFOPCstrings stringHandler) throws UnsupportedOperationException {
        return stringHandler.getNumericConstant(integer);
    }
}
