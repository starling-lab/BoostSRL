/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC;

/**
 *
 * @author twalker
 */
public class TermToDoubleTypeConverter implements TermToJavaTypeConverter<Double> {

    public static final TermToDoubleTypeConverter converter = new TermToDoubleTypeConverter();
    
    private TermToDoubleTypeConverter() {
        
    }

    public Class<Double> getJavaType() {
        return Double.class;
    }

    public Double convertFromTerm(Term term) throws UnsupportedOperationException {
        try {
            return Double.parseDouble( term.toString() );
        }
        catch(NumberFormatException nfe) {

        }

        return null;
    }

    public Term convertToTerm(Double value, HandleFOPCstrings stringHandler) throws UnsupportedOperationException {
        return stringHandler.getNumericConstant(value);
    }
}
