/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC;

import java.util.HashMap;
import java.util.Map;

/** This is the base=class for a Typed user defined literal.
 *
 * <p>Do not subclass this class directly.  Instead use AbstractTypedUserDefinedBooleanLiteral
 * or AbstractTypedUserDefinedFunctionAsLiteral.
 *
 * <p>See {@link UserDefinedLiteral} for help in choosing the correct abstract class
 * to base your user defined literal on.  Most of the book-keeping and Will types
 * are already handled by these classes.
 *
 * @author twalker
 */
public abstract class AbstractTypedUserDefinedLiteral extends AbstractUserDefinedLiteral {

    @SuppressWarnings("unchecked")
	protected Map<Class, TermToJavaTypeConverter> converters = new HashMap<Class, TermToJavaTypeConverter>();

    protected AbstractTypedUserDefinedLiteral(boolean cachingEnabled) {
        this(null, cachingEnabled);
    }

    @SuppressWarnings("unchecked")
	protected AbstractTypedUserDefinedLiteral(TermToJavaTypeConverter[] additionalTypeConverters, boolean cachingEnabled) {
        super(cachingEnabled);

        setupDefaultTypeConverters();

        if ( additionalTypeConverters != null ) {
            for (TermToJavaTypeConverter termToJavaTypeConverter : additionalTypeConverters) {
                addTypeConverter(termToJavaTypeConverter);
            }
        }
    }

    /** Checks to make sure all of the types have converts.
     *
     * @param types
     * @throws java.lang.IllegalArgumentException
     */
    @SuppressWarnings("unchecked")
	protected void checkTypes(Class ... types) throws IllegalArgumentException {
        if ( types != null ) {
            for (Class class1 : types) {
                if ( converters.get(class1) == null ) throw new IllegalArgumentException("Unknown type conversion " + class1 + ".  If you need to support this type, please write an appropriate type converter and pass it to the constructor.");
            }
        }
    }

    @SuppressWarnings("unchecked")
	public void addTypeConverter(TermToJavaTypeConverter typeConverter) {
        converters.put(typeConverter.getJavaType(), typeConverter);
    }

    @SuppressWarnings("unchecked")
	protected <T> T convert(Class<T> type, Term term) {
        TermToJavaTypeConverter<T> converter = converters.get(type);
        return converter.convertFromTerm(term);
    }

    @SuppressWarnings("unchecked")
	protected <T> Term convert(Class<T> type, T value, HandleFOPCstrings stringHandler) {
        TermToJavaTypeConverter<T> converter = converters.get(type);
        return converter.convertToTerm(value, stringHandler);
    }

    protected void setupDefaultTypeConverters() {
        addTypeConverter(TermToDoubleTypeConverter.converter);
        addTypeConverter(TermToIntegerTypeConverter.converter);
        addTypeConverter(TermToBooleanTypeConverter.converter);
        addTypeConverter(TermToStringTypeConverter.converter);
    }

}
