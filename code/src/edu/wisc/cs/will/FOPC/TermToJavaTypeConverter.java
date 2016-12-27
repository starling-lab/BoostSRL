/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC;

/**
 *
 * @param <T> Java class of the object that is converted to/from by this converter.
 * @author twalker
 */
public interface TermToJavaTypeConverter<T> {

    /** Returns the java type this convert produces.
     * 
     * @return Class of java type this converter produces.
     */
    public Class<T> getJavaType();

    /** Converts from the WILL Term to the java type specified by getJavaType().
     *
     * The willTerm argument may not be ground.  It is converter dependent
     * how non-ground terms are handled.  If the converter is unable to handle
     * non-ground terms, null will be returned to indicate a conversion failure.
     *
     * This is an optional method.  Converts need only support conversion in one
     * direction.  (Actually, they don't need to support conversion in either
     * direction, but then they aren't a very effective converter, are they?)
     *
     * @param term Term to be converted, possibly unground.
     * @return A java object of class specified by getJavaType() that willTerm
     * represents, or null if the term can not be converted.
     * @throws UnsupportedOperationException If this converter does not support
     * conversion in this direction.
     */
    public T convertFromTerm(Term term) throws UnsupportedOperationException;

    /** Converts from the Will Term to the java type specified by getJavaType().
     *
     * The willTerm argument may not be ground.  It is converter dependent
     * how non-ground terms are handled.  If the converter is unable to handle
     * non-ground terms, null will be returned to indicate a conversion failure.
     *
     * This is an optional method.  Converts need only support conversion in one
     * direction.  (Actually, the don't need to support conversion in either
     * direction, but then they aren't a very effective converter, are they?)
     *
     * @param object Object to be converted into a Term, guaranteed non-null.
     * @param stringHandler String handler to use to lookup FOPC entities if necessary. 
     * @return A Term representing the object.
     * @throws UnsupportedOperationException If this converter does not support
     * conversion in this direction.
     */
    public Term convertToTerm(T object, HandleFOPCstrings stringHandler) throws UnsupportedOperationException;
}
