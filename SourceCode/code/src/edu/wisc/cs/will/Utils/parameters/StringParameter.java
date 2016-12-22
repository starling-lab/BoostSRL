/*
 * StringParameter.java
 *
 * Created on August 27, 2007, 12:22 PM
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package edu.wisc.cs.will.Utils.parameters;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

/**
 *
 * @author twalker
 */
public class StringParameter extends Parameter<String> {
    
    public StringParameter(String name, String description, String defaultValue, boolean required, String setter) {
        super(name,description,defaultValue,required,setter);
    }
    
    public StringParameter(String name, String description, String defaultValue) {
        super(name,description,defaultValue,false,null);
    }
    
    public StringParameter(String name, String description, String defaultValue, boolean required) {
        super(name,description,defaultValue,required,null);
    }
    
    public StringParameter(String name, String description) {
        super(name,description,null, false, null);
    }

    @Override
    public void setValue(Object owner, String stringValue) throws IllegalParameterException {
        String value = null;
        
        if ( stringValue != null ) {
            value = stringValue;
        }
        
        if ( value == null ) {
            value = getDefaultValue();
        }
        
        if ( value == null && isRequired() ) {
            throw new ParameterRequiredException(getName());
        }
        
        if ( value != null ) {
            Method setter;
            try {
                setter = owner.getClass().getMethod(getSetter(), String.class);
                setter.invoke(owner, value);
            } catch (SecurityException ex) {
                throw new IllegalParameterException("Unable to set value for parameter " + this.getName(), ex);
            } catch (NoSuchMethodException ex) {
                throw new IllegalParameterException("Unable to set value for parameter " + this.getName(), ex);
            } catch (IllegalArgumentException ex) {
                throw new IllegalParameterException("Unable to set value for parameter " + this.getName(), ex);
            } catch (IllegalAccessException ex) {
                throw new IllegalParameterException("Unable to set value for parameter " + this.getName(), ex);
            } catch (InvocationTargetException ex) {
                throw new IllegalParameterException(ex.getCause().toString(), ex.getCause());
            }
        }
    }
    
}
