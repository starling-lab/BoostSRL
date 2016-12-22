/*
 * IntegerParameter.java
 *
 * Created on August 27, 2007, 12:22 PM
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package edu.wisc.cs.will.Utils.parameters;



import java.lang.reflect.Method;

/**
 *
 * @author twalker
 */
public class IntegerParameter extends Parameter<Integer> {
    
    public IntegerParameter(String name, String description, Integer defaultValue, boolean required, String setter) {
        super(name,description,defaultValue,required,setter);
    }
    
    public IntegerParameter(String name, String description, Integer defaultValue) {
        super(name,description,defaultValue,false,null);
    }
    
    public IntegerParameter(String name, String description, Integer defaultValue, boolean required) {
        super(name,description,defaultValue,required,null);
    }
    
    public IntegerParameter(String name, String description) {
        super(name,description,null, false, null);
    }

    public void setValue(Object owner, String stringValue) throws IllegalParameterException {
        Integer value = null;
        
        if ( stringValue != null ) {
            try {
                value = Integer.parseInt(stringValue);
            } catch (Exception e) {
                throw new IllegalParameterException(getName() + " = " + stringValue, e);
            }
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
                setter = owner.getClass().getMethod(getSetter(), Integer.class);
                setter.invoke(owner, value);
            } catch (NoSuchMethodException ex) {
                try {
                    setter = owner.getClass().getMethod(getSetter(), int.class);
                    setter.invoke(owner, value);
                }
                catch (Exception ex2) {
                    throw new IllegalParameterException("Unable to set value for parameter " + this.getName(), ex2);
                }
                
                
            } catch (Exception ex) {
                throw new IllegalParameterException("Unable to set value for parameter " + this.getName(), ex);
            } 
            
        }
    }
    
}
