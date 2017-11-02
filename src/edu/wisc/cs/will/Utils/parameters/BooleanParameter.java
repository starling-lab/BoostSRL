/*
 * BooleanParameter.java
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
public class BooleanParameter extends Parameter<Boolean> {
    
    public BooleanParameter(String name, String description, Boolean defaultValue, boolean required, String setter) {
        super(name,description,defaultValue,required,setter);
    }
    
    public BooleanParameter(String name, String description, Boolean defaultValue) {
        super(name,description,defaultValue,false,null);
    }
    
    public BooleanParameter(String name, String description, Boolean defaultValue, boolean required) {
        super(name,description,defaultValue,required,null);
    }
    
    public BooleanParameter(String name, String description) {
        super(name,description,null, false, null);
    }

    public void setValue(Object owner, String stringValue) throws IllegalParameterException {
        Boolean value = null;
        
        if ( stringValue != null ) {

            if ( stringValue.isEmpty() || stringValue.equals("1") ) {
                value = true;
            }
            else if ( stringValue.equals("0")) {
                value = false;
            }
            else {
                try {
                    value = Boolean.parseBoolean(stringValue);
                } catch (Exception e) {
                    throw new IllegalParameterException("Unable to parse boolean value for " + getName() + " = " + stringValue, e);
                }
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
                setter = owner.getClass().getMethod(getSetter(), Boolean.class);
                setter.invoke(owner, value);
            } catch (NoSuchMethodException ex) {
                try {
                    setter = owner.getClass().getMethod(getSetter(), boolean.class);
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
