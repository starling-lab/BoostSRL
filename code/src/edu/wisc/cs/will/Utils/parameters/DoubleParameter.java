/*
 * DoubleParameter.java
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
public class DoubleParameter extends Parameter<Double> {
    
    public DoubleParameter(String name, String description, double defaultValue, boolean required, String setter) {
        super(name,description,defaultValue,required,setter);
    }
    
    public DoubleParameter(String name, String description, double defaultValue) {
        super(name,description,defaultValue,false,null);
    }
    
    public DoubleParameter(String name, String description, double defaultValue, boolean required) {
        super(name,description,defaultValue,required,null);
    }
    
    public DoubleParameter(String name, String description) {
        super(name,description,null, false, null);
    }

    public void setValue(Object owner, String stringValue) throws IllegalParameterException {
        Double value = null;
        
        if ( stringValue != null ) {
            try {
                value = Double.parseDouble(stringValue);
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
                setter = owner.getClass().getMethod(getSetter(), Double.class);
                setter.invoke(owner, value);
            } catch (NoSuchMethodException ex) {
                try {
                    setter = owner.getClass().getMethod(getSetter(), double.class);
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
