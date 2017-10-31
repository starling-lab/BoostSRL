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
@SuppressWarnings("unchecked")
public class EnumParameter extends Parameter<Enum> {
    
    private Class<? extends Enum> enumType;

    enum Bob {
        a,b
    }

    public <T extends Enum> EnumParameter(Class<T> enumType, String name, String description, T defaultValue, boolean required, String setter) {
        super(name,description,defaultValue,required,setter);
        setEnumType(enumType);
    }
    
    public <T extends Enum> EnumParameter(Class<T> enumType, String name, String description, T defaultValue) {
        super(name,description,defaultValue,false,null);
        setEnumType(enumType);
    }
    
    public <T extends Enum> EnumParameter(Class<T> enumType, String name, String description, T defaultValue, boolean required) {
        super(name,description,defaultValue,required,null);
        setEnumType(enumType);
    }
    
    public EnumParameter(String name, String description) {
        super(name,description,null, false, null);
    }

    public void setValue(Object owner, String stringValue) throws IllegalParameterException {
        Enum value = null;
        
        if ( stringValue != null ) {
            try {
                value = Enum.valueOf(enumType, stringValue);
            } catch (IllegalArgumentException e) {

                String legalValues = "";
                try {
                    Method valuesMethod = enumType.getMethod("values");
                    Object[] values = (Object[]) valuesMethod.invoke(null);


                    for (int i = 0; i < values.length; i++) {
                        if (i > 0) {
                            legalValues += ", ";

                        }
                        legalValues += values.toString();
                    }
                } catch (NoSuchMethodException noSuchMethodException) {
                } catch (SecurityException securityException) {
                } catch (IllegalAccessException illegalAccessException) {
                } catch (IllegalArgumentException illegalArgumentException) {
                } catch (InvocationTargetException invocationTargetException) {
                }

                throw new IllegalParameterException("Parameter " + this.getName() + " value is illegal.  Legal values are: " + legalValues);
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
                setter = owner.getClass().getMethod(getSetter(), enumType);
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

    /**
     * @return the enumType
     */
    public Class<? extends Enum> getEnumType() {
        return enumType;
    }

    /**
     * @param enumType the enumType to set
     */
    public void setEnumType(Class<? extends Enum> enumType) {
        this.enumType = enumType;
    }
    
}
