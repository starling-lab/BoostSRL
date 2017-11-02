/*
 * ParameterInfo.java
 *
 * Created on August 27, 2007, 11:09 AM
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
package edu.wisc.cs.will.Utils.parameters;

/**
 *
 * @param <T>
 * @author twalker
 */
public abstract class Parameter<T extends Object> {

    private String name;

    private String description;

    private boolean required;

    private String setter;

    private T defaultValue;

    public Parameter(String name, String description, T defaultValue, boolean required, String setter) {
        setName(name);
        setDescription(description);
        setSetter(setter);
        setDefaultValue(defaultValue);
        setRequired(required);
    }

    /** Returns parameter name.
     * @return
     */
    public String getName() {
        return name;
    }

    public String getName(String prefix) {
        if (prefix == null) {
            return name;
        }
        return prefix + "_" + name;
    }

    /** Returns parameter description.
     * @return
     */
    public String getDescription() {
        return description;
    }

    /** Sets the value for the parameter of object
     * @param object
     *  @param stringValue String representation of parameter, may be null.
     * @throws IllegalParameterException
     */
    public abstract void setValue(Object object, String stringValue) throws IllegalParameterException;

    public void setName(String name) {
        this.name = name;
    }

    public void setDescription(String description) {
        this.description = description;
    }

    public boolean isRequired() {
        return required;
    }

    public void setRequired(boolean required) {
        this.required = required;
    }

    public String getSetter() {
        if (setter != null) {
            return setter;
        }

        String s;

        if (getName().length() > 1) {
            s = "set" + getName().substring(0, 1).toUpperCase() + getName().substring(1);
        }
        else {
            s = "set" + getName().substring(0, 1).toUpperCase();
        }

        return s;
    }

    public void setSetter(String setter) {
        this.setter = setter;
    }

    public T getDefaultValue() {
        return defaultValue;
    }

    public void setDefaultValue(T defaultValue) {
        this.defaultValue = defaultValue;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final Parameter<T> other = (Parameter<T>) obj;
        if ((this.name == null) ? (other.name != null) : !this.name.equals(other.name)) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        int hash = 3;
        hash = 73 * hash + (this.name != null ? this.name.hashCode() : 0);
        return hash;
    }

    @Override
    public String toString() {
        return getName() + "[" + getClass().getSimpleName() + "]";
    }
}
