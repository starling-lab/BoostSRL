/*
 * ParameterInfoList.java
 *
 * Created on August 27, 2007, 11:09 AM
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
package edu.wisc.cs.will.Utils.parameters;


import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

/**
 *
 * @author twalker
 */
@SuppressWarnings("unchecked")
public class ParameterList implements Iterable<Parameter>, Cloneable {

    private List<Parameter> parameters = new ArrayList<Parameter>();

    public ParameterList() {
    }

    public ParameterList(Parameter... parameters) {
        if (parameters != null) {
            for (int i = 0; i < parameters.length; i++) {
                this.parameters.add(parameters[i]);
            }
        }
    }

    public void addParameter(Parameter parameter) {
        if (parameters.contains(parameter)) {
            throw new IllegalStateException("Duplicate parameter added to ParameterList: " + parameter);
        }

        parameters.add(parameter);
    }

    public void addAll(ParameterList additionalParameters) {
        for (Parameter p : additionalParameters) {
            addParameter(p);
        }
    }

    @Override
    public Iterator<Parameter> iterator() {
        return parameters.iterator();
    }

    @Override
    public ParameterList clone() {
        ParameterList pl = new ParameterList();
        pl.addAll(this);
        return pl;
    }

    /** Processes the parameterValues, parsing the values and setting the results in the owner object using the appropriate setters.
     *
     * All of the parameters in the parameter list will be parsed against the values in parameterValueMap.
     * The Parameter.setValue method will be called for all parameters in the list.  Parameters without a
     * corresponding value in parameterValueMap will either recieve the default value or a ParameterRequiredException
     * will be thrown if it is a required parameter.
     * <p>
     * After all parameters are parsed, a map with the unrecognized parameters will be returned.
     *
     * @param owner Object which owns the parameters.  The appropriate setter methods will be called to set the fields based on the parsed values.
     * @param parameterValueMap Map of parameter names to parameter values.  This map is not modified.
     * @return a map with the unrecognized parameters.
     * @throws IllegalParameterException Thrown if a parameterValue is not of the correct format.
     * @throws ParameterRequiredException Thrown if a parameterValue is null or not in the parameterValueMap but is a required parameter.
     */
    public Map<String,String> setParameters(Object owner, Map<String,String> parameterValueMap) throws IllegalParameterException, ParameterRequiredException {

        Map<String,String> remainingParameters = new HashMap<String,String>( parameterValueMap );

        for (Parameter p : this) {
            String parameterName = p.getName();

            String parameterStringValue = parameterValueMap.get(parameterName);
            p.setValue(owner, parameterStringValue);

            remainingParameters.remove(parameterName);
        }

        return remainingParameters;
    }

    @Override
    public String toString() {
        return "ParameterList " + parameters.toString();
    }


}
