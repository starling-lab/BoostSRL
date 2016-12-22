/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.Utils.Filter;
import java.util.HashMap;
import java.util.Map;

/**
 *
 * @author twalker
 */
public class PredicateNameAndArityFilter implements Filter<PredicateNameAndArity> {

    private HandleFOPCstrings stringHandler;

    private Map<PredicateName, ArityFilter> nameToArityMap;

    public PredicateNameAndArityFilter(HandleFOPCstrings stringHandler) {
        this.stringHandler = stringHandler;
    }

    public boolean includeElement(PredicateNameAndArity predicateNameAndArity) {
        return includeElement(predicateNameAndArity.getPredicateName(), predicateNameAndArity.getArity());
    }

    public boolean includeElement(String predicateName, int arity) {
        return includeElement(stringHandler.getPredicateName(predicateName), arity);
    }
    
    public boolean includeElement(PredicateName predicateName, int arity) {
        boolean result = false;

        if ( nameToArityMap != null) {
            ArityFilter arityFilter = nameToArityMap.get(predicateName);

            if ( arityFilter != null ) {
                result = arityFilter.includeElement(arity);
            }
        }

        return result;
    }

    public void addLiteral(String predicateName, int arity) {
        addLiteral(stringHandler.getPredicateName(predicateName), arity);
    }

    public void addLiteral(PredicateName predicateName, int arity) {
        addArityFilterEntry(predicateName, arity);
    }

    public void addLiteral(PredicateNameAndArity predicateNameArity) {
        addArityFilterEntry(predicateNameArity.getPredicateName(), predicateNameArity.getArity());
    }

    public void addPredicate(String predicateName) {
        addPredicate(stringHandler.getPredicateName(predicateName));
    }

    public void addPredicate(PredicateName predicateName) {
        addArityFilterEntry(predicateName, -1);
    }

    public void removeLiteral(String predicateName, int arity) {
        removeLiteral(stringHandler.getPredicateName(predicateName), arity);
    }

    public void removeLiteral(PredicateName predicateName, int arity) {
        removeArityFilterEntry(predicateName, arity);
    }

    public void removeLiteral(PredicateNameAndArity predicateNameArity) {
        removeArityFilterEntry(predicateNameArity.getPredicateName(), predicateNameArity.getArity());
    }

    public void removePredicate(String predicateName) {
        removePredicate(stringHandler.getPredicateName(predicateName));
    }

    public void removePredicate(PredicateName predicateName) {
        removeArityFilterEntry(predicateName, -1);
    }

    public void clear() {
        nameToArityMap = null;
    }

    private void addArityFilterEntry(PredicateName predicateName, int arity) {
        if (nameToArityMap == null) {
            nameToArityMap = new HashMap<PredicateName, ArityFilter>();
        }

        ArityFilter arityFilter = nameToArityMap.get(predicateName);

        if (arityFilter == null) {
            arityFilter = new ArityFilter();
            nameToArityMap.put(predicateName, arityFilter);
        }

        if (arity == -1) {
            arityFilter.setIncludeAllArities(true);
        }
        else {
            arityFilter.addArity(arity);
        }
    }

    private void removeArityFilterEntry(PredicateName predicateName, int arity) {
        if (nameToArityMap != null) {
            ArityFilter arityFilter = nameToArityMap.get(predicateName);
            if (arityFilter != null) {
                if (arity == -1) {
                    arityFilter.setIncludeAllArities(false);
                }
                else {
                    arityFilter.removeArity(arity);
                }
            }
            if (arityFilter.isEmpty()) {
                nameToArityMap.remove(predicateName);
            }
        }
    }



    @Override
    public String toString() {

        StringBuilder sb = new StringBuilder();
        sb.append("{");

        boolean first = false;
        if ( nameToArityMap != null ) {
            for (Map.Entry<PredicateName, ArityFilter> entry : nameToArityMap.entrySet()) {
                PredicateName name = entry.getKey();
                ArityFilter arityFilter = entry.getValue();

                if ( arityFilter.isIncludeAllArities() ) {
                    if ( first == false ) {
                        sb.append(", ");
                    }

                    sb.append(name.name).append("/").append("*");

                    first = false;
                }
                else {
                    for (Integer arity : arityFilter) {
                        if ( first == false ) {
                            sb.append(", ");
                        }

                        sb.append(name.name).append("/").append(arity);

                        first = false;
                    }
                }
            }
        }

        sb.append("}");

        return sb.toString();

    }


}
