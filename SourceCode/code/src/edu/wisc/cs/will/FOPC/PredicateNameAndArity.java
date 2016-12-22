package edu.wisc.cs.will.FOPC;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import edu.wisc.cs.will.Utils.Utils;
import java.util.Set;

public class PredicateNameAndArity {

    private PredicateName predicateName;

    private int arity;

    private transient List<TypeSpec> types;

    public PredicateNameAndArity(PredicateName predicateName, int arity) {
        this.predicateName = predicateName;
        this.arity = arity;
    }
    
    public PredicateNameAndArity(HandleFOPCstrings stringHandler, String pNameAndAritySpec) {
		PredicateName pName = stringHandler.getPredicateName(pNameAndAritySpec.substring(0, pNameAndAritySpec.indexOf('/')));
		int           arity = Integer.parseInt(pNameAndAritySpec.substring(pNameAndAritySpec.indexOf('/') + 1));
		this.predicateName  = pName;
        this.arity          = arity;
    }

    public PredicateNameAndArity(DefiniteClause definiteClause) {
        Literal clauseHead = definiteClause.getDefiniteClauseHead();

        this.predicateName = clauseHead.predicateName;
        this.arity = clauseHead.numberArgs();
    }
    
    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final PredicateNameAndArity other = (PredicateNameAndArity) obj;
        if (this.predicateName != other.predicateName) { // JWS: any reason for the following????  && (this.predicateName == null || !this.predicateName.equals(other.predicateName))) {
            return false;
        }
        if (this.arity != other.arity) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        int hash = 5;
        hash = 23 * hash + (this.predicateName != null ? this.predicateName.hashCode() : 0);
        hash = 17 * hash + this.arity;
        return hash;
    }

    public PredicateName getPredicateName() {
        return predicateName;
    }

    public int getArity() {
        return arity;
    }

    public void setArity(int arityNew) {
        arity = arityNew;
    }

    public Type getType(int argumentIndex) {
        List<PredicateSpec> ps = predicateName.getTypeOnlyList(arity);
        if (ps != null && ps.size() > 0) {
            return ps.get(0).getTypeSpecList().get(argumentIndex).isaType;
        }
        else {
            return null;
        }
    }

    /** Returns the types of all arguments.
     * 
     * @return List of types, one for each argument.
     */
    public List<Type> getTypes() {
        List<Type> types = new ArrayList<Type>(arity);
        for (int i = 0; i < arity; i++) {
            types.add(getType(i));
        }
        return types;
    }

    /** Return the first typeSpec for the given argument.
     *
     * @param argumentIndex
     * @return
     */
    public List<TypeSpec> getTypeSpecs(int argumentIndex) {
        List<PredicateSpec> ps = predicateName.getTypeListForThisArity(arity);

        if (ps != null && ps.size() > 0) {

            List<TypeSpec> list = new ArrayList<TypeSpec>(ps.size());

            for (int i = 0; i < ps.size(); i++) {
                PredicateSpec predicateSpec = ps.get(i);

                list.add(predicateSpec.getTypeSpec(argumentIndex));
            }

            return list;
        }
        else {
            return Collections.EMPTY_LIST;
        }
    }

    /** Returns all of the Predicate specification attached to the predicate/arity.
     * 
     */
    public List<PredicateSpec> getPredicateSpecs() {
        List<PredicateSpec> result = predicateName.getTypeListForThisArity(arity);
        if ( result == null ) {
            result = Collections.EMPTY_LIST;
        }
        return result;
    }

    public void markAsSupportingPredicate(boolean okIfDup) {
    	//Utils.println("% markAsSupportingPredicate: " + this );
        predicateName.markAsSupportingPredicate(arity, okIfDup);
    }

    public void markAsInlinedPredicate() {
    	Utils.println("% markAsInlinedPredicate: " + this );    	
        predicateName.addInliner(arity);
    }

    public boolean isInlined() {
        return predicateName.isaInlined(arity);
    }

    public boolean isSupportingPrediate() {
        return predicateName.isaSupportingPredicate(arity);
    }

    public boolean isNonOperational() {
        return predicateName.isNonOperational(arity);
    }

    public Set<PredicateNameAndArity> getOperationalExpansions() {
        return predicateName.getOperationalExpansions(arity);
    }

    public void setCost(double cost) {
        getPredicateName().setCost(arity, cost, false);
    }

    public boolean isDeterminatePredicate() {
        return getPredicateName().isDeterminatePredicate(arity);
    }

    public int getDeterminateArgumentIndex() {
        return predicateName.getDeterminateArgumentIndex(arity);
    }

    public boolean isFunctionAsPredicate() {
        return predicateName.isFunctionAsPredicate(arity);
    }

    public boolean isDeterminateOrFunctionAsPred() {
        return predicateName.isDeterminateOrFunctionAsPred(arity);
    }

    public int getFunctionAsPredicateOutputIndex() {
        return predicateName.getFunctionAsPredicateOutputIndex(arity);
    }

    public int getDeterminateOrFunctionAsPredOutputIndex() {
        return predicateName.getDeterminateOrFunctionAsPredOutputIndex(arity);
    }

    public void setContainsCallable() {
        predicateName.setContainsCallable(arity);
    }

    public boolean getContainsCallable() {
        return predicateName.isContainsCallable(arity);
    }



    
    @Override
    public String toString() {
        return predicateName + "/" + arity;
    }
}
