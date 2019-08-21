/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.FOPC.visitors.SentenceVisitor;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author shavlik
 *
 */
@SuppressWarnings("serial")
public class Clause extends Sentence implements DefiniteClause {
	public  static final int defaultNumberOfLiteralsPerRowInPrintouts = 1;
	public  static final int maxLiteralsToPrint = 100; // This maximum applies INDEPENDENTLY to both the positive and negative literals.
	
	public  List<Literal> posLiterals;
	public  List<Literal> negLiterals;

	private Boolean       bodyContainsCut = null; // This is now a tristate-variable.  True/False mean the normal thing.  Null means not yet evaluated.

	private String        extraLabel      = null; // This is partially implemented so that we can take extraLabels from SingleClauseNodes and have them persist when clauses are created.  However, weight until we are sure we want the overhead of doing this, plus if a comment should be printed inside a comment, we might have parser problems.
	public String getExtraLabel()                  {	return extraLabel; }
	public void   setExtraLabel(String extraLabel) {this.extraLabel = extraLabel;	}
	
    public static long instancesCreated = 0;  // PROBABLY SHOULD PUT THESE IN THESE IN THE STRING HANDLER.  
    public Clause() {
    	instancesCreated++;
    }
    
	public Clause(HandleFOPCstrings stringHandler, List<Literal> posLiterals, List<Literal> negLiterals) { // If called this, there is no error checking to confirm 'sign' of literals. This is done to save cpu time.
    	this();
		this.stringHandler = stringHandler;
		this.posLiterals   = posLiterals;
		this.negLiterals   = negLiterals;
	}
	public Clause(HandleFOPCstrings stringHandler, List<Literal> posLiterals, List<Literal> negLiterals, String extraLabel) {
		this(stringHandler, posLiterals, negLiterals);
		this.extraLabel = extraLabel; // if (extraLabel != null) Utils.println("public Clause: " + extraLabel);
	}
	public Clause(HandleFOPCstrings stringHandler, Clause other)  {
    	this();
		this.stringHandler = stringHandler;
		this.posLiterals   = other.posLiterals;
		this.negLiterals   = other.negLiterals;
	}
	protected Clause(HandleFOPCstrings stringHandler, List<Literal> literals, boolean literalsAreAllPos) { // If not all positive, assumes all are negative.
    	this();
		this.stringHandler = stringHandler;
		if (literalsAreAllPos) {
			posLiterals = literals;
			negLiterals = null;
		}
		else {
			posLiterals = null;
			negLiterals = literals;
		}
	}
	protected Clause(HandleFOPCstrings stringHandler, Literal literal, boolean literalIsPos) {
    	this();
		this.stringHandler = stringHandler;
		if (literalIsPos) {
			posLiterals = new ArrayList<Literal>(1);
			posLiterals.add(literal);
			negLiterals = null;
		}
		else{
			negLiterals = new ArrayList<Literal>(1);
			negLiterals.add(literal);
			posLiterals = null;
		}
	}	
	public Clause(HandleFOPCstrings stringHandler, Literal literal,	boolean literalIsPos, String extraLabel) {
		this(stringHandler, literal, literalIsPos);
		this.extraLabel = extraLabel;
	}

	public boolean getSign(Literal lit) {
		if (posLiterals != null) { for (Literal litP : posLiterals) if (litP == lit) { return true;  } }
		if (negLiterals != null) { for (Literal litN : negLiterals) if (litN == lit) { return false; } }
		Utils.error("Did not find '" + lit + "' in " + toString());
		return false;
	}
	
	public void addPosLiteralToFront(Literal lit) {
		if (posLiterals == null) { posLiterals = new ArrayList<Literal>(1); }		
		posLiterals.add(0, lit);
	}	
	public void addNegLiteralToFront(Literal lit) {
		if (negLiterals == null) { negLiterals = new ArrayList<Literal>(1); }		
		negLiterals.add(0, lit);
	}	
	public void addPosLiteralToEnd(Literal lit) {
		if (posLiterals == null) { posLiterals = new ArrayList<Literal>(1); }		
		posLiterals.add(lit);
	}	
	public void addNegLiteralToEnd(Literal lit) {
		if (negLiterals == null) { negLiterals = new ArrayList<Literal>(1); }		
		negLiterals.add(lit);
	}
	
	// These allow a single FOR LOOP to walk through all the literals.
	public int getLength() {
		return Utils.getSizeSafely(posLiterals) + Utils.getSizeSafely(negLiterals);
	}
	public Literal getIthLiteral(int i) {
		int numberPosLiterals = Utils.getSizeSafely(posLiterals);
		if (i < numberPosLiterals) { return posLiterals.get(i); }
		return                              negLiterals.get(i - numberPosLiterals);
	}
	public boolean getSignOfIthLiteral(int i) { // Is the ith literal positive?
		int numberPosLiterals = Utils.getSizeSafely(posLiterals);
		return (i < numberPosLiterals);
	}

    public Literal getPosLiteral(int i) {
        if ( posLiterals == null ) throw new IndexOutOfBoundsException();
        return posLiterals.get(i);
    }

    public int getPosLiteralCount() {
        return posLiterals == null ? 0 : posLiterals.size();
    }

    public Literal getNegLiteral(int i) {
        if ( negLiterals == null ) throw new IndexOutOfBoundsException();
        return negLiterals.get(i);
    }

    public int getNegLiteralCount() {
        return negLiterals == null ? 0 : negLiterals.size();
    }

    /** Returns the list of positive literals with gaurantee of being non-null.
     *
     * @return Non-null list of Positive literals.
     */
    public List<Literal> getPositiveLiterals() {
        if ( posLiterals == null ) return Collections.EMPTY_LIST;
        else return posLiterals;
    }

    /** Returns the list of negative literals with gaurantee of being non-null.
     *
     * @return Non-null list of negative literals.
     */
    public List<Literal> getNegativeLiterals() {
        if ( negLiterals == null ) return Collections.EMPTY_LIST;
        else return negLiterals;
    }
    
    public Clause clearArgumentNamesInPlace() {
    	if (posLiterals != null) for (Literal pLit : posLiterals) { pLit.clearArgumentNamesInPlace(); }
    	if (negLiterals != null) for (Literal nLit : negLiterals) { nLit.clearArgumentNamesInPlace(); }
    	return this;
    }
	public Clause copyAndClearArgumentNames() {
		return copy(true).clearArgumentNamesInPlace();
	}

	/**
	 * Would any variables in this clause remain UNBOUND if this binding list were to be applied?
	 * @param theta
	 * @return
	 */
    @Override
	public boolean containsFreeVariablesAfterSubstitution(BindingList theta) { // Utils.println("CLAUSE: freeVariablesAfterSubstitution: " + theta + "  clause: " + this);
		if (posLiterals != null) { for (Literal litP : posLiterals) if (litP.containsFreeVariablesAfterSubstitution(theta)) { return true; } }
		if (negLiterals != null) { for (Literal litN : negLiterals) if (litN.containsFreeVariablesAfterSubstitution(theta)) { return true; } }
		return false;
	}	
	
	public void checkForCut() {
		if ( bodyContainsCut == null ) {

            boolean found = false;
            if (negLiterals != null) { // Mark that is clause contains a 'cut' - this info is needed at the time the head (i.e., the positive literal) is matched and we don't want to check everything a clause is used in resolution theorem proving.
                for (Literal lit : negLiterals) if (lit.predicateName.name.equals("!")) {
                    found = true;
                    if (debugLevel > 1) { Utils.println("checkForCut: This clause contains a cut: " + this); }
                    break;
                }
            }

            bodyContainsCut = found;
        }
	}
	
	// Could make this a subclass, but this seems fine.
    @Override
	public boolean isDefiniteClause() { // A disjunction of ONE positive and any number of negated literals is DEFINITE.  See http://en.wikipedia.org/wiki/Horn_clause
		return getPosLiteralCount() == 1;
	}

    @Override
    public boolean isDefiniteClauseRule() {
        return getPosLiteralCount() == 1 && getNegLiteralCount() > 0;
    }

    @Override
	public boolean isDefiniteClauseFact() { // A disjunction of ONE positive and any number of negated literals is DEFINITE.  See http://en.wikipedia.org/wiki/Horn_clause
		return getPosLiteralCount() == 1 && getNegLiteralCount() == 0;
	}

    @Override
    public Literal getDefiniteClauseHead() throws IllegalStateException{
        if ( isDefiniteClause() == false ) throw new IllegalStateException("Clause '" + this + "' is not a definite clause.");
        return posLiterals.get(0);
    }

    @Override
    public Literal getDefiniteClauseFactAsLiteral() throws IllegalStateException {
        if ( isDefiniteClauseFact() == false ) throw new IllegalStateException("Clause '" + this + "' is not a definite clause fact.");
        return posLiterals.get(0);
    }

    @Override
    public Clause getDefiniteClauseAsClause() throws IllegalStateException {
        if ( isDefiniteClause() == false ) throw new IllegalStateException("Clause '" + this + "' is not a definite clause.");
        return this;
    }

    @Override
    public List<Literal> getDefiniteClauseBody() {
        return getNegativeLiterals();
    }

    public boolean isDefiniteClauseVariant(DefiniteClause otherClause) {
        if ( this.isDefiniteClauseRule() != otherClause.isDefiniteClauseRule() ) {
            return false;
        }

        return isVariant(otherClause.getDefiniteClauseAsClause());
    }

    public BindingList unifyDefiniteClause(DefiniteClause otherDefiniteClause, BindingList bindingList) {
        if ( this.isDefiniteClauseRule() != otherDefiniteClause.isDefiniteClauseRule() ) {
            return null;
        }

        Clause otherClause = otherDefiniteClause.getDefiniteClauseAsClause();

        return unify(otherClause, bindingList);

    }

    public Sentence getAntecedent() {
        if ( getNegLiteralCount() == 0 ) {
            return stringHandler.trueLiteral;
        }
		return stringHandler.getClause( getNegativeLiterals(), null);
    }

    public Sentence getConsequence() {
        if ( getNegLiteralCount() == 0 ) {
            return stringHandler.trueLiteral;
        }
		return stringHandler.getClause( getPositiveLiterals(), null);
    }

    public int getArity() {
        if ( isDefiniteClause() == false ) throw new IllegalStateException("Clause '" + this + "' is not a definite clause.");
        return posLiterals.get(0).getArity();
    }

    public Type getType(int argument) {
        if ( isDefiniteClause() == false ) throw new IllegalStateException("Clause '" + this + "' is not a definite clause.");
        TypeSpec type = posLiterals.get(0).getArgument(argument).getTypeSpec();

        return type != null ? type.isaType : null;
    }

    public BindingList unify(Clause that) {
        return unify(that,null);
    }

    public BindingList unify(Clause that, BindingList bindingList) {
        if ( this.getPosLiteralCount() != that.getPosLiteralCount() || this.getNegLiteralCount() != that.getNegLiteralCount() ) {
            return null;
        }

        if ( bindingList == null ) bindingList = new BindingList();

        if ( this == that ) return bindingList;

        for (int i = 0; i < getPosLiteralCount(); i++) {
            bindingList = Unifier.UNIFIER.unify(this.getPosLiteral(i), that.getPosLiteral(i), bindingList);
            if ( bindingList == null ) return null;
        }

        for (int i = 0; i < getNegLiteralCount(); i++) {
            bindingList = Unifier.UNIFIER.unify(this.getNegLiteral(i), that.getNegLiteral(i), bindingList);
            if ( bindingList == null ) return null;
        }

        return bindingList;
    }

	public boolean isEmptyClause() {
		return getPosLiteralCount() == 0 && getNegLiteralCount() == 0;
	}
	
	public void appendClause(Clause otherClause) {
		if (otherClause.posLiterals != null) {
			if (posLiterals == null) { posLiterals = otherClause.posLiterals; } else { posLiterals.addAll(otherClause.posLiterals); }
		}
		if (otherClause.negLiterals != null) {
			if (negLiterals == null) { negLiterals = otherClause.negLiterals; } else { negLiterals.addAll(otherClause.negLiterals); }
		}
	}
	
	public void copyThenAppendClause(Clause otherClause) {
		Clause newCopy = copy(false);
		if (otherClause.posLiterals != null) {
			if (newCopy.posLiterals == null) { newCopy.posLiterals = otherClause.posLiterals; } else { newCopy.posLiterals.addAll(otherClause.posLiterals); }
		}
		if (otherClause.negLiterals != null) {
			if (newCopy.negLiterals == null) { newCopy.negLiterals = otherClause.negLiterals; } else { newCopy.negLiterals.addAll(otherClause.negLiterals); }
		}
	}
	
	// This is used in resolution theorem proving.
	public Clause copyThenAppendToNegativeLiterals(List<Literal> negatedLiterals) {
		Clause newCopy = copy(false);
		if (negatedLiterals != null) {
			if (newCopy.negLiterals == null) { newCopy.negLiterals = negatedLiterals; } else { newCopy.negLiterals.addAll(negatedLiterals); }
		}
		return newCopy;
	}
	
    @Override
	public Clause applyTheta(Map<Variable,Term> theta) {
		List<Literal> newPosLiterals = null;
		List<Literal> newNegLiterals = null;
		
		if (posLiterals != null) {
			newPosLiterals = new ArrayList<Literal>(posLiterals.size());
			for (Literal lit : posLiterals) { newPosLiterals.add(lit.applyTheta(theta)); }
		}
		if (negLiterals != null) {
			newNegLiterals = new ArrayList<Literal>(negLiterals.size());
			for (Literal lit : negLiterals) { newNegLiterals.add(lit.applyTheta(theta)); }
		}
		
		Clause newClause = (Clause) stringHandler.getClause(newPosLiterals, newNegLiterals, extraLabel).setWeightOnSentence(wgtSentence);
		// newClause.bodyContainsCut = bodyContainsCut; // We do NOT want this property to propagate here - it is only for the top-level clause, rather than clauses generated during resolution.
		return newClause;
	}

    @Override
    public Clause applyTheta(BindingList bindingList) {
        if ( bindingList != null ) {
            return applyTheta(bindingList.theta);
        }
        else {
            return this;
        }
    }

    @Override
    public BindingList isEquivalentUptoVariableRenaming(Sentence that, BindingList bindings) {
        if (that instanceof Clause == false) return null;

        Clause thatClause = (Clause) that;

        if ( this.getPosLiteralCount() != thatClause.getPosLiteralCount() ) return null;
        if ( this.getNegLiteralCount() != thatClause.getNegLiteralCount() ) return null;

        if ( bindings == null ) bindings = new BindingList();

        for (int i = 0; i < getPosLiteralCount(); i++) {
            bindings = this.getPosLiteral(i).isEquivalentUptoVariableRenaming(thatClause.getPosLiteral(i), bindings);
            if ( bindings == null ) return null;
        }

        for (int i = 0; i < getNegLiteralCount(); i++) {
            bindings = this.getNegLiteral(i).isEquivalentUptoVariableRenaming(thatClause.getNegLiteral(i), bindings);
            if ( bindings == null ) return null;
        }

        return bindings;
    }

	/*
	 * (non-Javadoc)
	 * @see edu.wisc.cs.will.FOPC.Sentence#copy(boolean, boolean)
	 */
    @Override
	public Clause copy(boolean recursiveCopy) {
		List<Literal> newPosLiterals = (posLiterals == null ? null : new ArrayList<Literal>(posLiterals.size()));
		List<Literal> newNegLiterals = (negLiterals == null ? null : new ArrayList<Literal>(negLiterals.size()));
		
		if (recursiveCopy) {
            if (posLiterals != null) {
                for (Literal p : posLiterals) {
                    newPosLiterals.add(p.copy(recursiveCopy));
                }
            }
            if (negLiterals != null) {
                for (Literal n : negLiterals) {
                    newNegLiterals.add(n.copy(recursiveCopy));
                }
            }
			Clause newClause = (Clause) stringHandler.getClause(newPosLiterals, newNegLiterals, extraLabel).setWeightOnSentence(wgtSentence);
			newClause.setBodyContainsCut(getBodyContainsCut());	
			return newClause;
		}
		if (posLiterals != null) { newPosLiterals.addAll(posLiterals); }
		if (negLiterals != null) { newNegLiterals.addAll(negLiterals); }
		Clause newClause = (Clause) stringHandler.getClause(newPosLiterals, newNegLiterals, extraLabel).setWeightOnSentence(wgtSentence);
		newClause.setBodyContainsCut(getBodyContainsCut());
		return newClause;
	}

    	/*
	 * (non-Javadoc)
	 * @see edu.wisc.cs.will.FOPC.Sentence#copy(boolean, boolean)
	 */
    @Override
	public Clause copy2(boolean recursiveCopy, BindingList bindingList) {
		List<Literal> newPosLiterals = (posLiterals == null ? null : new ArrayList<Literal>(posLiterals.size()));
		List<Literal> newNegLiterals = (negLiterals == null ? null : new ArrayList<Literal>(negLiterals.size()));

		if (recursiveCopy) {
            if (posLiterals != null) {
                for (Literal p : posLiterals) {
                    newPosLiterals.add(p.copy2(recursiveCopy, bindingList));
                }
            }
            if (negLiterals != null) {
                for (Literal n : negLiterals) {
                    newNegLiterals.add(n.copy2(recursiveCopy, bindingList));
                }
            }
			Clause newClause = (Clause) stringHandler.getClause(newPosLiterals, newNegLiterals).setWeightOnSentence(wgtSentence);
			//newClause.setBodyContainsCut(getBodyContainsCut());
			return newClause;
		}
		if (posLiterals != null) { newPosLiterals.addAll(posLiterals); }
		if (negLiterals != null) { newNegLiterals.addAll(negLiterals); }
		Clause newClause = (Clause) stringHandler.getClause(newPosLiterals, newNegLiterals).setWeightOnSentence(wgtSentence);
		//newClause.setBodyContainsCut(getBodyContainsCut());
		return newClause;
	}

    @Override
    public List<Clause> convertToClausalForm() {
		List<Clause> listClause = new ArrayList<Clause>(1);

        Clause clause = this;
        listClause.add(clause);
        return listClause;
    }
	

	public BindingList copyAndReplaceVariablesWithNumbers(StringConstant[] constantsToUse) {
		Collection<Variable> collectedFreeVariables = collectFreeVariables(null);
		if (collectedFreeVariables == null) { return null; }
		BindingList bl = new BindingList();
		int counter = 0;
		int numberOfConstants = constantsToUse.length;
		for (Variable var : collectedFreeVariables) {
			StringConstant nextConstant = (counter >= numberOfConstants
											? stringHandler.getStringConstant("WillConstant" + (++counter)) // Recall that these count from ONE.
											: constantsToUse[counter++]);
			bl.addBinding(var, nextConstant);
		}
		return bl;
	}
	
    @Override
	public boolean containsTermAsSentence() {
		return false;
	}

    @Override
	public Collection<Variable> collectAllVariables() {
		return collectFreeVariables(null);
	}

    @Override
	public Collection<Variable> collectFreeVariables(Collection<Variable> boundVariables) {
    	return collectFreeVariables(boundVariables, false, false);
    }

    public Collection<Variable> collectFreeVariables(Collection<Variable> boundVariables, boolean skipPosLiterals, boolean skipNegLiterals) {
		List<Variable>  result = null;
		
		if (!skipPosLiterals && posLiterals != null) for (Literal lit : posLiterals) {
			Collection<Variable> temp = lit.collectFreeVariables(boundVariables);
			
			if (temp != null) for (Variable var : temp) if (result == null || !result.contains(var)) {
				if (result == null) { result = new ArrayList<Variable>(4); } // Wait to create until needed.
				result.add(var);
			}	
		}
		if (!skipNegLiterals && negLiterals != null) for (Literal lit : negLiterals) {
			Collection<Variable> temp = lit.collectFreeVariables(boundVariables);
			
			if (temp != null) for (Variable var : temp) if (result == null || !result.contains(var)) {
				if (result == null) { result = new ArrayList<Variable>(4); } // Wait to create until needed.
				result.add(var);
			}		
		}						
		return result == null ? Collections.EMPTY_LIST : result;
	}
	@Override
	public int hashCode() {
		if (stringHandler.useFastHashCodeForClauses) { return super.hashCode(); }
		final int prime = (getBodyContainsCut() ? 4889 : 2447); // http://primes.utm.edu/lists/small/10000.txt
		int result = 1;
		result = prime * result
				+ ((negLiterals == null) ? 677 : negLiterals.hashCode() + 2531); // Make positive and negative literals different.
		result = prime * result
				+ ((posLiterals == null) ? 739 : posLiterals.hashCode() + 1889);
		return result;
	}
    @Override
	public boolean equals(Object other) { // TODO doesn't deal with permutations in the literals.  Not sure doing so is necessary; other code deals with canonical forms.
		if (this == other) { return true; }
		if (stringHandler.usingStrictEqualsForClauses()) { return false; }
		if (!(other instanceof Clause)) { return false; }
		Clause otherAsClause = (Clause) other;
		
		if (posLiterals != null) {
			if (otherAsClause.posLiterals == null) { return false; }
			if (posLiterals.size() != otherAsClause.posLiterals.size()) { return false; }
			for (int i = 0; i < posLiterals.size(); i++) {
				if (!posLiterals.get(i).equals(otherAsClause.posLiterals.get(i))) { return false; }
			}
		}
		if (negLiterals != null) {
			if (otherAsClause.negLiterals == null) { return false; }
			if (negLiterals.size() != otherAsClause.negLiterals.size()) { return false; }
			for (int i = 0; i < negLiterals.size(); i++) {
				if (!negLiterals.get(i).equals(otherAsClause.negLiterals.get(i))) { return false; }
			}
		}
		return true;
	}

    public ConnectedSentence asConnectedSentence() {
        Sentence b;
        Sentence a;

        if ( getNegLiteralCount() == 0 ) {
            a = stringHandler.trueLiteral;
        }
        else {
            a = stringHandler.getClause(negLiterals, null);
        }

        if ( getPosLiteralCount() == 0 ) {
            b = stringHandler.trueLiteral;
        }
        else {
            b = stringHandler.getClause(posLiterals, null);
        }

        return stringHandler.getConnectedSentence(a, ConnectiveName.IMPLIES, b);
    }
	
    @Override
	public BindingList variants(Sentence other, BindingList bindings) { 
	
        // We would really like to lazily create this if null, but that would
        // require a rewrite of all the other variant code...maybe later.
        if ( bindings == null ) bindings = new BindingList();

        if ( this == other ) {
            return bindings;
        }
        else if (other instanceof Clause) {
            Clause that = (Clause) other;

            if ( this.getPosLiteralCount() != that.getPosLiteralCount() || this.getNegLiteralCount() != that.getNegLiteralCount() ) {
                return null;
            }
            
            for (int i = 0; i < getPosLiteralCount(); i++) {
                bindings = this.getPosLiteral(i).variants(that.getPosLiteral(i), bindings);
                if ( bindings == null ) {
                    return null;
                }
            }


            for (int i = 0; i < getNegLiteralCount(); i++) {
                bindings = this.getNegLiteral(i).variants(that.getNegLiteral(i), bindings);
                if ( bindings == null ) {
                    return null;
                }
            }

            return bindings;
        }
        else {
            return null;
        }
	}
	
    @Override
	public boolean containsVariables() {
		if (posLiterals != null) for (Literal lit : posLiterals) if (lit.containsVariables()) { return true; }
		if (negLiterals != null) for (Literal lit : negLiterals) if (lit.containsVariables()) { return true; }
		return false;
	}
	
	// Clauses are already in clausal form, so no need to convert them.
    @Override
	protected boolean containsThisFOPCtype(String marker) {
		return false;
	}
    @Override
	protected Clause convertEquivalenceToImplication() {
		return this;
	}
    @Override
	protected Sentence eliminateImplications() {

        Sentence sentenceA = null;
        if (posLiterals != null) {
            for (Literal literal : posLiterals) {

                if (sentenceA == null) {
                    sentenceA = literal;
                }
                else {
                    sentenceA = stringHandler.getConnectedSentence(sentenceA, ConnectiveName.AND, literal);
                }
            }
        }

        Sentence sentenceB = null;
        if (negLiterals != null) {
            for (Literal literal : negLiterals) {

                Sentence notLiteral = stringHandler.getConnectedSentence(ConnectiveName.NOT, literal);

                if (sentenceB == null) {
                    sentenceB = literal;
                }
                else {
                    sentenceB = stringHandler.getConnectedSentence(sentenceB, ConnectiveName.OR, notLiteral);
                }
            }
        }

        if ( sentenceA != null && sentenceB != null ) {
            return stringHandler.getConnectedSentence(sentenceA, ConnectiveName.OR, sentenceB );
        }
        else if ( sentenceB != null ) {
            return sentenceB;
        }
        else {
            return sentenceA;
        }
	}
    @Override
	protected Sentence negate() {
		
        Sentence negation = null;

        if (posLiterals != null) {
            for (Literal literal : posLiterals) {
                Sentence notLiteral = stringHandler.getConnectedSentence(ConnectiveName.NOT, literal);

                if (negation == null) {
                    negation = notLiteral;
                }
                else {
                    negation = stringHandler.getConnectedSentence(negation, ConnectiveName.AND, notLiteral);
                }
            }
        }

        if (negLiterals != null) {
            for (Literal literal : negLiterals) {
                if (negation == null) {
                    negation = literal;
                }
                else {
                    negation = stringHandler.getConnectedSentence(negation, ConnectiveName.AND, literal);
                }
            }
        }

        return negation;
	}

    @Override
    protected List<Clause> convertToListOfClauses() {
        List<Clause> list =  new ArrayList<Clause>(1);
        list.add(this);
        return list;
    }


    @Override
	protected Clause moveNegationInwards() {
		return this; // Cannot go in any further.
	}
    @Override
	protected Clause skolemize(List<Variable> outerUniversalVars) {
		return this; // Cannot go in any further.
	}
    @Override
	protected Sentence distributeDisjunctionOverConjunction() {
		return this; // Cannot go in any further.
	}

    @Override
    protected Sentence distributeConjunctionOverDisjunction() {
        return this;
    }
		
	public static String toPrettyStringListOfClauses(String lineStarter, List<Clause> clauses) {
		String result = "[";
		boolean firstOne = true;
		
		if (clauses != null) for (Clause c : clauses) { 
			if (firstOne) { firstOne = false; } else { result += ",\n" + lineStarter; }
			result += " " + c.toString();
		}
		return result + " ]";
	}
	
	public String toPrettyString(int precedenceOfCaller) {

        if (renameVariablesWhenPrinting) {
            return toPrettyString("", precedenceOfCaller, new BindingList());
        }
		return toPrettyString("", precedenceOfCaller, (BindingList) null);
    }


    
    @Override
	public String toPrettyString(String lineStarter, int precedenceOfCaller, BindingList bindingList) { // Allow the 'lineStarter' to be passed in, e.g., the caller might want this to be quoted text.
		boolean useStdLogicNotation = stringHandler.printUsingStdLogicNotation();
		String  result     = returnWeightString();
		String  extra      = (extraLabel == null ? "" : " " +  extraLabel + " ");
		boolean firstOne   = true;
		int     counter    = 0;
		int     counter2   = 0;
		int     numPosLits = Utils.getSizeSafely(posLiterals);
		int     numNegLits = Utils.getSizeSafely(negLiterals);
		int     precedence = stringHandler.getConnectivePrecedence(stringHandler.getConnectiveName("=>"));
		int currentMaxLiteralsToPrint = (AllOfFOPC.truncateStrings ? maxLiteralsToPrint : 1000000); // Still use a huge limit just in case there is an infinite loop/
		
		if (numPosLits == 0 && numNegLits == 0) { return result + "true"  + extra; }

		if (numPosLits == 1 && numNegLits == 0) {
			return result       + posLiterals.get(0).toString(precedence, bindingList) + extra;
		}
		if (numPosLits == 0 && numNegLits == 1) {
			return result + "~" + negLiterals.get(0).toString(precedence, bindingList) + extra;
		}
		if (numPosLits == 0) { // In this case, write out the negative literals as a negated conjunction. I.e., 'p,q->false' is the same as '~p v ~q v false' which is the same as '~(p ^ q)'.
			result += "~(";
			counter2 = 0;
			if (negLiterals != null) for (Literal literal : negLiterals) {
				if (counter2++ > currentMaxLiteralsToPrint) { result += " ... [plus " + Utils.comma(Utils.getSizeSafely(negLiterals) - currentMaxLiteralsToPrint)+ " more negative literals]"; break; }
				if (firstOne) { firstOne = false; } else {result += " ^ "; }
				result += literal.toString(precedence, bindingList);
			}
			return result + ")" + extra;
		}

		if (precedenceOfCaller < precedence) { result += "("; }
		if (useStdLogicNotation) {
			if (numNegLits > 0) {
				counter2 = 0;
				for (Literal literal : negLiterals) {
					if (counter2++ > currentMaxLiteralsToPrint) { result += " ... [plus " + Utils.comma(Utils.getSizeSafely(negLiterals) - currentMaxLiteralsToPrint)+ " more negative literals]"; break; }
					if (firstOne) { firstOne = false; }
					else {
						if (++counter % stringHandler.numberOfLiteralsPerRowInPrintouts == 0) { result += " ^\n" + lineStarter; }
						else { result += " ^ "; }
					}
					result += literal.toString(precedence, bindingList);
				}
				result += " => ";
				if (stringHandler.numberOfLiteralsPerRowInPrintouts > 0 && numNegLits >= stringHandler.numberOfLiteralsPerRowInPrintouts) { result += "\n" + lineStarter; }
			}
			counter = 0;
			if (numPosLits > 0) {
				firstOne = true;
				counter2 = 0;
				for (Literal literal : posLiterals) {
					if (counter2++ > currentMaxLiteralsToPrint) { result += " ... [plus " + Utils.comma(Utils.getSizeSafely(posLiterals) - currentMaxLiteralsToPrint)+ " more positive literals]"; break; }
					if (firstOne) { firstOne = false; }
					else {
						if (++counter % stringHandler.numberOfLiteralsPerRowInPrintouts == 0) { result += " v\n" + lineStarter; }
						else { result += " v "; } // The POSITIVE literals didn't have deMorgan's law applied to them since they weren't negated:  '(P^Q)->(RvS)' becomes '~(P^Q) v R v S' which becomes '~P v ~Q v R v S'.
					}
					result += literal.toString(precedence, bindingList);
				}
			}
			else { Utils.error("Should not reach here (by construction)."); }
		}
		else {
			if (numPosLits > 0) {
				firstOne = true;
				counter2 = 0;
				for (Literal literal : posLiterals) {
					if (counter2++ > currentMaxLiteralsToPrint) { result += " ... [plus " + Utils.comma(Utils.getSizeSafely(posLiterals) - currentMaxLiteralsToPrint)+ " more positive literals]"; break; }
					if (firstOne) { firstOne = false; }
					else {
						if (++counter % stringHandler.numberOfLiteralsPerRowInPrintouts == 0) { result += ",\n" + lineStarter; }
						else { result += ", "; }
					}
					result += literal.toString(precedence, bindingList);
				}
                if ( numNegLits > 0 ) {
                    result += " :- " + extra;
                }
				if (stringHandler.numberOfLiteralsPerRowInPrintouts > 0 && numNegLits >= stringHandler.numberOfLiteralsPerRowInPrintouts) { 
					result += "\n" + lineStarter;
				}
			}
			else { Utils.error("Should not reach here (by construction)."); }
			counter = 0;
			if (numNegLits > 0) {
				firstOne = true;
				counter2 = 0;
				for (Literal literal : negLiterals) {
					if (counter2++ > currentMaxLiteralsToPrint) { result += " ... [plus " + Utils.comma(Utils.getSizeSafely(negLiterals) - currentMaxLiteralsToPrint)+ " more negative literals]"; break; }

					if (firstOne) { firstOne = false; }
					else {
						if (++counter % stringHandler.numberOfLiteralsPerRowInPrintouts == 0) { result += ",\n" + lineStarter; }
						else { result += ", "; }
					}
					result += literal.toString(precedence, bindingList);
				}
				if (numPosLits < 1) { result += extra; }
			}
		}
		if (precedenceOfCaller < precedence) { result += ")"; }
		return result;

//        StringBuilder sb = new StringBuilder();
//
//        appendString(sb, lineStarter, precedenceOfCaller, Integer.MAX_VALUE);
//
//        return sb.toString();
	}
    
    // TODO - lineStarter needs to be passed into literals as well.
    public String toPrettyString(String lineStarter, int precedenceOfCaller, int literalsPerRow) {
        return toPrettyString(lineStarter, precedenceOfCaller, literalsPerRow, null);
    }
	public String toPrettyString(String lineStarter, int precedenceOfCaller, int literalsPerRow, BindingList bindingList) {
		int temp = stringHandler.numberOfLiteralsPerRowInPrintouts;
		stringHandler.numberOfLiteralsPerRowInPrintouts = literalsPerRow;
		String result = toPrettyString(lineStarter, precedenceOfCaller, bindingList);
		stringHandler.numberOfLiteralsPerRowInPrintouts = temp;
        return result;
	}
    
    public String toStringOneLine(int precedenceOfCaller, BindingList bindingList) {
    	int holdT  = stringHandler.numberOfTermsPerRowInPrintouts;
    	int holdTL = stringHandler.numberOfTermsPerRowInPrintoutsForLiterals;
		int holdL  = stringHandler.numberOfLiteralsPerRowInPrintouts;
    	stringHandler.numberOfTermsPerRowInPrintouts    = Integer.MAX_VALUE;
		stringHandler.numberOfLiteralsPerRowInPrintouts = Integer.MAX_VALUE;
    	String result = toString(precedenceOfCaller, bindingList);
    	stringHandler.numberOfTermsPerRowInPrintouts            = holdT;
    	stringHandler.numberOfTermsPerRowInPrintoutsForLiterals = holdTL;
    	stringHandler.numberOfLiteralsPerRowInPrintouts         = holdL;
    	return result;
    }

        @Override
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		if (stringHandler.prettyPrintClauses) {
			return toPrettyString("", precedenceOfCaller, 10, bindingList);
		}

		// If we want these to print variables like in Yap, it will take some thought.
		// Could add a flag ("printMeAsIs") and when this is false, create a NEW literal, set printMeAsIs=true on it, call stringHandler.renameAllVariables(), and then toString(precedenceOfCaller) on the result ...
		
		String result = returnWeightString() + (AllOfFOPC.printUsingAlchemyNotation ? "" : "{ ");
		boolean firstOne = true;
		int currentMaxLiteralsToPrint = (AllOfFOPC.truncateStrings ? maxLiteralsToPrint : 1000000); // Still use a huge limit just in case there is an infinite loop/
		
		int counter = 0;
		if (posLiterals != null) for (Literal literal : posLiterals) {
			if (counter++ > currentMaxLiteralsToPrint) { result += " ... [plus " + Utils.comma(Utils.getSizeSafely(posLiterals) - currentMaxLiteralsToPrint)+ " more positive literals]"; break; }

			if (firstOne) { firstOne = false; } else {result += " v "; }
			result += literal.toString(precedenceOfCaller, bindingList);
		}
		counter = 0;
		if (negLiterals != null) for (Literal literal : negLiterals) {
			if (counter++ > currentMaxLiteralsToPrint) { result += " ... [plus " + Utils.comma(Utils.getSizeSafely(negLiterals) - currentMaxLiteralsToPrint)+ " more negative literals]"; break; }
			if (firstOne) { firstOne = false; } else {result += " v "; }
			result += (AllOfFOPC.printUsingAlchemyNotation ? "!" : "~") + literal.toString(precedenceOfCaller, bindingList); // NOTE: due to '!' WILL cannot read Alchemy files.  TODO fix.
		}
		return result + (AllOfFOPC.printUsingAlchemyNotation ? "" : " }") + (extraLabel == null ? "" : " /* " +  extraLabel + " */");

//        StringBuilder sb = new StringBuilder();
//
//        appendString(sb, "", precedenceOfCaller, Integer.MAX_VALUE);
//
//        return sb.toString();
	}

//    public int appendPrettyString(Appendable appendable, String newLineStarter, int precedenceOfCaller, int maximumLength) {
//
//        // I think I have probably broken the maximum literal per row handling for pretty print here...
//
//		return appendPrettyString(appendable, newLineStarter, precedenceOfCaller, maximumLength, stringHandler.numberOfLiteralsPerRowInPrintouts);
//
//    }
//
//    private int appendPrettyString(Appendable appendable, String newLineStarter, int precedenceOfCaller, int maximumLength, int literalsPerRow) {
//
//        int length = 0;
//
//        boolean useStdLogicNotation = stringHandler.lowercaseMeansVariable;
//        //int     counter2   = 0;
//        int numPosLits = Utils.getSizeSafely(posLiterals);
//        int numNegLits = Utils.getSizeSafely(negLiterals);
//        int precedence = stringHandler.getConnectivePrecedence(stringHandler.getConnectiveName("=>"));
//
//        length += appendWeightString(appendable);
//
//        try {
//            if (numPosLits == 0 && numNegLits == 0) {
//                appendable.append("true");
//                length += 4;
//            }
//            else if (numPosLits == 1 && numNegLits == 0) {
//                length += posLiterals.get(0).appendString(appendable, newLineStarter, precedence, maximumLength - length);
//
//            }
//            else if (numPosLits == 0 && numNegLits == 1) {
//                appendable.append("~");
//                length += 1;
//
//                length += negLiterals.get(0).appendString(appendable, newLineStarter, precedence, maximumLength - length);
//            }
//            else if (numPosLits == 0) { // In this case, write out the negative literals as a negated conjunction. I.e., 'p,q->false' is the same as '~p v ~q v false' which is the same as '~(p ^ q)'.
//                appendable.append("~(");
//                length += 2;
//
//                length += appendLiterals(appendable, newLineStarter, precedence, negLiterals, " ^ ", "", numNegLits, maximumLength - length - 1, literalsPerRow);
//
//                appendable.append(")");
//                length += 1;
//            }
//            else {
//                if (precedenceOfCaller < precedence) {
//                    appendable.append("(");
//                    length += 1;
//                }
//
//                if (useStdLogicNotation) {
//                    if (numNegLits > 0) {
//                        length += appendLiterals(appendable, newLineStarter, precedence, negLiterals, " ^ ", "", getLength(), maximumLength - length, literalsPerRow);
//
//                        appendable.append(" => ");
//                        length += 4;
//
//                        if (stringHandler.numberOfLiteralsPerRowInPrintouts > 0 && numNegLits >= stringHandler.numberOfLiteralsPerRowInPrintouts) {
//                            appendable.append("\n").append(newLineStarter);
//                        }
//                    }
//
//                    if (numPosLits > 0) {
//                        length += appendLiterals(appendable, newLineStarter, precedence, posLiterals, " v ", "", getPosLiteralCount(), maximumLength - length, literalsPerRow);
//                    }
//                }
//                else {
//                    if (numPosLits > 0) {
//                        length += appendLiterals(appendable, newLineStarter, precedence, posLiterals, ", ", "", getPosLiteralCount(), maximumLength - length - 4, literalsPerRow);
//
//                        appendable.append(" :- ");
//                        length += 4;
//
//                        if (stringHandler.numberOfLiteralsPerRowInPrintouts > 0 && numPosLits >= stringHandler.numberOfLiteralsPerRowInPrintouts) {
//                            appendable.append("\n").append(newLineStarter);
//                        }
//                    }
//
//                    if (numNegLits > 0) {
//                        length += appendLiterals(appendable, newLineStarter, precedence, negLiterals, ", ", "", getLength(), maximumLength - length, literalsPerRow);
//                    }
//                }
//
//                if (precedenceOfCaller < precedence) {
//                    appendable.append(")");
//                    length += 1;
//                }
//            }
//        } catch (IOException ioe) {
//        }
//
//        return length;
//    }
//
//
//
//    @Override
//    public int appendString(Appendable appendable, String newLineStarter, int precedenceOfCaller, int maximumLength)  {
//        if (stringHandler.prettyPrintClauses) {
//            return appendPrettyString(appendable, "", precedenceOfCaller, maximumLength, 10);
//        }
//
//        int length = 0;
//        try {
//            length += appendWeightString(appendable);
//
//            appendable.append("{ ");
//            length += 2;
//
//            length += appendLiterals(appendable, newLineStarter, precedenceOfCaller, posLiterals, " v ", "", getLength(), maximumLength-length-2, 0);
//
//            if ( getPosLiteralCount() > 0 ) {
//                appendable.append(" v ");
//                length += " v ".length();
//            }
//
//            length += appendLiterals(appendable, newLineStarter, precedenceOfCaller, negLiterals, " v ", "~", getNegLiteralCount(), maximumLength-length-2, 0);
//
//            appendable.append(" }");
//            length += 2;
//
//        } catch (IOException iOException) {
//
//        }
//
//        return length;
//    }
//
//    private int appendLiterals(Appendable appendable, String newLineStarter, int precedenceOfCaller, List<Literal> literals, String connective, String literalPrefix, int literalsLeft, int maximumLength, int literalsPerLine) {
//
//        int length = 0;
//        int counter = 0;
//
//        String literalType = (literals == posLiterals ? "positive" : "negative");
//
//        boolean firstOne = true;
//
//        try {
//            if (literals != null) {
//                for (Literal literal : literals) {
//                    if (counter > currentMaxLiteralsToPrint || (counter > 0 && length >= maximumLength)) {
//                        String countString = Utils.comma(Utils.getSizeSafely(literals) - currentMaxLiteralsToPrint);
//                        appendable.append(" ... [plus ").append(countString).append(" more ").append(literalType).append(" literals]");
//                        length += " ... [plus ".length() + countString.length() + " more ".length() + literalType.length() + " literals]".length();
//                        break;
//                    }
//
//                    if (firstOne == false) {
//                        appendable.append(connective);
//                        length += connective.length();
//                    }
//
//                    // Calculate how much room each literal gets...
//                    // If previous literals didn't use all their length, allow the rest
//                    // of the literals to use it.
//                    int lengthPerLiteral = Math.max(0, (maximumLength - length) / literalsLeft - connective.length() - literalPrefix.length());
//
//                    appendable.append(literalPrefix);
//                    length += literalPrefix.length();
//
//                    counter++;
//
//                    if ( literalsPerLine > 0 && counter % literalsPerLine == 0 ) {
//                        appendable.append("\n").append(newLineStarter);
//                    }
//
//                    length += literal.appendString(appendable, newLineStarter, precedenceOfCaller, lengthPerLiteral);
//
//                    firstOne = false;
//
//                }
//            }
//        } catch (IOException iOException) {
//        }
//
//        return length;
//    }


    /**
     * @return the bodyContainsCut
     */
    public Boolean getBodyContainsCut() {
        if ( bodyContainsCut == null ) checkForCut();

        return bodyContainsCut;
    }

    /** Set the bodyContainsCut parameter.
     *
     * <rant>
     * This really shouldn't be set directly, but since the
     * posLiterals and negLiterals are exposed (to the whole damn
     * world, ugg!) we have no choice but to handle this directly.
     * This is an extremely good example of something that for some
     * reason is being calculated on the outside, but should really
     * just be done internally as a side-effect to the getter and
     * setter code (or in this case the add/remove pos/neg literal
     * code that should exist but doesn't).
     * </rant>
     *
     * @param bodyContainsCut the bodyContainsCut to set
     */
    public void setBodyContainsCut(Boolean bodyContainsCut) {
        this.bodyContainsCut = bodyContainsCut;
    }

    @Override
    public Clause getNegatedQueryClause() throws IllegalArgumentException {

        Clause result = null;

        if ( getPosLiteralCount() == 0 ) {
            result = this;
        }
        else if ( getNegLiteralCount() == 0 ) {
            // If we have only positive literals, just flip things around.
            // This would be convenient, but I am not sure what it would
            // break, so I will comment it out for now.
            result = stringHandler.getClause(null, posLiterals);
            result.extraLabel = extraLabel;
        }
        else {
            throw new IllegalArgumentException("Clause could not be converted to legal SLDQuery clause: " + this + ".");
        }
        return result;
    }

    @Override
    public <Return,Data> Return accept(SentenceVisitor<Return,Data> visitor, Data data) {
        return visitor.visitClause(this, data);
    }
	@Override
	   public int countVarOccurrencesInFOPC(Variable v) {
        int total = 0;
        if (posLiterals != null) {
            for (Literal litP : posLiterals) {
                total += litP.countVarOccurrencesInFOPC(v);
            }
        }
        if (negLiterals != null) {
            for (Literal litN : negLiterals) {
                total += litN.countVarOccurrencesInFOPC(v);
            }
        }
        return total;
    }
    
}
