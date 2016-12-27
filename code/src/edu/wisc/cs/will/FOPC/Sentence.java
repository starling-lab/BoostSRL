/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import edu.wisc.cs.will.FOPC.visitors.SentenceVisitor;
import edu.wisc.cs.will.ILP.SentenceCompressor;
import java.io.IOException;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.Utils.Utils;
import java.util.Collections;

/**
 * @author shavlik
 *
 * This class represents a well-formed formula (wff) in FOPC.  One addition we're including is a WEIGHT on each sentence (since we're doing MLNs).
 * 
 * See http://en.wikipedia.org/wiki/First-order_logic or an AI textbook for more info.
 *
 */
@SuppressWarnings("serial")
public abstract class Sentence extends AllOfFOPC implements Serializable, SLDQuery, SentenceOrTerm {
	protected final static int    debugLevel = 0; // Used to control output from this project (0 = no output, 1=some, 2=much, 3=all).
	
	public    final static double maxWeight     = 300.0; // Since weights are used in exp^weight, want something that avoids overflow.	
	public    final static double minWeight     = -maxWeight;	 // Also want to avoid underflow (note: code does not yet use this).
    public    final static double defaultWeight = maxWeight + 1.0; // The default weight is 'infinity.'  (Note: the Example class has a weight as well; since these two weights have different semantics, we use two long names.) 
	protected              double wgtSentence   = defaultWeight;
	transient protected   HandleFOPCstrings stringHandler; // Add another field to everything so it can access this, and hence access things like lowercaseMeansVariable.
	
	/**
	 * The Sentence class represents a well-formed formula (wff) in FOPC.
	 */
	protected Sentence() {}
	protected Sentence(HandleFOPCstrings stringHandler) {
		this.stringHandler = stringHandler;
	}
	
	public HandleFOPCstrings getStringHandler() {
		return stringHandler;
	}

	public Sentence copyAndRenameVariables() {
		stringHandler.pushVariableHash();
		Sentence result = copy2(true);
		stringHandler.popVariableHash();
		return result;
	}

    public Sentence copy() {
		return copy(false);           // Default is to do a "top-level" copy.
	}

	public abstract Sentence copy(boolean recursiveCopy);
    
	public abstract boolean containsTermAsSentence();

    public final Sentence copy2() {
        return copy2(false, new BindingList());
    }

    public final Sentence copy2(boolean recursiveCopy) {
        return copy2(recursiveCopy, new BindingList());
    }

    public abstract Sentence copy2(boolean recursiveCopy, BindingList bindingList);

	public Sentence wrapFreeVariables() {
		Collection<Variable> boundVariables = new ArrayList<Variable>(1);
		Collection<Variable> freeVariables  = collectFreeVariables(boundVariables);
		
		if (freeVariables == null || freeVariables.size() <= 0) { return this; }
		if (debugLevel > 1) Utils.println("Need to wrap\n " + this + "\nin a ForAll due to these free variables: " + freeVariables);
		UniversalSentence result = new UniversalSentence(stringHandler, freeVariables, this);
		result.wgtSentence = wgtSentence; // Pull the weight out.  (Could check if the inner weight = maxWeight, but no big deal.
		wgtSentence = Sentence.maxWeight;
		return result;
	}
	
	public double getWeightOnSentence() {
		return wgtSentence;
	}	
	public Sentence setWeightOnSentence() { // Set to DEFAULT value if no arguments.
		wgtSentence = defaultWeight;
		return this; // Returning this makes it convenient to append '.setWeight' to new's.
	}
	public Sentence setWeightOnSentence(double weight) {
		this.wgtSentence = Math.max(minWeight, Math.min(maxWeight, weight)); // Keep in range.
		return this; // Returning this makes it convenient to append '.setWeight' to new's.
	}
	public void deltaWeightOnSentence(double delta) {
		setWeightOnSentence(wgtSentence + delta);
	}
	
	// In the original MLN paper in MLj, if one clause becomes N, divide the weights equally.  However, if at maxWeight, keep as is.
	// NOTE: this does not preserve the semantics of MLNs (e.g., 'weight [p(x) and q(x)]' not same as 'weight/2 p(x) and weight/2 q(x)', but we live with this so we can represent in clausal form.
	public Sentence divideWeightByN(double weight, int n) {
		if (weight > minWeight && weight < maxWeight) { this.wgtSentence = weight / n; }
		return this; // Returning this makes it convenient to append '.setWeight' to new's.
	}
	
	public Sentence negateWeight(double weight) {
		this.wgtSentence = Math.max(minWeight, Math.min(maxWeight, -weight)); // Keep in range.
		return this; // Returning this makes it convenient to append '.setWeight' to new's.
	}

    public Sentence getConjunctiveNormalForm() {
        Sentence sentence = this;

		if (debugLevel > 1) { Utils.println("\nCalling convertToClausalForm.\nOriginal form:\n "     + this); }
		// Convert equivalences to implications.   See pages 215 and 295-297 of Russell and Norvig, 2nd edition.
		boolean containsEquivalence = sentence.containsThisFOPCtype("equivalent"); // Do some initial scanning since these steps lead to complete copying.  (I'm not sure this is a big deal ..)
		if (containsEquivalence) { // Could also do these checks at each step, so only necessary parts are copied, but that might trade off too much time for space?
			sentence = sentence.convertEquivalenceToImplication(); // This can produce a SET of sentences, but they'll be conjoined with an AND.
			if (debugLevel > 1) { Utils.println("After convertEquivalenceToImplication():\n " + sentence); }
		}

		// Eliminate implications.
		boolean containsImplications = sentence.containsThisFOPCtype("implies");
		if (containsImplications) {
			sentence = sentence.eliminateImplications();
			if (debugLevel > 1) { Utils.println("After eliminateImplications():\n " + sentence); }
		}

		// Move negation inwards.
		boolean containsNegations = sentence.containsThisFOPCtype("not");
		if (containsNegations) {
			sentence = sentence.moveNegationInwards();
			if (debugLevel > 1) { Utils.println("After moveNegationInwards():\n " + sentence); }
		}

		// Skolemize.
		boolean needToSkolemize = sentence.containsThisFOPCtype("exists") || sentence.containsThisFOPCtype("forAll");
		if (needToSkolemize ) { // Need to do the dropUniversalQuantifiers.
			sentence = sentence.skolemize(null);
			if (debugLevel > 1) { Utils.println("After skolemize():\n " + sentence); }
		}

		// Distribute disjunctions over conjunctions.
		boolean containsDisjunction = sentence.containsThisFOPCtype("or");
		if (containsDisjunction) {
			sentence = sentence.distributeConjunctionOverDisjunction();
			if (debugLevel > 1) { Utils.println("After distributeDisjunctionOverConjunction():\n " + sentence); }
		}

        return sentence;
    }

	public List<Clause> convertToClausalForm() {
		Sentence sentence = this;

		if (debugLevel > 1) { Utils.println("\nCalling convertToClausalForm.\nOriginal form:\n "     + this); }
		// Convert equivalences to implications.   See pages 215 and 295-297 of Russell and Norvig, 2nd edition.
		boolean containsEquivalence = sentence.containsThisFOPCtype("equivalent"); // Do some initial scanning since these steps lead to complete copying.  (I'm not sure this is a big deal ..)
		if (containsEquivalence) { // Could also do these checks at each step, so only necessary parts are copied, but that might trade off too much time for space?
			sentence = sentence.convertEquivalenceToImplication(); // This can produce a SET of sentences, but they'll be conjoined with an AND.
			if (debugLevel > 1) { Utils.println("After convertEquivalenceToImplication():\n " + sentence); }
		}
		
		// Eliminate implications.
		boolean containsImplications = sentence.containsThisFOPCtype("implies");
		if (containsImplications) {
			sentence = sentence.eliminateImplications();
			if (debugLevel > 1) { Utils.println("After eliminateImplications():\n " + sentence); }
		}
		
		// Move negation inwards.
		boolean containsNegations = sentence.containsThisFOPCtype("not");
		if (containsNegations) {
			sentence = sentence.moveNegationInwards();
			if (debugLevel > 1) { Utils.println("After moveNegationInwards():\n " + sentence); }
		}
		
		// Skolemize.
		boolean needToSkolemize = sentence.containsThisFOPCtype("exists") || sentence.containsThisFOPCtype("forAll");
		if (needToSkolemize ) { // Need to do the dropUniversalQuantifiers.
			sentence = sentence.skolemize(null);
			if (debugLevel > 1) { Utils.println("After skolemize():\n " + sentence); }
		}

		// Distribute disjunctions over conjunctions.
		boolean containsDisjunction = sentence.containsThisFOPCtype("or");
		if (containsDisjunction) {
			double holdWgt = sentence.getWeightOnSentence();
			sentence.setWeightOnSentence(); // Set to the max weight.
			sentence = sentence.distributeDisjunctionOverConjunction();
			sentence.setWeightOnSentence(holdWgt); // We don't want to distribute this top-level weight just yet (convertToListOfClauses will do so).
			if (debugLevel > 1) { Utils.println("After distributeDisjunctionOverConjunction():\n " + sentence); }
		}
		
		// Eliminate variable-name clashes. We can do this step LAST (usually it is before Skolemization). 
		if (debugLevel > 0) { Utils.println("Clausal pre-form:\n "  + sentence); }

        //sentence = sentence.standardizeVariableNames(null, newToOldBindings);

        sentence = SentenceCompressor.getCompressedSentence(sentence);

        if (sentence instanceof Clause) {
            return Collections.singletonList((Clause)sentence);
        }
        else if(sentence instanceof Literal) {
			List<Clause> result = ((Literal) sentence).convertToListOfClauses();
			if (debugLevel > 0) { Utils.println("Clausal form:\n "  + result + "\n"); }
			if (result != null) { for (Clause c : result) { c.checkForCut(); }} // This isolated literal could be the cut, though that is unlikely.
			return result; // No need to rename variables since an isolated literal, and so will already have unique variables.
		}
        else if(sentence instanceof ConnectedSentence) {
			List<Clause> result = ((ConnectedSentence) sentence).convertToListOfClauses();
			if (debugLevel > 0) { Utils.println("Clausal form:\n "  + result + "\n"); }
			if (result != null && result.size() > 1) { // Need to rename all of these.
				List<Clause> renamedResult = new ArrayList<Clause>(result.size());
				for (Clause c : result) {
					Clause newClause = (Clause) c.copyAndRenameVariables().setWeightOnSentence(c.getWeightOnSentence());
					if (debugLevel > 1) { Utils.println("Copied form:\n "  + newClause + " from " + c); }
					newClause.checkForCut();
					renamedResult.add(newClause);
				}
				result = renamedResult;
			}
			return result;
		}
		Utils.error("Cannot yet handle this case: " + sentence);
		return null;
	}
	protected List<Clause> convertToListOfClauses() {
		Utils.error("This should not be reached, but reached by: " + this);
		return null;
	}
    
	protected Clause convertToClause() {
        List<Clause> clauses = convertToClausalForm();
        if (clauses != null && clauses.size() == 1) {
            return clauses.get(0);
        }
        else {
            Utils.error("Sentences can not be represented by a single clause.");
            return null;
        }
    }

	public List<Clause> convertForProofByNegation() {
		Sentence   negated    = negate().moveNegationInwards();
		if (debugLevel > 2) { Utils.println("    convertForProofByNegation: query='" + this + "'  negated='" + negated + "'"); }
		if (negated instanceof Literal)             { return                              negated.convertToListOfClauses(); }
		if (negated instanceof ConnectedSentence)   { return                              negated.convertToListOfClauses(); }
		if (negated instanceof ExistentialSentence) { return ((ExistentialSentence) negated).body.convertToListOfClauses(); }
		Utils.error("Should not reach here?");
		return null;
	}

	public abstract Collection<Variable> collectFreeVariables(Collection<Variable> boundVariables);
	public abstract Collection<Variable> collectAllVariables();
    @Override
	public abstract Sentence             applyTheta(Map<Variable,Term> bindings);
    public abstract Sentence             applyTheta(BindingList bindingList);

 //	public abstract int                  hashCode();
    @Override
	public abstract boolean              equals(Object other);
	public abstract boolean              containsVariables();
	public abstract BindingList          variants(Sentence other, BindingList bindings);
    public boolean                       isVariant(Sentence other) {
        return variants(other, new BindingList()) != null;
    }
	public abstract boolean              containsFreeVariablesAfterSubstitution(BindingList theta);

    public boolean                       isEquivalentUptoVariableRenaming(Sentence that) {
        return this.isEquivalentUptoVariableRenaming(that, new BindingList()) != null;
    }

    public abstract BindingList          isEquivalentUptoVariableRenaming(Sentence that, BindingList bindings);
	
	// These are all related to converting to clausal form.
	protected abstract boolean  containsThisFOPCtype(String marker);
	protected abstract Sentence convertEquivalenceToImplication();
	protected abstract Sentence eliminateImplications();
	protected abstract Sentence negate();
	protected abstract Sentence moveNegationInwards();
	protected abstract Sentence skolemize(List<Variable> outerUniversalVars);
	protected abstract Sentence distributeDisjunctionOverConjunction();
    protected abstract Sentence distributeConjunctionOverDisjunction();

    public boolean isGrounded() { return !containsVariables(); }
    public Term asTerm()        { return getStringHandler().getSentenceAsTerm(this, ""); }
    public Sentence asSentence() {
        return this;
    }

    /** Attempts to convert a sentence into a single clause.
     *
     * Converts the sentence to clauses via the convertToClausalForm() method.
     * If the clausal form contains a single clause, that clause is returned.
     * Otherwise an IllegalStateException is thrown.
     *
     * @return Sentence converted into a single clause, if possible.
     * @throws IllegalStateException Throws exception if the sentence can not be converted
     * into a single clause.
     */
    public Clause asClause() throws IllegalStateException {
        List<Clause> clauses = this.convertToClausalForm();
        if (clauses == null || clauses.size() != 1) {
            throw new IllegalStateException("Unable to convert sentence into single clause.  Sentence: \n" + this);
        }

        return clauses.get(0);
    }

//    protected Sentence standardizeVariableNames(Set<Variable> usedVariables, BindingList newToOldBindings) {
//        return this;
//    }
	
	public String returnWeightString() {
		if (wgtSentence < maxWeight) {
			if (AllOfFOPC.printUsingAlchemyNotation) { return Utils.truncate(wgtSentence, 4) + " "; } 
			return                                 "wgt = " + Utils.truncate(wgtSentence, 4) + " "; }
		return "";
	}

    public int appendWeightString(Appendable appendable) {

        int length = 0;
        
		try {
            if (wgtSentence < maxWeight) {
                String truncatedWgt = Utils.truncate(wgtSentence, 3);
                appendable.append("wgt = ").append(truncatedWgt).append(" ");
                length += 6 + truncatedWgt.length() + 1;
            }
        } catch (IOException iOException) {
        }

		return length;
	}

	// This is used to create weights strings without an instance (i.e., it is a static method).
	public static String returnWeightString(double wgt) {
		if (wgt < maxWeight) { return "wgt = " + Utils.truncate(wgt, 3) + " "; }
		return "";
	}
	
    public Literal extractLiteral() {
		if (this instanceof Literal) { return (Literal) this; }
		if (this instanceof UniversalSentence) {
			UniversalSentence univ = (UniversalSentence) this;
			return univ.body.extractLiteral();
		}
		if (this instanceof ConnectedSentence) {
			ConnectedSentence conn = (ConnectedSentence) this;
			if (ConnectiveName.isaNOT(conn.connective.name)) {
				return conn.sentenceB.extractLiteral();
			}
			Utils.error("Cannot extract a literal from: " + this);
		}
		Utils.error("Cannot extract a literal from: " + this); 
		return null;
	}

    public Clause getNegatedQueryClause() throws IllegalArgumentException {

        Clause result = null;

        List<Clause> clauses = convertToClausalForm();
        if ( clauses.size() == 0 ) {
            result = stringHandler.getClause();
        }
        else if ( clauses.size() == 1 ) {
            result = clauses.get(0).getNegatedQueryClause();
        }
        else {
            throw new IllegalArgumentException("Sentence could not be converted to legal SLDQuery clause: " + this + ".");
        }

        return result;
    }

    public <Return,Data> Return accept(SentenceVisitor<Return,Data> visitor, Data data) {
        return visitor.visitOtherSentence(this, data);
    }

    public String toPrettyString2() {
        return PrettyPrinter.print(this);
    }

       /** Methods for reading a Object cached to disk.
    *
    * @param in
    * @throws java.io.IOException
    * @throws java.lang.ClassNotFoundException
    */
    private void readObject(java.io.ObjectInputStream in) throws IOException, ClassNotFoundException {
        if ( in instanceof FOPCInputStream == false ) {
            throw new IllegalArgumentException(getClass().getCanonicalName() + ".readObject() input stream must support FOPCObjectInputStream interface");
        }

        in.defaultReadObject();

        FOPCInputStream fOPCInputStream = (FOPCInputStream) in;

        this.stringHandler = fOPCInputStream.getStringHandler();
    }
}
