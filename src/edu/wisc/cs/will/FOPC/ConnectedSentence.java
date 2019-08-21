/**
 * 
 */
package edu.wisc.cs.will.FOPC;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.FOPC.visitors.SentenceVisitor;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author shavlik
 *
 */
@SuppressWarnings("serial")
public class ConnectedSentence extends Sentence implements Serializable, Implication {
	protected static final int debugLevel = 0;  // Used to control output from this class (0 = no output, 1=some, 2=much, 3=all).

	protected Sentence       sentenceA;
	protected Sentence       sentenceB; // If the connective = NOT, this first sentence is ignored (and should be set to null).
	protected ConnectiveName connective;  // Should be one of "AND, OR, NOT, =>, <=>, etc" (case is ignored).
	
	/**
	 * A connected sentence is the combination of 
	 *    (a) two sentences combined by a connective
	 * or (b) a negated sentence.
     *
     * @param stringHandler
     * @param connective
     * @param B 
     */
	protected ConnectedSentence(HandleFOPCstrings stringHandler, ConnectiveName connective, Sentence B) {
		this.stringHandler = stringHandler;
		sentenceA = null;
		sentenceB = B;
		if (ConnectiveName.isaNOT(connective.name)) {
			this.connective = connective;
		}
		else {
			Utils.error("Unknown unary connective: " + connective);
		}
	}
	protected ConnectedSentence(HandleFOPCstrings stringHandler, Sentence A, ConnectiveName connective, Sentence B) {
		this.stringHandler = stringHandler;
		sentenceA = A;
		sentenceB = B;
		if (ConnectiveName.isaNOT(connective.name)) { // For ease of use, allow this here as well.
			this.connective = connective;
			sentenceA = null;
		}
		else {
			this.connective = connective;
		}
	}
	
	public Sentence getSentenceA() {
		return sentenceA;
	}	
	public Sentence getSentenceB() {
		return sentenceB;
	}	
	public ConnectiveName getConnective() {
		return connective;
	}
	
    @Override
	public ConnectedSentence copy(boolean recursiveCopy) {
		Sentence newA = sentenceA;
		Sentence newB = sentenceB;
		if (recursiveCopy) {
			newA = (sentenceA == null ? null : sentenceA.copy(recursiveCopy));
			newB = (sentenceB == null ? null : sentenceB.copy(recursiveCopy));
		}
		return (ConnectedSentence) stringHandler.getConnectedSentence(newA, connective, newB).setWeightOnSentence(wgtSentence);
	}

    @Override
	public ConnectedSentence copy2(boolean recursiveCopy, BindingList bindingList) {
		Sentence newA = sentenceA;
		Sentence newB = sentenceB;
		if (recursiveCopy) {
			newA = (sentenceA == null ? null : sentenceA.copy2(recursiveCopy, bindingList));
			newB = (sentenceB == null ? null : sentenceB.copy2(recursiveCopy, bindingList));
		}
		return (ConnectedSentence) stringHandler.getConnectedSentence(newA, connective, newB).setWeightOnSentence(wgtSentence);
	}

    @Override
	public Collection<Variable> collectAllVariables() {
		return collectFreeVariables(null);
	}
    @Override
	public Collection<Variable> collectFreeVariables(Collection<Variable> boundVariables) {
		Collection<Variable> freeA = (sentenceA == null ? null : sentenceA.collectFreeVariables(boundVariables));
		Collection<Variable> freeB = (sentenceB == null ? null : sentenceB.collectFreeVariables(boundVariables));
						
		return Variable.combineSetsOfVariables(freeA, freeB);
	}
	
    @Override
	public boolean containsTermAsSentence() {
		if (sentenceA == null && sentenceB == null) { Utils.error("Have a connected sentence where both A and B are null! " + this); }
		if (sentenceA == null) { return sentenceB.containsTermAsSentence(); }
		if (sentenceB == null) { return sentenceA.containsTermAsSentence(); }
		return sentenceA.containsTermAsSentence() || sentenceB.containsTermAsSentence();
	}

    @Override
	public boolean containsFreeVariablesAfterSubstitution(BindingList theta) {
		if (theta == null) { return false; }
		return ((sentenceA != null && sentenceA.containsFreeVariablesAfterSubstitution(theta)) ||
				(sentenceB != null && sentenceB.containsFreeVariablesAfterSubstitution(theta)));
	}	
	
    @Override
	public ConnectedSentence applyTheta(Map<Variable,Term> bindings) {
		Sentence newA = (sentenceA == null ? null : sentenceA.applyTheta(bindings));
		Sentence newB = (sentenceB == null ? null : sentenceB.applyTheta(bindings));
		
		return stringHandler.getConnectedSentence(newA, connective, newB);
	}

    @Override
    public ConnectedSentence applyTheta(BindingList bindingList) {
        if ( bindingList != null ) {
            return applyTheta(bindingList.theta);
        }
        else {
            return this;
        }
    }


	@Override
	public int hashCode() { // Need to have equal objects produce the same hash code.
		final int prime = 31;
		int result = 1;
		result = prime * result + ((sentenceA == null) ? 0 : sentenceA.hashCode());
		result = prime * result + ((sentenceB == null) ? 0 : sentenceB.hashCode());
		return result;
	}
    @Override
	public boolean equals(Object other) { // Note: symmetric cases, eg "A and B" = "B and A", are handled by variants().
		if (!(other instanceof ConnectedSentence)) { return false; }
		
		ConnectedSentence otherCsent = (ConnectedSentence) other;
		boolean equivA = (sentenceA == null ? otherCsent.sentenceA == null : sentenceA.equals(otherCsent.sentenceA));
		if (!equivA) { return false; }
		return (sentenceB == null ? otherCsent.sentenceB == null : sentenceB.equals(otherCsent.sentenceB));
	}
	
    @Override
	public BindingList variants(Sentence other, BindingList bindings) { // TODO handle symmetric cases, e.g. "A and B" = "B and A".
		if (!(other instanceof ConnectedSentence)) { return null; }


		
		ConnectedSentence otherConnectedSentence = (ConnectedSentence) other;

        ConnectiveName thisConnective = connective;
        ConnectiveName thatConnective = otherConnectedSentence.connective;

        if ( thisConnective.isSameConnective(thatConnective) == false ) {
            return null;
        }

		BindingList binds2 = (sentenceA == null ? (otherConnectedSentence.sentenceA == null ? bindings : null)
											    : sentenceA.variants(otherConnectedSentence.sentenceA, bindings));
		if (binds2 == null) { return null; }
		return (sentenceB == null ? (otherConnectedSentence.sentenceB == null ? binds2 : null)
				                  : sentenceB.variants(otherConnectedSentence.sentenceB, binds2));
	}

    @Override
    public BindingList isEquivalentUptoVariableRenaming(Sentence that, BindingList bindings) {

        if (that instanceof ConnectedSentence == false) return null;

        ConnectedSentence thatSentence = (ConnectedSentence) that;

        if ( this.connective.isSameConnective(thatSentence.connective) == false ) return null;

        if ( (this.sentenceA == null && thatSentence.sentenceA != null) || (this.sentenceA != null && thatSentence.sentenceA == null) ) return null;
        if ( (this.sentenceB == null && thatSentence.sentenceB != null) || (this.sentenceB != null && thatSentence.sentenceB == null) ) return null;

        if ( this.sentenceA != null ) {
            bindings = this.sentenceA.isEquivalentUptoVariableRenaming(thatSentence.sentenceA, bindings);
            if ( bindings == null ) return null;
        }

        if ( this.sentenceB != null ) {
            bindings = this.sentenceB.isEquivalentUptoVariableRenaming(thatSentence.sentenceB, bindings);
            if ( bindings == null ) return null;
        }

        return bindings;
    }

    @Override
	public boolean containsVariables() {		
		boolean gndA = (sentenceA == null ? false : sentenceA.containsVariables());
		if (gndA) { return true; }
		boolean gndB = (sentenceB == null ? false : sentenceB.containsVariables());
		return gndB;	
	}	

	// Clausal-form converter stuff.
    @Override
	protected boolean containsThisFOPCtype(String marker) {
		if (ConnectiveName.isaAND(       marker) && ConnectiveName.isaAND(       connective.name)) { return true; }
		if (ConnectiveName.isaOR(        marker) && ConnectiveName.isaOR(        connective.name)) { return true; }
		if (ConnectiveName.isaNOT(       marker) && ConnectiveName.isaNOT(       connective.name)) { return true; }
		if (ConnectiveName.isaIMPLIES(   marker) && ConnectiveName.isaIMPLIES(   connective.name)) { return true; }
		if (ConnectiveName.isaEQUIVALENT(marker) && ConnectiveName.isaEQUIVALENT(connective.name)) { return true; }
		boolean sentA = (sentenceA == null ? false : sentenceA.containsThisFOPCtype(marker)); // Handle NOT's case of one argument.
		if (sentA) { return true; }
		return sentenceB.containsThisFOPCtype(marker);
	}
	// Convert p <=> q into p => q and q => p.
    @Override
	protected ConnectedSentence convertEquivalenceToImplication() {
		Sentence newA = (sentenceA == null ? null : sentenceA.convertEquivalenceToImplication()); // Handle NOT.
		Sentence newB =                             sentenceB.convertEquivalenceToImplication();
		if (ConnectiveName.isaEQUIVALENT(connective.name)) {	
			ConnectiveName impliesConnective = stringHandler.getConnectiveName("=>");
			ConnectiveName andConnective     = stringHandler.getConnectiveName("^");
		
			Sentence resultAimpliesB = stringHandler.getConnectedSentence(newA, impliesConnective, newB).divideWeightByN(wgtSentence, 2); // According to the original MLN paper in MLj (page 8), split weights evenly when converting one weighted sentence into N.
			Sentence resultBimpliesA = stringHandler.getConnectedSentence(newB, impliesConnective, newA).divideWeightByN(wgtSentence, 2); // Need to have fresh variables for one of the two, but that'll be handled elsewhere.
			return stringHandler.getConnectedSentence(resultAimpliesB, andConnective, resultBimpliesA); // Don't put any weight on the AND.
		}
		return (ConnectedSentence) stringHandler.getConnectedSentence(newA, connective, newB).setWeightOnSentence(wgtSentence);
	}
	// Convert p => q into  ~p or q.
    @Override
	protected ConnectedSentence eliminateImplications() {
		Sentence newA = (sentenceA == null ? null : sentenceA.eliminateImplications()); // Handle NOT, which has only one argument.
		Sentence newB = sentenceB.eliminateImplications();
		if (ConnectiveName.isaBackwardsIMPLIES(connective.name)) {
			ConnectiveName orConnective = stringHandler.getConnectiveName("v");
			return (ConnectedSentence) stringHandler.getConnectedSentence(newA, orConnective, newB.negate()).setWeightOnSentence(wgtSentence);
		}
		if (ConnectiveName.isaIMPLIES(connective.name)) {
			ConnectiveName orConnective = stringHandler.getConnectiveName("v");
			return (ConnectedSentence) stringHandler.getConnectedSentence(newA.negate(), orConnective, newB).setWeightOnSentence(wgtSentence);
		}
		return (ConnectedSentence) stringHandler.getConnectedSentence(newA, connective, newB).setWeightOnSentence(wgtSentence);
	}
    @Override
	protected Sentence negate() {
		if (ConnectiveName.isaNOT(connective.name)) { return sentenceB; }
		if (ConnectiveName.isaAND(connective.name)) {
			// 'not(p and q)' becomes '~p or ~q' by DeMorgan's rule.
			Sentence negatedA = sentenceA.negate();
			Sentence negatedB = sentenceB.negate();
			ConnectiveName orConnective = stringHandler.getConnectiveName("v");
			return stringHandler.getConnectedSentence(negatedA, orConnective, negatedB).setWeightOnSentence(wgtSentence);
		}
		if (ConnectiveName.isaOR(connective.name)) {
			// 'not(p or q)' becomes '~p and ~q' by DeMorgan's rule.
			Sentence negatedA = sentenceA.negate();
			Sentence negatedB = sentenceB.negate();
			ConnectiveName andConnective = stringHandler.getConnectiveName("^");
			return stringHandler.getConnectedSentence(negatedA, andConnective, negatedB).setWeightOnSentence(wgtSentence);
		}
		Utils.error("Should not be negating connected sentences except those containing AND, OR, or NOT: " + this); // If negate needed more broadly, then make a new version or pass in a flag.
		return null;
	}
    @Override
	protected Sentence moveNegationInwards() {
		if (ConnectiveName.isaNOT(connective.name)) { return sentenceB.negate(); }
		Sentence newA = sentenceA.moveNegationInwards();
		Sentence newB = sentenceB.moveNegationInwards();
		return stringHandler.getConnectedSentence(newA, connective, newB).setWeightOnSentence(wgtSentence);
		
	}
    @Override
	protected ConnectedSentence skolemize(List<Variable> outerUniversalVars) {
		Sentence newA = (sentenceA == null ? null : sentenceA.skolemize(outerUniversalVars)); // Handle NOT.
		Sentence newB =                             sentenceB.skolemize(outerUniversalVars);
		return (ConnectedSentence) stringHandler.getConnectedSentence(newA, connective, newB).setWeightOnSentence(wgtSentence);
	}
    @Override
	protected ConnectedSentence distributeDisjunctionOverConjunction() {
		if (debugLevel > 0) { Utils.println("   distributeDisjunctionOverConjunction (connective='" + connective.name + "'): " + this); }
		Sentence newL = (sentenceA == null ? null : sentenceA.distributeDisjunctionOverConjunction());
		Sentence newR =                             sentenceB.distributeDisjunctionOverConjunction();
		if (ConnectiveName.isaOR(connective.name)) {
			boolean sentLeftIsaAND  = (newL instanceof ConnectedSentence && ConnectiveName.isaAND(((ConnectedSentence) newL).connective.name));
			boolean sentRightIsaAND = (newR instanceof ConnectedSentence && ConnectiveName.isaAND(((ConnectedSentence) newR).connective.name));
			 
			// According to the original MLN paper in MLj (page 8), split weights evenly when converting one weighted sentence into N.
			
			// (a ^ b) v (c ^ d) <==> ((a ^ b) v c) ^ ((a ^ b) v d) <==> (a v c) ^ (b v c) ^ (a v d) ^ (b v d)
			if (sentLeftIsaAND && sentRightIsaAND) {
				ConnectiveName andConnective = stringHandler.getConnectiveName("^");
				ConnectiveName  orConnective = stringHandler.getConnectiveName("v");
				Sentence               leftA = ((ConnectedSentence) newL).sentenceA;
				Sentence               leftB = ((ConnectedSentence) newL).sentenceB;
				Sentence              rightA = ((ConnectedSentence) newR).sentenceA;
				Sentence              rightB = ((ConnectedSentence) newR).sentenceB;
				ConnectedSentence        or1 = stringHandler.getConnectedSentence(leftA, orConnective, rightA);
				ConnectedSentence        or2 = stringHandler.getConnectedSentence(leftA, orConnective, rightB);
				ConnectedSentence        or3 = stringHandler.getConnectedSentence(leftB, orConnective, rightA);
				ConnectedSentence        or4 = stringHandler.getConnectedSentence(leftB, orConnective, rightB);
				Sentence              newOr1 = or1.distributeDisjunctionOverConjunction(); // Need to handle conjuncts with more than two items.
				Sentence              newOr2 = or2.distributeDisjunctionOverConjunction();
				Sentence              newOr3 = or3.distributeDisjunctionOverConjunction(); // Need to handle conjuncts with more than two items.
				Sentence              newOr4 = or4.distributeDisjunctionOverConjunction();
				ConnectedSentence       and1 = stringHandler.getConnectedSentence(newOr1,  andConnective, newOr2); 
				ConnectedSentence       and2 = stringHandler.getConnectedSentence(newOr3,  andConnective, newOr4);
				ConnectedSentence result = stringHandler.getConnectedSentence(and1, andConnective, and2).spreadWeightEquallyOverConjuncts(wgtSentence); // Spread the weight now.
				
				if (debugLevel > 2) { Utils.println("    resultLR = " + result); }
				return result;
			}
			// (a ^ b) v c  <==> (a v c) ^ (b v c)
			else if (sentLeftIsaAND) {
				ConnectiveName andConnective = stringHandler.getConnectiveName("^");
				ConnectiveName  orConnective = stringHandler.getConnectiveName("v");
				Sentence               leftA = ((ConnectedSentence) newL).sentenceA;
				Sentence               leftB = ((ConnectedSentence) newL).sentenceB;
				ConnectedSentence       left = stringHandler.getConnectedSentence(leftA, orConnective, newR);
				ConnectedSentence      right = stringHandler.getConnectedSentence(leftB, orConnective, newR);
				Sentence             newLeft =  left.distributeDisjunctionOverConjunction(); // Need to handle conjuncts with more than two items.
				Sentence            newRight = right.distributeDisjunctionOverConjunction();
				ConnectedSentence result = stringHandler.getConnectedSentence(newLeft, andConnective, newRight).spreadWeightEquallyOverConjuncts(wgtSentence); // Spread the weight now.
				if (debugLevel > 2) { Utils.println("    resultLonly = " + result); }
				return result;
			}
			//  a v (b ^ c) <==> (a v b) ^ (a v c)
			else if (sentRightIsaAND) {
				ConnectiveName andConnective = stringHandler.getConnectiveName("^");
				ConnectiveName  orConnective = stringHandler.getConnectiveName("v");
				Sentence              rightA = ((ConnectedSentence) newR).sentenceA;
				Sentence              rightB = ((ConnectedSentence) newR).sentenceB;
				ConnectedSentence       left = stringHandler.getConnectedSentence(newL, orConnective, rightA);
				ConnectedSentence      right = stringHandler.getConnectedSentence(newL, orConnective, rightB);
				Sentence             newLeft =  left.distributeDisjunctionOverConjunction(); // Need to handle conjuncts with more than two items.
				Sentence            newRight = right.distributeDisjunctionOverConjunction();
				ConnectedSentence result = stringHandler.getConnectedSentence(newLeft, andConnective, newRight).spreadWeightEquallyOverConjuncts(wgtSentence); // Spread the weight now.
				if (debugLevel > 2) { Utils.println("    resultRonly = " + result); }
				return result;
			}
			else {
				ConnectedSentence result =  (ConnectedSentence) stringHandler.getConnectedSentence(newL, connective, newR).setWeightOnSentence(wgtSentence);
				if (debugLevel > 2) { Utils.println("    resultNeither = " + result); }
				return result;
			}
		}
		if (ConnectiveName.isaNOT(connective.name)) {
			ConnectedSentence result = (ConnectedSentence) stringHandler.getConnectedSentence(newL, connective, newR).setWeightOnSentence(wgtSentence);
			if (debugLevel > 2) { Utils.println("    resultNOT = " + result); }
			return result;
		}
		if (ConnectiveName.isaAND(connective.name)) {
			ConnectedSentence result =(ConnectedSentence) stringHandler.getConnectedSentence(newL, connective, newR).setWeightOnSentence(wgtSentence);
			if (debugLevel > 2) { Utils.println("    resultAND = " + result); }
			return result;
		}
		Utils.error("Should not be distributing connected sentences except those containing AND, OR, or NOT: " + this); // If negate needed more broadly, then make a new version or pass in a flag.
		return null;
	}

    @Override
	protected ConnectedSentence distributeConjunctionOverDisjunction() {
		if (debugLevel > 0) { Utils.println("   distributeDisjunctionOverConjunction (connective='" + connective.name + "'): " + this); }
		Sentence newL = (sentenceA == null ? null : sentenceA.distributeConjunctionOverDisjunction());
		Sentence newR =                             sentenceB.distributeConjunctionOverDisjunction();
		if (ConnectiveName.isaAND(connective.name)) {
			boolean sentLeftIsaOR  = (newL instanceof ConnectedSentence && ConnectiveName.isaOR(((ConnectedSentence) newL).connective.name));
			boolean sentRightIsaOR = (newR instanceof ConnectedSentence && ConnectiveName.isaOR(((ConnectedSentence) newR).connective.name));

			// (a v b) ^ (c v d) <==> ((a v b) ^ c) v ((a v b) ^ d) <==> (a ^ c) v (b ^ c) v (a ^ d) v (b ^ d)
			if (sentLeftIsaOR && sentRightIsaOR) {
				ConnectiveName andConnective = stringHandler.getConnectiveName("^");
				ConnectiveName  orConnective = stringHandler.getConnectiveName("v");
				Sentence               leftA = ((ConnectedSentence) newL).sentenceA;
				Sentence               leftB = ((ConnectedSentence) newL).sentenceB;
				Sentence              rightA = ((ConnectedSentence) newR).sentenceA;
				Sentence              rightB = ((ConnectedSentence) newR).sentenceB;
				ConnectedSentence        and1 = stringHandler.getConnectedSentence(leftA, andConnective, rightA);
				ConnectedSentence        and2 = stringHandler.getConnectedSentence(leftA, andConnective, rightB);
				ConnectedSentence        and3 = stringHandler.getConnectedSentence(leftB, andConnective, rightA);
				ConnectedSentence        and4 = stringHandler.getConnectedSentence(leftB, andConnective, rightB);
				Sentence              newOr1 = and1.distributeConjunctionOverDisjunction(); // Need to handle conjuncts with more than two items.
				Sentence              newOr2 = and2.distributeConjunctionOverDisjunction();
				Sentence              newOr3 = and3.distributeConjunctionOverDisjunction(); // Need to handle conjuncts with more than two items.
				Sentence              newOr4 = and4.distributeConjunctionOverDisjunction();
				ConnectedSentence       or1 = stringHandler.getConnectedSentence(newOr1,  orConnective, newOr2);            // Use infinite weight here.
				ConnectedSentence       or2 = stringHandler.getConnectedSentence(newOr3,  orConnective, newOr4);            // Use infinite weight here.
				ConnectedSentence result = stringHandler.getConnectedSentence(or1, orConnective, or2); // Use infinite weight here.
				if (debugLevel > 2) { Utils.println("    resultLR = " + result); }
				return result;
			}
			// (a ^ b) v c  <==> (a v c) ^ (b v c)
			else if (sentLeftIsaOR) {
				ConnectiveName andConnective = stringHandler.getConnectiveName("^");
				ConnectiveName  orConnective = stringHandler.getConnectiveName("v");
				Sentence               leftA = ((ConnectedSentence) newL).sentenceA;
				Sentence               leftB = ((ConnectedSentence) newL).sentenceB;
				ConnectedSentence       left = (ConnectedSentence) stringHandler.getConnectedSentence(leftA, andConnective, newR).divideWeightByN(wgtSentence, 2);
				ConnectedSentence      right = (ConnectedSentence) stringHandler.getConnectedSentence(leftB, andConnective, newR).divideWeightByN(wgtSentence, 2);
				Sentence             newLeft =  left.distributeConjunctionOverDisjunction(); // Need to handle conjuncts with more than two items.
				Sentence            newRight = right.distributeConjunctionOverDisjunction();
				ConnectedSentence result = stringHandler.getConnectedSentence(newLeft, orConnective, newRight); // Use infinite weight here.
				if (debugLevel > 2) { Utils.println("    resultLonly = " + result); }
				return result;
			}
			//  a v (b ^ c) <==> (a v b) ^ (a v c)
			else if (sentRightIsaOR) {
				ConnectiveName andConnective = stringHandler.getConnectiveName("^");
				ConnectiveName  orConnective = stringHandler.getConnectiveName("v");
				Sentence              rightA = ((ConnectedSentence) newR).sentenceA;
				Sentence              rightB = ((ConnectedSentence) newR).sentenceB;
				ConnectedSentence       left = (ConnectedSentence) stringHandler.getConnectedSentence(newL, andConnective, rightA).divideWeightByN(wgtSentence, 2);
				ConnectedSentence      right = (ConnectedSentence) stringHandler.getConnectedSentence(newL, andConnective, rightB).divideWeightByN(wgtSentence, 2);
				Sentence             newLeft =  left.distributeConjunctionOverDisjunction(); // Need to handle conjuncts with more than two items.
				Sentence            newRight = right.distributeConjunctionOverDisjunction();
				ConnectedSentence result = stringHandler.getConnectedSentence(newLeft, orConnective, newRight); // Use infinite weight here.
				if (debugLevel > 2) { Utils.println("    resultRonly = " + result); }
				return result;
			}
			else {
				ConnectedSentence result =  (ConnectedSentence) stringHandler.getConnectedSentence(newL, connective, newR).setWeightOnSentence(wgtSentence);
				if (debugLevel > 2) { Utils.println("    resultNeither = " + result); }
				return result;
			}
		}
		if (ConnectiveName.isaNOT(connective.name)) {
			ConnectedSentence result = (ConnectedSentence) stringHandler.getConnectedSentence(newL, connective, newR).setWeightOnSentence(wgtSentence);
			if (debugLevel > 2) { Utils.println("    resultNOT = " + result); }
			return result;
		}
		if (ConnectiveName.isaOR(connective.name)) {
			ConnectedSentence result =(ConnectedSentence) stringHandler.getConnectedSentence(newL, connective, newR).setWeightOnSentence(wgtSentence);
			if (debugLevel > 2) { Utils.println("    resultAND = " + result); }
			return result;
		}
		Utils.error("Should not be distributing connected sentences except those containing AND, OR, or NOT: " + this); // If negate needed more broadly, then make a new version or pass in a flag.
		return null;
	}

    // Need to handle (A ^ (B ^ C)) by giving them all 1/3rd the weight, that than 1/2, 1/4th, and 1/4th.
    private ConnectedSentence spreadWeightEquallyOverConjuncts(double wgtSentenceToUse) {
		if (wgtSentenceToUse <= minWeight && wgtSentenceToUse >= maxWeight) { return this; }
		ConnectiveName andConnective = stringHandler.getConnectiveName("^");
		int numberOfConjuncts = countANDconnectives(andConnective);
		if (numberOfConjuncts < 1) { Utils.error("This should not happen: " + this); }
    	setWeightOnAllANDconnectives(andConnective, wgtSentenceToUse / numberOfConjuncts);
		return this;
	}

    private int countANDconnectives(ConnectiveName andConnective) {
    	if (connective != andConnective) { return 0; }
    	boolean AisConnected = sentenceA instanceof ConnectedSentence;
    	boolean BisConnected = sentenceB instanceof ConnectedSentence;
    	if (AisConnected && BisConnected) {
    		return 1 + ((ConnectedSentence) sentenceA).countANDconnectives(andConnective) + ((ConnectedSentence) sentenceB).countANDconnectives(andConnective);
    	}
    	if (AisConnected) {
    		return 1 + ((ConnectedSentence) sentenceA).countANDconnectives(andConnective);
    	}
    	if (BisConnected) {
    		return 1 + ((ConnectedSentence) sentenceB).countANDconnectives(andConnective);
    	}
    	return 1;
	}

    private void setWeightOnAllANDconnectives(ConnectiveName andConnective, double wgtSentenceToUse) {
    	if (connective != andConnective) { return; }
    	boolean AisConnected = sentenceA instanceof ConnectedSentence;
    	boolean BisConnected = sentenceB instanceof ConnectedSentence;
    	if (AisConnected && BisConnected) {
    		((ConnectedSentence) sentenceA).setWeightOnAllANDconnectives(andConnective, wgtSentenceToUse);
    		((ConnectedSentence) sentenceB).setWeightOnAllANDconnectives(andConnective, wgtSentenceToUse);
    	}
    	if (AisConnected) {
    		((ConnectedSentence) sentenceA).setWeightOnAllANDconnectives(andConnective, wgtSentenceToUse);
    	}
    	if (BisConnected) {
    		((ConnectedSentence) sentenceB).setWeightOnAllANDconnectives(andConnective, wgtSentenceToUse);
    	}
    	setWeightOnSentence(wgtSentenceToUse);
	}
    
//    @Override
//    protected Sentence standardizeVariableNames(Set<Variable> usedVariables, BindingList newToOldBindings) {
//        if ( usedVariables == null ) {
//            usedVariables = new HashSet<Variable>();
//        }
//
//        if ( newToOldBindings == null ) {
//            newToOldBindings = new BindingList();
//        }
//
//        Sentence newSentenceA = sentenceA.standardizeVariableNames(usedVariables, newToOldBindings);
//        Sentence newSentenceB = sentenceB.standardizeVariableNames(usedVariables, newToOldBindings);
//
//        if ( newSentenceA != sentenceA || newSentenceB != sentenceB ) {
//            ConnectedSentence newSentence = stringHandler.getConnectedSentence(newSentenceA, connective, newSentenceB);
//            newSentence.setWeightOnSentence(wgtSentence);
//            return newSentence;
//        }
//        else {
//            return this;
//        }
//    }


	// When this is called the sentence should be in conjunctive normal form.
    @Override
	protected List<Clause> convertToListOfClauses() {
		if (debugLevel > 1) { Utils.println(" convertToListOfClauses (connective=" + connective.name + "): " + this); }
		if (ConnectiveName.isaAND(connective.name)) {
			List<Clause> newL = sentenceA.convertToListOfClauses();
			List<Clause> newR = sentenceB.convertToListOfClauses();
			newL.addAll(newR);
			if (wgtSentence <= Sentence.minWeight || wgtSentence >= Sentence.maxWeight) { for (Clause c : newL) { c.setWeightOnSentence(wgtSentence);     } }
			else { int n = newL.size(); for (Clause c : newL) { c.setWeightOnSentence(wgtSentence / n); } }
			return newL;
		}
		if (ConnectiveName.isaOR(connective.name)) {
			Clause clause = convertToClause();
			clause.setWeightOnSentence(wgtSentence);
			List<Clause> result = new ArrayList<Clause>(1);
			result.add(clause);
			return result;						
		}
		if (ConnectiveName.isaNOT(connective.name) && sentenceB instanceof Literal) {
			Clause clause = convertToClause();
			clause.setWeightOnSentence(wgtSentence);
			List<Clause> result = new ArrayList<Clause>(1);
			result.add(clause);
			return result;						
		}
		Utils.error("Should not be convertToListOfClauses connected sentences except those containing AND, OR, or NOT(literal): " + this);
		return null;
	}	
    @Override
	protected Clause convertToClause() {
		if (ConnectiveName.isaOR(connective.name)) {
			Clause left  = sentenceA.convertToClause();
			Clause right = sentenceB.convertToClause();
			if      ( left.posLiterals == null) { left.posLiterals = right.posLiterals; }
			else if (right.posLiterals != null) { left.posLiterals.addAll(right.posLiterals); }
			if      ( left.negLiterals == null) { left.negLiterals = right.negLiterals; }
			else if (right.negLiterals != null) { left.negLiterals.addAll(right.negLiterals); }
			left.setWeightOnSentence(wgtSentence);
			return left;
		} else if (ConnectiveName.isaNOT(connective.name) &&  sentenceB instanceof Literal) {
			return ((Literal) sentenceB).convertToClause(false);
		}
		Utils.error("Should not be calling convertToClause on connected sentences except those containing OR or NOT(literal) - have '" + connective.name + "': " + this);
		return null;
	}
    @Override
	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		String  result = returnWeightString();
		int precedence = HandleFOPCstrings.getConnectivePrecedence_static(connective);
		
		if (ConnectiveName.isaNOT(connective.name)) {
			if (precedence < precedenceOfCaller) { return result + connective + "(" + sentenceB.toPrettyString(newLineStarter, precedence, bindingList) + ")"; }
			if (connective.name.equalsIgnoreCase("not")) { return result + connective + " " + sentenceB.toPrettyString(newLineStarter, precedence, bindingList); }
			return result + connective + sentenceB.toPrettyString(newLineStarter, precedence, bindingList);
		}
		String firstSpacer = (connective.name.equals(",") ? "" : " ");
		if (precedence > precedenceOfCaller) { return result + "(" + sentenceA.toPrettyString(newLineStarter, precedence, bindingList) + firstSpacer + connective + " " + sentenceB.toPrettyString(newLineStarter, precedence, bindingList) + ")"; }
		return result + sentenceA.toPrettyString(newLineStarter, precedence, bindingList) + firstSpacer + connective + " " + sentenceB.toPrettyString(newLineStarter, precedence, bindingList);
	}
    @Override
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		String  result = returnWeightString();
		int precedence = HandleFOPCstrings.getConnectivePrecedence_static(connective);
		
		//Utils.println("precedenceOfCaller=" + precedenceOfCaller + " and precedence=" + precedence + " for " + precedence + ".");
		if (ConnectiveName.isaNOT(connective.name)) {
			if (precedence < precedenceOfCaller) { return result + connective + "(" + sentenceB.toString(precedence, bindingList) + ")"; }
			if (connective.name.equalsIgnoreCase("not") || connective.name.equalsIgnoreCase("\\+")) { return result + connective + " " + sentenceB; }
			return result + connective + sentenceB;
		}
		String firstSpacer = (connective.name.equals(",") ? "" : " ");
		if (precedence > precedenceOfCaller) { return result + "(" + sentenceA.toString(precedence, bindingList) + firstSpacer + connective + " " + sentenceB.toString(precedence, bindingList) + ")"; }
		return result + sentenceA.toString(precedence, bindingList) + firstSpacer + connective + " " + sentenceB.toString(precedence, bindingList);
	}

    @Override
    public <Return,Data> Return accept(SentenceVisitor<Return,Data> visitor, Data data) {
        return visitor.visitConnectedSentence(this, data);
    }
	@Override
	public int countVarOccurrencesInFOPC(Variable v) {
		int total = 0;
		if (sentenceA != null) { total += sentenceA.countVarOccurrencesInFOPC(v); }
		if (sentenceB != null) { total += sentenceB.countVarOccurrencesInFOPC(v); } 
		return total;
	}

    public Sentence getAntecedent() {
        if ( getConnective() != ConnectiveName.IMPLIES) throw new IllegalStateException("Sentence is not an implication: " + this + ".");

        if ( sentenceA == null ) {
            return stringHandler.trueLiteral;
        }
        else {
            return sentenceA;
        }
    }

    public Sentence getConsequence() {
        if ( getConnective() != ConnectiveName.IMPLIES) throw new IllegalStateException("Sentence is not an implication: " + this + ".");

        if ( sentenceB == null ) {
            return stringHandler.trueLiteral;
        }
        else {
            return sentenceB;
        }
    }


}
