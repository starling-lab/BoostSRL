/**
 * 
 */
package edu.wisc.cs.will.MLN_Task;

import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;

/**
 * @author shavlik
 *
 */
public class PredNameArityPair {
	public PredicateName pName;
	public int           arity;

	/**
	 * 
	 */
	public PredNameArityPair(PredicateName pName, int arity) {
		this.pName = pName;
		this.arity = arity;
	}
	public PredNameArityPair(Literal lit) {
		this.pName = lit.predicateName;
		this.arity = lit.numberArgs();
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + arity;
		result = prime * result + ((pName == null) ? 0 : pName.hashCode());
		return result;
	}
	@Override
	public boolean equals(Object obj) { // We want equality to be more than '==' here.
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		final PredNameArityPair other = (PredNameArityPair) obj;
		if (arity != other.arity)
			return false;
		if (pName == null) {
			if (other.pName != null)
				return false;
		} else if (!pName.equals(other.pName))
			return false;
		return true;
	}
	public String toString() {
		return pName + "/" + arity;
	}

}
