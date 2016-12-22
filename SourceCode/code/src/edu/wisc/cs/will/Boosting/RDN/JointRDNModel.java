/**
 * 
 */
package edu.wisc.cs.will.Boosting.RDN;

import java.util.HashMap;

import edu.wisc.cs.will.DataSetUtils.Example;

/**
 * @author Tushar Khot
 *
 */
public class JointRDNModel  extends HashMap<String, ConditionalModelPerPredicate> {
	
	private static final long serialVersionUID = 7739914320561459606L;

	/*public double returnMarginalProbability(Example pex) {
		String pred = pex.predicateName.name;
		RDNModelPerPredicate model = get(pred);
		return model.returnConditionalProbabilityUsingILP(pex);
	}*/
}
