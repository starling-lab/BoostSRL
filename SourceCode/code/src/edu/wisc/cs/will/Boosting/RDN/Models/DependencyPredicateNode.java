/**
 * 
 */
package edu.wisc.cs.will.Boosting.RDN.Models;

import java.util.ArrayList;

import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateSpec;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author Tushar Khot
 *
 */
public class DependencyPredicateNode extends DependencyNode {
	private PredicateName predicate;
	// Order in Gibbs sampling
	private int order = -1;
	
	public enum PredicateType {
		HIDDEN,
		EVIDENCE,
		QUERY,
		COMPUTED,
		RECURSIVE,
	}
	// Default value is EVIDENCE
	private PredicateType type;
	
	public DependencyPredicateNode(PredicateName name) {
		super();
		type=PredicateType.EVIDENCE;
		setPredicate(name);
	}	
	
	public String labelForDOT() {
		String arglist = "";
		if (predicate != null && predicate.getTypeList() != null) {
			for (PredicateSpec spec : predicate.getTypeList()) {
				if (spec.getTypeSpecList() != null) {
					for (TypeSpec tspec : spec.getTypeSpecList()) {
						arglist += "," + tspec.getType();
					}
					arglist = arglist.replaceFirst(",", "");
					break;
				}
			}
		}
		return predicate.toString()  + "(" + arglist + ")" + (order == -1 ? "" : "[" + order + "]");
	}
	
	public String colorForDOT() { 
		switch(type) {
			case QUERY: return "gray52";
			case HIDDEN: return "gray62";
			case RECURSIVE: return "gray72";
			case COMPUTED: return "gray82";
			case EVIDENCE: return "gray92";
		}
		return "white";
	}
	public String textForDOT() {
		return "style=\"filled\" label=\"" + labelForDOT() +"\" color=\"" + colorForDOT() + "\"";
	}
	
	/**
	 * @return the predicate
	 */
	public PredicateName getPredicate() {
		return predicate;
	}
	/**
	 * @param predicate the predicate to set
	 */
	public void setPredicate(PredicateName predicate) {
		if (predicate.name.startsWith(WILLSetup.recursivePredPrefix)) {
			type = PredicateType.RECURSIVE;
		}
		this.predicate = predicate;
	}
	
	/**
	 * @return the type
	 */
	public PredicateType getType() {
		return type;
	}
	/**
	 * @param type the type to set
	 */
	public void setType(PredicateType type) {
		if (this.type != PredicateType.EVIDENCE) {
			Utils.waitHere("Changing type for " + this.labelForDOT() + " from " + this.type +" to " + type);
		}
		this.type = type;
	}

	/**
	 * @return the order
	 */
	public int getOrder() {
		return order;
	}

	/**
	 * @param order the order to set
	 */
	public void setOrder(int order) {
		this.order = order;
	}

	@Override
	public boolean ignoreNodeForDOT() {
		String predString = getPredicate().toString();
		if (predString.equals("all") ||
			predString.equals("is")  ||
			predString.equals("==")  ||
			predString.equals("=")  ||
			predString.equals("addList")  ||
			predString.equals(">")   ||
			predString.equals("!")   ||
			predString.equals("member")) {
			return true;
		}
		
		if (getType() == PredicateType.COMPUTED &&
			getChildren().isEmpty()) {
			return true;
		}
		return false;
	}

}
