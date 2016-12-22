/**
 * 
 */
package edu.wisc.cs.will.DataSetUtils;

import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.FOPC.Term;
import java.io.Serializable;

/**
 * @author shavlik
 *
 */
public class ArgSpec implements Serializable {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	public Term     arg;
	public TypeSpec typeSpec;
	/**
	 * 
	 */
	public ArgSpec(Term arg, TypeSpec typeSpec) {
		this.arg      = arg;
		this.typeSpec = typeSpec;
	}
	
	public String toString() {
		return arg + "[" + typeSpec + "]";
	}

}
