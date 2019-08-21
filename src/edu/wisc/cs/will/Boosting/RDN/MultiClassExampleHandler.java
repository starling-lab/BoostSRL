/**
 * 
 */
package edu.wisc.cs.will.Boosting.RDN;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.PredicateNameAndArity;
import edu.wisc.cs.will.FOPC.PredicateSpec;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.VectorStatistics;

/**
 * @author tkhot
 *
 */
public class MultiClassExampleHandler {

	
	private WILLSetup setup;
	/**
	 * Use a list for class arg index since more than one argument (combined) may be a class arg.
	 * E.g. genderAndGenre(person, gender!, genre!).
	 */
	Map<String, List<Integer>> predicateToClassArgIndex ;
	

	Map<String, ConstantLookupList> constantsForPredicate;
	
	public MultiClassExampleHandler() {
		this.setup = null;
		constantsForPredicate = null;
	}


	/**
	 * Initialize the class argument location for every predicate
	 */
	public void initArgumentLocation(WILLSetup setup) {
		this.setup = setup;
		predicateToClassArgIndex = new HashMap<String, List<Integer>>();
		// For each predicate
		for (PredicateNameAndArity pnaa : setup.getHandler().getKnownModes()) {
			String predName = pnaa.getPredicateName().name;
			if (predicateToClassArgIndex.containsKey(predName)) {
				Utils.error("Already seen predicate name: " + predName);
			}
			List<Integer> classArg = new ArrayList<Integer>();
			// For each pred spec
			for (PredicateSpec pspec : pnaa.getPredicateSpecs()) {
				// For each argument
				for (int i = 0; i < pspec.getTypeSpecList().size(); i++) {
					TypeSpec tspec = pspec.getTypeSpec(i);
					if (tspec.truthCounts == 1) {
						classArg.add(i);
					}
				}
			}
			
			if (classArg.size() > 0 ) {
				Utils.println("Setting class args for " + predName + " to: " + Utils.toString(classArg, ","));
				predicateToClassArgIndex.put(predName, classArg);
			}
			
		}
	}
	
	public RegressionRDNExample morphExample(Example eg) {
		RegressionRDNExample regEx = new RegressionRDNExample(eg.getStringHandler(), eg.extractLiteral().copy(true),
				  0, eg.provenance, eg.extraLabel, true);
		String pname = eg.predicateName.name;
		List<Term> constList = getConstantList(eg);
		if (!constantsForPredicate.containsKey(pname)) {
			Utils.error("Constant map not created for :" + pname);
			return null;
		}
		
		int vecsize = constantsForPredicate.get(pname).size();
		int index = constantsForPredicate.get(pname).getIndex(new ArgumentList<Term>(constList));
		if (index == -1) {
			Utils.error("Unexpected constant in " + eg);
		}
		regEx.setOriginalValue(index);
		regEx.setSampledValue(Utils.random0toNminus1(vecsize));
		double[] outputVector  = VectorStatistics.createIndicator(vecsize, index);
		regEx.setOutputVector(outputVector);
		// Not necessary, since the previous method internally sets hasregressionVector. 
		regEx.setHasRegressionVector(true);
		
		removeConstants(regEx);
		return regEx;
	}
	
	public void removeConstants(Literal lit) {
		List<Term> constList = getConstantList(lit);
		// Remove the arguments from the example
		for (Term arg : constList) {
			lit.removeArgument(arg);
		}
		lit.predicateName = lit.getStringHandler().getPredicateName(WILLSetup.multiclassPredPrefix + lit.predicateName.name);
	}
	
	public Example createExampleFromClass(RegressionRDNExample rex, int constantIndex) {
		if (!rex.predicateName.name.startsWith(WILLSetup.multiclassPredPrefix)) {
			Utils.error("expected a multi class example here." + rex.toPrettyString());
		}
		HandleFOPCstrings stringHandler = rex.getStringHandler();
		String pname = rex.predicateName.name.replaceFirst(WILLSetup.multiclassPredPrefix, "");
		PredicateName predNameObj = stringHandler.getPredicateName(pname); 
		List<Term> constList = constantsForPredicate.get(pname).constants.get(constantIndex);
		
		List<Term> newArgs = addToArgumentList(rex.getArguments(), constList, predicateToClassArgIndex.get(pname));
		
		Example eg = new Example(rex.getStringHandler(), predNameObj, newArgs, rex.provenance, rex.extraLabel, rex.getAnnotationTerm());
		
		return eg;
	}
	
	
	private List<Term> addToArgumentList(List<Term> arguments,
										List<Term> constList, List<Integer> indexList) {
		int newSize = arguments.size() + indexList.size();
		List<Term> newArgs = new ArrayList<Term>(newSize);
		int indexCtr = 0;
		int argCtr   = 0;
		for (int i = 0; i < newSize; i++) {
			
			if (i == indexList.get(indexCtr)) {
				if (indexCtr >= constList.size()) {
					Utils.error("More constants needed to fill index: " + Utils.toString(indexList, ",") + " than present in: " + Utils.toString(constList, ","));
				}
				newArgs.add(constList.get(indexCtr++));
			} else {
				if (argCtr >= arguments.size()) {
					Utils.error("More arguments needed to fill args: " + Utils.toString(arguments, ",") + " than present in: " + Utils.toString(indexList, ","));
				}
				newArgs.add(arguments.get(argCtr++));
			}
		}
		
		return newArgs;
		
	}


	public void addConstantsFromLiterals(List<? extends Literal> facts) {
		if (constantsForPredicate == null) {
			constantsForPredicate = new HashMap<String, MultiClassExampleHandler.ConstantLookupList>();
		}
		
		for (Literal lit : facts) {
			String pName = lit.predicateName.name;
			// If it has class args
			if (predicateToClassArgIndex.containsKey(pName)) {
				List<Term> constList = getConstantList(lit);
				// Add constants
				if (!constantsForPredicate.containsKey(pName)) {
					constantsForPredicate.put(pName, new ConstantLookupList());
				}
				constantsForPredicate.get(pName).addConstant(new ArgumentList<Term>(constList));
			}
		}
	}
	
	public void updateConstantList(String predicate, ConstantLookupList constList) {
		if (constantsForPredicate == null) {
			Utils.error("constantsForPredicate not initialized!");
		} else {
			if (!constantsForPredicate.containsKey(predicate)) {
				Utils.error("Missing predicate: " + predicate);
			} else {
				ConstantLookupList oldList = constantsForPredicate.get(predicate);
				for (ArgumentList<Term> termLists : oldList.constants) {
					if (!constList.constantIndex.containsKey(termLists)) {
						Utils.error("New constant seen in the testset: " + Utils.toString(termLists, ","));
					}
				}
				constantsForPredicate.put(predicate, constList);
			}
		}
	}
	
	private List<Term> getConstantList(Literal lit) {
		List<Term> constList = new ArrayList<Term>();
		String pName = lit.predicateName.name;
		for (Integer index : predicateToClassArgIndex.get(pName)) {
			constList.add(lit.getArgument(index));
		}
		return constList;
	}


	public boolean isMultiClassPredicate(String predicate) {
		if (predicateToClassArgIndex != null && predicateToClassArgIndex.containsKey(predicate)) {
			return true;
		}
		return false;
	}

	public int numConstantsForPredicate(String predicate) {
		ConstantLookupList cll =  constantsForPredicate.get(predicate);
		if (cll == null) {
			return 2;
		}
		return cll.size();
	}
	
	
	public static class ConstantLookupList {
		
		
		private final static String startList = "{";
		private final static String endList = "}";
		private final static String startTermList = "(";
		private final static String endTermList = ")";
		private final static String startTerm = "\"";
		private final static String endTerm = "\"";
		//private final static char delim = ',';
		
		public ConstantLookupList() {
			this.constants = new ArrayList<ArgumentList<Term>>();
			this.constantIndex = new HashMap<ArgumentList<Term>, Integer>();
		}

		public int getIndex(ArgumentList<Term> constList) {
			if (!constantIndex.containsKey(constList)) {
				Utils.println("Unexpected constList: " + Utils.toString(constList, ",") + " in " + this.toString());
				return -1;
			} 
			return constantIndex.get(constList);
		}

		public int size() {
			return constants.size();
		}
		private List<ArgumentList<Term>> constants ;
		
		private Map<ArgumentList<Term>, Integer> constantIndex;
		
		public void addConstant(ArgumentList<Term> addThis) {
			if (!constantIndex.containsKey(addThis)) {
				int index = constants.size();
				constants.add(addThis);
				constantIndex.put(addThis, index);
				Utils.println("Adding constant: " + Utils.toString(addThis, ","));
			}
		}

		public void load(WILLSetup setup, String line) {
			if (!line.startsWith(startList)) {
				Utils.error("Starts with wrong character: " + line);
				return;
			}
			
			int index = startList.length();
			line = line.substring(index);
			while (!line.startsWith(endList)) {
				ArgumentList<Term> constList = new ArgumentList<Term>();
				if (!line.startsWith(startTermList)) {
					Utils.error("Starts with wrong character: " + line);
					return;
				}
				line = line.substring(startTermList.length());
				while (!line.startsWith(endTermList)) {
					if (!line.startsWith(startTerm)) {
						Utils.error("Starts with wrong character: " + line);
						return;
					}
					line = line.substring(startTerm.length());
					int end = line.indexOf(endTerm);
					String term = line.substring(0, end);
					Term constTerm  = setup.getHandler().getStringConstant(term);
					constList.add(constTerm);
					line = line.substring(end+1);
					//if (line.charAt(0) == delim) { line = line.substring(1); }
				}
				addConstant(constList);
				line = line.substring(endTermList.length());
				//if (line.charAt(0) == delim) { line = line.substring(1); }
			}
			line = line.substring(endList.length());
			if (!line.isEmpty()) {
				Utils.error("Still leftover string after parsing constants: " + line);
			}
		}
		
		public String toString() {
			StringBuffer sb = new StringBuffer();
			sb.append(startList);
			for (ArgumentList<Term> termList : constants) {
				sb.append(startTermList);
				for (Term term : termList) {
					sb.append(startTerm);
					sb.append(term.toString());
					sb.append(endTerm);
				}
				sb.append(endTermList);
			}
			sb.append(endList);
			return sb.toString();
		}
		
		
	}

	public static class ArgumentList<T> extends ArrayList<T> {

		/**
		 * 
		 */
		private static final long serialVersionUID = 5435503324007711494L;

		public ArgumentList() {
			super();
			// TODO Auto-generated constructor stub
		}

		public ArgumentList(Collection<? extends T> c) {
			super(c);
			// TODO Auto-generated constructor stub
		}

		public ArgumentList(int initialCapacity) {
			super(initialCapacity);
			// TODO Auto-generated constructor stub
		}
		
		@Override
		public int hashCode() {
			int code = 0;
			int prime = 31;
			for (T item : this) {
				code += prime * item.hashCode();
			}
			return code;
		} 
		
		@Override 
		public boolean equals(Object other) {
			if (!(other instanceof ArgumentList<?>)) {
				return false;
			}
			ArgumentList<T> otherList = (ArgumentList<T>)other;
			if (otherList.size() != this.size()) {
				return false;
			}
			for (int i = 0; i < this.size(); i++) {
				T item1 = this.get(i);
				T item2 = otherList.get(i);
				if (!item1.equals(item2)) {
					return false;
				}
			}
			return true;
		}
		
	}
	
	
	
	
}
