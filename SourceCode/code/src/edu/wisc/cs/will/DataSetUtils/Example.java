/**
 * 
 */
package edu.wisc.cs.will.DataSetUtils;

import edu.wisc.cs.will.FOPC.BindingList;
import java.io.FileNotFoundException;
import edu.wisc.cs.will.Utils.condor.CondorFileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.FOPC.Function;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Variable;
import edu.wisc.cs.will.Utils.Utils;
import java.io.Serializable;
import java.util.Collection;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * @author shavlik
 *
 */
public class Example extends Literal implements Serializable {
	/**
	 * TODO - should also handle NAMED arguments.
	 */
	private static final long serialVersionUID = 1L;
	/**
	 * 
	 */
	public static final int inTrainPrimeSet = 0;
	public static final int inTuneSet       = 1; // trainPrimeSet + tuneSet = trainSet
	public static final int inTestSet       = 2; // trainSet + testSet = allExamples
	// This weight must be used only for scoring nodes by RDN/MLN-Boost. This weight is used to handle the positive/negative example skew as well as sub-sampling negatives.
	//private double scoringWeightOnExample   = 1.0;  
	
	private double weightOnExample = 1.0; // Note there is also wgtSentence!  This weight is for use in algorithms like Boosting, where wgtSentence is for use in, say, Markov Logic Networks.
	public  String provenance      = ""; // Indicates the 'reason' for this example.
	private Term   annotationTerm  = null;  // This term (presumably a StringConstant) can be used (if set) instead of the example itself when reporting examples.
 //	public int    marker     = inTrainPrimeSet;	
	public String extraLabel = null; // Examples can be labeled wrt some other information and when this information is present, it is used to report how the examples at some node are distributed wrt these labels. 

	public Example(HandleFOPCstrings stringHandler, PredicateName predicateName, List<Term> arguments, String provenance, String extraLabel, Term annotationTerm) {
		this.stringHandler  = stringHandler;
		this.predicateName  = predicateName; // Handle signs by placing examples in POS or NEG lists.
		this.provenance     = provenance;
		this.extraLabel     = extraLabel;
		setArguments(arguments);
	//	Utils.println("Created a new example (" + provenance + ", label = " + extraLabel + "): " + predicateName + arguments);
	}
	public Example(HandleFOPCstrings stringHandler, Literal literal, String provenance) {
		this(stringHandler, literal, provenance, null);
	}
	public Example(HandleFOPCstrings stringHandler, Literal literal, String provenance, String extraLabel) {
		this(stringHandler, literal, provenance, extraLabel, null);
	}
	public Example(HandleFOPCstrings stringHandler, Literal literal, String provenance, String extraLabel, Term annotationTerm) {
		this(stringHandler, literal.predicateName, literal.getArguments(), provenance, extraLabel, annotationTerm);
	}	
	public Example(Literal literal) {
		this(literal.getStringHandler(), literal.predicateName, literal.getArguments(), null, null, null);
	}
	public Example(Function f) {
		this(f.getStringHandler(), f.getStringHandler().getPredicateName(f.functionName.name), f.getArguments(), null, null, null);
	}
	
	/* (non-Javadoc)
	 * @see edu.wisc.cs.will.FOPC.AllOfFOPC#applyTheta(java.util.Map)
	 */
	@Override
	public Example applyTheta(Map<Variable,Term> theta) {
		List<Term> arguments = getArguments();
		List<Term> newArgs = (arguments == null ? null : new ArrayList<Term>(arguments.size()));
		if (arguments != null) for (Term t : arguments) { newArgs.add(t.applyTheta(theta)); }
		return new Example(stringHandler, predicateName, newArgs, provenance, extraLabel, annotationTerm); // Be sure to USE ALL LOCAL arguments.
	}

    @Override
    public Example applyTheta(BindingList bindingList) {
        if ( bindingList != null ) {
            return applyTheta(bindingList.theta);
        }
		return this;
    }
    @Override
    public Example copy(boolean recursiveCopy) {
    	Example copy = new Example(super.copy(recursiveCopy)); // A bit of waste to make two instances, but better to save duplicating code.
    	copy.weightOnExample = weightOnExample;
    	copy.provenance      = provenance;
    	copy.annotationTerm  = annotationTerm;
     //	copy.marker          = marker;	
    	copy.extraLabel      = extraLabel;
    	return copy;
    }
    
    public static String makeLabel(Collection<Example> examples) {
    	if (Utils.getSizeSafely(examples) < 1) { return null; }
    	String result = null;
    	Map<String,Integer> countPerLabel = null;
    	
    	for (Example ex : examples) {
    		String label = ex.extraLabel;  // Utils.println("   makeLabel = " + label + " for " + ex);
    		if (label != null) {
    			if (countPerLabel == null) { countPerLabel = new HashMap<String,Integer>(4); }
    			Integer lookup = countPerLabel.get(label);
    			if (lookup == null) { lookup = 1; } else { lookup++; }
    			countPerLabel.put(label, lookup);
    		}
    	}
    	if (countPerLabel != null) {
    		result = "/*";
    		for (String key : countPerLabel.keySet()) {
    			result += " " + key + Utils.comma(countPerLabel.get(key));  // Assume the code that created the key included a '=', ':', ' ', etc to separate the key from the count.
    		}
    		result += " */";
    	}
    //	Utils.waitHere("   results: " + result);
    	return result;
    }

	public static void labelTheseExamples(String label, Collection<? extends Example> examples) {
		if (Utils.getSizeSafely(examples) < 1) { return; }
		for (Example ex : examples) {
			if (ex.extraLabel == null) { 
				ex.extraLabel = label; 
			//	Utils.println("label = " + label + " for " + ex);
			} else if ("".equals(label))       { Utils.waitHere("Do you want to label with the empty string?");  //  JWS added for debugging (June 16, 2010).
			} else if (ex.extraLabel != label) {
				// Synthetic negs will have a label "createdNeg" which will be overwritten by "neg". TODO have a cleaner way of doing this. 
				if ("createdNeg".equals(ex.extraLabel)) {
					ex.extraLabel = label;
				} else {
					Utils.waitHere("This example already has label = '" + ex.extraLabel + "'.\nDo you really want to rename it to '" + label + "'?\nExample: " + ex);
				}
			}
		}		
	}
	
	// Copied this from Utils.java and added the ability to print the 'provenance' of examples.
	public static void writeObjectsToFile(String fileName, List<? extends Example> examples, String finalEOLchars, String headerStringToPrint) {  // If object is a number, need an extra space so the period doesn't look like a decimal point.
		
        CondorFileOutputStream outStream = null;

        try {
			outStream = new CondorFileOutputStream(Utils.ensureDirExists(fileName));
			PrintStream         stream = new PrintStream(outStream);
			if (headerStringToPrint != null) { stream.println(headerStringToPrint); }
			for (Example ex : examples) { 
				stream.println(ex.toString() + finalEOLchars + " % Provenance: " + ex.provenance);
			}
		}
		catch (FileNotFoundException e) {
			Utils.reportStackTrace(e);
			Utils.error("Unable to successfully open this file for writing: " + fileName + ".  Error message: " + e.getMessage());
		}
        finally {
            if (outStream != null) {
                try {
                    outStream.close();
                } catch (IOException ex) {
                }
            }
        }
	}
	public double getWeightOnExample() {
		return weightOnExample;
	}
	public void setWeightOnExample(double weightOnExample) {
		if (weightOnExample < 0.0001) {
			Utils.waitHere("Setting weight to zero!!: " + weightOnExample + " for " + this.toString());
		}
		this.weightOnExample = weightOnExample;
	}

    /** Returns the sum of the weights of all examples in <code>examples</code>.
     *
     * @param examples
     * @return
     */
    public static double getWeightOfExamples(Collection<? extends Example> examples) {
        double weight = 0;

        if (examples != null) {
            for (Example example : examples) {
                weight += example.getWeightOnExample();
            }
        }

        return weight;
    }
    
    public void setAnnotationTerm(Term annotationTerm) {
		this.annotationTerm = annotationTerm;
	}
	public Term getAnnotationTerm() {
		return annotationTerm;
	}
	/*
	public double getScoringWeightOnExample() {
		return scoringWeightOnExample;
	}
	public void setScoringWeightOnExample(double scoringWeightOnExample) {
		this.scoringWeightOnExample = scoringWeightOnExample;
	}*/
}
