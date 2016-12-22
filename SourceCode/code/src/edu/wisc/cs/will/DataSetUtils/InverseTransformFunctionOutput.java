package edu.wisc.cs.will.DataSetUtils;

import edu.wisc.cs.will.Utils.Utils;

public class InverseTransformFunctionOutput {

	public static final int ident   = 0;  public static final String identStr   = "identity"; // This isn't built into the ILP system since it isn't being used.
	public static final int sqrt    =-1;  public static final String sqrtStr    = "sqrt";     // Probably should only use one of these.
	public static final int sqrtSafe=-2;  public static final String sqrtSafeStr= "sqrtSafe"; //  sqrt(X)=0 if x is negative.
	public static final int sqrtAbs = 1;  public static final String sqrtAbsStr = "sqrtAbs";  //  sqrt(abs(X))
	public static final int log2    = 2;  public static final String log2Str    = "log2";
	public static final int log     = 3;  public static final String logStr     = "log";
	public static final int log10   = 4;  public static final String log10Str   = "log10";
	public static final int exp     = 5;  public static final String expStr     = "exp";
	public static final int sin     = 6;  public static final String sinStr     = "sin";
	public static final int cos     = 7;  public static final String cosStr     = "cos";
	public static final int tan     = 8;  public static final String tanStr     = "tan";
	public static final String[] functionNames = {identStr, sqrtAbsStr, log2Str, logStr, log10Str, expStr, sinStr, cosStr, tanStr};
	public static final int lastValue = 8;
	
	// Assume we want to learn y = G(f(x)), where f(x) is well modeled as a linear function of vector x.
	// We can then transform y using inverseG() and use a linear-function learner on the transformed y.
	// Here y_new = inverseG(G(f(x))) = f(x).
	//
	// The static's above show the G's this code can handle.
	// For example, if y = sqrt(f(x)), we create y_new = y^2 = f(x).
	//
	// NOTE: the calling method should catch errors, since sometimes inverses don't exist (eg, for arc cos).
	// Also note that inverses of trig functions use RADIANS (since this code simply calls Java's Math class).
	//
	// This is a STATIC function since it maintains no state.
	public static void inverseTransform(double[] outputValues, double[] newOutputValues, String functionToInvert) {

		if (functionToInvert == null) { Utils.error("A functionToInvert is needed.  Your provided NULL."); }
		int transformer = -1;
		if (     functionToInvert.equalsIgnoreCase(identStr)) {
			transformer = InverseTransformFunctionOutput.ident;
		}
		else if (functionToInvert.equalsIgnoreCase(sqrtStr)) {
			transformer = InverseTransformFunctionOutput.sqrt;
		}
		else if (functionToInvert.equalsIgnoreCase(sqrtSafeStr)) {
			transformer = InverseTransformFunctionOutput.sqrtSafe;
		}
		else if (functionToInvert.equalsIgnoreCase(sqrtAbsStr)) {
			transformer = InverseTransformFunctionOutput.sqrtAbs;
		}
		else if (functionToInvert.equalsIgnoreCase(logStr)) {
			transformer = InverseTransformFunctionOutput.log;
		}
		else if (functionToInvert.equalsIgnoreCase(log2Str)) {
			transformer = InverseTransformFunctionOutput.log2;
		}
		else if (functionToInvert.equalsIgnoreCase(log10Str)) {
			transformer = InverseTransformFunctionOutput.log10;
		}
		else if (functionToInvert.equalsIgnoreCase(expStr)) {
			transformer = InverseTransformFunctionOutput.exp;
		}
		else if (functionToInvert.equalsIgnoreCase(sinStr)) {
			transformer = InverseTransformFunctionOutput.sin;
		}
		else if (functionToInvert.equalsIgnoreCase(cosStr)) {
			transformer = InverseTransformFunctionOutput.cos;
		}
		else if (functionToInvert.equalsIgnoreCase(tanStr)) {
			transformer = InverseTransformFunctionOutput.tan;
		}
		else { Utils.error("Unknown function to invert: " + functionToInvert); }
		
		inverseTransform(outputValues, newOutputValues, transformer);
	}
	public static void inverseTransform(double[] outputValues, double[] newOutputValues, int transformer) {
		
		for (int i = 0; i < outputValues.length; i++) {
			
			double oldValue = outputValues[i];
			double newValue = Double.NaN;
			switch (transformer) {
				case InverseTransformFunctionOutput.ident:   newValue = oldValue;               break;
				case InverseTransformFunctionOutput.sqrt:    newValue = oldValue * oldValue;    break;
				case InverseTransformFunctionOutput.sqrtAbs: newValue = oldValue * oldValue;    break;
				case InverseTransformFunctionOutput.sqrtSafe:newValue = oldValue * oldValue;    break;
				case InverseTransformFunctionOutput.log2:    newValue = Math.pow( 2, oldValue); break;
				case InverseTransformFunctionOutput.log:     newValue = Math.exp(oldValue);     break;
				case InverseTransformFunctionOutput.log10:   newValue = Math.pow(10, oldValue); break;
				case InverseTransformFunctionOutput.exp:     newValue = Math.log(oldValue);     break;
				case InverseTransformFunctionOutput.sin:     newValue = Math.asin(oldValue);    break; // These will be in RADIANS.
				case InverseTransformFunctionOutput.cos:     newValue = Math.acos(oldValue);    break;
				case InverseTransformFunctionOutput.tan:     newValue = Math.atan(oldValue);    break;
				default: // Should not reach here due to checks above.
					Utils.error("Unknown transformer: " + transformer);
			}
			newOutputValues[i] = newValue;
		}
	}
	
	public static double transform(double value, int transformer) {
		switch (transformer) {
		case InverseTransformFunctionOutput.ident:   return value;
		case InverseTransformFunctionOutput.sqrt:    return Math.sqrt(value);
		case InverseTransformFunctionOutput.sqrtSafe:return Math.sqrt(Math.max(0.0, value));
		case InverseTransformFunctionOutput.sqrtAbs: return Math.sqrt(Math.abs(value));
		case InverseTransformFunctionOutput.log2:    return (value > 0 ? Math.log(value) / Math.log(2) : Double.NaN);
		case InverseTransformFunctionOutput.log:     return (value > 0 ? Math.log(value)               : Double.NaN);
		case InverseTransformFunctionOutput.log10:   return (value > 0 ? Math.log10(value)             : Double.NaN);
		case InverseTransformFunctionOutput.exp:     return Math.exp(value);
		case InverseTransformFunctionOutput.sin:     return Math.sin(value);
		case InverseTransformFunctionOutput.cos:     return Math.cos(value);
		case InverseTransformFunctionOutput.tan:     return Math.tan(value);
		default: // Should not reach here due to checks above.
			Utils.error("Unknown transformer: " + transformer);
			return Double.NaN;
	}
	}
	
	public static boolean containsNaNorInfinity(double[] values) {
		for (int i = 0; i < values.length; i++) {
			if (Double.isNaN(values[i]) || Double.isInfinite(values[i])) { return true; }
		}
		return false;
	}
	
	public static String getFunctionName(int i) {
		if (i < 0 || i > functionNames.length) { Utils.error("Unknown function-name index: " + i); }
		return functionNames[i];
	}
}
