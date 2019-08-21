/**
 * 
 */
package edu.wisc.cs.will.Boosting.OneClass;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import edu.wisc.cs.will.Utils.Utils;

/**
 * @author tkhot
 *
 */
public class FeatureVector {
	List<Double> features;
	
	public List<String> pathFeatures;
	
	public boolean usepath = true;
	public FeatureVector() {
		features = new ArrayList<Double>();
		pathFeatures = new ArrayList<String>();
	}
	
	public double getDistance(FeatureVector other) {
		
		
		if (usepath) {
			double dist = 0;
			double count = 0;
			for (int i = 0; i < pathFeatures.size(); i++) {
				String a = pathFeatures.get(i);
				String b = other.pathFeatures.get(i);
				int diffChar = getDiffChar(a, b);
				if (diffChar != -1) {
					dist += Math.exp(-diffChar+1);
				} else {
					dist += 0;
				}
				count++;
			}
			if (count == 0) count=1;
			return dist/count;
		}
		Utils.waitHere("Not using path features!!");
		if (features.size() != other.features.size()) {
			Utils.error("Comparing unequal feature vectors");
		}
		for (int i = 0; i < features.size(); i++) {
			if (Utils.diffDoubles(other.getFeature(i), this.getFeature(i))) {
				return 1;
			}
		}
		
		return 0;
	}
	
	private int getDiffChar(String a, String b) {
		for (int i = 0; i < a.length(); i++) {
			if (a.charAt(i) != b.charAt(i)) {
				return i;
			}
		}
		return -1;
	}

	public double getFeature(int index) {
		return features.get(index);
	}

	public void append(double fval) {
		
		if (Utils.diffDoubles(fval, 0.0) && Utils.diffDoubles(fval, 1.0)) {
			Utils.error("Can only handle boolean features");
		}
		features.add(fval);
	}

	public void append(FeatureVector featureVector) {
		if (usepath) { pathFeatures.addAll(featureVector.pathFeatures); }
		features.addAll(featureVector.features);
	}
	
	public void parseString(String fvec) {
		if (usepath) {
			fvec = fvec.replace("[", "").replace("]", "");
			String[] parts = fvec.split("\\|");
			pathFeatures = new ArrayList<String>(Arrays.asList(parts));
		} else {
			Utils.waitHere("Cant parse non path features");
		}
	}
	public String toString() {
		String result = "";

		if (usepath) {
			for (int i = 0; i < pathFeatures.size(); i++) {
				if (i == pathFeatures.size() - 1) {
					result += pathFeatures.get(i);
				} else {
					result += pathFeatures.get(i) + "|";
				}
			}	
		} else {
			for (int i = 0; i < features.size(); i++) {
				result += Utils.diffDoubles(features.get(i), 1.00) ? "0" : "1" ;
			}
		}
		
		return "[" + result +"]";
	}
	public static void main(String[] args) {
		// Test
		
		
		FeatureVector fvec = new FeatureVector();
		fvec.usepath = false;
		fvec.append(0);
		fvec.append(0);
		fvec.append(1);
		fvec.append(0);
		
		System.out.println(fvec);
		
		FeatureVector fvec2 = new FeatureVector();
		fvec2.usepath = false;
		fvec2.append(0);
		fvec2.append(1);
		fvec2.append(1);
		fvec2.append(0);
		System.out.println(fvec2);
		
		//fvec.append(fvec2);
		//System.out.println(fvec);
		
		FeatureVector fvec3 = new FeatureVector();
		FeatureVector pvec1 = new FeatureVector();
		FeatureVector pvec2 = new FeatureVector();
		
		pvec1.pathFeatures.add("0110");
		pvec2.pathFeatures.add("1001");
		fvec3.append(pvec1);
		fvec3.append(pvec2);
		
		String saveStr = fvec3.toString();
		System.out.println(saveStr);
		FeatureVector vec = new FeatureVector();
		vec.parseString(saveStr);
		System.out.println(vec.toString());		
		
		
		
	}

	public String toMatlabString() {
		String result = "";

		for (int i = 0; i < features.size(); i++) {
			if (i != 0) {
				result += " ";
			}
			result += Utils.diffDoubles(features.get(i), 1.00) ? "0" : "1" ;
			
		}
		
		return result;
	}
}
