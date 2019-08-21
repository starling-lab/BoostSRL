/**
 * 
 */
package edu.wisc.cs.will.Boosting.OneClass;

import java.util.ArrayList;
import java.util.List;

import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author tkhot
 *
 */
public class BuildPairWiseScore {

	private PropositionalizationModel model;
	
	public BuildPairWiseScore(PropositionalizationModel currModel) {
		model = currModel;
	}

	public PairWiseExampleScore buildScore(List<RegressionRDNExample> all_exs) {
		// Map<String, FeatureVector> currFeatures = new HashMap<String, FeatureVector>();
		List<FeatureVector> features = new ArrayList<FeatureVector>();
		// Get features for each example
//		for (RegressionRDNExample rex : all_exs) {
//			String key = ((Example)rex).toString();
//			if (!currFeatures.containsKey(key)) {
//				FeatureVector vec = model.getFeatureVector(rex);
//				currFeatures.put(key, vec);
//			}
//		}
		PairWiseExampleScore score = new PairWiseExampleScore();
		score.currCount = model.treeList.size();
		int numLabelled = 0;
		for (int i = 0; i < all_exs.size(); i++) {
			RegressionRDNExample rex = all_exs.get(i);
			FeatureVector vec = model.getFeatureVector(rex);
			features.add(vec);
			int cat = rex.getOriginalValue();
			// If not multiclass, ignore negative examples
			if (!rex.isHasRegressionVector()) {
				if (cat == 0) { cat = -1; } else { numLabelled++;} 
			} else {
				Utils.error("Can't handle multiclass examples in OCC");
			}
			score.addExample(rex, cat);
		}
		
		score.numLabelled = numLabelled;
		if (numLabelled == 0) {
			Utils.waitHere("No labelled examples");
		} else {
			Utils.println("Examples: " + numLabelled);
		}
		
		for (int i = 0; i < all_exs.size(); i++) {
			FeatureVector v1 = features.get(i);
			for (int j = i+1; j < all_exs.size(); j++) {
				FeatureVector v2 = features.get(j);
				double dist = getDistanceBetween(v1, v2);
				score.addDistance(all_exs.get(i), all_exs.get(j), dist);
			}
		}
		
		
		return score;
		
	}
	
	public double getDistanceBetween(FeatureVector v1, FeatureVector v2) {
		return v1.getDistance(v2);
	}
	

}
