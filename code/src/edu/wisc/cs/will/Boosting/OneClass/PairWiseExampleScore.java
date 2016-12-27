/**
 * 
 */
package edu.wisc.cs.will.Boosting.OneClass;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.Utils.Utils;

/**
 * @author tkhot
 *
 */
public class PairWiseExampleScore {

	
	Map<String, Double> currentPairWiseDistance;
	
	Map<String, Integer> exampleCategory;
	
	int currCount= 0;
	
	// double currBandwidth = 1;
	
	int numLabelled = 0;
	
	private KernelEstimator kernelEst;
	
	public PairWiseExampleScore() {
		currentPairWiseDistance = new HashMap<String, Double>();
		exampleCategory         = new HashMap<String, Integer>();
		kernelEst 				= new KernelEstimator();
	}
	
	public static String getExamplePairKey(Example eg1, Example eg2) {
		String eg1String = eg1.toPrettyString();
		String eg2String = eg2.toPrettyString();
		
		if (eg1String.equals(eg2String)) {
			Utils.error("Distance between the same examples: " + eg1String);
		}
		// To make sure that order of examples doesn't matter
		if (eg1String.compareTo(eg2String) > 0) {
			return eg1String + "::::" + eg2String; 
		}
		return eg2String + "::::" + eg1String;
	}
	
	
	
	public double calculateKernelScore(List<Example> trueBranch,
								 List<Example> falseBranch, int depth) {
	
		double score = 0;
		
		double changeInKDE = 0;
		int kdeCounter = 0;
		double changeInEnt = 0;
		double changeInDist = 0;
		int distCounter = 0;
		int numLabelledHere=0;
		for (int i = 0; i < trueBranch.size(); i++) {
			Example x_i = trueBranch.get(i);
			int cat_i = getCategory(x_i);
			
			for (int j = 0; j < falseBranch.size(); j++) {
				Example x_j = falseBranch.get(j);
				int cat_j = getCategory(x_j);
				
				double dist = getDistance(x_i, x_j);
				double updateDist = kernelEst.getDistance(depth); // Math.exp(-depth);
				double new_dist = (dist*currCount + updateDist)/(currCount + 1);
				double old_kVal = kernelEst.getKernelValue(dist); // getKernelVal(dist);
				double new_kVal = kernelEst.getKernelValue(new_dist);  //getKernelVal(new_dist);
			
				// If different class
				if (cat_i != cat_j) {
					// The change in distance effects the entropy
					// TODO(TVK)
					
					double changeForXi = (1/((double)(numLabelled) * kernelEst.getBandwidth())) * (new_kVal - old_kVal);
					changeInKDE -= changeForXi * (1 - dist);
					
					kdeCounter+=1;
				}
				
				if ((cat_i == cat_j) && cat_i != -1) {
					double changeForXi = (1/((double)(numLabelled-1) * kernelEst.getBandwidth())) * (new_kVal - old_kVal);
					double changeForXj = changeForXi  ;
					changeInKDE += changeForXi + changeForXj;
					kdeCounter += 2;
				}
				
				changeInDist += dist - new_dist;
				distCounter += 1;
			}
		}
		
		
		for (int i = 0; i < trueBranch.size(); i++) {
			Example x_i = trueBranch.get(i);
			int cat_i = getCategory(x_i);
			if (cat_i != -1) { numLabelledHere ++;}
			for (int j = i+1; j < trueBranch.size(); j++) {
				Example x_j = trueBranch.get(j);
				int cat_j = getCategory(x_j);
				
				double dist = getDistance(x_i, x_j);
				double updateDist = 0; // Same branch, no change in distance
				double new_dist = (dist*currCount + updateDist)/(currCount + 1);
				double old_kVal = kernelEst.getKernelValue(dist); // getKernelVal(dist);
				double new_kVal = kernelEst.getKernelValue(new_dist);  //getKernelVal(new_dist);
				
				// If different class
				if (cat_i != cat_j) {
					// The change in distance effects the entropy
					// TODO(TVK)
					
					double changeForXi = (1/((double)(numLabelled) * kernelEst.getBandwidth())) * (new_kVal - old_kVal);
					changeInKDE -= changeForXi * (1 - dist);
					
					kdeCounter+=1;
				}
				
				if ((cat_i == cat_j) && cat_i != -1) {
					double changeForXi = (1/((double)(numLabelled-1) * kernelEst.getBandwidth()))* (new_kVal - old_kVal);
					double changeForXj = changeForXi;
					if (dist != 0) {
						// Utils.println("change:" + changeForXi + "dist:" + dist +" newDist:"+new_dist);
						// Utils.println(old_kVal +":" + new_kVal);
					}
					changeInKDE += changeForXi + changeForXj;
					kdeCounter += 2;
				}
				
				changeInDist += dist - new_dist;
				distCounter += 1;
			}
		}
		
		for (int i = 0; i < falseBranch.size(); i++) {
			Example x_i = falseBranch.get(i);
			int cat_i = getCategory(x_i);
			if (cat_i != -1) { numLabelledHere ++;}
			for (int j = i+1; j < falseBranch.size(); j++) {
				Example x_j = falseBranch.get(j);
				int cat_j = getCategory(x_j);
				
				double dist = getDistance(x_i, x_j);
				double updateDist = 0; // Same branch, no change in distance
				double new_dist = (dist*currCount + updateDist)/(currCount + 1);
				double old_kVal = kernelEst.getKernelValue(dist); // getKernelVal(dist);
				double new_kVal = kernelEst.getKernelValue(new_dist);  //getKernelVal(new_dist);
				
				// If different class
				if (cat_i != cat_j) {
					// The change in distance effects the entropy
					// TODO(TVK)
					
					double changeForXi = (1/((double)(numLabelled) * kernelEst.getBandwidth())) * (new_kVal - old_kVal);
					changeInKDE -= changeForXi * (1 - dist);
					
					kdeCounter+=1;
				}
				
				if ((cat_i == cat_j) && cat_i != -1) {
					double changeForXi =(1/((double)(numLabelled-1) * kernelEst.getBandwidth())) * (new_kVal - old_kVal);
					double changeForXj = changeForXi;
					changeInKDE += changeForXi + changeForXj;
					kdeCounter += 2;
				}
				
				changeInDist += dist - new_dist;
				distCounter += 1;
			}
		}
		
		score = (numLabelledHere != 0 ? (changeInKDE/(double)numLabelledHere) : 0) + 1*(distCounter != 0 ? (changeInDist/ (double)distCounter): 0);
		Utils.println("Score=" + score);
		Utils.println("changeInKDE=" + changeInKDE + " counter = " + numLabelledHere);
		Utils.println("changeInDist= " + changeInDist + " counter = " + distCounter);
		return score;
	}
	/*private double getKernelVal(double dist) {
		return (3.0/4.0) * (1.0 - Math.pow((dist/currBandwidth), 2.0));
	}*/

	
	/**
	 * Higher score is worse.
	 * @param trueBranch
	 * @param falseBranch
	 * @return
	 */
	public double calculateScore(List<Example> trueBranch,
								 List<Example> falseBranch, int depth) {
		System.out.println("TEMP: Calculating distance between " + trueBranch.size() + " & " + falseBranch.size());
		double score = 0;
		double UvUDist = 0;
		double LivLjDist = 0;
		double UvLDist = 0;
		double LivLiDist = 0;
		
		int UvUCount = 0;
		int LivLjCount = 0;
		int UvLCount = 0;
		int LivLiCount = 0;
		
		int Ucount1 = 0;
		int Lcount1 = 0;
		int Ucount2 = 0;
		int Lcount2 = 0;
		double updateDist = Math.exp(-depth);
		double distChange = 0;
		for (int i = 0; i < trueBranch.size(); i++) {
			Example trueEg  = trueBranch.get(i);
			int trueCat = getCategory(trueEg);
			if (trueCat == -1) {
				Ucount1++;
			} else {
				Lcount1++;
			}
			for (int j = 0; j < falseBranch.size(); j++) {
				Example falseEg = falseBranch.get(j);
				int falseCat  = getCategory(falseEg);
				if (i == 0) {
					if (falseCat == -1) {
						Ucount2 ++ ;
					} else {
						Lcount2 ++;
					}
				}
				double dist = getDistance(trueEg, falseEg);
				double new_dist = (dist*currCount + updateDist)/(currCount + 1);
				double zero_dist = (dist*currCount + 0)/(currCount + 1); 
				// Both examples are from the unlabelled class
				if (trueCat == -1 && falseCat == -1) {
					// Do not want to separate examples that already are distant
					UvUDist +=  dist;
					UvUCount++;
					distChange += (zero_dist - new_dist);

				}
				
				// Both examples have different classes
				if (trueCat != falseCat) {
					// Both are labelled examples
					if (trueCat != -1 && falseCat != -1) {
						// Increasing distance between such examples (unless already separated) is preferred
						LivLjDist += dist;
						LivLjCount++;
					} else {
						// One of the examples is unlabelled
						UvLDist += dist;
						UvLCount++;
						distChange += Math.abs(new_dist - 0.5) - Math.abs(zero_dist - 0.5);
					}
				}
				// Both examples have the same label
				if (trueCat == falseCat && trueCat != -1) {
					LivLiDist += dist;
					LivLiCount ++;
					distChange += (new_dist - zero_dist);
				}
			}
		}
		int Ucount=Ucount1 + Ucount2;
		int Lcount=Lcount1 + Lcount2;
		
		if (Ucount == 0) { Ucount = 1;}
		if (Lcount == 0) { Lcount = 1;}
		Utils.println("TEMP: Calculate score from: " + Lcount + ":" + Ucount + ":" + trueBranch.size() + ":" + falseBranch.size());
		Utils.println("UvUcount=" + UvUCount);
		Utils.println("UvUdist=" + UvUDist);
		Utils.println("UvLcount=" + UvLCount);
		Utils.println("UvLdistt=" + UvLDist);
		Utils.println("LivLicount=" + LivLiCount);
		Utils.println("LivLidist=" + LivLiDist);		
		Utils.println("distChange=" + distChange);		
		
		return distChange;
//		score = 1 - ((UvUCount - UvUDist)/(Ucount*Ucount)  // Use 1- to minimize this score  
//				+ (LivLjCount - LivLjDist)/(Lcount*Lcount) 
//				- (LivLiCount - LivLiDist)/(Lcount*Lcount) 
//				+ (UvLCount - UvLDist)/(Ucount*Lcount));
//		// TODO Auto-generated method stub
//		return score;
	}

	private int getCategory(Example eg) {
		if (!exampleCategory.containsKey(eg.toPrettyString())) {
			Utils.error("No category info for " + eg);
		}
		return exampleCategory.get(eg.toPrettyString());
	}

	public void addDistance(Example eg1,
			Example eg2, double dist) {
		String key  = getExamplePairKey(eg1, eg2);
		currentPairWiseDistance.put(key, dist);
	}
	
	public void addExample(Example eg, int category) {
		exampleCategory.put(eg.toPrettyString(), category);
	}


	public double getDistance(Example eg1, Example eg2) {
		String key =  getExamplePairKey(eg1, eg2);
		if (!currentPairWiseDistance.containsKey(key)) {
			Utils.error("No distance stored between " + eg1 + " and " + eg2);
		} 
		return currentPairWiseDistance.get(key);
	}

	public double getVariance(List<Example> examples) {
		return 1 - (1/examples.size());
		// TODO Auto-generated method stub
		//return calculateScore(examples, new ArrayList<Example>());
	}
	public static List<Example> removeFromCopy(List<Example> allEgs, List<Example> subtractEg) {
		List<Example> copy  = new ArrayList<Example>(allEgs);
		copy.removeAll(subtractEg);
		return copy;
	}

}
