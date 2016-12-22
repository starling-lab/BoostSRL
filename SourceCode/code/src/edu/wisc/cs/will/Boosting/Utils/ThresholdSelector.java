/**
 * 
 */
package edu.wisc.cs.will.Boosting.Utils;

import java.util.ArrayList;
import java.util.Collections;
import edu.wisc.cs.will.ILP.CoverageScore;

/**
 * @author Tushar Khot
 *
 */
public class ThresholdSelector {

	class ProbabilityResult {
		public ProbabilityResult(double prob, boolean posEg) {
			super();
			this.prob = prob;
			this.posEg = posEg;
		}
		public String toString() {
			return prob +":" + posEg;
		}
		
		public double prob;
		public boolean posEg;
	}
	
	public class descendingProbs implements java.util.Comparator<ProbabilityResult> {
		 public int compare(ProbabilityResult ob1, ProbabilityResult ob2) {
		   if (ob1.prob == ob2.prob) {
			   if (ob1.posEg && ob2.posEg) {
				   return 0;
			   }
			   if (ob1.posEg && !ob2.posEg) {
				   return -1;
			   }
			   if (!ob1.posEg && ob2.posEg) {
				   return 1;
			   }
			   if (!ob1.posEg && !ob2.posEg) {
				   return 0;
			   }
		   } else {
			   return (int) Math.ceil(ob2.prob - ob1.prob);
		   }
		   return 0;
		 }
		} 
	
	ArrayList<ProbabilityResult> results;
	public double lastComputedF1 = Double.NaN;
	public ThresholdSelector() {
		results = new ArrayList<ProbabilityResult>();
	}
	public void addProbResult(double prob, boolean posEg) {
		results.add(new ProbabilityResult(prob, posEg));
	}
	
	public double selectBestThreshold() {
		Collections.sort(results, new descendingProbs());
		CoverageScore score = new CoverageScore();
		int numP=0;
		int numN=0;
		for (ProbabilityResult res : results) {
			if (res.posEg)
				numP++;
			else
				numN++;
		}
		score.setCounts(0, 0, numN, numP);
		
		double bestThreshold = 0;
		double bestF1=0;
		double lastProb=1;
		//boolean lastSign=true;
		//boolean flippedSign = false;
		for (ProbabilityResult res : results) {
			//System.out.println(res);
			//if (!flippedSign && lastSign != res.posEg) {
//				flippedSign = true;
			//}
			if (lastProb != res.prob) {
				double f1 = score.getF1();
				//System.out.println(f1);
				if (f1 > bestF1) {
					bestThreshold = (lastProb + res.prob)/2;
					bestF1 = f1;
				}
				lastProb = res.prob;
			}
			if (res.posEg) {
				score.setTruePositives(score.getTruePositives() + 1);
				score.setFalseNegatives(score.getFalseNegatives()-1);
			} else {
				score.setFalsePositives(score.getFalsePositives()+1);
				score.setTrueNegatives(score.getTrueNegatives()-1);
			}
		}
		System.out.println("Best F1 = " + bestF1);
		lastComputedF1 = bestF1;
		return bestThreshold;
	}
	
	public static void main(String[] args) {
		ThresholdSelector selec = new ThresholdSelector();
		selec.addProbResult(0.9, true);
		selec.addProbResult(0.8, true);
		selec.addProbResult(0.7, true);
		selec.addProbResult(0.6, true);
		selec.addProbResult(0.5, true);
		selec.addProbResult(0.9, true);
		selec.addProbResult(0.55, false);
		selec.addProbResult(0.65, false);
		selec.addProbResult(0.45, false);
		selec.addProbResult(0.35, false);
		selec.addProbResult(0.5, false);
		selec.selectBestThreshold();
	}
}
