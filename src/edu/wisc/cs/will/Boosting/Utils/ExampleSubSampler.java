/**
 * 
 */
package edu.wisc.cs.will.Boosting.Utils;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.SortedSet;
import java.util.TreeSet;

import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.VectorStatistics;

/**
 * @author tkhot
 *
 */
public class ExampleSubSampler {

	private WILLSetup willSetup;
	private CommandLineArguments cmdArgs;
	
    private boolean useTopKResidueExamples  = false;
    private double  negSampleRatioForTopK	= 2.0;
    private boolean sampleByRegressionSquare= false;
    private boolean influenceTrimming 		= false;
    private boolean histogramSampling  		= false;
    private boolean removeTopNExamples      = false;
    private double  influenceAlpha			= 0.8;
    
	public ExampleSubSampler(WILLSetup setup, CommandLineArguments args) {
		this.willSetup = setup;
		this.cmdArgs = args;
		init();
		
	}
	
	private void init() {
		String lookup;
		if ((lookup =  willSetup.getHandler().getParameterSetting("topNeg")) != null) {
			negSampleRatioForTopK = Double.parseDouble(lookup);
			useTopKResidueExamples = true;
		}
		if ((lookup =  willSetup.getHandler().getParameterSetting("sampleByResidue")) != null) {
			sampleByRegressionSquare = Boolean.parseBoolean(lookup);
		}
		if ((lookup =  willSetup.getHandler().getParameterSetting("influenceTrimming")) != null) {
			influenceTrimming = Boolean.parseBoolean(lookup);
		}
		if ((lookup =  willSetup.getHandler().getParameterSetting("influenceAlpha")) != null) {
			influenceAlpha = Double.parseDouble(lookup);
		}
		if ((lookup =  willSetup.getHandler().getParameterSetting("histSampling")) != null) {
			histogramSampling = Boolean.parseBoolean(lookup);
		}
		if ((lookup =  willSetup.getHandler().getParameterSetting("removeTopEg")) != null) {
			removeTopNExamples = Boolean.parseBoolean(lookup);
		}
	}
	
	public List<RegressionRDNExample> sampleExamples(List<RegressionRDNExample> all_exs) {
		if (useTopKResidueExamples) {
			return sampleTopK(all_exs);
		}
		if (sampleByRegressionSquare) {
			return sampleByRegression(all_exs);
		}
		if (influenceTrimming) {
			return trimByInfluence(all_exs);
		}
		if (histogramSampling) {
			return histogramSample(all_exs);
		}
		if (removeTopNExamples) {
			// TODO : Add the method to remove the most likely examples here.
			// Use isOriginalTruthValue to figure out positive/negative examples within all_exs
			// Use outputvalue for the current regression output value. outputvalue is not the gradient i.e.,
			// difference between true value and current value(I - P) but is the value returned by \psi.
			
		}
		return all_exs;
	}

	private List<RegressionRDNExample> histogramSample(List<RegressionRDNExample> all_exs) {
		double binSize = 0.05;
		double min = 0;
		double max = 1;
		int numBins = (int)Math.ceil((max-min)/binSize);
		ArrayList<RegressionRDNExample>[] egs = new ArrayList[numBins];
		for (int i = 0; i < numBins; i++) {
			egs[i] = new ArrayList<RegressionRDNExample>();
		}
		for (RegressionRDNExample eg : all_exs) {
			double val = Math.abs(eg.getOutputValue());
			int bin = (int)Math.floor((val - min)/binSize);
			bin = Math.min(bin, numBins - 1);
			egs[bin].add(eg);
		}
		List<RegressionRDNExample> resultEgs = new ArrayList<RegressionRDNExample>();
		// Select 10% of the example and minimum 5 examples
		double prob=0.05;
		int minEg = 30;
		for (int i = 0; i < egs.length; i++) {
			ArrayList<RegressionRDNExample> egBin = egs[i];
			if (egBin.size() == 0) {
				continue;
			}
			double egSize = egBin.size() * prob;
			egSize = Math.floor(Math.min(egBin.size(), Math.max(minEg, egSize)));
			double wt = egBin.size() / egSize;
			List<RegressionRDNExample> selectedEgs=Utils.chooseRandomNfromThisList((int)egSize, egBin);
			if (wt > 1) {
				Utils.println("Shrinking to " + egSize + " for bin:" + i);
				for (RegressionRDNExample selEg : selectedEgs) {
					selEg.setWeightOnExample(selEg.getWeightOnExample() * wt);
				}
			} else {
				Utils.println("No Shrinking to bin:" + i);
			}
			resultEgs.addAll(selectedEgs);
		}
		
		// TODO Auto-generated method stub
		return resultEgs;
	}

	private List<RegressionRDNExample> trimByWeight(List<RegressionRDNExample> all_exs) {
		double min_abs_grad = Double.POSITIVE_INFINITY;
		for (int i = 0; i < Utils.getSizeSafely(all_exs); i++) {
			RegressionRDNExample eg = all_exs.get(i);
			if (min_abs_grad > Math.abs(eg.getOutputValue())) {
				min_abs_grad = Math.abs(eg.getOutputValue());
			}
		}
		List<RegressionRDNExample> newExamples = new ArrayList<RegressionRDNExample>();
		for (RegressionRDNExample rex : all_exs) {
			double absGrad = Math.abs(rex.getOutputValue());
			if (absGrad > 0.02) {
				newExamples.add(rex);
			}
		}
		Utils.println("Reduced the number of examples to: " + newExamples.size() + " from " + all_exs.size());
		Utils.println("where output:" + min_abs_grad);
		if (newExamples.size() < ((double)all_exs.size()/1.5)) {
			Utils.waitHere();
		}
		return newExamples;
	}
	
	private List<RegressionRDNExample> trimByInfluence(List<RegressionRDNExample> all_exs) {
		
		SortedSet<RegressionRDNExample> topExamples = new TreeSet<RegressionRDNExample>(new WeightComparator());
		topExamples.addAll(all_exs);
		List<RegressionRDNExample> newExamples = new ArrayList<RegressionRDNExample>();
		double totalWt = 0;
		for (RegressionRDNExample rex : topExamples) {
			if (totalWt == 0) { Utils.println("Starting with: "  + ExampleSubSampler.getWeight(rex)); }
			totalWt += ExampleSubSampler.getWeight(rex);
		}
		Utils.println("total wt=" + totalWt + " in " + topExamples.size());
		double stopAtWt = totalWt * (influenceAlpha);
		
		for (RegressionRDNExample rex : topExamples) {
			double wt = ExampleSubSampler.getWeight(rex);
			stopAtWt= stopAtWt - wt;
			newExamples.add(rex);
			if (stopAtWt < 0) { Utils.println("Stopped at: " + wt); break;}
		}
		Utils.println("Reduced the number of examples to: " + newExamples.size() + " from " + all_exs.size());
		return newExamples;
	}

	private List<RegressionRDNExample> sampleByRegression(
			List<RegressionRDNExample> all_exs) {
		int pos = 0;
		int neg = 0;
		double min_abs_grad = Double.POSITIVE_INFINITY;
		List<RegressionRDNExample> negExs = new ArrayList<RegressionRDNExample>();
		List<RegressionRDNExample> posExs = new ArrayList<RegressionRDNExample>();
		for (int i = 0; i < Utils.getSizeSafely(all_exs); i++) {
			RegressionRDNExample eg = all_exs.get(i);

			if (!eg.isOriginalTruthValue()) {
				negExs.add(eg);
				neg++;
			} else {
				posExs.add(eg);
				pos ++;
			}
			if (min_abs_grad > Math.abs(eg.getOutputValue())) {
				min_abs_grad = Math.abs(eg.getOutputValue());
			}

		}
		
		List<RegressionRDNExample> newNegExamples = new ArrayList<RegressionRDNExample>();
		double minGrad = Double.MAX_VALUE; // FOr debugging
		double maxGrad = Double.NEGATIVE_INFINITY;
		
		for (RegressionRDNExample negEx : negExs) {
			//double samplingProb = Math.sqrt(Math.pow(negEx.outputValue,2));
			double samplingProb = 10*Math.pow(Math.abs(negEx.getOutputValue()),2);
			if (samplingProb > 1) {
				//Utils.waitHere("The output values/residues exceed 1. Can't use squared outputs for sampling prob." + negEx.outputValue);
				samplingProb = 1;
			}
			if (Utils.random() < samplingProb) {
				if (false && cmdArgs.reweighExamples) {
					RegressionRDNExample newNegEx = new RegressionRDNExample(negEx);
					// Don't want to weigh any example by more than 1000 times
					double wtPerEg = Math.min(1/samplingProb, 1000);
					newNegEx.setWeightOnExample(negEx.getWeightOnExample() * wtPerEg);
					newNegExamples.add(newNegEx);
				} else {
					newNegExamples.add(negEx);
				}
				if (minGrad > negEx.getOutputValue()) {
					 minGrad = negEx.getOutputValue();
				}
				if (maxGrad < negEx.getOutputValue()) {
					 maxGrad = negEx.getOutputValue();
				}
			}
		}
		Utils.print("Shrunk negative examples to " + newNegExamples.size() + " from " + negExs.size() + " with gradients between " + minGrad + " & " + maxGrad);
		newNegExamples.addAll(posExs);
		return newNegExamples;

	}

	private List<RegressionRDNExample> sampleTopK(List<RegressionRDNExample> all_exs) {
		int pos = 0;
		int neg = 0;
		double min_abs_grad = Double.POSITIVE_INFINITY;
		List<RegressionRDNExample> negExs = new ArrayList<RegressionRDNExample>();
		List<RegressionRDNExample> posExs = new ArrayList<RegressionRDNExample>();
		for (int i = 0; i < Utils.getSizeSafely(all_exs); i++) {
			RegressionRDNExample eg = all_exs.get(i);

			if (!eg.isOriginalTruthValue()) {
				negExs.add(eg);
				neg++;
			} else {
				posExs.add(eg);
				pos ++;
			}
			if (min_abs_grad > Math.abs(eg.getOutputValue())) {
				min_abs_grad = Math.abs(eg.getOutputValue());
			}

		}

		if ((double)neg > (double)pos * negSampleRatioForTopK) { 
			int numbOrigNegExamplestoUse = (int)Math.floor(pos * negSampleRatioForTopK);
			List<RegressionRDNExample> newNegExamples = getTopKExamples(negExs, numbOrigNegExamplestoUse);
			//double ratio = (double)neg / (double)numbOrigNegExamplestoUse;
			/*for (Example eg : newNegExamples) {
				// Dont reweigh examples here as we picked the "worst" examples and so it 
				// is not truely a random sample.
			if (cmdArgs.isReweighExamples()) {
					eg.setWeightOnExample(eg.getWeightOnExample() * ratio);
				}
			}*/
			newNegExamples.addAll(posExs);
			return newNegExamples;
		} 
		return all_exs;
	}

	private List<RegressionRDNExample> getTopKExamples(List<RegressionRDNExample> negExs,
			int numbOrigNegExamplestoUse) {
		
		if (numbOrigNegExamplestoUse <= 0 || numbOrigNegExamplestoUse >= negExs.size()) {
			return negExs;
		}
		SortedSet<RegressionRDNExample> topExamples = new TreeSet<RegressionRDNExample>(new GradientComparator());
		
		for (RegressionRDNExample eg : negExs) {
			topExamples.add(eg);
			while(topExamples.size() > numbOrigNegExamplestoUse) {
				// Utils.println("Filtering example: " + topExamples.last());
				topExamples.remove(topExamples.last());
			}
		}
		Utils.println("Kept examples between: " + topExamples.last().getOutputValue() + " and " + topExamples.first().getOutputValue());
		return new ArrayList<RegressionRDNExample>(topExamples);
	}
	public class GradientComparator implements Comparator<RegressionRDNExample> {

		@Override
		public int compare(RegressionRDNExample r1, RegressionRDNExample r2) {
			if (r1.equals(r2)) {
				return 0;
			}
			double v1 = Math.abs(r1.getOutputValue());
			double v2 = Math.abs(r2.getOutputValue());
			if (v1 > v2) {
				return -1;
			}
			return 1;
		}
	}
	
	public class WeightComparator implements Comparator<RegressionRDNExample> {

		@Override
		public int compare(RegressionRDNExample r1, RegressionRDNExample r2) {
			if (r1.equals(r2)) {
				return 0;
			}
			
			double v1 = ExampleSubSampler.getWeight(r1);
			double v2 = ExampleSubSampler.getWeight(r2);
			if (v1 > v2) {
				return -1;
			}
			return 1;
		}
	}

	public static double getWeight(RegressionRDNExample ex) {
		ProbDistribution prob = ex.getProbOfExample();
		if (prob.isHasDistribution()) {
			double[] dist = prob.getProbDistribution();
			double[] oneMinusDist = VectorStatistics.addScalar(VectorStatistics.scalarProduct(dist, -1), 1);
			return VectorStatistics.dotProduct(dist, oneMinusDist);
		} else {
			double p = prob.getProbOfBeingTrue();
			return p * (1-p);
		}
	}
}
