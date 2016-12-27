package edu.wisc.cs.will.MLN_WeightLearning;

import java.util.Collection;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.MLN_Inference.AllOfInference;
import edu.wisc.cs.will.MLN_Inference.Gibbs;
import edu.wisc.cs.will.MLN_Inference.MCSAT;
import edu.wisc.cs.will.MLN_Inference.SAT;
import edu.wisc.cs.will.MLN_Task.GroundClause;
import edu.wisc.cs.will.MLN_Task.GroundedMarkovNetwork;
import edu.wisc.cs.will.MLN_Task.TimeStamp;
import edu.wisc.cs.will.Utils.Utils;

/**
 * This is the pre-conditioned scaled conjugate gradient method.
 * 
 * @author pavan and shavlik
 */
public class PSCG extends DiscriminativeWeightLearning {
	private final static int debugLevel = 0;
	
    public  final static double lambda_default                   = 100.0;
    public  final static int    numMCMCstepsPerIteration_default =  500;
    public  final static int    numLearningSteps_default         = 100;
    
    private double   lambda                      = lambda_default;
    private int      numMCMCstepsPerIteration    = numMCMCstepsPerIteration_default;
    private int      numLearningSteps            = numLearningSteps_default;
    private int      maxNumberOfStarts_SampleSAT = SAT.maxNumberOfStarts_default;
    private int      maxNumberOfFlips_SampleSAT  = SAT.maxNumberOfFlips_default;
    
    private double[] preConditioner;
    private double[] currGradient;
    private double[] prevGradient;
    private double[] searchDirection;
    private double[] prevSearchDirection;
    private double[] Hd;	// Product of Hessian and search direction.
    private double[] step;
//  private double[] Hg;
    private double[] expNumTrueGroundings;
    private double[] expSqrNumTrueGroundings;
    private double[] deltaPred;
//  private double[] prevSearcDirection;
    
    private boolean  usePreConditioner = true;
//  private boolean  backTracked;
    private double   alpha;
    private double   maxLambda = Integer.MAX_VALUE;
    private double   minLLChangeCutoff = 0.0001;
    private Gibbs    gibbsSampler;
    private MCSAT    mcsatSampler;
   
    public PSCG(GroundedMarkovNetwork groundedMarkovNetwork) {
    	super(groundedMarkovNetwork);
    	setupPSCG();
    }
    public PSCG(GroundedMarkovNetwork groundedMarkovNetwork, int numLearningSteps) {
		super(groundedMarkovNetwork);
		this.numLearningSteps = numLearningSteps;
		setupPSCG();
    }    
    public PSCG(GroundedMarkovNetwork groundedMarkovNetwork, int numLearningSteps, int numMCMCstepsPerIteration, double lambda) {
    	super(groundedMarkovNetwork);
    	this.numLearningSteps         = numLearningSteps;
    	this.numMCMCstepsPerIteration = numMCMCstepsPerIteration;
	    this.lambda                   = lambda;
	    setupPSCG();
    }  
    public PSCG(GroundedMarkovNetwork groundedMarkovNetwork, int numLearningSteps, int numMCMCstepsPerIteration, double lambda, 
    		    int maxNumberOfStarts_SampleSAT, int maxNumberOfFlips_SampleSAT) {
		super(groundedMarkovNetwork);
		this.numLearningSteps            = numLearningSteps;
		this.numMCMCstepsPerIteration    = numMCMCstepsPerIteration;
		this.lambda                      = lambda;
		this.maxNumberOfStarts_SampleSAT = maxNumberOfStarts_SampleSAT;
		this.maxNumberOfFlips_SampleSAT  = maxNumberOfFlips_SampleSAT;
		setupPSCG();
	} 
	private void setupPSCG() {
		expNumTrueGroundings    = new double[numberOfClausesUsed];
		expSqrNumTrueGroundings = new double[numberOfClausesUsed];
		preConditioner          = new double[numberOfClausesUsed];
	    currGradient            = new double[numberOfClausesUsed];
	    prevGradient            = new double[numberOfClausesUsed];
	    searchDirection         = new double[numberOfClausesUsed];
	    prevSearchDirection     = new double[numberOfClausesUsed];
	    step                    = new double[numberOfClausesUsed];
	    Hd                      = new double[numberOfClausesUsed];
	    deltaPred               = new double[numberOfClausesUsed];
	    gibbsSampler            = new Gibbs(groundedMarkovNetwork, AllOfInference.prior_for_being_true_default);
    	mcsatSampler            = new MCSAT(groundedMarkovNetwork, AllOfInference.prior_for_being_true_default, maxNumberOfStarts_SampleSAT, maxNumberOfFlips_SampleSAT);
	}
    
    /**
     * Learns the weights of clauses.
     * 
     * @return The clause objects with their learned weights.
     */
	public Collection<Clause> learn(TimeStamp timeStamp) {		
		updateWeights(timeStamp);		
		assignActualValuesToGroundLiterals(timeStamp);
		return groundedMarkovNetwork.getAllClausesThatWereGrounded();
	}
	
	/**
	 * This is the conjugate-gradient algorithm to compute the weights of clauses.
	 */
    public void updateWeights(TimeStamp timeStamp)  {
    	long startTime = -1;
    	for (int i = 0; i < numLearningSteps; i++) {
			if (debugLevel > 0) { 
			//	Utils.print("% PSCG: Conjugate-gradient step #" + i);
	    		long   endTime   = System.currentTimeMillis();
	    		double timeTaken = (endTime - startTime) / 1000.0;
    			if (startTime  > 0) { Utils.println(".   Took " + Utils.truncate(timeTaken, 2) + " seconds."); }
    			else                { Utils.println("."); }
				startTime = endTime;
			}
            computeExpectationCounts();
            setPreConditioner();
            computeGradient();
          //  updateMissingLiterals(); // For EM on hidden/missing literal.
            double delta = 0.0;
            if (i >= 1) { delta = adjustLambda(); }
            if (delta < 0) {
            	for (int j = 0; j < numberOfClausesUsed; j++) { 
            		Clause clause = indexToClause[j];
                    clause.deltaWeightOnSentence(-step[j]);
                    Collection<GroundClause> gndClauses = groundedMarkovNetwork.getAllGroundClauses(clause);
        			if (gndClauses != null) for (GroundClause gndClause : gndClauses) { gndClause.setWeightOnSentence(clause.getWeightOnSentence()); }
                }
            }
            
            double beta = 0;            
            if (i >= 1) {
            	double betaNum = 0.0;
                double betaDen = 0.0;
                for (int j = 0; j < numberOfClausesUsed; j++) {
                    betaNum += currGradient[j] * preConditioner[j] * (currGradient[j] - prevGradient[j]);
                    betaDen += prevGradient[j] * preConditioner[j] * prevGradient[j];  
                } 
                if (betaDen != 0) { beta = betaNum / betaDen; }
                if (debugLevel > 1) { Utils.println("% PSCG:  beta = " + Utils.truncate(beta, 4)); }
            }
               
            // Get the new search direction.
            for (int j = 0; j < numberOfClausesUsed; j++) {
                searchDirection[j] = -preConditioner[j] * currGradient[j] + beta * prevSearchDirection[j];
                // Utils.println("d g " + searchDirection[i]  + " " + currGradient[i]);
            }
           
            Hd    = getHessianVectorProduct(searchDirection);
//          Hg    = getHessianVectorProduct(currGradient);
            alpha = computeQuadraticStepLength();
            if (debugLevel > 1) { Utils.println("% PSCG:  alpha = " + Utils.truncate(alpha, 4)); }
           
            if (alpha < 0) {
            	for (int j = 0; j < numberOfClausesUsed; j++) { searchDirection[j] = -preConditioner[j] * currGradient[j]; }               
                Hd = getHessianVectorProduct(searchDirection);
                alpha = computeQuadraticStepLength();
            }
            
            for (int j = 0; j < numberOfClausesUsed; j++) { step[j] = alpha * searchDirection[j]; }            	
            if (-dotProd(step, currGradient) < minLLChangeCutoff) { break; }
            
            for (int j = 0; j < numberOfClausesUsed; j++) {
            	Clause clause = indexToClause[j];
            	prevGradient[j]        = currGradient[j];
            	prevSearchDirection[j] = searchDirection[j];
                clause.deltaWeightOnSentence(step[j]);
                Collection<GroundClause> gndClauses = groundedMarkovNetwork.getAllGroundClauses(clause);
    			if (gndClauses != null) for (GroundClause gndClause : gndClauses) { gndClause.setWeightOnSentence(clause.getWeightOnSentence()); }
            } 
    	}     
    }
   
    /**
     * This method estimates various counts like the expected number of true groundings
     * of a clause, and the square of expected number of true grounding of a clause.
     * MCMC sampling is done to get these expectation counts.
     */
    private void computeExpectationCounts() {    	
        double[] sumNumTrueGroundings    = new double[numberOfClausesUsed];
        double[] sumSqrNumTrueGroundings = new double[numberOfClausesUsed];
        for (int i = 0; i < numMCMCstepsPerIteration; i++) {
            if (MCMCsamplingType == GIBBS_SAMPLING) { gibbsSampler.getNextSample(); }
            else { mcsatSampler.getNextSample(); }
            for (int j = 0; j < numberOfClausesUsed; j++) {
            	Clause clause = indexToClause[j];
            	double numTrueGroundings = groundedMarkovNetwork.numberOfSatisfiedGroundClauses(clause);
         //       Utils.println("Groundings for clause: " + j + "=" + numTrueGroundings);
                sumNumTrueGroundings[j]    += numTrueGroundings;
                sumSqrNumTrueGroundings[j] += numTrueGroundings * numTrueGroundings;
            }                       
        }
        if (MCMCsamplingType != GIBBS_SAMPLING) {
        	mcsatSampler.cleanUpSampleGenerator();
        }
        for (int i = 0; i < numberOfClausesUsed; i++) {
            expNumTrueGroundings[i]    = sumNumTrueGroundings[i]    / numMCMCstepsPerIteration;
            expSqrNumTrueGroundings[i] = sumSqrNumTrueGroundings[i] / numMCMCstepsPerIteration;
        }       
    }
   
    /**
     * Computes the gradient at the current point in weight space.
     */
    private void computeGradient() {
    	double sum =  0.0;
    	double max = -0.1;
    	int worstClauseIndex = -1;
    	for (int i = 0; i < numberOfClausesUsed; i++) {
    		if (debugLevel > 1) { Utils.println("% PSCG:   Clause #" + i + " actual(#sat) = " + Utils.truncate(numSatisfiedGroundClausesInDatabase[i], 3) + ", expected(#sat) = " + Utils.truncate(expNumTrueGroundings[i], 3)); }
    		currGradient[i] = expNumTrueGroundings[i] - numSatisfiedGroundClausesInDatabase[i];
    		double abs =  Math.abs(currGradient[i]);
    		sum += abs;
    		if (print1normGradient && abs > max) { max = abs; worstClauseIndex = i; }
    		if (debugLevel > 1) { Utils.println("% PSCG:       currGradient = " + Utils.truncate(currGradient[i],4) + "   sum = " + Utils.truncate(sum, 4)); }
    	}
    	if (print1normGradient) { Utils.println("% PSCG: 1-norm of gradient (avg over the " + Utils.comma(numberOfClausesUsed) + " clauses): " + Utils.truncate(sum / numberOfClausesUsed, 3) + ".  The infinity norm = " + Utils.truncate(max, 0) + " from clause '" + indexToClause[worstClauseIndex] + "'.\n"); }
    }
    
    /**
     * Computes the product of the Hessian and a vector.
     * 
     * @param v The vector whose product we want to get with the Hessian
     * @return The product of the Hessian and the vector v.
     */
    private double[] getHessianVectorProduct(double[] v) {
        double sumVN = 0;
        double[]   sumN              = new double[numberOfClausesUsed];
        double[]   sumNiVN           = new double[numberOfClausesUsed];
        double[]   numTrueGroundings = new double[numberOfClausesUsed];
        for (int i = 0; i < numMCMCstepsPerIteration; i++) {
        	if (MCMCsamplingType == GIBBS_SAMPLING) gibbsSampler.getNextSample();
            else mcsatSampler.getNextSample();
            double vn = 0;
            for (int j = 0; j < numberOfClausesUsed; j++) {
            	Clause clause = indexToClause[j];
                numTrueGroundings[j] = groundedMarkovNetwork.numberOfSatisfiedGroundClauses(clause);               
            }
            for (int j = 0; j < numberOfClausesUsed; j++) {
                vn += v[j] * numTrueGroundings[j];
            }
            sumVN += vn;
            for (int j = 0; j < numberOfClausesUsed; j++) {
                sumN[j]    += numTrueGroundings[j];
                sumNiVN[j] += numTrueGroundings[j] * vn;
            }           
        }
        if (MCMCsamplingType != GIBBS_SAMPLING) {
        	mcsatSampler.cleanUpSampleGenerator();
        }
        double[]   result = new double[numberOfClausesUsed];
        double E_VN = sumVN / numMCMCstepsPerIteration;
        for (int i = 0; i < numberOfClausesUsed; i++) {
            double E_Ni = sumN[i] / numMCMCstepsPerIteration;
            double E_NiVN = sumNiVN[i] / numMCMCstepsPerIteration;
            result[i] = E_NiVN - E_Ni * E_VN;
        }
        return result;
    }
   
    /**
     * Computes the size of the step length to be used in the search direction.
     */
    private double computeQuadraticStepLength() {
        double dHd = dotProd(searchDirection, Hd);
        double dd  = dotProd(searchDirection, searchDirection);
        double dg  = dotProd(searchDirection, currGradient);
        if (debugLevel > 2) { Utils.println("  dg: dHd: dd = " + dg + " " + dHd + " " + dd); }
        double alpha = -dg / (dHd + lambda * dd);
        return alpha;
    }
   
    /**
     * This method adjusts the value of lambda, which reflects our trust in the size
     * of the region where the quadratic assumption holds.
     * 
     * @return The ratio of real and predicted changes in function values as a result
     * of the previous step.
     */
    private double adjustLambda() {
        double realDist = computeRealDist();
        double predDist = computePredDist();
       
        double delta = realDist / predDist;
        if (predDist != 0 && delta > 0.75)
            lambda /= 2;
        if (delta < 0.25) {
            if (lambda * 4 > maxLambda)
                lambda = maxLambda;
            else
                lambda *= 4;
        }
        if (debugLevel > 1) { Utils.println("% PSCG:  delta = " + Utils.truncate(delta, 4) + " lambda = " + Utils.truncate(lambda, 4)); }
        return delta;
    }
   
    /**
     * This is a lower bound on the real change in the function value.
     */
    private double computeRealDist() {      
    	// "step" is the step taken in the previous iteration to move to a point
    	// where the gradient is "currGradient".
        return dotProd(step, currGradient);
    }
   
    /**
     * This is the change in function value according to the quadratic assumption.
     * 
     */
    private double computePredDist() {
    	// It should be remembered that if we take a "step" from point a to point b, the
        // change in gradient is H.step. So this takes the mean of previous and current gradients
        // and dot products with step to get the change in function value.
        double[]   avgPred = new double[numberOfClausesUsed];     
        deltaPred = getHessianVectorProduct(step);  // "step" is the step taken in the previous iteration.
        for (int i = 0; i < numberOfClausesUsed; i++) {
            avgPred[i] = prevGradient[i] + deltaPred[i] / 2.0;
        }
        return dotProd(step, avgPred);
    }
   
    private double dotProd(double[] a, double[] b) {
        double dotProd = 0;
        int length = Math.max(a.length, b.length); // Should match, but assume shorter is padded with zeroes.
        for (int i = 0; i < length; i++)  {
            dotProd += a[i] * b[i];            
        }
        return dotProd;
    }
   
    /**
     * This function sets the value if the preconditioner. If a preconditioner is to
     * be used, the value is set to the inverse of the diagonalized Hessian, else
     * all the preconditioner values are set to 1. 
     */ 
    public void setPreConditioner() {
        preConditioner = new double[numberOfClausesUsed];
        if (usePreConditioner) {        	
        	for (int i = 0; i < numberOfClausesUsed; i++) {
            	//Utils.println("" + expSqrNumTrueGroundings[i] + " " + expNumTrueGroundings[i]);
            	double variance_i = expSqrNumTrueGroundings[i] - (expNumTrueGroundings[i] * expNumTrueGroundings[i]);  
                if (variance_i == 0) {
                	preConditioner[i] = 1.0;
                } else {
                	preConditioner[i] = 1.0 / (variance_i);    
                //Utils.println("" + preConditioner[i]);
                }
            }
        } else for (int i = 0; i < numberOfClausesUsed; i++) { preConditioner[i] = 1.0; }
    }    
}
