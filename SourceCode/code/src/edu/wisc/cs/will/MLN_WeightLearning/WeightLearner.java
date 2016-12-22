package edu.wisc.cs.will.MLN_WeightLearning;

import java.util.Collection;

import edu.wisc.cs.will.FOPC.Clause;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.MLN_Inference.SAT;
import edu.wisc.cs.will.MLN_Task.GroundedMarkovNetwork;
import edu.wisc.cs.will.MLN_Task.MLN_Task;
import edu.wisc.cs.will.MLN_Task.ProcessCommandLineString;
import edu.wisc.cs.will.MLN_Task.TimeStamp;
import edu.wisc.cs.will.Utils.Utils;

/**
 * Sample command line parameters:
 * -dir ../Testbeds/univ/       -theory univ.mln       -dp univ_pos_evidence.db -q advisedBy/2,professor/1,student/1 -pos univ_pos_queries.db -pscg -dribble
 * -dir ../Testbeds/biasedDice/ -theory biasedDice.mln                          -q Outcome/2,Odd/0,Even/0            -pos biasedDice_pos.txt  -pscg -dribble
 * 
 * STILL IN OLD STYLE:
 * -i ../Testbeds/univ/univ.mln -dp ../Testbeds/univ/train.db -q advisedBy/2,professor/1,student/1 -e inPhase/2,hasPosition/2,publication/2 -vp
 * 
 * @author pavan and shavlik
 */

public class WeightLearner {
	@SuppressWarnings("unused")
	private static final int debugLevel = 0;
	
	private static final int VOTED_PERCEPTRON = 0;
	private static final int PSCG_ALG         = 1;
	
	private HandleFOPCstrings        stringHandler         = new HandleFOPCstrings();
	private FileParser               parser                = new FileParser(stringHandler);
	private MLN_Task                 task                  = new MLN_Task(  stringHandler);
	private ProcessCommandLineString commandLineProcessor  = new ProcessCommandLineString(stringHandler, parser, task);
	private GroundedMarkovNetwork  groundedMarkovNetwork = null;
  
	private int     learningAlgo                             = PSCG_ALG;
	private int     numStarts_MCSAT                          = SAT.maxNumberOfStarts_default;
	private int     numStepsPerStart_MCSAT                   = SAT.maxNumberOfFlips_default;
	
	private int     numMCMCstepsPerIteration_PSCG            = PSCG.numMCMCstepsPerIteration_default;
	private double  lambda_PSCG                              = PSCG.lambda_default;
	
	private boolean useDifferentEtas                         = VotedPerceptron.useDifferentEtas_default;	
	private int     numStarts_votedPerceptron                = VotedPerceptron.numStarts_default;
	private int     numStepsPerStart_votedPerceptron         = VotedPerceptron.numStepsPerStart_default;
	private int     numMCMCstepsPerIteration_votedPerceptron = VotedPerceptron.numMCMCstepsPerIteration_default;
	private int     typeOfEstimation_votedPerceptron         = VotedPerceptron.typeOfEstimation_default;
	private double  eta_votedPerceptron                      = VotedPerceptron.eta_default;
	
	private int     typeOfInitialWeights_discrimLearning     = DiscriminativeWeightLearning.typeOfInitialWeights_default;
	private boolean print1normGradient_discrimLearning       = DiscriminativeWeightLearning.print1normGradient_default;
	
	private int     numLearningSteps                         = -1; // If this is still non-positive, then use the default value for the method in question.

	public WeightLearner() {
	}
	
	public Collection<Clause> learnWgts(String[] args) {
		commandLineProcessor.processOptions(args);
		
		TimeStamp timeStamp = new TimeStamp("WeightLearner");
		long start = System.currentTimeMillis();
		DiscriminativeWeightLearning discriminativeWgtLearner = null;

		groundedMarkovNetwork = task.createReducedNetwork();
		groundedMarkovNetwork.prepareForInference(timeStamp); // TODO - do this automatically?
		numLearningSteps = commandLineProcessor.choose(numLearningSteps, commandLineProcessor.numLearningSteps);
		switch(getLearningAlgo(commandLineProcessor.learningAlgo)) {
			case VOTED_PERCEPTRON: 
				discriminativeWgtLearner = new VotedPerceptron(groundedMarkovNetwork,
						                                       (numLearningSteps > 0 ? numLearningSteps : VotedPerceptron.numLearningSteps_default), 
						                                       commandLineProcessor.choose(numStarts_votedPerceptron,                commandLineProcessor.numStarts_votedPerceptron),
						                                       commandLineProcessor.choose(numStepsPerStart_votedPerceptron,         commandLineProcessor.numStepsPerStart_votedPerceptron),
						                                       commandLineProcessor.choose(numMCMCstepsPerIteration_votedPerceptron, commandLineProcessor.numMCMCstepsPerIteration_votedPerceptron),
															   getTypeOfEstimation(                                                  commandLineProcessor.typeOfEstimation_votedPerceptron),
															   commandLineProcessor.choose(eta_votedPerceptron,                      commandLineProcessor.eta_votedPerceptron), 
															   getUseDifferentEtas(                                                  commandLineProcessor.useDifferentEtas_votedPerceptron));
				break;
			case PSCG_ALG: 
				discriminativeWgtLearner = new PSCG(groundedMarkovNetwork,
													(numLearningSteps > 0 ? numLearningSteps : PSCG.numLearningSteps_default),
													commandLineProcessor.choose(numMCMCstepsPerIteration_PSCG, commandLineProcessor.numMCMCstepsPerIteration_PSCG),
													commandLineProcessor.choose(lambda_PSCG,                   commandLineProcessor.lambda_PSCG),
													commandLineProcessor.choose(numStarts_MCSAT,               commandLineProcessor.numStarts_MCSAT), 
													commandLineProcessor.choose(numStepsPerStart_MCSAT,        commandLineProcessor.numStepsPerStart_MCSAT));
				break;
		}
		
		// Set these directly instead of passing in to the constructors (since argument lists getting so long).
		discriminativeWgtLearner.typeOfInitialWeights = getTypeOfInitialWeights(commandLineProcessor.typeOfInitialWeights_discrimLearning);
		discriminativeWgtLearner.print1normGradient   = getPrint1NormGradient(  commandLineProcessor.print1normGradient_discrimLearning);
			
		Collection<Clause> weightedClauses = discriminativeWgtLearner.learn(new TimeStamp("WeightLearner"));
		discriminativeWgtLearner.print();
		long end = System.currentTimeMillis();
		double timeTaken = (end - start) / 1000.0;
		Utils.println("\n% Total time taken for learning = " + timeTaken + " seconds.");
		return weightedClauses;
	}
	
	private boolean getPrint1NormGradient(String booleanValue) {
		if      (booleanValue == null)                   { return print1normGradient_discrimLearning; }
		else if (booleanValue.equalsIgnoreCase("true"))  { return true; }
		else if (booleanValue.equalsIgnoreCase("false")) { return false; }
		Utils.error("Unknown value: " + booleanValue);
		return false;
	}

	private boolean getUseDifferentEtas(String booleanValue) {
		if      (booleanValue == null)                   { return useDifferentEtas; }
		else if (booleanValue.equalsIgnoreCase("true"))  { return true; }
		else if (booleanValue.equalsIgnoreCase("false")) { return false; }
		Utils.error("Unknown value: " + booleanValue);
		return false;
	}

	private int getLearningAlgo(String learningAlgoString) {
		if      (learningAlgoString == null)                  { return learningAlgo; }
		else if (learningAlgoString.equalsIgnoreCase("VP"))   { return VOTED_PERCEPTRON; }
		else if (learningAlgoString.equalsIgnoreCase("PSGC")) { return PSCG_ALG; }
		Utils.error("Unknown value: " + learningAlgoString);
		return -1;
	}

	private int getTypeOfInitialWeights(String initWgtString) {
		if      (initWgtString == null)                    { return typeOfInitialWeights_discrimLearning; }
		else if (initWgtString.equalsIgnoreCase("zero"))   { return VotedPerceptron.ALL_ZERO; }
		else if (initWgtString.equalsIgnoreCase("random")) { return VotedPerceptron.RANDOM; }
		else if (initWgtString.equalsIgnoreCase("lcr"))    { return VotedPerceptron.LOG_COUNTS_RATIO; }
		Utils.error("Unknown value: " + initWgtString);
		return -1;
	}

	private int getTypeOfEstimation(String typeOfEstimation) {
		if      (typeOfEstimation == null)                  { return typeOfEstimation_votedPerceptron; } 
		else if (typeOfEstimation.equalsIgnoreCase("sat"))  { return VotedPerceptron.SATinfer; }
		else if (typeOfEstimation.equalsIgnoreCase("mcmc")) { return  VotedPerceptron.MCMC; }
		else if (typeOfEstimation.equalsIgnoreCase("pl"))   { return  VotedPerceptron.PSEUDO_LIKELIHOOD; }
		Utils.error("Unknown value: " + typeOfEstimation);
		return -1;
	}

	public static void main(String[] args) {
		args = Utils.chopCommentFromArgs(args);
		WeightLearner wgtLearner = new WeightLearner();		
		wgtLearner.learnWgts(args);
	}
}
