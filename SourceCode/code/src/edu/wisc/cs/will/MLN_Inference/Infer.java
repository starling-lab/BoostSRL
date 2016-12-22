package edu.wisc.cs.will.MLN_Inference;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.MLN_Task.GroundLiteral;
import edu.wisc.cs.will.MLN_Task.GroundedMarkovNetwork;
import edu.wisc.cs.will.MLN_Task.MLN_Task;
import edu.wisc.cs.will.MLN_Task.MLNreductionProblemTooLargeException;
import edu.wisc.cs.will.MLN_Task.ProcessCommandLineString;
import edu.wisc.cs.will.MLN_Task.TimeStamp;
import edu.wisc.cs.will.MLN_Task.Wrapper;
import edu.wisc.cs.will.Utils.Utils;

/**
 * This is the main file for doing inference via command-line interaction.
 * 
 * Sample command-line arguments:
 * 
 *  -dir ../Testbeds/concussion/ -theory concussion_theory.txt -modes concussion_bk.txt -pf concussion_facts.txt -h hurt/1 -q unhurt/1 -brute -dribble
 *  -dir ../Testbeds/concussion/ -theory concussion_theory.txt -modes concussion_bk.txt -pf concussion_facts.txt -q hurt/1             -brute -dribble
 *  
 *  -dir ../Testbeds/univ/                            -theory univ.mln            -pf univ_pos_evidence.db                  -q advisedBy/2,professor/1,student/1  -gibbs -dribble
 *  -dir ../Testbeds/citeseer/ -modes citeseer_bk.txt -theory citeseer_theory.txt -pf citeseer_facts.txt                    -q InField/3,SameBib/2                -ms    -dribble
 *  -dir ../Testbeds/cora/     -modes cora_bk.txt     -theory cora_theory.txt     -pf cora_facts.txt                        -q InField/3,SameBib/2                -ms    -dribble
 *
 *  -dir ../Testbeds/advised_small/ -modes test.db    -theory univ.mln            -p  hasPosition/2,publication/2,inPhase/2 -q  advisedBy/2,student/1,professor/1 -ms    -dribble
 *  -dir ../Testbeds/smoking/       -modes test.db    -theory smoking.mln         -pf pos.mln -nf neg.mln                   -qf query.mln                         -ms    -dribble
 *
 * STILL IN OLD STYLE
 * -i ../Testbeds/chunk59/chunk59.mln    -dp ../Testbeds/chunk59/g1500_s0.db   -q  in_bin/3 -e teammateDistanceToGoalie_inRange/3,distanceToGoalie_inRange/3,angleToGoalPartAndGoalie_inRange/3,distanceToTeammate_inRange/3,distanceToGoalPart_inRange/3,angleToTeammateAndGoalie_inRange/3,angleFromTopRight_inRange/3,teammateDistanceToGoal_inRange/3,differentShotLocations/2,oppositeShotLocations/2,timeLeft_inRange/3,equals/2 -gibbs
 * 
 * @author pavan and shavlik
 * 
 */
public class Infer extends AllOfInference {
	private static final int debugLevel  = 0;
	
	private HandleFOPCstrings        stringHandler         = new HandleFOPCstrings();
	private FileParser               parser                = new FileParser(stringHandler);
	private MLN_Task                 task                  = new MLN_Task(  stringHandler);
	private GroundedMarkovNetwork    groundedMarkovNetwork = null;
	private ProcessCommandLineString commandLineProcessor  = new ProcessCommandLineString(stringHandler, parser, task);
	
	// To avoid circularities in projects, need to store these here (TODO - clean up). 
	private int     burninSteps           = MCMCInference.burnInSteps_default;
	private int     maxMCMCSteps          = MCMCInference.maxMCMCsteps_default;	
	private int     numberMCMCtrials      = MCMCInference.numberOfMCMCtrials_default;
	private int     numbStarts_SAT        = SAT.maxNumberOfStarts_default;
	private int     numbStepsPerStart_SAT = SAT.maxNumberOfFlips_default;
	private double  temperatureSA         = SampleSAT.temperatureSA_default;
	private double  probOfWalkSAT         = SampleSAT.probOfWalkSAT_default;
	private int     maxNumStepsAfterSoln_sampleSAT = SampleSAT.maxNumStepsAfterSoln_sampleSAT_default;
	private boolean doingLazyInference    = false;

	
	public Infer() {
	}
	
	private List<InferenceResult> inference(String[] args) {
		long startTime = System.currentTimeMillis();
			
		List<Sentence> precomputeThese = parser.getSentencesToPrecompute(0); // Note that this is the set of ALL precompute's encountered during any file reading.
		if (precomputeThese != null) { // Note: these can be more than ONE list of sentences to precompute, so need to use all.
			Utils.println("Have " + precomputeThese.size() + " sentences to precompute.  ***** THIS IS NOT YET IMPLEMENTED. ****");
			Utils.waitHere();
		}	
		
		// Process the command-line arguments.
		commandLineProcessor.processOptions(args);			
		
		// Some sanity checks on command-line parameters.
		if (task.getQueryLiterals() == null && task.getQueryPredNames() == null && !commandLineProcessor.interactive)  { Utils.error("No query literal information was entered.");	}
		if (task.getTotalNumberOfClauses() < 1) { Utils.error("No clauses have been supplied."); }
		
		// If the user hasn't supplied any negative-evidence ground literals, we use the closed-world assumption.
		task.setClosedWorldAssumption(task.getNegEvidenceLiterals() == null);
		
		if (commandLineProcessor.interactive) { readEvalPrint(); }		
		if (debugLevel > -10) {
			Utils.println("\n% Number of clauses: "               + Utils.comma(task.getTotalNumberOfClauses()));
			Utils.println(  "% Number of query ground literals: " + Utils.comma(Utils.getSizeSafely(task.getQueryLiterals())));
			if (task.getPosEvidenceLiterals() == null) { Utils.println("% There is no positive evidence."); }
			else { Utils.println("% Number of positive-evidence literals: " + Utils.comma(task.getPosEvidenceLiterals())); }
			if (task.isClosedWorldAssumption(null))    { Utils.println("% Using the closed-world assumption."); }
			else {				                         Utils.println("% Not using-closed world assumption."); }
			if (task.getNegEvidenceLiterals() == null) { Utils.println("% There is no explicit negative evidence."); }
			else { Utils.println("Number of negative-evidence literals: " + Utils.comma(task.getNegEvidenceLiterals())); }
			if (commandLineProcessor.inferenceAlgo == ProcessCommandLineString.GIBBS || commandLineProcessor.inferenceAlgo == ProcessCommandLineString.MC_SAT) {
				Utils.println("% Max number of burn-in steps = " + Utils.comma(burninSteps));
				Utils.println("% Max number of MCMC steps    = " + Utils.comma(maxMCMCSteps));
			}
			Utils.println("");
		}
		long middleTime = System.currentTimeMillis();	
		List<InferenceResult> result = infer();
		long endTime    = System.currentTimeMillis();
		if (debugLevel > -10) {
			Utils.println("\n% Time for inference: " + Utils.convertMillisecondsToTimeSpan(endTime - middleTime, 3) + ".");
			Utils.println(  "% Total time:         " + Utils.convertMillisecondsToTimeSpan(endTime -  startTime, 3) + ".");
		}
		return result;
	}
	public List<InferenceResult> infer() {
		return infer(null);
	}
	private List<InferenceResult> infer(Map<GroundLiteral,String> documentationForQueries) {
		// Start the inference algorithm.
		Inference infer = null;
		long   start = System.currentTimeMillis();
		long   end;
		if (groundedMarkovNetwork == null) {
			groundedMarkovNetwork = task.createReducedNetwork();
			if (debugLevel > -10) {
				end       = System.currentTimeMillis();
				Utils.println("\n%   Took " + Utils.convertMillisecondsToTimeSpan(end - start, 3) + " to create the grounded network.");
			//	Utils.waitHere();
				start = end;
			}
		//	Utils.waitHere("Ready to collect the remaining groundings."); 
			doingLazyInference = groundedMarkovNetwork.prepareForInference(new TimeStamp("infer")); // TODO - do this automatically?
			if (debugLevel > -10) {
				end       = System.currentTimeMillis();
				Utils.println("\n%   Took " + Utils.convertMillisecondsToTimeSpan(end - start, 3) + " to " + (doingLazyInference ? " prepare for lazy inference." : " fully ground the reduced MarkovNetwork instance."));
				start = end;
			}
		}
		
		switch(commandLineProcessor.inferenceAlgo) {
			case ProcessCommandLineString.BRUTE_FORCE:
				if (doingLazyInference) { Utils.error("Lazy brute-force inference has not yet been implemented."); }
				Utils.println("% Starting brute-force inference ...");
				infer = new BruteForceInference(groundedMarkovNetwork);
				break;
			case ProcessCommandLineString.GIBBS:
				if (doingLazyInference) { Utils.error("Lazy Gibbs inference has not yet been implemented."); }
				Utils.println("% Starting Gibbs inference ...");
				infer = new GibbsInference(groundedMarkovNetwork,
										   commandLineProcessor.choose(burninSteps,      commandLineProcessor.burninSteps),
										   commandLineProcessor.choose(maxMCMCSteps,     commandLineProcessor.maxMCMCSteps),
										   commandLineProcessor.choose(numberMCMCtrials, commandLineProcessor.numberMCMCtrials));
				break;
			case ProcessCommandLineString.MC_SAT:
				Utils.println("% Starting MC_SAT inference ...");
				infer = new MCSATInference(groundedMarkovNetwork, MCMCInference.prior_for_being_true_default, 
										   commandLineProcessor.choose(burninSteps,                    commandLineProcessor.burninSteps),
										   commandLineProcessor.choose(maxMCMCSteps,                   commandLineProcessor.maxMCMCSteps),
										   commandLineProcessor.choose(numberMCMCtrials,               commandLineProcessor.numberMCMCtrials),
										   commandLineProcessor.choose(numbStarts_SAT,                 commandLineProcessor.numbStarts_SAT),
										   commandLineProcessor.choose(numbStepsPerStart_SAT,          commandLineProcessor.numbStepsPerStart_SAT),
										   commandLineProcessor.choose(probOfWalkSAT,                  commandLineProcessor.probOfWalkSAT),
										   commandLineProcessor.choose(temperatureSA,                  commandLineProcessor.temperatureSA),
										   commandLineProcessor.choose(maxNumStepsAfterSoln_sampleSAT, commandLineProcessor.maxNumStepsAfterSoln_sampleSAT));
				break;
		}
		
		List<InferenceResult> result = null;
		try {
			result = infer.findQueryState(task.getQueryLiterals(), documentationForQueries);
		} catch (MLNreductionProblemTooLargeException e) {
			Utils.reportStackTrace(e);
			Utils.error("Problem too large ...");
		}
		if (debugLevel > 1) {
			end       = System.currentTimeMillis();
			Utils.println("\n%   Took " + Utils.convertMillisecondsToTimeSpan(end - start, 3) + " to find all the query states.");
			start = end;
		}
		if (task.getQueryLiterals() != null) for (GroundLiteral lit : task.getQueryLiterals()) {
			lit.setValueOnly(true, null); // The probabilities are for the case when the value of these literals = true, so set that to avoid confusion.
		}
		Utils.println("\n% *********************");
		Utils.println(  "% Results of inference:");
		Utils.println(  "% *********************");
		infer.displayOutput();
		return result;
	}
	
	private void readEvalPrint() {
		BufferedReader br     = new BufferedReader(new InputStreamReader(System.in));
		boolean        quit   = false;
		stringHandler         = new HandleFOPCstrings();
		task                  = new MLN_Task(stringHandler);
		do {
			String line = "";
			try {
				Utils.println("Enter the query literals on a single line delimited by commas.");
				Utils.flush();
				line = br.readLine();
				String queryStr = commandLineProcessor.formatLine(line);				
				Set<Literal> queryLiterals = new HashSet<Literal>(Wrapper.convertStringToLiteralList(queryStr, parser, stringHandler));
				task.setQueryLiterals(queryLiterals, false); // Allow overriding of previous query.
				infer();
				Utils.println("Do you want to continue? ");
				Utils.flush();
				line = br.readLine();
				if (line.equalsIgnoreCase("done") || line.equalsIgnoreCase("done;") || line.equalsIgnoreCase("done.") ||
					line.equalsIgnoreCase("quit") || line.equalsIgnoreCase("quit;") || line.equalsIgnoreCase("quit.") ||
					line.equalsIgnoreCase("exit") || line.equalsIgnoreCase("exit;") || line.equalsIgnoreCase("exit.") ||
					line.equalsIgnoreCase("halt") || line.equalsIgnoreCase("halt;") || line.equalsIgnoreCase("halt.") ||
					line.equalsIgnoreCase("no")   || line.equalsIgnoreCase("no;")   || line.equalsIgnoreCase("no.")) {
					quit = true;
				}
			} catch (IOException e) { Utils.error("Error while reading line: " + line); }
		} while (!quit);
		System.exit(0);		
	}
	
	public static void main(String[] args) {
		args = Utils.chopCommentFromArgs(args);
		Infer instance = new Infer();
		instance.stringHandler.numberOfLiteralsPerRowInPrintouts = 4;
		instance.inference(args);
	}
}