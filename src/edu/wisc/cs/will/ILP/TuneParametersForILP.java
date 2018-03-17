package edu.wisc.cs.will.ILP;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.wisc.cs.will.FOPC.PredicateName;
import edu.wisc.cs.will.FOPC.RelevanceStrength;
import edu.wisc.cs.will.FOPC.RelevantLiteral;
import edu.wisc.cs.will.FOPC.Theory;
import edu.wisc.cs.will.FOPC.TypeSpec;
import edu.wisc.cs.will.Utils.MessageType;
import edu.wisc.cs.will.Utils.Stopwatch;
import edu.wisc.cs.will.Utils.TimeScale;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

/**
 * This is the default ONION class.  If is necessary to have the 
 * successive parameter settings get more complicated, the user can set onionLayers
 * or a programmer can 'wrap' on another class ala' a real onion.  TODO - allow the setting of Beta rather than using F1 all the time.
 * 
 * @author shavlik
 * 
 */

public class TuneParametersForILP {
	protected final static int debugLevel = 2; // Used to control output from this project (0 = no output, 1=some, 2=much, 3=all).
	
	private boolean giveItTheCollegeTry = true; // If true, try one last fast run when no good solution can be found.
	private double  finalMinPrecision   = -1; // If in [0,1) will use this for one last run when no good solution can be found.
	private int     finalMinPosCoverage = -1;
	private int     finalMaxLength      = -1;
	
	// The following, if true, overrides forLengthsLessThanThisOnlyFitTrainSet.
	private boolean useSingleTrainTuneSplit = false; // This is a special case, where ONE FOLD is used and split into disjoint TRAIN and TUNE sets (though if TUNE set it empty, then the TRAIN SET is also used as the TUNE set; results on the TUNE are used to choose parameters).
	private double  firstTrainExample       = 0.0;   // These define how the train and tune sets will be carved out of the training examples.  These numbers are FRACTIONS (ie, so relative to dataset size).  Examples that are in both [firstTrain,lastTrain] and [firstTune,lastTune] go into the TRAIN SET.  If the tune set if empty, the train set is also used as the tune set.  Both pos and neg are processed identically.
	private double  lastTrainExample        = 1.0;
	private double  firstTuneExample        = 0.0;
	private double  lastTuneExample         = 1.0;
	public void setSingleTrainTuneSplitRanges(double firstTrainExample, double lastTrainExample, double firstTuneExample, double lastTuneExample) {
		this.firstTrainExample = firstTrainExample;
		this.lastTrainExample  = lastTrainExample;
		this.firstTuneExample  = firstTuneExample;
		this.lastTuneExample   = lastTuneExample;
	}

	// Choose one of these as what are trying to maximize.
	public enum ReasonToStopEarly { useBestPrecisionToStopEarly, useBestRecallToStopEarly, useBestAccuracyToStopEarly, useBestF1toStopEarly }
	public      ReasonToStopEarly theReasonToStopEarly = ReasonToStopEarly.useBestF1toStopEarly;
	
	private OnionFilter  filter = null;
	private ILPouterLoop outerLooper;
	
	// Already enough input parameters are being supported, so make this be user set-able.  Defaults to one hour.
	private int    maxSecondsToSpend = 60 * 60; // If negative, no limit.  Otherwise do not start another setting if this many seconds have been expended. 
	private long   start, startLastCombo; // Units are milliseconds.
	
	public List<ILPparameterSettings> onionLayers; // The list of onionLayers to try.
	public ILPparameterSettings       bestSetting;	
	public String                     descriptionOfOnionProcessingNeeded = null;
	public CrossValidationResult   bestResults;
	public boolean                    bestBasedOnCrossValidation = true;
	public Set<RelevantLiteral>       relevantLiterals;
	
	
	// These control the onionLayers considered.
	// Can set these as follows in files read in by the parser, for example:
	//		setParam: numbersOfClausesToTry = "1, 2, 4, 8, 16".
	//		setParam: lengthsToTry          = "1, 2, 3, 7, 10, 100";
	//	    setParam: forLengthsLessThanThisOnlyFitTrainSet = 5;
	
	//TODO add setParam for numberOfMaxNodesToConsiderLevels
	
	public int[]    numbersOfClausesToTry   = {1, 3, 15}; // TODO - more clauses won't help minPrecision of the theory.  And maybe not the accuracy.  Determine even if 100% accuracy on the UNCOVERED EXAMPLES would meet the spec.  If not, skip. (This is done for CV, not other Onion things, such as allowing more clauses.)
	public int[]    lengthsToTry            = {1, 3, 7};
    public double[] minimumPrecisionToTry   = {0.99, 0.90, 0.75, 0.00}; // Use 0.0 as the last value (using 0.5 should produce same behavior) - the minimum-precision calculation will be used based on the number of positive and negative examples.
    public int      numberOfMaxNodesToConsiderLevels = 3; // From N equals this DOWN TO 1, divide maxNodesToConsider and maxNodesToCreate by 10^(N-1).  [Use 2^(N-1)?]
    
    public boolean tryFlipFloppingExamples               = true;
	public int     forLengthsLessThanThisOnlyFitTrainSet =  100; // Override cross validation in these cases.  NOTE: DEFAULT SET SPECIALLY FOR THE MLj 2010 PAPER WHERE WE USE THE FIRST 100 EXAMPLES FOR TRAINING AND THE SECOND 100 FOR TESTING.
		
	// These determine when we have an acceptable rule set and, hence, can stop considering variations.  (If these don't stop things, then the settings with the best F1 score is returned [TODO allow things other than F1]).
	// NOTE: these also serve as the minimal ACCURACY (of a full theory) in order to stop.
	public double minimalTrainSetWeightedPrecisionToStop        = 0.99; // If negative, don't compute train-set accuracy.         Note: specific onionLayers can override.
	public double minimalTrainSetWeightedRecallToStop           = 0.99; // Remember scores are adjusted by the m-estimates.
	public double minimalTrainSetWeightedF1toStop               = 0.99;
	public double minimalTrainSetWeightedAccuracyToStop         = 0.99;
	public double minimalCrossValidationWeightedPrecisionToStop = 0.99; // If negative, don't compute cross-validation accuracy.  Note: specific onionLayers can override.
	public double minimalCrossValidationWeightedRecallToStop    = 0.99;
	public double minimalCrossValidationWeightedF1toStop        = 0.99; 
	public double minimalCrossValidationWeightedAccuracyToStop  = 0.99;

	public  int maxNumbExamplesToUseLeaveOneOut = 25; // These cannot be read via the parser's setParam (since doesn't seem necessary).
	public  int defaultNforCrossValidation      = 10; // These cannot be read via the parser's setParam (since doesn't seem necessary).
	private int numberOfFoldsToUse              = -1; // If negative look at number of examples to decide.   This can be set via setParam HOWEVER if it has been passed in to a constructor, the passed-in value will take precedence.

	private CrossValidationFoldResult bestFold; // When doing N-fold cross validation to select parameter, we might want to have ONE model to use (alternately, the caller can use the best settings and do more more training run).
	
	// Lots of constructor options.
	public TuneParametersForILP(ILPouterLoop outerLooper) {
		this.outerLooper = outerLooper;
		onionLayers     = new ArrayList<ILPparameterSettings>(8);
		relevantLiterals = outerLooper.innerLoopTask.stringHandler.getCollectionOfRelevantLiterals();
	}
	public TuneParametersForILP(ILPouterLoop outerLooper, int numberOfFoldsToUse) {
		this.outerLooper        = outerLooper;
		this.numberOfFoldsToUse = numberOfFoldsToUse;
		onionLayers     = new ArrayList<ILPparameterSettings>(8);
		relevantLiterals = outerLooper.innerLoopTask.stringHandler.getCollectionOfRelevantLiterals();
	}
	public TuneParametersForILP(ILPouterLoop outerLooper, int numberOfFoldsToUse, Set<RelevantLiteral> relevantLiterals) {
		this(outerLooper, numberOfFoldsToUse);
		this.relevantLiterals = relevantLiterals;
	}
	public TuneParametersForILP(ILPouterLoop outerLooper, Set<RelevantLiteral> relevantLiterals) {
		this(outerLooper);
		this.relevantLiterals = relevantLiterals;
	}
	public TuneParametersForILP(ILPouterLoop outerLooper, double minimalCrossValidationWeightedPrecisionToStop) {
		this(outerLooper);
	//	this.minimalTrainSetWeightedPrecisionToStop        = minimalTrainSetWeightedPrecisionToStop;  PROBABLY THIS WON'T BE SET TOO OFTEN, SO DON'T CLUTTER THE ARGUMENTS.  USER CAN EXPLICITLY SET.
		this.minimalCrossValidationWeightedPrecisionToStop = minimalCrossValidationWeightedPrecisionToStop;
	}
	public TuneParametersForILP(ILPouterLoop outerLooper, int numberOfFoldsToUse, double minimalCrossValidationWeightedPrecisionToStop) {
		this(outerLooper, numberOfFoldsToUse);
	//	this.minimalTrainSetWeightedPrecisionToStop        = minimalTrainSetWeightedPrecisionToStop;  PROBABLY THIS WON'T BE SET TOO OFTEN, SO DON'T CLUTTER THE ARGUMENTS.  USER CAN EXPLICITLY SET.
		this.minimalCrossValidationWeightedPrecisionToStop = minimalCrossValidationWeightedPrecisionToStop;
	}
	public TuneParametersForILP(ILPouterLoop outerLooper, Set<RelevantLiteral> relevantLiterals, double minimalCrossValidationWeightedPrecisionToStop) {
		this(outerLooper, minimalCrossValidationWeightedPrecisionToStop);
		this.relevantLiterals = relevantLiterals;
	}
	public TuneParametersForILP(ILPouterLoop outerLooper, int numberOfFoldsToUse, Set<RelevantLiteral> relevantLiterals, double minimalCrossValidationWeightedPrecisionToStop) {
		this(outerLooper, numberOfFoldsToUse, minimalCrossValidationWeightedPrecisionToStop);
		this.relevantLiterals = relevantLiterals;
	}
	public TuneParametersForILP(ILPouterLoop outerLooper, List<ILPparameterSettings> combinations) {
		this.outerLooper  = outerLooper;
		this.onionLayers = combinations;
		relevantLiterals  = outerLooper.innerLoopTask.stringHandler.getCollectionOfRelevantLiterals();
	}
	public TuneParametersForILP(ILPouterLoop outerLooper, int numberOfFoldsToUse, List<ILPparameterSettings> combinations) {
		this.outerLooper  = outerLooper;
		this.numberOfFoldsToUse = numberOfFoldsToUse;
		this.onionLayers = combinations;
		relevantLiterals  = outerLooper.innerLoopTask.stringHandler.getCollectionOfRelevantLiterals();
	}
	public TuneParametersForILP(ILPouterLoop outerLooper, List<ILPparameterSettings> combinations, double minimalCrossValidationWeightedPrecisionToStop) {
		this(outerLooper, combinations);
	//	this.minimalTrainSetWeightedPrecisionToStop        = minimalTrainSetWeightedPrecisionToStop; // See comment above.
		this.minimalCrossValidationWeightedPrecisionToStop = minimalCrossValidationWeightedPrecisionToStop;
	}
	public TuneParametersForILP(ILPouterLoop outerLooper, int numberOfFoldsToUse, List<ILPparameterSettings> combinations, double minimalCrossValidationWeightedPrecisionToStop) {
		this(outerLooper, numberOfFoldsToUse, combinations);
	//	this.minimalTrainSetWeightedPrecisionToStop        = minimalTrainSetWeightedPrecisionToStop; // See comment above.
		this.minimalCrossValidationWeightedPrecisionToStop = minimalCrossValidationWeightedPrecisionToStop;
	}
	// These next constructors allow the caller to provide the 'layers of the Onion.' 
	public TuneParametersForILP(ILPouterLoop outerLooper, Set<RelevantLiteral> relevantLiterals, List<ILPparameterSettings> combinations) {
		this.outerLooper = outerLooper;
		if (combinations == null) { Utils.error("Should not call this with combinations = null."); } 
		this.onionLayers     = combinations;
		this.relevantLiterals = relevantLiterals;
	}
	public TuneParametersForILP(ILPouterLoop outerLooper, int numberOfFoldsToUse, Set<RelevantLiteral> relevantLiterals, List<ILPparameterSettings> combinations) {
		this.outerLooper = outerLooper;
		this.numberOfFoldsToUse = numberOfFoldsToUse;
		if (combinations == null) { Utils.error("Should not call this with combinations = null."); } 
		this.onionLayers     = combinations;
		this.relevantLiterals = relevantLiterals;
	}
	public TuneParametersForILP(ILPouterLoop outerLooper, Set<RelevantLiteral> relevantLiterals, List<ILPparameterSettings> combinations, double minimalCrossValidationWeightedPrecisionToStop) {
		this(outerLooper, relevantLiterals, combinations);
	//	this.minimalTrainSetWeightedPrecisionToStop        = minimalTrainSetWeightedPrecisionToStop; // See comment above.
		this.minimalCrossValidationWeightedPrecisionToStop = minimalCrossValidationWeightedPrecisionToStop;
	}
	public TuneParametersForILP(ILPouterLoop outerLooper, int numberOfFoldsToUse, Set<RelevantLiteral> relevantLiterals, List<ILPparameterSettings> combinations, double minimalCrossValidationWeightedPrecisionToStop) {
		this(outerLooper, numberOfFoldsToUse, relevantLiterals, combinations);
	//	this.minimalTrainSetWeightedPrecisionToStop        = minimalTrainSetWeightedPrecisionToStop; // See comment above.
		this.minimalCrossValidationWeightedPrecisionToStop = minimalCrossValidationWeightedPrecisionToStop;
	}
	
	/////////////////////////////////////////////////////////////////
	
	public void setFilter(OnionFilter filter) { // Enough input arguments, so require this to be separately set.
		this.filter = filter;
	}
	
	public int getNumberOfFoldsToUse() {
		return numberOfFoldsToUse;
	}
	public void setNumberOfFoldsToUse(int numberOfFoldsToUse) {
		this.numberOfFoldsToUse = numberOfFoldsToUse;
	}
	
	// Use some hard-wired default settings.
	private void setupDefaultParameterCombinations() {
		ILPparameterSettings temp  = null;
		List<RelevanceStrength> relevanceLevelsToTry = new ArrayList<RelevanceStrength>(1);		

		String   vStr  = null;
		List<String> items = null;
		vStr = outerLooper.innerLoopTask.stringHandler.getParameterSetting("numbersOfClausesToTry");
		if (vStr != null) { 
			String stripStr = vStr.replaceAll("\"|'", ""); // Drop the first and last quote marks.
			// This method can't handle leading or trailing quote marks as it can have conflicting meanings.
			// Quotes can be safely removed here because we know the inputs are only numbers.
			items = Utils.parseListOfStrings(stripStr);
			
			//Utils.waitHere("numbersOfClausesToTry = " + vStr + "  |items| = " + items.size());
			numbersOfClausesToTry = new int[items.size()];
			int counter = 0;
			for (String item : items) {
				numbersOfClausesToTry[counter++] = Integer.parseInt(item);
			}
		}
		vStr = outerLooper.innerLoopTask.stringHandler.getParameterSetting("lengthsToTry");
		if (vStr != null) {
			String stripStr = vStr.replaceAll("\"|'", ""); // Drop the first and last quote marks.
			items = Utils.parseListOfStrings(stripStr);
			//Utils.waitHere("lengthsToTry = " + vStr + "  |items| = " + items.size());
			lengthsToTry = new int[items.size()];
			int counter = 0;
			for (String item : items) {
				lengthsToTry[counter++] = Integer.parseInt(item.trim());
			}
		}
		vStr = outerLooper.innerLoopTask.stringHandler.getParameterSetting("tryFlipFloppingExamples");
		if (vStr != null) { tryFlipFloppingExamples = Boolean.parseBoolean(vStr); }
		vStr = outerLooper.innerLoopTask.stringHandler.getParameterSetting("forLengthsLessThanThisOnlyFitTrainSet");
		if (vStr != null) { forLengthsLessThanThisOnlyFitTrainSet = Integer.parseInt(vStr); }
		vStr = outerLooper.innerLoopTask.stringHandler.getParameterSetting("minimalTrainSetWeightedPrecisionToStop");
		if (vStr!= null) {                                                  minimalTrainSetWeightedPrecisionToStop = Double.parseDouble(vStr); }
		vStr = outerLooper.innerLoopTask.stringHandler.getParameterSetting("minimalTrainSetWeightedRecallToStop");
		if (vStr!= null) {                                                  minimalTrainSetWeightedRecallToStop    = Double.parseDouble(vStr); }
		vStr = outerLooper.innerLoopTask.stringHandler.getParameterSetting("minimalTrainSetWeightedAccuracyToStop");
		if (vStr!= null) {                                                  minimalTrainSetWeightedAccuracyToStop = Double.parseDouble(vStr); }
		vStr = outerLooper.innerLoopTask.stringHandler.getParameterSetting("minimalTrainSetWeightedF1toStop");
		if (vStr!= null) {                                                  minimalTrainSetWeightedF1toStop    = Double.parseDouble(vStr); }
		vStr = outerLooper.innerLoopTask.stringHandler.getParameterSetting("minimalTrainSetWeightedF1ToStop"); // Allow a likely misspelling.
		if (vStr!= null) {                                                  minimalTrainSetWeightedF1toStop    = Double.parseDouble(vStr); }
		vStr = outerLooper.innerLoopTask.stringHandler.getParameterSetting("minimalCrossValidationWeightedPrecisionToStop");
		if (vStr!= null) {                                                  minimalCrossValidationWeightedPrecisionToStop = Double.parseDouble(vStr); }
		vStr = outerLooper.innerLoopTask.stringHandler.getParameterSetting("minimalCrossValidationWeightedRecallToStop");
		if (vStr!= null) {                                                  minimalCrossValidationWeightedRecallToStop    = Double.parseDouble(vStr); }
		vStr = outerLooper.innerLoopTask.stringHandler.getParameterSetting("minimalCrossValidationWeightedAccuracyToStop");
		if (vStr!= null) {                                                  minimalCrossValidationWeightedAccuracyToStop = Double.parseDouble(vStr); }
		vStr = outerLooper.innerLoopTask.stringHandler.getParameterSetting("minimalCrossValidationWeightedF1toStop");
		if (vStr!= null) {                                                  minimalCrossValidationWeightedF1toStop    = Double.parseDouble(vStr); }
		vStr = outerLooper.innerLoopTask.stringHandler.getParameterSetting("minimalCrossValidationWeightedF1ToStop"); // Allow a likely misspelling.
		if (vStr!= null) {                                                  minimalCrossValidationWeightedF1toStop    = Double.parseDouble(vStr); }
		if (numberOfFoldsToUse < 0) { // See if the caller already set this.  If so, don't override.
			vStr = outerLooper.innerLoopTask.stringHandler.getParameterSetting("numberOfFoldsToUse");
			if (vStr!= null) {                                                  numberOfFoldsToUse = Integer.parseInt(vStr); }
		}
		
		int numberPosExamples = Utils.getSizeSafely(outerLooper.innerLoopTask.getPosExamples());
		int numberNegExamples = Utils.getSizeSafely(outerLooper.innerLoopTask.getNegExamples());
		int totalNumbExamples = numberPosExamples + numberNegExamples;
				
		// Decide which relevance levels to consider.
		if (relevantLiterals == null || outerLooper.innerLoopTask.isRelevanceEnabled() == false) {
			relevanceLevelsToTry.add(null); // This means use all.
		} else {
			boolean havePossibleAnswer     = false;
			boolean haveStrongestRelevance = false;
			boolean haveRelevance          = false;
			boolean haveMildestRelevance   = false;
			boolean haveNeutralRelevance   = false;
			boolean haveIrrelevance        = false;

            if ( outerLooper.innerLoopTask.isRelevanceEnabled() ) {

                Stopwatch s = new Stopwatch();
                Utils.println("% [Onion] Generating advice to determine onion levels.");

                LearnOneClause learnOneClause = outerLooper.innerLoopTask;

                int oldClauseIndex = learnOneClause.getAdviceProcessor().getAnonymousClauseIndex();
                int oldLevel = AdviceProcessor.debugLevel;
                AdviceProcessor.debugLevel = 0;

                ActiveAdvice activeAdvice = learnOneClause.getAdviceProcessor().getActiveAdvice(RelevanceStrength.getWeakestRelevanceStrength(), learnOneClause.getPosExamples(), learnOneClause.getNegExamples());

                havePossibleAnswer = activeAdvice.hasActiveAdvice(RelevanceStrength.getStrongestRelevanceStrength(true), RelevanceStrength.getStrongestRelevanceStrength(false));
                haveStrongestRelevance = activeAdvice.hasActiveAdvice(RelevanceStrength.getStrongestRelevanceStrength(false), RelevanceStrength.getDefaultRelevanceStrength());
                haveRelevance = activeAdvice.hasActiveAdvice(RelevanceStrength.getDefaultRelevanceStrength(), RelevanceStrength.getMildestPositiveRelevanceStrength());
                haveMildestRelevance = activeAdvice.hasActiveAdvice(RelevanceStrength.getMildestPositiveRelevanceStrength(), RelevanceStrength.getNeutralRelevanceStrength());
                haveNeutralRelevance = activeAdvice.hasActiveAdvice(RelevanceStrength.getNeutralRelevanceStrength(), RelevanceStrength.getMildestNegativeRelevanceStrength());
                haveIrrelevance = activeAdvice.hasActiveAdvice(RelevanceStrength.getMildestNegativeRelevanceStrength(), RelevanceStrength.getWeakestRelevanceStrength());

                learnOneClause.getAdviceProcessor().retractRelevanceAdvice();

                learnOneClause.getAdviceProcessor().setAnonymousClauseIndex(oldClauseIndex);

                Utils.println("% [Onion] Advice generation and checking complete (" + TimeScale.MILLSECOND.getBestFormattedString(s.getTotalTimeInMilliseconds(), "%.2f%s") + ").");

                AdviceProcessor.debugLevel = oldLevel;
            }
			
            for (RelevantLiteral rf : relevantLiterals) {
                if (outerLooper.innerLoopTask.checkForBodyMode(rf.getPName(), rf.getArity()) && outerLooper.innerLoopTask.getProver().getClausebase().checkForPossibleMatchingAssertions(rf.getPName(), rf.getArity())) {
                    if (debugLevel > 1) {
                        Utils.println("% setDefaultParameterSettingsToConsider: Have this relevance literal = " + rf.getPName() + "/" + rf.getArity() + " " + rf);
                    }
                    if (!novelLiteral(rf.getPName())) {
                    }
                    else if (rf.atLeastThisRelevant(RelevanceStrength.getStrongestRelevanceStrength(true))) {
                        havePossibleAnswer = true;
                    }
                    else if (rf.atLeastThisRelevant(RelevanceStrength.getStrongestRelevanceStrength(false))) {
                        haveStrongestRelevance = true;
                    }
                    else if (rf.atLeastThisRelevant(RelevanceStrength.getDefaultRelevanceStrength())) {
                        haveRelevance = true;
                    }
                    else if (rf.atLeastThisRelevant(RelevanceStrength.getMildestPositiveRelevanceStrength())) {
                        haveMildestRelevance = true;
                    }
                    else if (rf.atLeastThisRelevant(RelevanceStrength.getNeutralRelevanceStrength())) {
                        haveNeutralRelevance = true;
                    }
                    else if (rf.atMostThisRelevant(RelevanceStrength.getMildestNegativeRelevanceStrength())) {
                        haveIrrelevance = true;
                    }
                }
                else {
                    if (debugLevel > -1) {
                        Utils.println("% setDefaultParameterSettingsToConsider: Have IGNORED (possibly because no mode has been defined) this relevance literal = " + rf.getPName() + "/" + rf.getArity() + " " + rf);
                    }
                }
            }
			if (!haveNeutralRelevance) {// This is trickier since some can be by default.
				haveNeutralRelevance = ILPparameterSettings.modeExistsNotInTheseRelevances(relevantLiterals, outerLooper.innerLoopTask.stringHandler.getKnownModes());
			}
			
			// First use only Possible-Answer's, which combine ALL positive and negative examples.
			if (havePossibleAnswer)                    { relevanceLevelsToTry.add(RelevanceStrength.getStrongestRelevanceStrength(true));   } // Only the COMBINED-EVERYTHING rules.
			// Next use relevance about individual examples as well.
		//	if (haveStrongestRelevance)                { relevanceLevelsToTry.add(RelevanceStrength.getStrongestRelevanceStrength(false));  } // Include combined rules about individual examples.
			// Next see if any other relevance statements.
			if (haveRelevance || haveMildestRelevance) { relevanceLevelsToTry.add(RelevanceStrength.getMildestPositiveRelevanceStrength()); } // Anything mentioned in relevance.
			// See if any neutral relevance.
			if (haveNeutralRelevance) { relevanceLevelsToTry.add(haveIrrelevance ? RelevanceStrength.NEUTRAL : null); } // If no irrelevance, can use everything here.
			// Finally, use everything.
			if (haveIrrelevance)      { relevanceLevelsToTry.add(null); }

			if (debugLevel > -2) {
				Utils.println("% havePossibleAnswer     = " + havePossibleAnswer);
				Utils.println("% haveStrongestRelevance = " + haveStrongestRelevance);
				Utils.println("% haveRelevance          = " + haveRelevance);
				Utils.println("% haveMildestRelevance   = " + haveMildestRelevance);
				Utils.println("% haveNeutralRelevance   = " + haveNeutralRelevance);
				Utils.println("% haveIrrelevance        = " + haveIrrelevance);
			//	Utils.waitHere("check out the above");
			}
		}

		// TODO - consider using 'features in previous lesson' etc.
		int maxNumberOfClauses = Math.max( 100, outerLooper.maxNumberOfClauses);
		int maxBodyLength      = Math.max(  50, outerLooper.innerLoopTask.maxBodyLength);
		int maxNodes           = Math.max( 100, outerLooper.innerLoopTask.getMaxNodesToCreate());
		int maxNodesToExpand   = Math.max( 100, outerLooper.innerLoopTask.getMaxNodesToConsider());
		int numPosExamples     = outerLooper.getNumberOfPosExamples(); // These are zero, so we're asking too early.  TODO
		int numNegExamples     = outerLooper.getNumberOfNegExamples();
	//	int numberOfFolds      = (numberOfFoldsToUse > 0 ? numberOfFoldsToUse : getNumberOfFoldsToUse(numPosExamples + numNegExamples));
		if (numNegExamples < numPosExamples / 2 && numNegExamples < 3) { tryFlipFloppingExamples = false; } // Don't flip flop with so few negatives.
	//	if (numberOfFolds < 1) { throw new Error("Have number of folds = " + numberOfFolds); }
		double holdMestPos = outerLooper.innerLoopTask.getMEstimatePos();
		double holdMestNeg = outerLooper.innerLoopTask.getMEstimateNeg();
		int counter = 1;
		// Utils.waitHere("numbersOfClausesToTry = " + toStringIntArray(numbersOfClausesToTry) + ",  lengthsToTry = " + toStringIntArray(lengthsToTry));
		// Utils.waitHere("numPosExamples = " + numPosExamples + ", numNegExamples = " + numNegExamples);

		clearPreviousBestPrecision();
		if (numberOfMaxNodesToConsiderLevels < 1) { numberOfMaxNodesToConsiderLevels = 1; }
        for (double minimumPrecision : minimumPrecisionToTry) if (minimumPrecision >= 0.0 && minimumPrecision <= 1.0)  {
        	for (int maxNodesLevel = numberOfMaxNodesToConsiderLevels; maxNodesLevel >= 1; maxNodesLevel--) if (maxNodesLevel >= 0 && maxNodesLevel <= 100)  {
	        	for (RelevanceStrength minRelStrength : relevanceLevelsToTry)                                     {
	        		for (int clauses : numbersOfClausesToTry) if (clauses >= 1 && clauses <= maxNumberOfClauses)  {
	        			for (int length : lengthsToTry)       if (length  >= 0 && length  <= maxBodyLength)       {
	                    	for (int flipFlop = 0; flipFlop <= (tryFlipFloppingExamples ? 1 : 0); flipFlop++)     {	                    		
	                    		double minimumPrecisionToUse = minimumPrecision;
	                    		double bestPossiblePrecision = (flipFlop == 0 ? numPosExamples : numNegExamples) / (flipFlop == 0 ? numPosExamples + holdMestPos : numNegExamples + holdMestNeg);  // Make sure we don't exceed the score of a perfect rule (due to m-estimates).
	                            double alwaysGuessMajority   = (flipFlop == 0 ? numPosExamples : numNegExamples) / (numPosExamples + numNegExamples + holdMestPos + holdMestNeg); // TODO - these should all be WEIGHTED COUNTS (if they are not already).
	                            
	                    	//	Utils.println("minimumPrecisionA = " + minimumPrecisionToUse);
	                            if (alwaysGuessMajority < 0.5) { alwaysGuessMajority = 1 - alwaysGuessMajority; }
	                            minimumPrecisionToUse = Math.max(1 - 0.90 * (1 - alwaysGuessMajority), minimumPrecisionToUse); // Need to have no more than 90% of the error of always guessing the majority category.  If this is more than the previous precision level, we have already done this one.
	                            double minimumPrecisionForAcceptableTheory = Math.min(0.999 * bestPossiblePrecision, minimumPrecisionToUse); // This is also used for Recall, Accuracy, and F1; whichever is the chosen metric.
	                        //	Utils.println("minimumPrecisionB = " + minimumPrecisionToUse);
	                            minimumPrecisionToUse = Math.min(0.999 * bestPossiblePrecision, mapNumberOfClausesToMinPrecision(minimumPrecisionToUse, clauses)); // If we are going to learn multiple clauses, we can afford to be more precise on each one.
	                    	//	Utils.println("minimumPrecisionC = " + minimumPrecisionToUse);
	                            if (minimumPrecisionToUse >= getPreviousMinPrecision(clauses, length, flipFlop)) {
	                        //    	Utils.println("  skip because " + minimumPrecisionToUse + " >= " + getPreviousMinPrecision(clauses, length, flipFlop));
	                            	continue; 
	                            }
	                            int scaleMaxNodes = (int) Math.pow(10, maxNodesLevel); // Have some simple minimums (also see setMaxNodesToConsider below).  Seems that creating the root counts as node created (which makes sense), so dont have less than 2.	                            
	                            if (scaleMaxNodes > maxNodes || scaleMaxNodes > maxNodesToExpand) {
	                        //    	Utils.println("  skip because " + scaleMaxNodes + " > min(" + maxNodesToExpand + ", " + maxNodes + ")");
	                            	continue; 
	                            }
	                            // Don't do this correction until AFTER the above test or some odd behavior results (eg, the first layer might have more than 1 allowed clause).
	                            double bonusNodesForPrecision = Math.max(1.0, 2 - minimumPrecisionToUse); // As precision gets lower, allow creating/expanding a few more more nodes.
	                            int maxNodesToUse = (int) Math.max(2, bonusNodesForPrecision * maxNodes / scaleMaxNodes);  // Want these to be at least 1 (OK to check one [2?] node, the root - might quickly find a theory of all length-one rules).
	                            
	                        //  Utils.waitHere("  setting #" + counter + ", minRelStrength = " + minRelStrength + ", |clauses| = " + clauses + ",  maxLen = " + length + ", flip = " + flipFlop);
	                            temp = new ILPparameterSettings(outerLooper, this, getAnnotationString(counter, minimumPrecisionToUse, minRelStrength, clauses, length, flipFlop, maxNodesToUse));
	                            temp.setOnionLayer(counter);
                                temp.setMinPrecision(  minimumPrecisionToUse);
	                            setPreviousMinPrecision(clauses, length, flipFlop, minimumPrecisionToUse);
	                            temp.setMinPosCoverage(mapNumberOfClausesToMinPosCoverage(minimumPrecisionToUse, clauses));
                                temp.setMaxBodyLength(length);
	                            temp.setMaxNodesToCreate(  maxNodesToUse);
	                            temp.setMaxNodesToConsider(Math.max(10, maxNodesToExpand / scaleMaxNodes));
	                            temp.setMaxNegCoverage(outerLooper.innerLoopTask.getMaxNegCoverage()); // Do we want to change as function of some FOR LOOP item's value?
	                            temp.setMEstimatePos(flipFlop == 0 ? holdMestPos : holdMestNeg);
	                            temp.setMEstimateNeg(flipFlop == 0 ? holdMestNeg : holdMestPos);
	                            temp.setMaxNumberOfCycles(2*clauses); // Allow two tries per # of acceptable clauses.
	                            temp.setMaxNumberOfClauses( clauses);
	                            temp.onlyConsiderFeaturesAtLeastThisRelevant(minRelStrength);
	                            temp.setStarModeMap(chooseStarModeMap(minRelStrength, totalNumbExamples, numberPosExamples, clauses));
	                            if (!useSingleTrainTuneSplit && length < forLengthsLessThanThisOnlyFitTrainSet) {   // If great coverage with such a short clause, don't bother with cross validation.  TODO - rethink this.
	                                temp.setRunCrossValidation(false); //Utils.waitHere("trainset: " + forLengthsLessThanThisOnlyFitTrainSet);
	                                temp.setRunAllAsTrainSet(  true);
	                                temp.setMinPrecisionToStop(Math.min(minimalTrainSetWeightedPrecisionToStop, theReasonToStopEarly == ReasonToStopEarly.useBestPrecisionToStopEarly ? minimumPrecisionForAcceptableTheory : 1.0)); // This is for the full theory.
	                                temp.setMinRecallToStop(   Math.min(minimalTrainSetWeightedRecallToStop,    theReasonToStopEarly == ReasonToStopEarly.useBestRecallToStopEarly    ? minimumPrecisionForAcceptableTheory : 1.0)); // While minimumPrecisionToUse is per rule.
	                                temp.setMinAccuracyToStop( Math.min(minimalTrainSetWeightedAccuracyToStop,  theReasonToStopEarly == ReasonToStopEarly.useBestAccuracyToStopEarly  ? minimumPrecisionForAcceptableTheory : 1.0));
	                                temp.setMinF1toStop(       Math.min(minimalTrainSetWeightedF1toStop,        theReasonToStopEarly == ReasonToStopEarly.useBestF1toStopEarly        ? minimumPrecisionForAcceptableTheory : 1.0));
	                            } else {
	                                temp.setRunCrossValidation(true); //Utils.waitHere("cv" + forLengthsLessThanThisOnlyFitTrainSet);
	                                temp.setRunAllAsTrainSet(  false);
	                                temp.setMinPrecisionToStop(Math.min(minimalCrossValidationWeightedPrecisionToStop, theReasonToStopEarly == ReasonToStopEarly.useBestPrecisionToStopEarly ? minimumPrecisionForAcceptableTheory : 1.0)); // This is for the full theory.
	                                temp.setMinRecallToStop(   Math.min(minimalCrossValidationWeightedRecallToStop,    theReasonToStopEarly == ReasonToStopEarly.useBestRecallToStopEarly    ? minimumPrecisionForAcceptableTheory : 1.0)); // While minimumPrecisionToUse is per rule.
	                                temp.setMinAccuracyToStop( Math.min(minimalCrossValidationWeightedAccuracyToStop,  theReasonToStopEarly == ReasonToStopEarly.useBestAccuracyToStopEarly  ? minimumPrecisionForAcceptableTheory : 1.0));
	                                temp.setMinF1toStop(       Math.min(minimalCrossValidationWeightedF1toStop,        theReasonToStopEarly == ReasonToStopEarly.useBestF1toStopEarly        ? minimumPrecisionForAcceptableTheory : 1.0));
	                            }
	                            
	                //			Utils.waitHere("bestPossiblePrecision = " + bestPossiblePrecision + "  alwaysGuessMajority = " + alwaysGuessMajority + "  clauses = " + clauses + "  theReasonToStopEarly = " + theReasonToStopEarly + "  minPrecision = " + minimumPrecision);
	                            
	                            temp.setFlipFlopPosAndNegExamples(flipFlop == 1);
	                            temp.setModesToUse();
	                            if (filter == null || !filter.skipThisSetting(temp, true)) {
	                                Utils.println("%   Add combo #" + counter + (filter != null ? " via filter = '" + filter + "'." : "."));
                                    Utils.println("%     " + temp.toStringShort());
	                                onionLayers.add(temp);
	                            }
                                counter++; // In case we want to do something different after the first N settings.
	                        }
						}
					}
				}
        	}
		}
		if (Utils.getSizeSafely(onionLayers) < 1) {
			Utils.warning("No combinations survived the filter. So adding the last one encountered:\n%   " + temp);
			if (temp == null) {
				Utils.error("Had NO combinations to add!");
			} else {
				onionLayers.add(temp);  // If NO onionLayers survived, keep the last one.
			}
		}
		//Utils.waitHere("The Onion has been created.");
	}
	
	private Map<Integer,Double> bestPrecPerContext = new HashMap<Integer,Double>(32);
	private int getKeyForPreviousBestPrecision(int clauses, int length, int flipFlop) {
		return clauses + 1000 * length + flipFlop * 1000000;
	}
	private void clearPreviousBestPrecision() {	
		bestPrecPerContext = new HashMap<Integer,Double>(32);
	}
	private void setPreviousMinPrecision(int clauses, int length, int flipFlop,	double minimumPrecision) {
		int key = getKeyForPreviousBestPrecision(clauses, length, flipFlop);
		Double lookup = bestPrecPerContext.get(key);
		if (lookup != null) { if (lookup != minimumPrecision) Utils.println(MessageType.ONION_VERBOSE_LAYER_CREATION, "%  setPreviousMinPrecision: for key = " + key + ", oldValue = " + lookup + " and newValue = " + minimumPrecision + " but these should not be different."); }
		else { bestPrecPerContext.put(key, minimumPrecision); }
	}
	private double getPreviousMinPrecision(int clauses, int length, int flipFlop) {
		int key = getKeyForPreviousBestPrecision(clauses, length, flipFlop);
		Double lookup = bestPrecPerContext.get(key);
	//	Utils.println("% getPreviousMinPrecision: for key = " + key + ", the previous value is " + lookup);
		if (lookup != null) { return lookup; }
		return 1.0;
	}

	private Set<PredicateName> notNovelPnames = null;
	// We don't want Onion layers that ONLY uses these predicates.  They will either waste time or overfit (there is a small chance some tasks have true definitions expressed only using these). 
	private boolean novelLiteral(PredicateName pName) { // Also cross-check with Theory.simplify
		if (notNovelPnames == null)  {
			notNovelPnames = new HashSet<PredicateName>(16);
			notNovelPnames.add(outerLooper.innerLoopTask.stringHandler.getPredicateName("sameAs"));
			notNovelPnames.add(outerLooper.innerLoopTask.stringHandler.getPredicateName("different"));
			notNovelPnames.add(outerLooper.innerLoopTask.stringHandler.getPredicateName("isaInterestingNumber"));
			notNovelPnames.add(outerLooper.innerLoopTask.stringHandler.getPredicateName("isaInterestingSymbol"));
			notNovelPnames.add(outerLooper.innerLoopTask.stringHandler.getPredicateName("isaInterestingList"));
			notNovelPnames.add(outerLooper.innerLoopTask.stringHandler.getPredicateName("isaInterestingComposite"));          // NOTE: this is some leakage of the BL project into WILL.
			notNovelPnames.add(outerLooper.innerLoopTask.stringHandler.getPredicateName("isaDifferentInterestingComposite")); // NOTE: this is some leakage of the BL project into WILL.
			notNovelPnames.add(outerLooper.innerLoopTask.stringHandler.getPredicateName("isaDifferentInterestingNumber"));
			notNovelPnames.add(outerLooper.innerLoopTask.stringHandler.getPredicateName("isaDifferentInterestingSymbol"));
			notNovelPnames.add(outerLooper.innerLoopTask.stringHandler.getPredicateName("isaDifferentInterestingList"));
		}
		return !notNovelPnames.contains(pName);
	}
	

    private boolean checkForRelevantAdvice(ActiveAdvice activeAdvice, RelevanceStrength relevanceStrength) {
        
        return activeAdvice.hasActiveAdvice(relevanceStrength);
    }

	public boolean useStandardModeMapAlgo = true; // See comments below.
	private int chooseStarModeMap(RelevanceStrength minRelStrength, int totalNumbExamples, int numberPosExamples, int numberClauses) {	
	//	Utils.waitHere("totalNumbExamples=" + totalNumbExamples);
		if (useStandardModeMapAlgo) {			
			return (minRelStrength != null && minRelStrength.compareTo(RelevanceStrength.getDefaultRelevanceStrength()) >= 0
	                ?  TypeSpec.minusOrConstantMode
	                :  (totalNumbExamples < 1 || numberPosExamples >= 5 * numberClauses ? TypeSpec.minusOrConstantMode : TypeSpec.minusMode)); // If very few examples, make it harder to use constants.
		}
		// This one is tailored to the BL Year2 lessons, where often there was only one positive example.
		return (minRelStrength != null && minRelStrength.compareTo(RelevanceStrength.getDefaultRelevanceStrength()) >= 0
                ?  TypeSpec.novelMode  // Unless considering everything possible, don't use constants.  Some will come from isaInterestingSymbol/Number.
                :  (totalNumbExamples < 1 || numberPosExamples >= 5 * numberClauses ? TypeSpec.novelOrConstantMode : TypeSpec.novelMode)); // Don't use constants if have only a few positive examples, since too easy to fit.

	}
	
	private String getAnnotationString(int counter, double minPrecision, RelevanceStrength minRelStrength, int clauses, int length, int flipFlop, int maxNodesToUse) {
		// Return a string that gives a terse description of this Onion layer.
		String result = "ONION Layer #" + Utils.comma(counter) + (flipFlop > 0 ? ", flipped" : "") + ", minPrec=" + Utils.truncate(minPrecision, 2) + ", maxC=" + clauses + ", maxL=" + length + (minRelStrength == null ? "" : ", minRel=" + minRelStrength + ", maxNodes=" + (maxNodesToUse >= 1000 ? (maxNodesToUse / 1000) + "K" : maxNodesToUse));
		return result;
	}
	private double mapNumberOfClausesToMinPosCoverage(double numerator, int numbClauses) {
		int denominator = 1;
		if      (numbClauses >= 5) { denominator = 10; } // If numerator=1, then require 10% of positive examples be covered.
		else if (numbClauses >= 3) { denominator =  7; } // 14%
		else if (numbClauses == 2) { denominator =  5; } // 20%
		return numerator /  denominator;
	}
	private double mapNumberOfClausesToMinPrecision(double original, int numbClauses) {
		double multiplier = 1.0;
		if      (numbClauses >= 5) { multiplier = 1.100; } // Since the recall per rule will be lowered, we can afford to look for more accurate rules.
		else if (numbClauses >= 3) { multiplier = 1.050; } // These might be too low?
		else if (numbClauses == 2) { multiplier = 1.025; }
		return  Math.min(0.99999, multiplier * original); // Make sure it didn't get set too high (though this is also checked elsewhere).
	}
	
	public int getNumberOfFoldsToUse(int totalNumberOfExamples) { // Do leave-one-out unless a lot of examples.
		if (totalNumberOfExamples > maxNumbExamplesToUseLeaveOneOut) { return defaultNforCrossValidation; } // If a lot, do N-fold cross validation.
		return totalNumberOfExamples;		
	}
	
	public void run() throws SearchInterrupted {
		start = System.currentTimeMillis();
		if (Utils.getSizeSafely(onionLayers) < 1) {
			setupDefaultParameterCombinations();
		}
		if (Utils.getSizeSafely(onionLayers) < 1) { Utils.error("Need to have some combinations to tune parameters."); }
				
		int    counter               = 0;
		double bestScore             = Double.NEGATIVE_INFINITY; // Use this in case the FOR loops does NOT stop early.
		double bestTrainsetPrecision = Double.NEGATIVE_INFINITY;
		double bestTrainsetRecall    = Double.NEGATIVE_INFINITY;
		double bestTrainsetAccuracy  = Double.NEGATIVE_INFINITY;
		double bestTrainsetF1        = Double.NEGATIVE_INFINITY;
		double bestCVprecision       = Double.NEGATIVE_INFINITY;
		double bestCVrecall          = Double.NEGATIVE_INFINITY;
		double bestCVaccuracy        = Double.NEGATIVE_INFINITY;
		double bestCVf1              = Double.NEGATIVE_INFINITY;
		int    minimalMaxNumberOfClausesSeen = Integer.MAX_VALUE;
		int    maximalBodyLengthSeen         = 0;
		Utils.println("\n% Have " + Utils.comma(onionLayers) + " Onion combinations to try.");
		int numberOfCombos     = Utils.getSizeSafely(onionLayers);
		int currentComboNumber = 0;
		if (numberOfCombos > 0) for (ILPparameterSettings setting : onionLayers) {
           
            ILPSearchAction action = outerLooper.innerLoopTask.fireOnionLayerStarting(this, setting);

            if ( action == ILPSearchAction.PERFORM_LOOP) {
                 try {
                    startLastCombo = System.currentTimeMillis();
                    currentComboNumber++;
                    long runningTime                = System.currentTimeMillis() - start;
                    int  timeLeftInSeconds          = (int)  (maxSecondsToSpend - (runningTime / 1000)); // Utils.waitHere("maxSecondsToSpend = " + maxSecondsToSpend);
                    long timeForThisComboInMillisec = (long) (1000 * timeLeftInSeconds * Math.max(0.05, 1 - (numberOfCombos - currentComboNumber) / (double) numberOfCombos)); // Uniformly spread the remaining time over the remaining combo's, but give at least 5% of the total time.
                    if (maxSecondsToSpend >= 0 && timeLeftInSeconds <= 0) {
                        // Use 'err' here so we see these.
                        Utils.printlnErr("\n% Have been running for over " + Utils.convertMillisecondsToTimeSpan(runningTime, 0) + ", which exceeds the time budget of " + Utils.convertMillisecondsToTimeSpan(maxSecondsToSpend) + ".");
                        break;
                    }
                    minimalMaxNumberOfClausesSeen = Math.min(minimalMaxNumberOfClausesSeen, setting.getMaxNumberOfClauses());
                    maximalBodyLengthSeen         = Math.min(maximalBodyLengthSeen,         setting.getMaxBodyLength());

                    // Use 'err' here so we see these.
                    String s = "\n%----------------------------\n% CONSIDERING Settings #" + setting.getOnionLayer() + " ("+  Utils.comma(++counter) + " of " + Utils.comma(onionLayers) + ")."
                                    + "\n% (The ONION has been running for a total of " + TimeScale.MILLSECOND.getBestFormattedString(runningTime, "%.2f%s")
                                    + (maxSecondsToSpend < Long.MAX_VALUE
                                            ? "\n%  and has " + TimeScale.MILLSECOND.getBestFormattedString(1000L * maxSecondsToSpend - runningTime, "%.2f%s")+ " left;\n%  "
                                                    + TimeScale.MILLSECOND.getBestFormattedString(timeForThisComboInMillisec, "%.2f%s") + " have been allotted for this setting)\n"
                                            : ")\n%\n")
                                    + setting;

                    if ( "twalker".equals(System.getProperty("user.name")) ) {
                        Utils.println(s);
                    }
                    else {
                        Utils.printlnErr(s);
                    }


                    if (setting.isRunAllAsTrainSet()) {

                        if (useSingleTrainTuneSplit) { Utils.waitHere("Do we want useSingleTrainTuneSplit=true here?  Or should this be done via CV"); }




                        CrossValidationResult results = setting.runAllAsTrainSet(bestTrainsetPrecision, bestTrainsetRecall, bestTrainsetAccuracy, bestTrainsetF1, timeForThisComboInMillisec);

                        if (results == null) {
                            if (debugLevel > 0) { Utils.println("\n%    Could not beat the best trainset results seen so far of precision = "
                                                +                   Utils.truncate(bestTrainsetPrecision, 4) + (theReasonToStopEarly == ReasonToStopEarly.useBestPrecisionToStopEarly ? "*"  : "")
                                                + ", recall = "   + Utils.truncate(bestTrainsetRecall,    4) + (theReasonToStopEarly == ReasonToStopEarly.useBestRecallToStopEarly    ? "*"  : "")
                                                + ", accuracy = " + Utils.truncate(bestTrainsetAccuracy,  4) + (theReasonToStopEarly == ReasonToStopEarly.useBestAccuracyToStopEarly  ? "*"  : "")
                                                + ", and F1 = "   + Utils.truncate(bestTrainsetF1,        4) + (theReasonToStopEarly == ReasonToStopEarly.useBestF1toStopEarly        ? "*." : ".")
                                                ); }
                            continue;
                        }
                        double trainsetWeightedPrecision  = results.getAverageTrainingPrecision(); // TODO - could mask these out via theReasonToStopEarly, but that doesn't seem necessary yet.
                        double trainsetWeightedRecall     = results.getAverageTrainingRecall();
                        double trainsetWeightedAccuracy   = results.getAverageAccuracy();
                        double trainsetWeightedF1         = results.getAverageFBeta();
                        double local_minimalTrainSetWeightedPrecisionToStop = setting.getMinPrecisionToStop();
                        double local_minimalTrainSetWeightedRecallToStop    = setting.getMinRecallToStop();
                        double local_minimalTrainSetWeightedF1toStop        = setting.getMinF1toStop();
                        double local_minimalTrainSetWeightedAccuracyToStop  = setting.getMinAccuracyToStop();

                        switch (theReasonToStopEarly) {
                            case useBestPrecisionToStopEarly: bestTrainsetPrecision = Math.max(trainsetWeightedPrecision, bestTrainsetPrecision); break;
                            case useBestRecallToStopEarly:    bestTrainsetRecall    = Math.max(trainsetWeightedRecall,    bestTrainsetRecall);    break;
                            case useBestAccuracyToStopEarly:  bestTrainsetAccuracy  = Math.max(trainsetWeightedAccuracy,  bestTrainsetAccuracy);  break;
                            case useBestF1toStopEarly:        bestTrainsetF1        = Math.max(trainsetWeightedF1,        bestTrainsetF1);        break;
                            default: Utils.writeMe();
                        }

                        if (debugLevel > 0 && trainsetWeightedPrecision > 0.0 && trainsetWeightedRecall > 0.0) { // && (trainsetWeightedPrecision > bestTrainsetPrecision || trainsetWeightedRecall > bestTrainsetRecall)) {
                            Utils.println("\n% Trainset results for");
                            Utils.println(""  + setting + "\n");
                            Utils.println(" " + results.getBestOverallFoldByAccuracy().getTheory());
                            Utils.println(" " + results);
                            Utils.println("% precision = " + Utils.truncate(trainsetWeightedPrecision, 3) + " vs trainset min = " + Utils.truncate(local_minimalTrainSetWeightedPrecisionToStop, 3));
                            Utils.println("% recall    = " + Utils.truncate(trainsetWeightedRecall,    3) + " vs trainset min = " + Utils.truncate(local_minimalTrainSetWeightedRecallToStop,    3));
                            Utils.println("% accuracy  = " + Utils.truncate(trainsetWeightedAccuracy,  3) + " vs trainset min = " + Utils.truncate(local_minimalTrainSetWeightedAccuracyToStop,  3));
                            Utils.println("% F1        = " + Utils.truncate(trainsetWeightedF1,        3) + " vs trainset min = " + Utils.truncate(local_minimalTrainSetWeightedF1toStop,        3));
                            //Utils.waitHere();
                        }

                        if (theReasonToStopEarly == ReasonToStopEarly.useBestPrecisionToStopEarly && trainsetWeightedPrecision >= local_minimalTrainSetWeightedPrecisionToStop) {
                            if (debugLevel > 1) {
                                Utils.println("\n% Can stop because the theory's (weighted) trainset precision (" + Utils.truncate(trainsetWeightedPrecision, 2) +
                                              ") reached the minimum specified ("    + Utils.truncate(local_minimalTrainSetWeightedPrecisionToStop, 2) +  ").");
                            }
                            bestSetting = setting;
                            bestResults = results;
                            bestBasedOnCrossValidation = false;
                            doFinalCleanup("Stopped because the theory's (weighted) trainset precision (" + Utils.truncate(trainsetWeightedPrecision, 2) +
                                            ") reached the minimum specified (" + Utils.truncate(local_minimalTrainSetWeightedPrecisionToStop, 2)   +  ")",
                                            currentComboNumber, setting);
                            return;
                        }

                        if (theReasonToStopEarly == ReasonToStopEarly.useBestRecallToStopEarly && trainsetWeightedRecall    >= local_minimalTrainSetWeightedRecallToStop ) {
                            if (debugLevel > 1) {
                                Utils.println("\n% Can stop the theory's because the theory's (weighted) trainset recall (" + Utils.truncate(trainsetWeightedRecall, 2) +
                                              ") reached the minimum specified ("    + Utils.truncate(local_minimalTrainSetWeightedRecallToStop, 2) +  ").");
                            }
                            bestSetting = setting;
                            bestResults = results;
                            bestBasedOnCrossValidation = false;
                            doFinalCleanup("Stopped because the theory's (weighted) trainset recall (" + Utils.truncate(trainsetWeightedRecall, 2) +
                                              ") reached the minimum specified ("    + Utils.truncate(local_minimalTrainSetWeightedRecallToStop, 2)  +  ")",
                                            currentComboNumber, setting);
                            return;
                        }

                        if (theReasonToStopEarly == ReasonToStopEarly.useBestAccuracyToStopEarly && trainsetWeightedAccuracy >= local_minimalTrainSetWeightedAccuracyToStop) {
                            if (debugLevel > 1) {
                                Utils.println("\n% Can stop because the theory's (weighted) trainset accuracy (" + Utils.truncate(trainsetWeightedAccuracy, 2) +
                                              ") reached the minimum specified ("    + Utils.truncate(local_minimalTrainSetWeightedAccuracyToStop, 2) +  ").");
                            }
                            bestSetting = setting;
                            bestResults = results;
                            bestBasedOnCrossValidation = false;
                            doFinalCleanup("Stopped because the theory's (weighted) trainset accuracy (" + Utils.truncate(trainsetWeightedAccuracy, 2) +
                                              ") reached the minimum specified ("    + Utils.truncate(local_minimalTrainSetWeightedAccuracyToStop, 2)  +  ")",
                                            currentComboNumber, setting);
                            return;
                        }

                        if (theReasonToStopEarly == ReasonToStopEarly.useBestF1toStopEarly && trainsetWeightedF1 >= local_minimalTrainSetWeightedF1toStop) {
                            if (debugLevel > 1) {
                                Utils.println("\n% Can stop because the theory's (weighted) trainset F1 (" + Utils.truncate(trainsetWeightedF1, 2) +
                                              ") reached the minimum specified ("    + Utils.truncate(local_minimalTrainSetWeightedF1toStop, 2) +  ").");
                            }
                            bestSetting = setting;
                            bestResults = results;
                            bestBasedOnCrossValidation = false;
                            doFinalCleanup("Stopped because the theory's (weighted) trainset F1 (" + Utils.truncate(trainsetWeightedF1, 2) +
                                              ") reached the minimum specified ("    + Utils.truncate(local_minimalTrainSetWeightedF1toStop, 2) +  ")",
                                            currentComboNumber, setting);
                            return;
                        }

                        // Since this is on the TRAINSET, there is a small multiplicative penalty here (the leading multiplier) compared to the cross-validation results.
                        double score = -1;
                        switch (theReasonToStopEarly) {
                            case useBestPrecisionToStopEarly: score = trainsetWeightedPrecision; break;
                            case useBestRecallToStopEarly:    score = trainsetWeightedRecall;    break;
                            case useBestAccuracyToStopEarly:  score = trainsetWeightedAccuracy;  break;
                            case useBestF1toStopEarly:        score = trainsetWeightedF1;        break;
                            default: Utils.writeMe();
                        }
                        score *= 0.95;
                        if (score > bestScore) {
                            bestScore   = score;
                            bestSetting = setting;
                            bestResults = results;
                            bestBasedOnCrossValidation = false;
                            if (debugLevel > 0) { Utils.println("% New best score found (on trainset, so scaled by 0.95): " + Utils.truncate(score, 3)); }
                        }
                    } else if (setting.isRunCrossValidation()) {
                        CrossValidationResult results = (useSingleTrainTuneSplit
                                                                ? setting.runWithSpecifiedTrainTuneSplit(firstTrainExample, lastTrainExample, firstTuneExample, lastTuneExample,
                                                                                                         bestCVprecision, bestCVrecall, bestCVaccuracy, bestCVf1, timeForThisComboInMillisec)
                                                                : setting.runCrossValidation(            bestCVprecision, bestCVrecall, bestCVaccuracy, bestCVf1, timeForThisComboInMillisec));
                        if (results == null) {
                            if (debugLevel > -10) { Utils.println("\n%    Could not beat the best CV results seen so far of precision = "
                                    +                   Utils.truncate(bestCVprecision, 4) + (theReasonToStopEarly == ReasonToStopEarly.useBestPrecisionToStopEarly ? "*"  : "")
                                    + ", recall = "   + Utils.truncate(bestCVrecall,    4) + (theReasonToStopEarly == ReasonToStopEarly.useBestRecallToStopEarly    ? "*"  : "")
                                    + ", accuracy = " + Utils.truncate(bestCVaccuracy,  4) + (theReasonToStopEarly == ReasonToStopEarly.useBestAccuracyToStopEarly  ? "*"  : "")
                                    + ", and F1 = "   + Utils.truncate(bestCVf1,        4) + (theReasonToStopEarly == ReasonToStopEarly.useBestF1toStopEarly        ? "*." : ".")
                                    ); }
                            continue;
                        }
                        double tunesetWeightedPrecision = results.getAverageTestingPrecision();
                        double tunesetWeightedRecall    = results.getAverageTestingRecall();
                        double tunesetWeightedAccuracy  = results.getAverageTestingAccuracy();
                        double tunesetWeightedF1        = results.getAverageTestingFBeta();
                        double local_minimalCrossValidationWeightedPrecisionToStop = setting.getMinPrecisionToStop();
                        double local_minimalCrossValidationWeightedRecallToStop    = setting.getMinRecallToStop();
                        double local_minimalCrossValidationWeightedF1toStop        = setting.getMinF1toStop();
                        double local_minimalCrossValidationWeightedAccuracyToStop  = setting.getMinAccuracyToStop();
                        switch (theReasonToStopEarly) {
                            case useBestPrecisionToStopEarly: bestCVprecision = Math.max(tunesetWeightedPrecision, bestCVprecision); break;
                            case useBestRecallToStopEarly:    bestCVrecall    = Math.max(tunesetWeightedRecall,    bestCVrecall);    break;
                            case useBestAccuracyToStopEarly:  bestCVaccuracy  = Math.max(tunesetWeightedAccuracy,  bestCVaccuracy);  break;
                            case useBestF1toStopEarly:        bestCVf1        = Math.max(tunesetWeightedF1,        bestCVf1);        break;
                            default: Utils.writeMe();
                        }

                        if (debugLevel > 0) { // && (tunesetWeightedPrecision > bestCVprecision || bestCVrecall > tunesetWeightedRecall)) {
                            Utils.println("\n% Cross-validation results for");
                            Utils.println("" + setting + "\n");
                            Utils.println(" " + results.getBestOverallFoldByAccuracy().getTheory());
                            Utils.println(" " + results);
                            Utils.println("% precision = " + Utils.truncate(tunesetWeightedPrecision, 3) + " vs cv min = " + Utils.truncate(local_minimalCrossValidationWeightedPrecisionToStop, 3));
                            Utils.println("% recall    = " + Utils.truncate(tunesetWeightedRecall,    3) + " vs cv min = " + Utils.truncate(local_minimalCrossValidationWeightedRecallToStop,    3));
                            Utils.println("% accuracy  = " + Utils.truncate(tunesetWeightedAccuracy,  3) + " vs cv min = " + Utils.truncate(local_minimalCrossValidationWeightedAccuracyToStop,  3));
                            Utils.println("% F1        = " + Utils.truncate(tunesetWeightedF1,        3) + " vs cv min = " + Utils.truncate(local_minimalCrossValidationWeightedF1toStop,        3));
                        //	Utils.waitHere();
                        }

                        if (theReasonToStopEarly == ReasonToStopEarly.useBestPrecisionToStopEarly && tunesetWeightedPrecision >= local_minimalCrossValidationWeightedPrecisionToStop) {
                            if (debugLevel > 0) {
                                Utils.println("\n% Can stop because the theory's (weighted) tuneset precision (" + Utils.truncate(tunesetWeightedPrecision, 2) +
                                              ") reached the minimum specified ("    + Utils.truncate(local_minimalCrossValidationWeightedPrecisionToStop, 2) +  ").");
                            }
                            bestSetting = setting;
                            bestResults = results;
                            bestBasedOnCrossValidation = true;
                            doFinalCleanup("Stopped because the theory's (weighted) tuneset precision (" + Utils.truncate(tunesetWeightedPrecision, 2) +
                                              ") reached the minimum specified ("    + Utils.truncate(local_minimalCrossValidationWeightedPrecisionToStop, 2) +  ")",
                                            currentComboNumber, setting);
                            return;
                        }

                        if (theReasonToStopEarly == ReasonToStopEarly.useBestRecallToStopEarly && tunesetWeightedRecall    >= local_minimalCrossValidationWeightedRecallToStop ) {
                            if (debugLevel > 0) {
                                Utils.println("\n% Can stop the theory's because (weighted) tuneset recall ("  + Utils.truncate(tunesetWeightedRecall, 2) +
                                              ") reached the minimum specified ("    + Utils.truncate(local_minimalCrossValidationWeightedRecallToStop, 2) +  ").");
                            }
                            bestSetting = setting;
                            bestResults = results;
                            bestBasedOnCrossValidation = true;
                            doFinalCleanup("Stopped because the theory's (weighted) tuneset recall ("  + Utils.truncate(tunesetWeightedRecall, 2) +
                                              ") reached the minimum specified ("    + Utils.truncate(local_minimalCrossValidationWeightedRecallToStop, 2) +  ")",
                                              currentComboNumber, setting);
                            return;
                        }

                        if (theReasonToStopEarly == ReasonToStopEarly.useBestAccuracyToStopEarly && tunesetWeightedAccuracy >= local_minimalCrossValidationWeightedAccuracyToStop) {
                            if (debugLevel > 1) {
                                Utils.println("\n% Can stop because the theory's (weighted) tuneset accuracy (" + Utils.truncate(tunesetWeightedAccuracy, 2) +
                                              ") reached the minimum specified ("    + Utils.truncate(local_minimalCrossValidationWeightedAccuracyToStop, 2) +  ").");
                            }
                            bestSetting = setting;
                            bestResults = results;
                            bestBasedOnCrossValidation = true;
                            doFinalCleanup("Stopped because the theory's (weighted) tuneset accuracy (" + Utils.truncate(tunesetWeightedAccuracy, 2) +
                                              ") reached the minimum specified ("    + Utils.truncate(local_minimalCrossValidationWeightedAccuracyToStop, 2) +  ")",
                                            currentComboNumber, setting);
                            return;
                        }

                        if (theReasonToStopEarly == ReasonToStopEarly.useBestF1toStopEarly && tunesetWeightedF1 >= local_minimalCrossValidationWeightedF1toStop) {
                            if (debugLevel > 1) {
                                Utils.println("\n% Can stop because the theory's (weighted) tuneset F1 (" + Utils.truncate(tunesetWeightedF1, 2) +
                                              ") reached the minimum specified ("    + Utils.truncate(local_minimalCrossValidationWeightedF1toStop, 2) +  ").");
                            }
                            bestSetting = setting;
                            bestResults = results;
                            bestBasedOnCrossValidation = true;
                            doFinalCleanup("Stopped because the theory's (weighted) tuneset F1 (" + Utils.truncate(tunesetWeightedF1, 2) +
                                              ") reached the minimum specified ("    + Utils.truncate(local_minimalCrossValidationWeightedF1toStop, 2) +  ")",
                                            currentComboNumber, setting);
                            return;
                        }

                        double score = -1;
                        switch (theReasonToStopEarly) {
                            case useBestPrecisionToStopEarly: score = tunesetWeightedPrecision; break;
                            case useBestRecallToStopEarly:    score = tunesetWeightedRecall;    break;
                            case useBestAccuracyToStopEarly:  score = tunesetWeightedAccuracy;  break;
                            case useBestF1toStopEarly:        score = tunesetWeightedF1;        break;
                            default: Utils.writeMe();
                        }

                        if (score > bestScore) {
                            bestScore = score;
                            bestSetting = setting;
                            bestResults = results;
                            bestBasedOnCrossValidation = true;
                            if (debugLevel > 0) { Utils.println("% New best score found (via cross validation): " + Utils.truncate(score, 3)); }
                        }
                    }  else {
                        Utils.error("Skipped this setting: " + setting);
                    }
                } catch (SearchInterrupted e) {
                    if (debugLevel > 0) { Utils.println("% Stopped cross-validation early because the search was interrupted for some reason: " + e + "\n" + (debugLevel < 1 ? setting : "")); }
                    Utils.reportStackTrace(e);
                    Utils.error("Should this happen?");
                }

                outerLooper.innerLoopTask.fireOnionLayerFinished(this, setting);
            }
            else if ( action == ILPSearchAction.SKIP_ITERATION ) {
                Utils.println("ILPSearchListener skipped onion layer " + setting.getOnionLayer() + ".");
            }
            else if ( action == ILPSearchAction.TERMINATE_LOOP ) {
                Utils.println("ILPSearchListener terminated Onion search after prior to layer " + setting.getOnionLayer() + ".");
                break;
            }
        }
		
		if (debugLevel > 0) {
			if (bestSetting != null) {
				Utils.println("\n% The best results, with best score = " + Utils.truncate(bestScore, 3) + ", obtained from" + (bestBasedOnCrossValidation ? " cross validation." : " train-set only."));
				Utils.println(  "% " + bestSetting);
				Utils.println(  "% Best results = " + bestResults);
			} else if (giveItTheCollegeTry) {  // TODO - slowly retract the allowable coverage of negative examples.
				// If nothing found, run Onion Layer 0 ... N until something found that meets the minimal specifications or 100 seconds are up.
				startLastCombo = System.currentTimeMillis();
				Utils.warning("\n% Nothing acceptable was found using the provided parameters and the time allowed, so giving it the ol' college try.");
				for (int rerun = 0; rerun < onionLayers.size(); rerun++) {
					ILPparameterSettings settingToUse = onionLayers.get(rerun); // TODO - should we COPY?
					if (settingToUse.getMaxNumberOfClauses() > minimalMaxNumberOfClausesSeen) { break; }
					if (maximalBodyLengthSeen == settingToUse.getMaxBodyLength()) { 
						settingToUse.setMaxBodyLength(maximalBodyLengthSeen + 1); // This is a little risky if there is only one body length, since might create too big of a search space, but seems safe enough to add 1.
					}
					settingToUse.markAsReconsidered();
					settingToUse.setMinPosCoverage(0); // I.e., recall.
					settingToUse.setMinPrecision(0.0);
					settingToUse.setMaxNodesToCreate(   1000);
					settingToUse.setMaxNodesToConsider(   10);
					settingToUse.setMaxNegCoverage(    10000);
					// Need to score even if not satisfied on the seed example?
					double hold_clausesMustCoverFractPosSeeds = settingToUse.outerLooper.innerLoopTask.clausesMustCoverFractPosSeeds;
					settingToUse.outerLooper.innerLoopTask.clausesMustCoverFractPosSeeds = 0.0;
					// Should we reset this minFractionOfPosCoveredToStop?  I think this just impacts EARLY stopping, which we might need, but let's wait to reset this.
					Utils.println("\n% RECONSIDERING Setting #" + (rerun + 1) + " (modified to perform a 'find anything' run).\n" + settingToUse);
					CrossValidationResult results = settingToUse.runAllAsTrainSet(0.0, 0.0, 0.0, 0.0, 30000); // Allow 30 seconds.
					settingToUse.outerLooper.innerLoopTask.clausesMustCoverFractPosSeeds = hold_clausesMustCoverFractPosSeeds;
					bestResults = results;
					Theory theory = (bestFold != null ? getTheoryFromBestFold() : null);
					if (theory != null && theory.haveTheory()) {
						bestSetting = settingToUse;
						Utils.warning("\n% The college-try theory:\n% " + theory.toPrettyString("%   ", Integer.MAX_VALUE));
						doFinalCleanup("The good ol' college try produced an answer", Utils.getSizeSafely(onionLayers) + 1 + rerun, settingToUse);
						return;
					}
					Utils.println("% RECONSIDERING Setting #" + (rerun + 1) + " led to nothing being learned.");
					if (System.currentTimeMillis() - start > 100 * 1000) { // TODO should make this 100 be a class variable. 
						Utils.warning("% Even the college try wasn't able to find something in 100 seconds, so fully giving up."); 
						doFinalCleanup("The good ol' college try also failed to produce an answer, so no theory learned",
					   					Utils.getSizeSafely(onionLayers) + 1 + rerun, null);
						return;
					}
				}
				doFinalCleanup("No theory was learned by the good ol' college try", Utils.getSizeSafely(onionLayers) + 1, null);
				return;
			} else if (finalMaxLength >= 0 || finalMinPosCoverage >= 0 || finalMinPrecision >= 0) { // This is used in 'control' experiments where no advice is used.
				startLastCombo = System.currentTimeMillis();
				ILPparameterSettings settingToUse = onionLayers.get(0);
				settingToUse.markAsReconsidered();
				if (finalMaxLength      >  0) { settingToUse.setMaxBodyLength( finalMaxLength);      }
				if (finalMinPosCoverage >= 0) { settingToUse.setMinPosCoverage(finalMinPosCoverage); }
				if (finalMinPrecision   >= 0) { settingToUse.setMinPrecision(  finalMinPrecision);   }
				settingToUse.setMaxNodesToCreate(    1000);
				settingToUse.setMaxNodesToConsider(    10);
				settingToUse.setMaxNegCoverage(    100000);
				double hold_clausesMustCoverFractPosSeeds = settingToUse.outerLooper.innerLoopTask.clausesMustCoverFractPosSeeds;
				settingToUse.outerLooper.innerLoopTask.clausesMustCoverFractPosSeeds = 0.5;
				Utils.println("\n% RECONSIDERING Setting #1 (modified to perform a 'find best rule' run).\n" + settingToUse);
				CrossValidationResult results = settingToUse.runAllAsTrainSet(0.0, 0.0, 0.0, 0.0, 300000); // Allow 300 seconds.
				settingToUse.outerLooper.innerLoopTask.clausesMustCoverFractPosSeeds = hold_clausesMustCoverFractPosSeeds;
				bestResults = results;
				Theory theory = (bestFold != null ? getTheoryFromBestFold() : null);
				if (theory != null && theory.haveTheory()) {
					bestSetting = settingToUse;
					Utils.warning("\n% The college-try theory:\n% " + theory.toPrettyString("%   ", Integer.MAX_VALUE));
					doFinalCleanup("The good ol' college try (v2) produced an answer", Utils.getSizeSafely(onionLayers) + 1, settingToUse);
					return;
				} else if (System.currentTimeMillis() - start > 300 * 1000) { 
					Utils.warning("% Even the college try wasn't able to find something in 300 seconds, so fully giving up."); 
					doFinalCleanup("The good ol' college try (v2) also failed to produce an answer, so no theory learned",
		   								Utils.getSizeSafely(onionLayers) + 1, null);
					return;
				} else {
					Utils.println("% RECONSIDERING Setting #0 led to nothing being learned.");
				}
				doFinalCleanup("No theory was learned by the good ol' college try (v2)", Utils.getSizeSafely(onionLayers) + 1, null);
				return;
			} else {
				Utils.println("\n% Nothing acceptable was found using the provided parameters and the time allowed (plus giveItTheCollegeTry = " + giveItTheCollegeTry + ").\n");
			}
		}
		doFinalCleanup("No theory was learned", Utils.getSizeSafely(onionLayers) + 1, null);
		return;
	}
	
	public Theory getTheoryFromBestFold() {
		if (bestFold == null) { doFinalCleanupIfStillNeeded(); }
		if (bestFold == null) {
			Utils.warning("Asked for theory from best fold, but best fold could not be computed.");
			return null;
		}
		return bestFold.getTheory();
	}
	
	public String getResultsFromBestFold() {
		if (bestFold == null) { doFinalCleanupIfStillNeeded(); }
		if (bestFold == null) {
			Utils.warning("Asked for results from best fold, but best fold could not be computed.");
			return null;
		}
		return bestFold.getAllExamplesCoverageScore().toLongString();
	}
	
	public Gleaner getGleanerFromBestFold() {
		if (bestFold == null) { doFinalCleanupIfStillNeeded(); }
		if (bestFold == null) {
			Utils.warning("Asked for gleaner from best fold, but best fold could not be computed.");
			return null;
		}
		return bestFold.getGleaner();
	}
	
	private boolean called_doFinalCleanup = false;
	private void doFinalCleanupIfStillNeeded() {
		if (called_doFinalCleanup) { return; }
		doFinalCleanup("Unexpected call to doFinalCleanup()", Utils.getSizeSafely(onionLayers) + 1, null);
	}
	public static final boolean allOnionDocOnOneLine = false; // If true, then easier to concatenate all of these.
	private void doFinalCleanup(String reason, int settingNumber, ILPparameterSettings setting) {
		if (called_doFinalCleanup) { return; }
		called_doFinalCleanup = true;
		long totalTime       = System.currentTimeMillis() - start;
		long thisSettingTime = System.currentTimeMillis() - startLastCombo;
		String breaker       = (allOnionDocOnOneLine ? ",  " : ".\n    "); // Indent later lines a bit more, so concatenation is still useful (though sorting wont be).
		descriptionOfOnionProcessingNeeded = "    " + reason + breaker + "Spent " + Utils.convertMillisecondsToTimeSpan(totalTime, 3) + " overall (and " + Utils.convertMillisecondsToTimeSpan(thisSettingTime, 3) + " on the last ONION parameter settings)" 
												             + breaker + (setting == null ? "ONION Setting #" + settingNumber + " (no other info recorded)." : "ONION Setting #" + settingNumber + " " + setting.toStringShort() + ".");
		
		if (bestResults == null) { bestFold = null; return; }

		switch (theReasonToStopEarly) {
		//	case useBestPrecisionToStopEarly: bestFold = bestResults.getBestOverallFoldByPrecision(); break;
		//	case useBestRecallToStopEarly:    bestFold = bestResults.getBestOverallFoldByRecall();    break;
			case useBestAccuracyToStopEarly:  bestFold = bestResults.getBestOverallFoldByAccuracy();  break;
			case useBestF1toStopEarly:        bestFold = bestResults.getBestOverallFoldByF1();        break;
			default: /*Utils.writeMe();*/
		}
	}
	public int getMaxSecondsToSpend() {
		return maxSecondsToSpend;
	}
	public void setMaxSecondsToSpend(int maxSecondsToSpend) {
		if (maxSecondsToSpend < 0) { Utils.waitHere("maxSecondsToSpend = " + maxSecondsToSpend); }
		this.maxSecondsToSpend = maxSecondsToSpend;
	}
	
	public void setGiveItTheOldCollegeTry(boolean giveItTheCollegeTry) {
		this.giveItTheCollegeTry = giveItTheCollegeTry;
	}
	
	public void relaxMinPrecisonAtEnd(double finalMinPrecision) {
		this.finalMinPrecision = finalMinPrecision;
	}
	
	public void relaxMaxLengthAtEnd(int finalMaxLength) {
		this.finalMaxLength = finalMaxLength;
	}
	
	public void relaxMinPosCoverageAtEnd(int finalMinPosCoverage) {
		this.finalMinPosCoverage = finalMinPosCoverage;
	}
	
	@SuppressWarnings("unused")
	private String toStringIntArray(int[] array) {
		if (array == null) { return "[]"; }
		String result = "[";
		boolean needComma = false;
		for (int i : array) { if (needComma) { result += ", "; } else { needComma = true; } result += + i; } 
		return result + "]";
	}
	
	public CrossValidationFoldResult getBestFold() {
		return bestFold;
	}
	public void setBestFold(CrossValidationFoldResult bestFold) {
		this.bestFold = bestFold;
	}
	
	public boolean isUseSingleTrainTuneSplit() {
		return useSingleTrainTuneSplit;
	}
	public void setUseSingleTrainTuneSplit(boolean useSingleTrainTuneSplit) {
		this.useSingleTrainTuneSplit = useSingleTrainTuneSplit;
	}
	
}
