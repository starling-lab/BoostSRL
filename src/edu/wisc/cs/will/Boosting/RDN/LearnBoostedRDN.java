/**
 * 
 */
package edu.wisc.cs.will.Boosting.RDN;

import java.io.BufferedWriter;
import java.io.File;  import java.io.FileWriter;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;

import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.Utils.condor.CondorFileInputStream;
import edu.wisc.cs.will.Utils.condor.CondorFileOutputStream;
import edu.wisc.cs.will.Utils.condor.CondorFileWriter;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;

import edu.wisc.cs.will.Boosting.Common.RunBoostedModels;
import edu.wisc.cs.will.Boosting.Common.SRLInference;
import edu.wisc.cs.will.Boosting.EM.HiddenLiteralSamples;
import edu.wisc.cs.will.Boosting.EM.HiddenLiteralState;
import edu.wisc.cs.will.Boosting.KBAdvice.Advice;
import edu.wisc.cs.will.Boosting.RDN.Models.PhiFunctionForRDN;
import edu.wisc.cs.will.Boosting.RDN.Models.RelationalDependencyNetwork;
import edu.wisc.cs.will.Boosting.Trees.LearnRegressionTree;
import edu.wisc.cs.will.Boosting.Trees.RegressionTree;
import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;
import edu.wisc.cs.will.Boosting.Utils.CommandLineArguments;
import edu.wisc.cs.will.Boosting.Utils.ExampleSubSampler;
import edu.wisc.cs.will.Boosting.Utils.LineSearch;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Theory;
import edu.wisc.cs.will.FOPC.TreeStructuredTheory;
import edu.wisc.cs.will.ILP.ILPouterLoop;
import edu.wisc.cs.will.Utils.ProbDistribution;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.VectorStatistics;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

/**
 * @author Tushar Khot
 *
 */
public class LearnBoostedRDN {
	protected final static int debugLevel = 1; // Used to control output from this class (0 = no output, 1=some, 2=much, 3=all).

	private CommandLineArguments cmdArgs;
	private ExampleSubSampler egSubSampler;
	private WILLSetup setup;

	public List<RegressionRDNExample> egs    = null;
	private String  targetPredicate          = null;
	private int     maxTrees                 = 10;
	private double  minGradientForSame       = 0.0002;
	private double  minPercentageSameForStop = 0.8;
	private String  yapSettingsFile;
	private boolean resampleExamples        = true;
	private boolean newInputFileForEachTree = true;
	private boolean stopIfFewChanges        = false;
	private boolean performLineSearch       = false;
	private boolean learnSingleTheory 		= false;
	private boolean disableBoosting			= false;
    private boolean printGradients = false;
    
    private long learningTimeTillNow = 0;
    
    public Map<Example,Double> adviceGradients = null; 

	public LearnBoostedRDN(CommandLineArguments cmdArgs, WILLSetup setup) {
		this.cmdArgs = cmdArgs;
		this.setup = setup;
		maxTrees = cmdArgs.getMaxTreesVal();
		setParamsUsingSetup(setup);
		if(cmdArgs.isUseYapVal()) {
			learnSingleTheory=false;
		}
		if (cmdArgs.isDisabledBoosting()) {
			disableBoosting=true;
		}
		egSubSampler = new ExampleSubSampler(setup, cmdArgs);
	}

	/**
	 * @deprecated
	 * @param predicate
	 * @param yapFile
	 * @param caller
	 * @return
	 */
	public ConditionalModelPerPredicate learnModel(String predicate, String yapFile, RunBoostedModels caller) {
		setYapSettingsFile(yapFile);
		targetPredicate = predicate;
		ConditionalModelPerPredicate rdn = new ConditionalModelPerPredicate(setup);
		if (!cmdArgs.isDisableAdvice()) {
			String adviceFile = setup.getOuterLooper().getWorkingDirectory() + "/" + cmdArgs.getPriorAdvice();
			JointRDNModel fullModel = new JointRDNModel();
			fullModel.put(targetPredicate, rdn);
			// TODO (TVK) repeated work here. We are loading the same advice over and over for each target predicate.
			BoostingUtils.loadAdvice(setup, fullModel, adviceFile, false);
		}
		SingleModelSampler sampler = new SingleModelSampler(rdn, setup, null, false);
		learnNextModel(caller, sampler, rdn, maxTrees);
		return rdn;
	}
	
	public void learnNextModel(RunBoostedModels caller, SRLInference sampler, ConditionalModelPerPredicate rdn, int numMoreTrees) {

		Utils.println("\n% Learn model for: " + targetPredicate);
		long start = (debugLevel > 0 ? System.currentTimeMillis() : 0);
		//if (!cmdArgs.isLearnRegression()) {
		// Call facts and examples the first time.
			setup.prepareFactsAndExamples(targetPredicate);
		//}
		if (debugLevel > 1) { Utils.println("%  Have prepared facts.");}
		if (cmdArgs.isNoTargetModesInitially() && rdn.getNumTrees() == 0) {
			setup.removeAllTargetsBodyModes();
		}
		learnRDN(targetPredicate, rdn,sampler, getYapSettingsFile(), caller, numMoreTrees);
		if (debugLevel > 0) { 
			long end = System.currentTimeMillis();
			learningTimeTillNow += (end-start);
			if (rdn.getNumTrees() == maxTrees) {
				Utils.println("% Time taken to learn model for '" + targetPredicate + "': " + Utils.convertMillisecondsToTimeSpan(end - start, 3) + ".");
			}
		}
	}


	public void learnRDN(String pred, ConditionalModelPerPredicate rdn, SRLInference sampler, String yapFile, RunBoostedModels caller, int numMoreTrees) { // Thought we needed the 'caller' but we don't - leave it here, though, in case we do end up needing it.
		String saveModelName = BoostingUtils.getModelFile(cmdArgs, pred, true);
		if(rdn.getNumTrees() == 0) {
			rdn.setTargetPredicate(pred);
			rdn.setTreePrefix(pred + (cmdArgs.getModelFileVal() == null ? "" : "_" + cmdArgs.getModelFileVal()));
			if (learnSingleTheory) {
				rdn.setHasSingleTheory(true);
				rdn.setSetup(setup);
				List<Sentence> bkClauses = setup.getInnerLooper().getParser().parse(getComputationPrologRules(maxTrees));
				rdn.addSentences(bkClauses);
			}
		}
		

		List<RegressionRDNExample> old_eg_set = null;
		long start = System.currentTimeMillis();
		if (disableBoosting) {
			maxTrees=1;
			rdn.setLog_prior(0);
			// Increase the depth and number of clauses
			// TODO : Maybe make this settable ? Or assume caller sets it ?
			ILPouterLoop outerLoop = setup.getOuterLooper();
			outerLoop.setMaxTreeDepth(10);
			outerLoop.setMaxTreeDepthInLiterals(12);
			outerLoop.maxNumberOfClauses = 20;
			outerLoop.maxNumberOfCycles = 20;
			outerLoop.setMaxAcceptableNodeScoreToStop(0.0001);
		}
		//TODO(TVK!)
		if (// cmdArgs.isLearnMLN() || 
			cmdArgs.isLearnRegression()) {
			rdn.setLog_prior(0);
		}
		
		if (cmdArgs.isLearnMLN() && cmdArgs.isLearningMLNClauses()) {
			setup.getOuterLooper().setMaxBodyLength(cmdArgs.getMaxMLNClauseLength());
			setup.getOuterLooper().maxNumberOfClauses = cmdArgs.getNumberOfMLNClauses();
			setup.getOuterLooper().maxNumberOfCycles = cmdArgs.getNumberOfMLNClauses();
			setup.getInnerLooper().beamWidth = 10;
		}
		
		// Learn maxTrees models.
		int i = 0;
		if (rdn.getNumTrees() == 0 && cmdArgs.useCheckPointing()) {
			loadCheckPointModel(rdn);
		}

		// check if rdn already has some trees from checkpoint
		i=rdn.getNumTrees();
		
		int maxTreesForThisRun = Math.min(maxTrees, (i+numMoreTrees));
	
		if(i >= maxTrees) {
			rdn.setNumTrees(maxTrees);
		}
		if (i == 0) {
			if (!cmdArgs.isUseYapVal()) { 
				dumpTheoryToFiles(null, -1, -1);  // Print something initially in case a run dies (i.e., be sure to erase any old results right away).
			}
		}
		for (; i < maxTreesForThisRun; i++) {
			if (i >= maxTrees/2) {
				setup.addAllTargetModes();
			}
			
			long end = System.currentTimeMillis();
			if (cmdArgs.isLearnMLN() && cmdArgs.isLearningMLNClauses()) {
				setup.getOuterLooper().setMaxBodyLength((i/4)+1);
				setup.getOuterLooper().maxNumberOfClauses = (20/(i+1));
				setup.getOuterLooper().maxNumberOfCycles = (20/(i+1));
			}
			if (i > 0 && debugLevel > 0) {
				Utils.println("% Time taken to learn " + Utils.comma(i) + " trees is " + Utils.convertMillisecondsToTimeSpan(learningTimeTillNow + end - start, 3) + ".\n");
			}
			
			// Do we need this here? It is called before executeOuterLoop and in dumpTheoryToFiles.
			setup.getOuterLooper().resetAll();
			if ((sampler instanceof SingleModelSampler) &&
				doEarlyStop(old_eg_set, (SingleModelSampler)sampler)) { // THIS NEEDS TO BE EXTENDED TO HANDLE MULTIPLE TREES.
				if (RunBoostedRDN.numbModelsToMake > 1) { Utils.error("THIS NEEDS TO BE EXTENDED TO HANDLE MULTIPLE TREES."); }
				break;
			}

			for (int modelNumber = 0; modelNumber < RunBoostedRDN.numbModelsToMake; modelNumber++) { // This code assumes modelNumber=0 is learned first.
				// Build data set for this model in this iteration.
				long bddstart = System.currentTimeMillis();						
				List<RegressionRDNExample> newDataSet = buildDataSet(targetPredicate, sampler, getGradientFile(i));
				CombinedTree.addToFinalSet(newDataSet); //Kaushik
				long bbend = System.currentTimeMillis();
				Utils.println("Time to build dataset: " + Utils.convertMillisecondsToTimeSpan(bbend-bddstart));
				RegressionTree tree = null;
				if (cmdArgs.isUseYapVal()) {
					tree = getYapTree( newDataSet, modelNumber, i);
				} else {
					tree = getWILLTree(newDataSet, modelNumber, i);
				}
				if (debugLevel > 1) { reportStats(); }
				double stepLength = 1;
				if (!disableBoosting) {
					stepLength = cmdArgs.getDefaultStepLenVal();
					// Currently can't handle line search and single theory, since we need regression values for a single tree.
					// TODO add support for single theory too.
					if (performLineSearch && !learnSingleTheory) {
						LineSearch    searcher = new LineSearch();
						PhiFunctionForRDN func = new PhiFunctionForRDN(rdn, tree, newDataSet);
						double        newAlpha = searcher.getStepLength(func);
						stepLength = (newAlpha == 0 ? stepLength : newAlpha);
					} else {
						if (performLineSearch && learnSingleTheory) {
							Utils.waitHere("Can't handle both line search and single theory. Disable one.");
						}
					}
				}
				
				rdn.addTree(tree, stepLength, modelNumber);  // This code assume modelNumber=0 is learned first.
				old_eg_set = newDataSet;
			}
			rdn.updateSetOfTrees();
			if (cmdArgs.useCheckPointing()) {
				createCheckPointForModel(rdn, saveModelName);
			}
			if ((i + 1) % 10 == 0) { 
				rdn.saveModel(saveModelName);
			} // Every now and then save the model so we can see how it is doing.
		}
		if (stopIfFewChanges) { 
			Utils.println("Stopped after " + Utils.comma(i) + " trees.");
		}
		if (i >= maxTrees && !cmdArgs.isUseYapVal()) { 
			addPrologCodeForUsingAllTrees(rdn, i); 
		}
		CombinedTree.setFinalRegTree(getWILLTree(CombinedTree.getFinalDataSet(),0,10)); //kaushik

	}

	private String getGradientFile(int i) {
		return setup.getOuterLooper().getWorkingDirectory() + "/gradients_" + i + ".txt";
	}

	public void loadCheckPointModel(ConditionalModelPerPredicate rdn) {
		String saveModelName = BoostingUtils.getModelFile(cmdArgs, targetPredicate, true);
		String chkPointFile = BoostingUtils.getCheckPointFile(saveModelName);
		File willFile = getWILLsummaryFile();
		File chkFile = new File(chkPointFile);
		if (chkFile.exists() && chkFile.length() > 0) {
//		if (Utils.fileExists(chkPointFile)) {
			Utils.println("Loading checkpoint model from " + chkPointFile);
			rdn.loadModel(chkPointFile, setup, -1);
			Utils.println("Found " + rdn.getNumTrees() + " trees in checkpoint");
			String addString = "\n//// Loaded checkpoint from " + chkPointFile + " at " + Utils.getDateTime() + 
							  ".\n//// Number of trees loaded:" + rdn.getNumTrees() ;
			Utils.appendString(willFile, addString);
		}
		if (!resampleExamples) {
			String chkptEgFile = BoostingUtils.getCheckPointExamplesFile(saveModelName);
			if (Utils.fileExists(chkptEgFile)) {
				Utils.appendString(willFile, "\n//// Also loaded examples from " + chkptEgFile);
				try {

					ObjectInputStream ois = new ObjectInputStream(new CondorFileInputStream(chkptEgFile));

					Object obj = ois.readObject();
					while(obj != null) {
						RegressionRDNExample ex = (RegressionRDNExample)obj;
						egs.add(ex);
						obj = ois.readObject();
					}

					ois.close();
				} 
				catch(Exception e) {
					Utils.reportStackTrace(e);
					Utils.error("Problem in writing examples in createCheckPointForModel.");
				}
			}
		}
		
		String chkptLitFile = BoostingUtils.getCheckPointFlattenedLitFile(saveModelName);
		if (Utils.fileExists(chkptLitFile)) {
			List<Literal> lits = setup.getInnerLooper().getParser().readLiteralsInPureFile(chkptLitFile);
			addToFlattenedLiterals(lits);
			Utils.appendString(willFile, "\n//// Also loaded " + theseFlattenedLits.size() + " flattened literals from " + chkptLitFile);
		}
	}

	private void createCheckPointForModel(ConditionalModelPerPredicate rdn, String saveModelName) {
		String chkptFile = BoostingUtils.getCheckPointFile(saveModelName);
		rdn.saveModel(chkptFile);
		
		// Save the examples if not re-sampling e.g.s
		if (!resampleExamples) {
			String chkptEgFile = BoostingUtils.getCheckPointExamplesFile(saveModelName);
			// Need to write examples only during first iteration
			if (Utils.fileExists(chkptEgFile)) {
				try {

					ObjectOutputStream oos = new ObjectOutputStream(new CondorFileOutputStream(chkptEgFile));
					for (RegressionRDNExample eg : egs) {
						oos.writeObject(eg);
					}
					oos.close();
				} 
				catch(Exception e) {
					Utils.reportStackTrace(e);
					Utils.error("Problem in writing examples in createCheckPointForModel.");
				}
			}
		}
		
		File chkptLitFile = new CondorFile(BoostingUtils.getCheckPointFlattenedLitFile(saveModelName));
		Utils.writeStringToFile("// Checkpointed flattened literals\n", chkptLitFile);
		
		try {
			BufferedWriter ckptLitWriter = new BufferedWriter(new FileWriter(chkptLitFile));
			for (Literal lit : theseFlattenedLits) {
				ckptLitWriter.write(lit.toString() + "\n");
			}
			ckptLitWriter.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}
	

	private void setParamsUsingSetup(WILLSetup willSetup) {
		String lookup;
		if ((lookup =  willSetup.getHandler().getParameterSetting("resampleEgs")) != null) {
			resampleExamples = Boolean.parseBoolean(lookup);
		}
		if ((lookup =  willSetup.getHandler().getParameterSetting("singleTheory")) != null) {
			learnSingleTheory = Boolean.parseBoolean(lookup);
		}
		if ((lookup =  willSetup.getHandler().getParameterSetting("lineSearch")) != null) {
			performLineSearch = Boolean.parseBoolean(lookup);
		}
		
	}

	private Collection<Literal> theseFlattenedLits = new HashSet<Literal>(4);
	private RegressionTree getWILLTree(List<RegressionRDNExample> newDataSet, int modelNumber, int i) {
		TreeStructuredTheory th = null;
		Theory thry = null;
		try {
			// WILL somehow loses all the examples after every run.  TODO - JWS: Guess there is some final cleanup. 
			setup.getOuterLooper().setPosExamples(BoostingUtils.convertToListOfExamples(newDataSet));
			// Make sure the invented predicates (if any) have unique names.
			setup.getHandler().setInventedPredicateNameSuffix("_" + (i + 1));
			setup.getOuterLooper().setPrefixForExtractedRules("");
			if (learnSingleTheory) {
				setup.getOuterLooper().setPostfixForExtractedRules(getTreeSuffix(i + 1));
			} else {
				setup.getOuterLooper().setPostfixForExtractedRules("");
			}
			
			thry = setup.getOuterLooper().executeOuterLoop();

			if (thry instanceof TreeStructuredTheory) {
				th = (TreeStructuredTheory)thry;
				Collection<Literal> currentFlattenedLits = th.getUniqueFlattenedLiterals();
				addToFlattenedLiterals(currentFlattenedLits);
				if (i==10) dumpTheoryToFiles(th,modelNumber,10);
				else dumpTheoryToFiles(th, modelNumber, i);
			}
		} catch (SearchInterrupted e) {
			Utils.reportStackTrace(e);
			Utils.error("Problem in getWILLTree.");
		}
		
		LearnRegressionTree learner = new LearnRegressionTree(setup);
		RegressionTree      tree    = learner.parseTheory(thry);
		return tree;
	}


	private RegressionTree getYapTree(List<RegressionRDNExample> newDataSet, int modelNumber, int i) {
		// Give new dataset to tree learner.
		String prefix =  cmdArgs.getModelDirVal() + "/yap/"; 

		String outfile = prefix + "Output" + targetPredicate + i + ".pl";
		String infile  = prefix + "Input"  + targetPredicate + (newInputFileForEachTree? i : "") +	BoostingUtils.getLabelForModelNumber(modelNumber) + ".pl";
		Utils.ensureDirExists(infile);
		try {
			writeDataSetForYap(newDataSet, infile);
		} catch (IOException e1) {
			Utils.reportStackTrace(e1);
			Utils.error("Problem in getYapTree.");
		}
		runYapTreeLearner(infile, outfile);
		// Add tree to set of boosted trees.

		LearnRegressionTree learner = new LearnRegressionTree(setup);
		try {
			RegressionTree tree = learner.parsePrologRegressionTrees(outfile);
			return tree;
			//tree.printTrees();
		} catch (NumberFormatException e) {
			Utils.reportStackTrace(e);
			Utils.error("Problem in getYapTree.");
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Problem in getYapTree.");
		}
		// Technically, should never reach here because of the catch statements before.
		return null;
	}


	private void runYapTreeLearner(String infile, String outfile) {
		String yapPath        = cmdArgs.getYapBinVal();
		String yapTreeLearner = cmdArgs.getTreelearnerVal();
		String command        = yapPath + " -l  " + yapTreeLearner + " -- " + infile + " " +  getYapSettingsFile() + " " + outfile ;
		// Call yap here
		Process p;
		try {
			System.out.println("Running yap command:" + command);
			p = Runtime.getRuntime().exec(command);
			InputStream is = p.getInputStream();
			int c;
			while((c=is.read()) != -1) {
				System.out.print((char)c);
			}
			p.waitFor();
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Problem in runYapTreeLearner.");
		} catch (InterruptedException e) {
			Utils.reportStackTrace(e);
			Utils.error("Problem in runYapTreeLearner.");
		}
	}

	private boolean doEarlyStop(List<RegressionRDNExample> old_eg_set, SingleModelSampler sampler) {
		if (stopIfFewChanges && old_eg_set != null) {
			int numOfEgSame = getNumUnchangedEx(old_eg_set, minGradientForSame, sampler);
			if (debugLevel > 0) { Utils.println("% Only " + numOfEgSame + " out of " + Utils.getSizeSafely(old_eg_set)); }
			if (((double)numOfEgSame/(double)old_eg_set.size()) > minPercentageSameForStop) {
				return true;
			} 
		} else {
			if(old_eg_set != null) {
				int numOfEgSame = getNumUnchangedEx(old_eg_set, minGradientForSame, sampler);
				if (debugLevel > 0) { Utils.println("% Only " + numOfEgSame + " out of " + Utils.getSizeSafely(old_eg_set) + " converged."); }
			}
		}
		return false;
	}

	private int getNumUnchangedEx(List<RegressionRDNExample> oldEgSet, double grad, SingleModelSampler sampler) {
		int counter=0;
		for (Example ex : oldEgSet) {
			RegressionRDNExample eg = (RegressionRDNExample)ex;
			ProbDistribution old_prob = eg.getProbOfExample();

			sampler.getExampleProbability(eg);
			ProbDistribution new_prob = eg.getProbOfExample();

			// double eg_grad = Math.abs((new_prob - old_prob)); // / old_prob);
			ProbDistribution diff = new ProbDistribution(old_prob);
			diff.scaleDistribution(-1);
			diff.addDistribution(new_prob);
			double eg_grad = diff.norm();
			if (eg_grad < grad) {
				counter++;
			} else {
				//
			}
			//System.out.println(eg +" " + new_prob +" " + old_prob +" " + eg_grad);
		}
		return counter;
	}

	private void writeDataSetForYap(List<RegressionRDNExample> newDataSet, String infile) throws IOException {
		BufferedWriter writer=null;
		try {
			writer = new BufferedWriter(new CondorFileWriter(Utils.ensureDirExists(infile)));
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Problem in writeDataSetForYap.");
		}
		boolean oldQMark = setup.getHandler().doVariablesStartWithQuestionMarks();
		setup.getHandler().usePrologNotation();

		int counter=1;
		for (RegressionRDNExample ex : newDataSet) {
			if (Utils.diffDoubles(ex.getWeightOnExample(), 1)) {
				Utils.waitHere("Weighted examples wont work with Yap. Remove weights or use WILL.");
			}
			
			String literal = "";

			literal = "example("  + counter++ + "," + ex.toString() +  "," + ex.getOutputValue() + ").";
			//}
			//System.out.println(ex.toString());
			writer.write(literal + "\r\n");
		}
		Iterable<Literal> lits = setup.getInnerLooper().getFacts();
		for (Literal lit : lits) {
			if(!lit.predicateName.name.equals("length") &&
					!lit.predicateName.name.endsWith("ontainsText") &&
					!lit.predicateName.name.endsWith("ordString") ) {
				//	System.out.println(lit.predicateName.name);
				writer.write(lit.toString() + ".\r\n");
			}
		}

		if (oldQMark) { setup.getHandler().setVariablesStartWithQuestionMarks(); }
		writer.close();
		System.out.println("Writer closed");
	}

	public void getSampledPosNegEx(List<RegressionRDNExample> all_exs) {

		if (egs != null) {
			for (int i = 0; i < Utils.getSizeSafely(egs); i++) {
				RegressionRDNExample eg = egs.get(i);
				eg.clearCache();
			}
		}
		if (!resampleExamples) {
			if (egs != null) {
				all_exs.addAll(egs);
				return;
				//	return numPosEx;
			}
		} else {
			// Only sample the second time onwards.
			if (egs != null) {
				setup.prepareExamplesForTarget(targetPredicate);
			}
		}
		all_exs.addAll(BoostingUtils.castToListOfRegressionRDNExamples(setup.getOuterLooper().getPosExamples()));
		Utils.println("% Dataset size: " + Utils.comma(all_exs));
		egs = all_exs;
	}

	private List<RegressionRDNExample> buildDataSet(String targetPredicate, SRLInference sampler, String gradFile) {
		List<RegressionRDNExample> all_exs = new ArrayList<RegressionRDNExample>();
		double scaleFactor = 1e8; // Used in EM to scale up the gradients

		getSampledPosNegEx(        all_exs);
		// No need to get sample probabilities as there is no \psi_0 or gradient.
		if (!disableBoosting) {
			Utils.println("Computing probabilities");
			long start = System.currentTimeMillis();
			if (setup.getLastSampledWorlds() != null) {
				if (cmdArgs.getHiddenStrategy().equals("MAP")) { 
					sampler.getProbabilitiesUsingSampledStates(setup.getLastSampledWorlds(), all_exs);
				} else {
					 if (cmdArgs.getHiddenStrategy().equals("EM")) {
						 // Expand the examples to have one example for every hidden state. i.e. 
						 // create NxW examples from N examples and W hidden states
						 int old_size = all_exs.size();
						 all_exs = createExamplesForEachState(setup.getLastSampledWorlds(), all_exs, sampler);
						 Utils.println("Created " + all_exs.size() + " from " + old_size + " examples and " + setup.getLastSampledWorlds().getWorldStates().size() + " world states");
						 if (!cmdArgs.isIgnoreStateProb()) {
							 double mostLikelyStateProb = 0;
							 for (HiddenLiteralState currState : setup.getLastSampledWorlds().getWorldStates()) {
								 double currStateProb = currState.getStatePseudoProbability();
								 if (currStateProb > mostLikelyStateProb) { mostLikelyStateProb = currStateProb; }
							 }
							 scaleFactor = 1 / (1 * mostLikelyStateProb);
						 }
						// Utils.waitHere("Scaled gradients by: " + scaleFactor + " since max prob=" + mostLikelyStateProb);		 
					 } else {
						 Utils.error("What to do with the hidden states ? Set strategy to MAP or EM. Currently set as : " + cmdArgs.getHiddenStrategy());
					 }
				}
			} else {
				sampler.getProbabilities(all_exs);
//				for (RegressionRDNExample regressionRDNExample : all_exs) {
//					Utils.println("The dataset example regression value:" + regressionRDNExample.toPrettyString() + " reg val:" + regressionRDNExample.originalRegressionOrProbValue);
//				}
			}
			long end = System.currentTimeMillis();
			Utils.println("prob time:"+Utils.convertMillisecondsToTimeSpan(end-start));
		}
		
		
		// Update facts based on the sampled states
		if (cmdArgs.getHiddenStrategy().equals("MAP")) {
			SRLInference.updateFactsFromState(setup, setup.getLastSampledWorlds().getWorldStates().get(0));
		}
		BufferedWriter gradWriter = null;
		// for debugging
		boolean foundhidden = false;
		
		for (int i = 0; i < Utils.getSizeSafely(all_exs); i++) {
			
			RegressionRDNExample eg = all_exs.get(i);
			eg.clearCache();
			if(cmdArgs.isLearnRegression() || cmdArgs.isLearnProbExamples()) {
				eg.setOutputValue(eg.originalRegressionOrProbValue - eg.getProbOfExample().getProbOfBeingTrue());
				// Utils.println("Set gradient: " + eg.getOutputValue());
				continue;
			}
			
			if (eg.isHiddenLiteral()) { foundhidden = true; }
			if (disableBoosting) {
				// TODO What would be the best value ?
				if (eg.isOriginalTruthValue()) {
					eg.setOutputValue(4);
					
				} else {
					eg.setOutputValue(-4);
				}
			} else {
				ProbDistribution probDistr = eg.getProbOfExample();
				if (probDistr.isHasDistribution()) {
					double[] base_prob = null;					
					double[] distr = probDistr.getProbDistribution();
					if (eg.isHiddenLiteral()) {
						// Utils.error("Can't handle distributions for hidden examples");
						ProbDistribution base_distr = null;
						if (cmdArgs.getHiddenStrategy().equals("EM")) {
							if (((RegressionRDNExample)eg).getStateAssociatedWithOutput() == null) {
								Utils.error("Associated state not set for example: " + eg);
							}
							HiddenLiteralState stateForEx = ((RegressionRDNExample)eg).getStateAssociatedWithOutput();
							base_distr = stateForEx.getConditionalDistribution(eg);
						} else {
							base_distr = setup.getLastSampledWorlds().sampledProbOfExample(eg);
						}
						base_prob = base_distr.getProbDistribution();
					} else {
						base_prob = VectorStatistics.createIndicator(distr.length, eg.getOriginalValue());
					}

					// double[] indic = VectorStatistics.createIndicator(distr.length, eg.getOriginalValue());
					double[] grad  = VectorStatistics.subtractVectors(base_prob, distr);
					
					// Only update for EM
					if (cmdArgs.getHiddenStrategy().equals("EM")) {
						if (((RegressionRDNExample)eg).getStateAssociatedWithOutput() == null) {
							Utils.error("Associated state not set for example: " + eg);
						}
						if (!cmdArgs.isIgnoreStateProb()) {
							double stateProb = ((RegressionRDNExample)eg).getStateAssociatedWithOutput().getStatePseudoProbability();
							grad = VectorStatistics.scalarProduct(grad, stateProb*scaleFactor);
						}
					}
					eg.setOutputVector(grad);
				} else {
					double prob = probDistr.getProbOfBeingTrue();
					if (eg.isHiddenLiteral()) {
						
						// Debugging
						if (!(cmdArgs.getHiddenStrategy().equals("EM") || cmdArgs.getHiddenStrategy().equals("MAP"))) {
							Utils.error("Using hidden examples for non-EM strategies: " + cmdArgs.getHiddenStrategy());
						}

						if (cmdArgs.getHiddenStrategy().equals("EM")) {
							if (((RegressionRDNExample)eg).getStateAssociatedWithOutput() == null) {
								Utils.error("Associated state not set for example: " + eg);
							}
							HiddenLiteralState stateForEx = ((RegressionRDNExample)eg).getStateAssociatedWithOutput();
							ProbDistribution exampleDistr = stateForEx.getConditionalDistribution(eg);
							if (cmdArgs.isIgnoreStateProb()) {
								eg.setOutputValue(exampleDistr.getProbOfBeingTrue() - prob);
							} else {
								double probYminusEx = stateForEx.getStatePseudoProbability() / exampleDistr.probOfTakingValue(stateForEx.getAssignment(eg));
								double gradient = (exampleDistr.getProbOfBeingTrue() * probYminusEx) - (probYminusEx * prob);
								eg.setOutputValue(gradient*scaleFactor);
							}
						} else {
							ProbDistribution base_prb_dist = setup.getLastSampledWorlds().sampledProbOfExample(eg);
							if (base_prb_dist.isHasDistribution()) {
								Utils.waitHere("Should not have distribution");
							}
							double base_prb = base_prb_dist.getProbOfBeingTrue();
							eg.setOutputValue(base_prb - prob);
						}
						
						// Utils.println("Setting grad for " + eg.toPrettyString("") + " at " + base_prb + " - " + prob + " = " + eg.outputValue);
					} else {
						double stateProb = 1;
						// Only set for EM
						if (cmdArgs.getHiddenStrategy().equals("EM")) {
							if (cmdArgs.isIgnoreStateProb()) { 
								stateProb = 1.0; 
							} else { 
								if (((RegressionRDNExample)eg).getStateAssociatedWithOutput() == null) {
									Utils.error("Associated state not set for example: " + eg);
								}
								stateProb = scaleFactor * ((RegressionRDNExample)eg).getStateAssociatedWithOutput().getStatePseudoProbability();
							}
						}
						if (cmdArgs.isSoftM()){
							// Softm
							double alpha = cmdArgs.getAlpha();
						    double beta = cmdArgs.getBeta();
							if (eg.isOriginalTruthValue()) {
								eg.setOutputValue(1 - prob/(prob + (1-prob)* Math.exp(alpha)));					
							} else {
								eg.setOutputValue(1 - prob/(prob + (1-prob)* Math.exp(-beta)));
							}
						} else if (adviceGradients=null){
							// Neither advice nor softm
							if (eg.isOriginalTruthValue()) {
								eg.setOutputValue(stateProb * (1 - prob));					
							} else {
								eg.setOutputValue(stateProb * (0 - prob));
							}
						} else {
							// Advice
							if (eg.isOriginalTruthValue()) {
								eg.setOutputValue(cmdArgs.getAdviceWt() * adviceGradients.get(eg) + (1-cmdArgs.getAdviceWt())*(stateProb * (1 - prob)));
							} else {
								eg.setOutputValue(cmdArgs.getAdviceWt() * adviceGradients.get(eg) + (1-cmdArgs.getAdviceWt())*(stateProb * (0 - prob)));
							}
						}
					}
				}
				if (printGradients ) {
					try {
						if (gradWriter == null) {
							gradWriter = new BufferedWriter(new FileWriter(gradFile));
						}
						gradWriter.write(eg.getOutputValue() + " " + eg.isOriginalTruthValue());
						gradWriter.newLine();
					} catch (IOException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				}
			}
		//	Utils.println(eg.toPrettyString());
		}
		if (!foundhidden) {
			Utils.println("No hidden examples for : " + targetPredicate);
		}
		all_exs = egSubSampler.sampleExamples(all_exs);
		if (gradWriter != null) {
			try {
				gradWriter.close();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		return all_exs;
	}
	

	private List<RegressionRDNExample> createExamplesForEachState(
			HiddenLiteralSamples lastSampledWorlds,
			List<RegressionRDNExample> all_exs, SRLInference sampler) {
		List<RegressionRDNExample> new_Exs = new ArrayList<RegressionRDNExample>();
		for (HiddenLiteralState state : lastSampledWorlds.getWorldStates()) {
			//Utils.println("State prob:" + state.getStatePseudoProbability());
			// Set facts using the hidden state
			SRLInference.updateFactsFromState(setup, state);
			// Needed by the tree learning code to set the facts required by each example
			state.updateStateFacts(setup);
			// Calculate probabilities given the current state
			sampler.getProbabilities(all_exs);
			for (RegressionRDNExample rex : all_exs) {
				// Create a copy as we are going to set the sampled state for each example. 
				RegressionRDNExample newRex = new RegressionRDNExample(rex);
				newRex.setStateAssociatedWithOutput(state);
				new_Exs.add(newRex);
			}
		}
		
		// Subsample examples
		if (cmdArgs.getEmSampleProb() < 1) {
			for (int i = new_Exs.size()-1 ; i >= 0 ; i--) {
				if (Utils.random() > cmdArgs.getEmSampleProb()) {
					new_Exs.remove(i);
				}
			}
		}
		return new_Exs;
	}

	// ------------------------------------------------------
	// ------------------------------------------------------
	// Functions that write various useful theory/prolog files
	// ------------------------------------------------------
	// ------------------------------------------------------
	public static final String LOG_PRIOR_PREDICATE = "logPrior";
	public static final String STEPLEN_PREDICATE_PREFIX = "stepLength";

	private File getWILLsummaryFile() {  // Always recompute in case 'targetPredicate' changes.
	//	return new CondorFile(getWILLFile(setup.getOuterLooper().getWorkingDirectory() + "/" +  cmdArgs.getModelDirVal(), cmdArgs.getModelFileVal(), targetPredicate));
		return Utils.ensureDirExists(getWILLFile(cmdArgs.getModelDirVal(), cmdArgs.getModelFileVal(), targetPredicate));
	}
	
	public static final String getWILLFile(String dir, String postfix, String predicate) {
		String filename = dir + "/WILLtheories/" + predicate + "_learnedWILLregressionTrees" + BoostingUtils.getLabelForCurrentModel();
		if (postfix != null) {
			filename += "_" + postfix;
		}
		filename += Utils.defaultFileExtensionWithPeriod;
		return filename;
	}

	public void reportStats() {
		setup.reportStats();
		Utils.println("\n% Memory usage by LearnBoostedRDN:");
		Utils.println("%  |egs|                = " + Utils.comma(egs));
		Utils.println("%  |theseFlattenedLits| = " + Utils.comma(theseFlattenedLits));
	}


	private void addToFlattenedLiterals(Collection<Literal> lits) { // Written by JWS.
		if (lits == null) { return; }
		for (Literal lit : lits) {			
			if (lit.member(theseFlattenedLits, false)) { 
				// Utils.println(" " + lit + " already in " + theseFlattenedLits); 
			}
			else { theseFlattenedLits.add(lit); } 
		}
	}
	private void dumpTheoryToFiles(Theory th, int modelNumber, int i) {
		String stringToPrint=null;
		if (i==10) stringToPrint = (i < 0 ? "" : "\n%%%%%  WILL-Produced Tree " + "Combined" + " @ " + Utils.getDateTime() + ".  [" + Utils.reportSystemInfo() + "]  %%%%%\n\n"); 
		else stringToPrint = (i < 0 ? "" : "\n%%%%%  WILL-Produced Tree #" + (i + 1) + " @ " + Utils.getDateTime() + ".  [" + Utils.reportSystemInfo() + "]  %%%%%\n\n");
		if (debugLevel > 0 && i >= 0) { Utils.println(stringToPrint); }
		File file = getWILLsummaryFile();
		if (i >= 0) { Utils.appendString(file, stringToPrint + th.toPrettyString(), cmdArgs.useLockFiles); } 
		else { // Write a file right away in case a run crashes.
			
			// First save the old model file
			// Rename single model files.
			if (file.exists()) {
				RunBoostedRDN.renameAsOld(file);
			}
			
			
			stringToPrint = setup.getHandler().getStringToIndicateCurrentVariableNotation();  // Assume we don't change the variable indicator mid-run.
			stringToPrint += "\n% maxTreeDepthInNodes                 = " + Utils.comma(setup.getOuterLooper().getMaxTreeDepth())                        + "\n";
			stringToPrint +=   "% maxTreeDepthInLiterals              = " + Utils.comma(setup.getOuterLooper().getMaxTreeDepthInLiterals())              + "\n";
			stringToPrint +=   "% maxNumberOfLiteralsAtAnInteriorNode = " + Utils.comma(setup.getOuterLooper().getMaxNumberOfLiteralsAtAnInteriorNode()) + "\n";
			stringToPrint +=   "% maxFreeBridgersInBody               = " + Utils.comma(setup.getOuterLooper().innerLoopTask.maxFreeBridgersInBody)      + "\n";
			stringToPrint +=   "% maxNumberOfClauses                  = " + Utils.comma(setup.getOuterLooper().maxNumberOfClauses)                       + "\n";
			stringToPrint +=   "% maxNodesToConsider                  = " + Utils.comma(setup.getOuterLooper().innerLoopTask.getMaxNodesToConsider())    + "\n";
			stringToPrint +=   "% maxNodesToCreate                    = " + Utils.comma(setup.getOuterLooper().innerLoopTask.getMaxNodesToCreate())      + "\n";
			stringToPrint +=   "% maxAcceptableNodeScoreToStop        = " + Utils.truncate(setup.getOuterLooper().getMaxAcceptableNodeScoreToStop(), 3)  + "\n";
			stringToPrint +=   "% negPosRatio                         = " + Utils.truncate(cmdArgs.getSampleNegsToPosRatioVal(),3)                       + "\n";
			stringToPrint +=   "% testNegPosRatio                     = " + Utils.truncate(cmdArgs.getTestNegsToPosRatioVal(),  3)                       + "\n";
			stringToPrint +=   "% # of pos examples                   = " + Utils.comma(setup.getOuterLooper().getNumberOfPosExamples())                 + "\n";
			stringToPrint +=   "% # of neg examples                   = " + Utils.comma(setup.getOuterLooper().getNumberOfNegExamples())                 + "\n";
			// Utils.waitHere("dumpTheoryToFiles: \n" + stringToPrint);
			Utils.writeStringToFile(stringToPrint + "\n", file); 
		}
		if (i >= 0) {
			if (debugLevel > 0) { Utils.println(th.toPrettyString()); }
			// 	Model directory is set to the working directory as the default value.
			if (th instanceof TreeStructuredTheory) {
				String tree_dotfile = cmdArgs.getModelDirVal() + "bRDNs/dotFiles/WILLTreeFor_" + targetPredicate + i + BoostingUtils.getLabelForCurrentModel() + ".dot";
				Utils.ensureDirExists(tree_dotfile);
				if(i<cmdArgs.getMaxTreesVal())
				((TreeStructuredTheory)th).writeDOTFile(tree_dotfile);
			}
		}
	}

	/**
	 * 
	 * @param i The tree index(starts from 1)
	 * @return Suffix that is used for filenames and rules.
	 */
	public static String getTreeSuffix(int i) {
		return "_tree" + i;
	}
	 
	public static final String stepLengthPredicate(int i) {
		return LearnBoostedRDN.STEPLEN_PREDICATE_PREFIX + getTreeSuffix(i);
	}
	
	private void addPrologCodeForUsingAllTrees(ConditionalModelPerPredicate rdn, int numberOfTrees) { // Added by JWS.
		if (numberOfTrees < 1) { return; }
		File file = getWILLsummaryFile();
		List<Literal> targets = setup.getInnerLooper().getTargets();
		Literal       target  = null;
		if (Utils.getSizeSafely(targets) == 1) { target = targets.get(0); } else { Utils.error("Should only have one target.  Have: " + targets); }
		if (!target.predicateName.name.equals(targetPredicate) && !target.predicateName.name.equals(WILLSetup.multiclassPredPrefix + targetPredicate) ) { 
			Utils.error("These predicate names should match: targetPredicate = " + targetPredicate + " and target = " + target); 
		}

		String stringToPrint = "\n\n%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n%%%%%  Final call for computing score for " + targetPredicate + ".  %%%%%\n%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n\n";

		for (int i = 0; i < numberOfTrees; i++) {
			String sentence = rdn.getStepLengthSentence(i+1);
			stringToPrint += sentence +"\n";
		}
		
		stringToPrint += "\n" + rdn.getLogPriorSentence();

		stringToPrint += "\n" + getComputationPrologRules(numberOfTrees); 
		if (!theseFlattenedLits.isEmpty()) {
			stringToPrint += "\nflattenedLiteralsInThisSetOfTrees(" + targetPredicate + ", " + theseFlattenedLits.size() + ", [\n";
			boolean firstTime = true;
			for (Literal lit : theseFlattenedLits) {
				if (firstTime) { firstTime = false; } else { stringToPrint += ",\n"; }
				stringToPrint += "   " + lit;
			}
			stringToPrint += "]).";
			theseFlattenedLits.clear();
		} else {
			stringToPrint += "\nflattenedLiteralsInThisSetOfTrees(0, []).";
		}

		Utils.appendString(file, stringToPrint, cmdArgs.useLockFiles);
		if (debugLevel > 0) { Utils.println(stringToPrint); }
	}



	private String getComputationPrologRules(int numberOfTrees) {
		String totalStr    = setup.getInnerLooper().getStringHandler().convertToVarString("Total");
		String treeStr     = setup.getInnerLooper().getStringHandler().convertToVarString("TreesToUse");
		String stepStr     = setup.getInnerLooper().getStringHandler().convertToVarString("StepLen");
		String logPriorStr = setup.getInnerLooper().getStringHandler().convertToVarString("LogPrior");
		
		String argsString  = "";
		// The error checking whether this matches the target predicate is done in addPrologCodeForUsingAllTrees.
		List<Literal> targets = setup.getInnerLooper().getTargets();
		Literal       target  = null;
		if (Utils.getSizeSafely(targets) == 1) { target = targets.get(0); } else { Utils.error("Should only have one target.  Have: " + targets); }

		for (int i = target.numberArgs() - 1; i >= 0; i--) { argsString = target.getArgument(i) + ", " + argsString; }
		String stringToPrint = targetPredicate + "(" + argsString + totalStr + ") :- // A general accessor. \n";
		stringToPrint += "   " + targetPredicate + "(" + argsString + "1000000, "  + totalStr + "), !.\n";
		stringToPrint += targetPredicate + "(" + argsString + totalStr + ") :- waitHere(\"This should not fail\", " + targetPredicate + "(" + argsString + totalStr + ")).\n\n";

		stringToPrint += targetPredicate + "(" + argsString + treeStr + ", "  + totalStr + ") :- // A tree-limited accessor (e.g., for tuning the number of trees to use).\n";
		stringToPrint += "   " + LOG_PRIOR_PREDICATE + "(" + logPriorStr + "),\n";
		for (int i = 1; i <= numberOfTrees; i++) {
			stringToPrint += "   getScore_" + targetPredicate + getTreeSuffix(i) + "(" + argsString + treeStr + ", " + totalStr + i + "),\n";
		}

		stringToPrint += "   " + totalStr + " is " + logPriorStr ;
		for (int i = 1; i <= numberOfTrees; i++) {
			stringToPrint += " + " + totalStr + i;
		}
		stringToPrint += ",\n   !.\n" + targetPredicate + "(" + argsString + treeStr + ", " + totalStr + ") :- waitHere(\"This should not fail\", " + targetPredicate + "(" + argsString + treeStr + ", " + totalStr + ")).\n";
		for (int i = 1; i <= numberOfTrees; i++) { 
			stringToPrint += "\ngetScore_" + targetPredicate + getTreeSuffix(i) + "(" + argsString + treeStr + ", 0.0) :- " + i + " > " + treeStr + ", !.";
			stringToPrint += "\ngetScore_" + targetPredicate + getTreeSuffix(i) + "(" + argsString + treeStr + ", " + totalStr + i + ") :- " + 
							targetPredicate + "_tree" + i + "(" + argsString + totalStr + "), " + stepLengthPredicate(i) + "(" + stepStr + "), " + 
							totalStr + i + " is " + totalStr +" * " + stepStr +  ".\n";
		}
		return stringToPrint;
	}
	public String getTargetPredicate() {
		return targetPredicate;
	}

	public void setTargetPredicate(String targetPredicate) {
		this.targetPredicate = targetPredicate;
	}

	/**
	 * @param yapSettingsFile the yapSettingsFile to set
	 */
	public void setYapSettingsFile(String yapSettingsFile) {
		this.yapSettingsFile = yapSettingsFile;
	}

	/**
	 * @return the yapSettingsFile
	 */
	public String getYapSettingsFile() {
		return yapSettingsFile;
	}

}
