/**
 * 
 */
package edu.wisc.cs.will.Boosting.OneClass;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;
import edu.wisc.cs.will.Boosting.RDN.MultiClassExampleHandler;
import edu.wisc.cs.will.Boosting.RDN.RegressionRDNExample;
import edu.wisc.cs.will.Boosting.RDN.RunBoostedRDN;
import edu.wisc.cs.will.Boosting.RDN.WILLSetup;
import edu.wisc.cs.will.Boosting.RDN.MultiClassExampleHandler.ConstantLookupList;
import edu.wisc.cs.will.Boosting.Trees.FeatureTree;
import edu.wisc.cs.will.Boosting.Trees.RegressionMLNModel;
import edu.wisc.cs.will.Boosting.Trees.RegressionTree;
import edu.wisc.cs.will.Boosting.Utils.BoostingUtils;
import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.HandleFOPCstrings.VarIndicator;
import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CondorFileReader;
import edu.wisc.cs.will.Utils.condor.CondorFileWriter;

/**
 * @author tkhot
 *
 */
public class PropositionalizationModel {

	private String predicate;
	
	private int numTrees;
	
	List<FeatureTree> treeList;
	
	/**
	 * Save the constants for this predicate, if multiclass
	 */
	private ConstantLookupList constList = null;
	
	/**
	 * Prefix for every tree used while storing the tree.
	 * Generally set to the targetPredicate 
	 */
	private String treePrefix;
	
	
	private List<FeatureVector> oneClassExamples = null;
	
	public PropositionalizationModel() {	
		numTrees     = 0;
		treeList     = new ArrayList<FeatureTree>();
	}
	
	public void setTargetPredicate(String pred) {
		predicate = pred;
		
	}

	public int getNumTrees() {
		return numTrees;
	}

	public void saveModel(String filename) {
		Utils.println("% Saving model in: " + filename);
		Utils.ensureDirExists(filename);
		try {
			BufferedWriter writer = new BufferedWriter(new CondorFileWriter(filename, false)); // Create a new file.
			// Store the necessary facts
				// Number of trees
			writer.write(Integer.toString(numTrees));
			writer.newLine();
			// Prefix for boosted trees
			writer.write(treePrefix);
			writer.newLine();
			
			// target predicate
			writer.write(predicate);
			writer.newLine();
			
			// feature vectors
			if (oneClassExamples != null) {
			writer.write(Utils.toString(oneClassExamples, ","));
			writer.newLine();
			}
			
			// Now save the trees.
			for (int i = 0; i < numTrees; i++) {
				
				treeList.get(i).saveToFile(getTreeFilename(filename, treePrefix, i)); 
				
			}
			writer.close();	
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("saveMode: IO exception");
		}
	}
	
	public void loadModel(String filename, WILLSetup setup, int loadMaxTrees) {

		try {
			BufferedReader reader = new BufferedReader(new CondorFileReader(filename));
			String line = null;
			// Number of trees
			line = reader.readLine();
			int numberOfTrees = Integer.parseInt(line);
			
			// Only limit trees if >= 0
			if (loadMaxTrees >= 0) {
				// Make sure the numberOfTrees >= loadMaxTrees
				if (numberOfTrees < loadMaxTrees) {
					Utils.error("Number of trees in the model (" + numberOfTrees + ") is less than the trees to be loaded (" + loadMaxTrees + ").\nFile: " + filename);
				} else {
					if (numberOfTrees > loadMaxTrees) {
						Utils.println("Model had " + numberOfTrees + " trees but loading only " + loadMaxTrees);
					}
				}
				numberOfTrees = loadMaxTrees;
			}
			
			// Prefix for boosted trees
			line = reader.readLine();
			treePrefix = line;
			
			// target predicate
			line = reader.readLine();
			predicate = line;
			
			String vec=reader.readLine();
			if (! vec.isEmpty()) {
				oneClassExamples = new ArrayList<FeatureVector>();
				String[] examples = vec.split(",");
				for (int i = 0; i < examples.length; i++) {
					FeatureVector fvec = new FeatureVector();
					fvec.parseString(examples[i]);
					oneClassExamples.add(fvec);
				}
			}
			
			for (int i = 0; i < numberOfTrees; i++) {
					FeatureTree ftree = new FeatureTree(setup);
					String fileToLoad = getTreeFilename(filename, treePrefix, i);
					Utils.println("%   loadModel (#" + Utils.comma(i) + "): " + fileToLoad);
					ftree.loadFromFile(fileToLoad);
					treeList.add(ftree);
			}
			reader.close();
			Utils.println("%  Done loading " + Utils.comma(numberOfTrees) + " models.");
		} catch (FileNotFoundException e) {
			Utils.reportStackTrace(e);
			Utils.error("Problem encountered reading model:\n " + filename);
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Problem encountered reading model:\n " + filename);
		}
		
	}
	

	public void setTreePrefix(String prefix) {
		this.treePrefix = prefix;
		
	}

	public void setNumTrees(int maxTrees) {
		this.numTrees = maxTrees;		
	}

	public void addTree(FeatureTree tree) {
		treeList.add(tree);
		numTrees++;
	}

	public FeatureVector getFeatureVector(RegressionRDNExample rex) {
		FeatureVector features = new FeatureVector();
		for (FeatureTree ftree : treeList) {
			features.append(ftree.getFeatureVector(rex));
		}
		return features;
	}
	
	
	public void reparseModel(WILLSetup setup) {
			for (FeatureTree ftree : treeList) {
				ftree.setSetup(setup);
				ftree.reparseFeatureTree();
			}
			
		
		// Also reload the constants
		if (constList != null) {
			ConstantLookupList newConstList = new MultiClassExampleHandler.ConstantLookupList();
			newConstList.load(setup, constList.toString());
			setup.getMulticlassHandler().updateConstantList(predicate, newConstList);
		}
	}


	private String getTreeFilename(String modelFile, String prefix, int i) {
		int lastPos = modelFile.lastIndexOf('/');
		String path = modelFile.substring(0, lastPos + 1); 
		path += "Trees/" + prefix + BoostingUtils.getLabelForCurrentModel() + "Tree" + i +  ".tree";
		Utils.ensureDirExists(path);
		return path;
	}

	/**
	 * @return the oneClassExamples
	 */
	public List<FeatureVector> getOneClassExamples() {
		return oneClassExamples;
	}

	/**
	 * @param oneClassExamples the oneClassExamples to set
	 */
	public void setOneClassExamples(List<FeatureVector> oneClassExamples) {
		this.oneClassExamples = oneClassExamples;
	}

}
