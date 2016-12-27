package edu.wisc.cs.will.DataSetUtils;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.StringTokenizer;

import edu.wisc.cs.will.FOPC.HandleFOPCstrings;
import edu.wisc.cs.will.FOPC.Literal;

import edu.wisc.cs.will.FOPC.Sentence;
import edu.wisc.cs.will.FOPC.Term;

import edu.wisc.cs.will.FOPC_MLN_ILP_Parser.FileParser;
import edu.wisc.cs.will.MLN_Task.Wrapper;

/**
 * Creates 1-D bins by thresholding the values. Two kinds of constructors. One uses a string of positive examples separated by "." The other uses a list
 * of Example. Two functions are used for creation of bins. One uses a List<Sentence> for facts and List<Literal> for modes. The other uses string and 
 * stringBuffer. Either of these can be used for creation of the bins.
 * 
 */

public class CreateBins {

	private static String MODE = "mode:";
	private static String posExamples = null;
/*	private List<Sentence> factsList;
	private List<Example> posExampleList;
	private List<PredicateName> modesList;
*/	
	private HandleFOPCstrings stringHandler = new HandleFOPCstrings();
	private FileParser        parser        = new FileParser(stringHandler);
	public CreateBins(String posExString) {
		posExamples = posExString;		
	}

	public CreateBins(List<Example> posExampleList){
		posExamples = posExampleList.toString();
	}
	
	/*
	 * Takes facts and modes. Creates 1-D bin for the facts and appends them to the facts List. Similarly, the modes are appended too.
	 */	

	public void binFacts(List<Sentence> factsList, List<Literal> modesList){
		
		ArrayList<Literal> numberPredicateList = fetchNumberPredicates(modesList);
		String factsArray[] = new String[factsList.size()];
		int count = 0;
		for(Sentence currFact: factsList){
			factsArray[count] += currFact.toString();
			count++;
		}
		String facts = null;
		StringBuffer modes = new StringBuffer();
		for(Literal currPred:numberPredicateList){
			String predName = currPred.predicateName.toString();
			ArrayList<NumberObject> valueIndexList = new ArrayList<NumberObject>();
			for (String currFact : factsArray) {
				String[] currFactArray = convertStrToArray(currFact, "(");
				String factName = currFactArray[0].toLowerCase();
				if (factName.equals(predName)) {
					// Fact has the same name as the predicate. Now, extract the
					// number.
					String[] argsArray = convertStrToArray(currFactArray[1], ",");
					// argsArray[0] contains the world index ex: world1.
					String currIndex = "";// argsArray[0];
					for (String currArg : argsArray) {
						currArg = currArg.trim();
						currIndex += currArg;
						currIndex += ", ";

						try {
							Integer intValue = Integer.parseInt(currArg);
							int value = intValue.intValue();
							NumberObject currObj = new NumberObject();
							String index = currIndex.replaceAll(" " + currArg + ", ", "");
							currObj.worldIndex = index;
							currObj.value = value;
							currObj.pos = isCurrExamplePositive(posExamples,argsArray[0]);
							valueIndexList.add(currObj);

						} catch (Exception e) {

						}

					}

				}

			}

			// valueIndexList consists of all the Index,value pairs for the
			// current predicate.
			NumberObjectComparator currComparator = new NumberObjectComparator();
			Collections.sort(valueIndexList, currComparator);
			if (valueIndexList == null) {
				continue;
			}

			ArrayList<Double> boundaryValues = getBoundaryValues(valueIndexList);
			if (boundaryValues.isEmpty()) {
				continue;
			}
			
			String currMode = currPred.toString();
			
			for (Double boundaryV : boundaryValues) {
				double boundary = boundaryV.doubleValue(); // !!!!!!!!!!!
				String tempMode = "" + currMode;

				String tempString = "_lte__" + safeNumberName(boundary) + "(";
				String tempCurrMode = tempMode.replace("(", tempString);
				// String newMode = tempCurrMode.replace(" -number,", "");
				String newMode = tempCurrMode;
				modes.append(newMode);
				modes.append("\n");
				tempMode = "" + currMode;
				tempString = "_gte__" + safeNumberName(boundary) + "(";
				tempCurrMode = tempMode.replace("(", tempString);
				// newMode = tempCurrMode.replace(" -number,", "");
				newMode = tempCurrMode;
				modes.append(newMode);
				modes.append("\n");
				Literal tempNewMode = Wrapper.convertStringToLiteral(newMode, parser, stringHandler);
				modesList.add(tempNewMode);
				

				for (NumberObject currObj : valueIndexList) {
					String currFact = "";
					String factStringIndex = "(" + currObj.worldIndex;
					for (String tempFact : factsArray) {
						String tempPredName = tempFact.substring(0, tempFact
								.indexOf("("));
						if (tempPredName.toLowerCase().equals(predName)) {
							if (tempFact.indexOf(factStringIndex) != -1) {
								currFact += tempFact;
								break;
							}
						}
					}
					// Add to the facts
					if (currObj.value <= boundary) {
						@SuppressWarnings("unused")
						String tempPredName = currFact.substring(0, currFact
								.indexOf("("));

						String tempFact = currFact.replace("(", "_lte__"
								+ safeNumberName(boundary) + "(");

						facts += tempFact;
						facts += "\n";

					}
					if (currObj.value >= boundary) {
						@SuppressWarnings("unused")
						String tempPredName = currFact.substring(0, currFact
								.indexOf("("));

						String tempFact = currFact.replace("(", "_gte__"
								+ safeNumberName(boundary) + "(");
						facts += tempFact;
						facts += "\n";
						/*
						 * Add the new fact to the facts list
						 */
						Sentence newFact = Wrapper.convertStringToLiteral(tempFact, parser, stringHandler);
						factsList.add(newFact);
					}

				}

			}
			
		}
		
		
		
		
		
		
	}
	
	/*
	 * Function to get the number predicates from the modes and returns them as an array list. Currently handles number and float. Can be extended to include integer etc
	 */
	
	public ArrayList<Literal> fetchNumberPredicates(List<Literal> inputList) {

		ArrayList<Literal> finalModeList = new ArrayList<Literal>();
		//String[] stringArray = inputBuffer.toString().split(MODE); // Remove mode: from the modes and consider the rest
		
		for(Literal currMode : inputList){
			boolean isANumberPredicate = false;
			for(Term currTerm : currMode.getArguments()){
				if((currTerm.toString().equals("number"))||(currTerm.toString().equals("float"))){
					isANumberPredicate = true;
				}
			}
			
			if(isANumberPredicate){
				finalModeList.add(currMode);
			}
		}
		return finalModeList;
	}
	
	
	/*
	 * Takes facts and modes. Creates 1-D bin for the facts and appends them to the facts string and returns the fact string. Since modes are of type StringBuffer, it just appends to the modes.
	 */	
	public String binFactsModes(String facts, StringBuffer modes) {		
		ArrayList<String> numberPredicateList = fetchNumberPredicatesFromModes(modes);
		
		for (String predName : numberPredicateList) {
			
			String[] factsArray = facts.toString().split("\n");
			ArrayList<NumberObject> valueIndexList = new ArrayList<NumberObject>();
			for (String currFact : factsArray) {
				String[] currFactArray = convertStrToArray(currFact, "(");
				String factName = currFactArray[0].toLowerCase();
				if (factName.equals(predName)) {
					// Fact has the same name as the predicate. Now, extract the
					// number.
					String[] argsArray = convertStrToArray(currFactArray[1], ",");
					// argsArray[0] contains the world index ex: world1.
					String currIndex = "";// argsArray[0];
					for (String currArg : argsArray) {
						currArg = currArg.trim();
						currIndex += currArg;
						currIndex += ", ";

						try {
							Integer intValue = Integer.parseInt(currArg);
							int value = intValue.intValue();
							NumberObject currObj = new NumberObject();
							String index = currIndex.replaceAll(" " + currArg + ", ", "");
							currObj.worldIndex = index;
							currObj.value = value;
							currObj.pos = isCurrExamplePositive(posExamples,argsArray[0]);
							valueIndexList.add(currObj);

						} catch (Exception e) {

						}

					}

				}

			}

			// valueIndexList consists of all the Index,value pairs for the
			// current predicate.
			NumberObjectComparator currComparator = new NumberObjectComparator();
			java.util.Collections.sort(valueIndexList, currComparator);
			if (valueIndexList == null) {
				continue;
			}

			ArrayList<Double> boundaryValues = getBoundaryValues(valueIndexList);
			if (boundaryValues.isEmpty()) {
				continue;
			}
			String[] modesArray = modes.toString().split("\n");
			String currMode = "";
			int count = 0;
			for (String tempMode : modesArray) {

				if (tempMode.indexOf(predName + "(") != -1) {
					currMode += tempMode;
					break;
				}
				count++;
			}

			for (Double boundaryV : boundaryValues) {
				double boundary = boundaryV.doubleValue(); // !!!!!!!!!!!
				String tempMode = "" + currMode;

				String tempString = "_lte__" + safeNumberName(boundary) + "(";
				String tempCurrMode = tempMode.replace("(", tempString);
				// String newMode = tempCurrMode.replace(" -number,", "");
				String newMode = tempCurrMode;
				modes.append(newMode);
				modes.append("\n");
				tempMode = "" + currMode;
				tempString = "_gte__" + safeNumberName(boundary) + "(";
				tempCurrMode = tempMode.replace("(", tempString);
				// newMode = tempCurrMode.replace(" -number,", "");
				newMode = tempCurrMode;
				modes.append(newMode);
				modes.append("\n");

				for (NumberObject currObj : valueIndexList) {
					String currFact = "";
					String factStringIndex = "(" + currObj.worldIndex;
					for (String tempFact : factsArray) {
						String tempPredName = tempFact.substring(0, tempFact
								.indexOf("("));
						if (tempPredName.toLowerCase().equals(predName)) {
							if (tempFact.indexOf(factStringIndex) != -1) {
								currFact += tempFact;
								break;
							}
						}
					}
					// Add to the facts
					if (currObj.value <= boundary) {
						@SuppressWarnings("unused")
						String tempPredName = currFact.substring(0, currFact
								.indexOf("("));

						String tempFact = currFact.replace("(", "_lte__"
								+ safeNumberName(boundary) + "(");

						facts += tempFact;
						facts += "\n";

					}
					if (currObj.value >= boundary) {
						@SuppressWarnings("unused")
						String tempPredName = currFact.substring(0, currFact
								.indexOf("("));

						String tempFact = currFact.replace("(", "_gte__"
								+ safeNumberName(boundary) + "(");
						facts += tempFact;
						facts += "\n";
					}

				}

				int temp = 0;
				temp++;
			}

			// }

		}
		
		return facts;
		
	}
	
	
	
	/*
	 * Function to get the number predicates from the modes and returns them as an array list. Currently handles number and float. Can be extended to include integer etc
	 */
	
	public ArrayList<String> fetchNumberPredicatesFromModes(StringBuffer inputBuffer) {

		ArrayList<String> finalArrayList = new ArrayList<String>();
		String[] stringArray = inputBuffer.toString().split(MODE); // Remove mode: from the modes and consider the rest
		for (int i = 0; i < stringArray.length; i++) {
			String strTemp = stringArray[i];
			int j = strTemp.indexOf("number");
			int k = strTemp.indexOf("float");
			if ((j != -1) || (k != -1)) {
				String[] stringTempArray = convertStrToArray(strTemp, "("); // split the string into two halves: 1. before ( and 2. after (
				finalArrayList.add(stringTempArray[0].trim()); // add only the predicate name i.e., one before (
			}
		}

		return finalArrayList;
	}
	
	/*
	 * Converts a string to an array of strings based on the delimiter 
	 */
	
	public String[] convertStrToArray(String strList, String delimeter) {
		String[] strArray = null;
		if (strList != null) {
			StringTokenizer strTokenizer = new StringTokenizer(strList,
					delimeter);
			strArray = new String[strTokenizer.countTokens()];
			int count = 0;
			while (strTokenizer.hasMoreElements()) {
				strArray[count] = strTokenizer.nextToken();
				count++;
			}
		}
		return strArray;
	}

	/*
	 *  Get the boundary values based on the pos and neg values. The NumberObject associates the class with each of the value.
	 */
	
	public ArrayList<Double> getBoundaryValues(ArrayList<NumberObject> valueIndexList) {
		ArrayList<Double> boundaryValues = new ArrayList<Double>();
		int num_values = valueIndexList.size();

		int seg1_start = 0;
		int seg1_end = seg1_start;
		while ((seg1_end < (num_values - 1))
				&& (valueIndexList.get(seg1_start).value == valueIndexList
						.get(seg1_end + 1).value))
			seg1_end++;
		boolean seg1_has_pos = false;
		boolean seg1_has_neg = false;
		for (int i = seg1_start; i <= seg1_end; i++)
			if (valueIndexList.get(i).pos == true)
				seg1_has_pos = true;
			else
				seg1_has_neg = true;
		while (seg1_end < (num_values - 1)) {
			int seg2_start = seg1_end + 1;
			int seg2_end = seg2_start;
			while ((seg2_end < (num_values - 1))
					&& (valueIndexList.get(seg2_start).value == valueIndexList
							.get(seg2_end + 1).value))
				seg2_end++;
			boolean seg2_has_pos = false;
			boolean seg2_has_neg = false;
			for (int i = seg2_start; i <= seg2_end; i++)
				if (valueIndexList.get(i).pos == true)
					seg2_has_pos = true;
				else
					seg2_has_neg = true;
			if ((seg1_has_pos && (seg1_has_neg || seg2_has_neg))
					|| (seg1_has_neg && seg2_has_pos)) {
				double value = (double) (valueIndexList.get(seg1_end).value + valueIndexList
						.get(seg2_start).value) / 2;
				boundaryValues.add(value);
			}
			seg1_start = seg2_start;
			seg1_end = seg2_end;
			seg1_has_pos = seg2_has_pos;
			seg1_has_neg = seg2_has_neg;
		}

		return boundaryValues;
	}
	
	static private String safeNumberName(double value) {
		Double dvalue = new Double(value);
		String name = dvalue.toString();
		return (name.replace('.', '_').replace('+', 'p').replace('-', 'm'));
	}
	
	public boolean isCurrExamplePositive(String posEx, String index) {
		//String[] posExampleArray = posEx.split("\n");
		String[] posExampleArray = posEx.split(".");
		for (String currPosEx : posExampleArray) {
			int c = currPosEx.indexOf(index);
			if (c != -1)
				return true;
		}

		return false;

	}

	public static void main(String args){
		
	}
	
	
}


class NumberObject {
	public String worldIndex;
	public int value;
	public boolean pos;
	public boolean lessThanSplit;

}

class NumberObjectComparator implements Comparator<NumberObject> {
	public int compare(NumberObject a, NumberObject b) {
		if (a.value < b.value)
			return -1;
		if (a.value == b.value)
			return 0;
		return 1;

	}
}
