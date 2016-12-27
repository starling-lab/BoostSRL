package edu.wisc.cs.will.Boosting.KBAdvice;

import java.util.ArrayList;
import java.util.List;

public class AdviceInstance {
	public List<String> prefTargets;
	public List<String> nonPrefTargets;
	public String clauseFile;
	
	public AdviceInstance() {
		prefTargets = new ArrayList<String>();
		nonPrefTargets = new ArrayList<String>();
	}
	
	public void addPrefTarget(String s) {
		prefTargets.add(s);
	}
	
	public void addNonPrefTarget(String s) {
		nonPrefTargets.add(s);
	}
	
	public void setFile(String s) {
		clauseFile = s;
	}
	
	public String getFile() {
		return clauseFile;
	}
	
}
