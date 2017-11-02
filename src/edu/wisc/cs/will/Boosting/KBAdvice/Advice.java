package edu.wisc.cs.will.Boosting.KBAdvice;

import java.util.ArrayList;
import java.util.List;

public class Advice {
	public List<AdviceInstance> advice;
	
	public Advice() {
		advice = new ArrayList<AdviceInstance>();
	}
	
	public void addAdvice(AdviceInstance adv){
		advice.add(adv);
	}
	

}
