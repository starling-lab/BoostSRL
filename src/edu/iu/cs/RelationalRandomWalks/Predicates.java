package edu.iu.cs.RelationalRandomWalks;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.Stack;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Predicates {
		
	public static boolean BalancedBracketCheck(String str)
	{
		Stack<Character> stack = new Stack<Character>();

	    char c;
	    for(int i=0; i < str.length(); i++) {
	    	c = str.charAt(i);
	    	if(c=='(')
	    		stack.push(c);
	    	else if(c==')')
	    	{
	    		if(stack.empty())
	    			return false;
	    		else
	    			stack.pop();
	    	}
	   }
	    
	    if(stack.empty())
	    	return true;
	    else
	    	return false;
	    
	}
	
	void CreatePredicatesInAlchemyFormat(HashSet<String> RW,String path) throws IOException
	{
		String NewLine,StoreAddress;
		boolean var;
		NewLine="";
		int stat;
		HashMap<Integer,Integer> statistics = new HashMap<Integer,Integer>(); 
		
		File file2 = new File(path);
		String parentDirName = file2.getAbsoluteFile().getParent();
		StoreAddress        = parentDirName+"/RWRPredicates.txt";
		File file = new File(StoreAddress);
		file.createNewFile();
		BufferedWriter writer = new BufferedWriter(new FileWriter(file));
		for(String lineRWR:RW){
			var = BalancedBracketCheck(lineRWR);
								
			if(var==false)
			{
				System.out.println("Bracket Imbalance: Correct it First !");
				return;
			}
					
			Pattern p = Pattern.compile("\\((.*?)\\)");
			Matcher m = p.matcher(lineRWR);
				
			int[] RStart = new int[1000];
			int[] REnd = new int[1000];
			int count=0;	
			
			while(m.find()) {
				RStart[count] = m.start();
				REnd[count] = m.end();
				count++;
				
			}
			
			if(statistics.get(count)!=null)
			{
				stat = statistics.get(count);
				statistics.put(count, stat+1);
			}
			else
			{
				statistics.put(count, 1);
			}
			
			NewLine ="";	
			for(int i=0;i<count;i++)
			{
				String rel,Arg1,Arg2;
				if(i==count-1)
				{
				  Arg2 = lineRWR.substring(REnd[i], lineRWR.length());
				}
				else
				{
					Arg2 = lineRWR.substring(REnd[i],RStart[i+1]);
				}
				
				if(i==0)
				{
					Arg1 = lineRWR.substring(0, RStart[i]);
				}
				else
				{
					Arg1 = lineRWR.substring(REnd[i-1],RStart[i]);
				}
				rel=lineRWR.substring(RStart[i]+1, REnd[i]-1);
				NewLine = NewLine+rel+"("+Arg1+","+Arg2+"),";
			}
			NewLine=NewLine.substring(0,NewLine.length()-1);
			System.out.println(NewLine);
			writer.write(NewLine+"\n");			
		}	
		writer.close();
		
		Set<Integer> key = statistics.keySet();
		System.out.println();
		System.out.println();
		int TotalRW=0;
		for(int k:key)
		{
			TotalRW = TotalRW+statistics.get(k);
			System.out.println("Path Length: "+k+" Number of Random Walks: "+statistics.get(k));
		}
		
		System.out.println("Total Random Walks: "+TotalRW);
		
		System.out.println();
		System.out.println();
		System.out.println("Final Random Walks Stored at :"+StoreAddress);

	}
	
	public static void main(String[] args) throws IOException {
		// TODO Auto-generated method stub
	}
}


