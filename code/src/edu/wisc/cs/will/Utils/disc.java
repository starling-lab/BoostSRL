package edu.wisc.cs.will.Utils;

import java.io.*;
import java.util.ArrayList;
import java.util.Collections;

import com.sun.xml.internal.ws.util.StringUtils;

import java.io.File;


class DiscPred{
	String prename=null;
	public String[] argsloc=null;
	public String[] binNum = null;
}
public class disc {	
	
	public static DiscPred trial(String line)
	{
	DiscPred D = new DiscPred();
	String[] mode = line.split("\\:");
	String[] pred = null;
	String[] temp = null;
	String[] args = null;
	String[] bins = null;
	if (mode[0].equals("disc"))
	{
		pred = mode[1].split("\\(\\[");
		pred[0]=pred[0].replace(" ", "");
		temp = pred[1].split("\\,\\[");
		temp[0] = temp[0].replace("]", "");
		temp[1] = temp[1].replace("]).", "");
		args=temp[0].split(",");
		bins=temp[1].split(",");
		}
	D.argsloc=args;
	D.binNum=bins;
	D.prename=pred[0];
	
	if (D.argsloc.length!=D.binNum.length)
	   {
		Utils.error("The argument array and the binsize array do not have equal number of elements");
	   }
	
	return D;	
	}
    public void Discretization(String DirectoryPath) throws IOException {
    	String [] trial=null;
    	trial=DirectoryPath.split("/");
    	String bkdp= DirectoryPath;
    	String factsdp=DirectoryPath;
    	String mergefile=DirectoryPath;
    	String delfile=DirectoryPath;
    	String preddp=DirectoryPath;
    	trial[trial.length-1]=trial[trial.length-1].replace("/","");
    	String [] trial1=trial[trial.length-1].split("\\\\");
    	String trial2=trial[trial.length-1].replace("\\"+trial1[trial1.length-1],"\\");
    	String prefix = trial1[trial1.length-1];
    	String bkname=prefix+"_bk.txt";
    	String alterbkpath=factsdp;
    	String factspath=factsdp+prefix+"_facts.txt";
    	String predpath=preddp+prefix+"_facts_";
    	//String predpath=preddp+"train_facts_";
    	String outpath=predpath+"disc.txt";
    	FileInputStream fstreamtemp = new FileInputStream(DirectoryPath+bkname);
        BufferedReader brtemp = new BufferedReader(new InputStreamReader(fstreamtemp));
        String strLinetemp;
        String[] bkline=null;
        String bkpath=null;
        boolean check=false;
        
        //Reading the background file in train folder, get the path of the background file outside
        while ((strLinetemp = brtemp.readLine()) != null && check==false)  
        {
        	if((strLinetemp.contains("import:"))&&(!strLinetemp.contains("//")))
        	{	bkline=strLinetemp.split("\\/");
        		bkline[1]=bkline[1].replaceAll("\".", "");   
        		bkpath=bkdp.replace(trial[trial.length-1]+"/", trial2+bkline[1]);
          		check=true;
        	}
        	else if((!strLinetemp.contains("import:")))
        	{
        		bkpath=alterbkpath.replace("/","\\"+prefix+"_bk.txt");
        		check=true;
        	}
        }
        brtemp.close();

        FileInputStream fstream = new FileInputStream(bkpath);
        
        BufferedReader br = new BufferedReader(new InputStreamReader(fstream));
        BufferedReader br_disc = new BufferedReader(new InputStreamReader(fstream));
        
        String strLine;
        
        //This object is an instance of Discpred class, contains predname, argloc, binNum
        ArrayList<DiscPred> DP = new ArrayList<DiscPred>();	        
        
          while ((strLine = br.readLine()) != null)   {
        	 if(strLine.contains("disc"))
        		if(!strLine.contains("//"))
                  DP.add(trial(strLine));
           }    
          br.close();

          String strLine1;
          int[] range = new int[50];
          //ArrayList<ArrayList<Double>> multD = new ArrayList<ArrayList<Double>> ();
          //ArrayList<ArrayList<Double>> threshold = new ArrayList<ArrayList<Double>> ();
          ArrayList<String> filenames = new ArrayList<>();
          ArrayList<String> prednames = new ArrayList<>();
          
          
          //For each predicate
          //Integer count_pred=0;
          for (DiscPred g: DP) 
          {	
        	  Integer a1=0; 
        	  ArrayList<ArrayList<Double>> multD = new ArrayList<ArrayList<Double>> ();
              ArrayList<ArrayList<Double>> threshold = new ArrayList<ArrayList<Double>> ();
              
           //loops over every argument of the predicate to be discretized
           for (String a: g.argsloc)
           {
        	   
            ArrayList<Double> listofNum = new ArrayList<Double>();

            Integer al = Integer.valueOf(a)-1;           
            FileInputStream ostream = new FileInputStream(factspath);
            BufferedReader br1 = new BufferedReader(new InputStreamReader(ostream));
            while ((strLine1 = br1.readLine()) != null)   
            {
        	  if(strLine1.contains(g.prename) && !strLine1.contains("//") )
        	  {	 String[] temp=strLine1.split("\\(");
        	     temp[1]=temp[1].replace(").", "");
        		 String[] arg=temp[1].split(",");
        		 Double x = Double.valueOf(arg[al]);
        		 listofNum.add(x);
        	   }       	
             }
            Collections.sort(listofNum);
            range[a1]=listofNum.size();
            //range[al]=listofNum.size();
        
    	    multD.add(listofNum);	
            ArrayList<Double> tval = new ArrayList<Double>();
            int n=0;
            int bn=0;
            System.out.println("The bin number is"+  g.binNum[a1]);
            if(g.binNum[a1].equals("d"))
            {	  if (range[a1]<8)
        	   {
        	     bn = 2;
        	    }
            else
        	{
        	//sturge's formula for calculating optimal number of bin
        	bn=(int) Math.ceil((Math.log(range[a1])-1));
        	}
            }
            else if(!(g.binNum[a1]).matches("^[0-9]+$"))
            {
        	Utils.error("You need to mention the letter d for discretizing an argument using default bin size!!");
        	
            }	
        
            else
           {
             bn = Integer.valueOf(g.binNum[a1]);
            }
        int tbn=bn-1;
        while(n<range[a1]-1 && tbn>0)
        {	tbn=tbn-1;
        	n=n+((range[a1]/bn)-1);
        	tval.add((multD.get(a1)).get(n));   
        	n++;
        }
        threshold.add(tval);
        System.out.println(threshold);
        br1.close();
        a1++;
        }     
        
        //Discretizing all arguments of a single predicate    
        FileInputStream nstream = new FileInputStream(factspath);
        BufferedReader br2 = new BufferedReader(new InputStreamReader(nstream));
        BufferedWriter bw = new BufferedWriter(new FileWriter(new File(predpath+g.prename+".txt")));
        filenames.add(prefix+"_facts_"+g.prename+".txt");
        prednames.add(g.prename);
        String strLine2;
        String out= "";
    	while ((strLine2 = br2.readLine()) != null)   
    	{        
    	if(strLine2.contains(g.prename) && !strLine2.contains("//") )
    	{	String[] temp=strLine2.split("\\(");
    	    temp[1]=temp[1].replace(").", "");
    		String[] arg=temp[1].split(",");
            String o="";
            Integer a2=0;
    		for(String b:g.argsloc)
    		{
    		 Integer al = Integer.valueOf(b)-1;	
    		 Double a = Double.valueOf(arg[al]); 
    		 boolean discrete=false;
    		 int i;
    		 for(i=0; i<(threshold.get(a2)).size();i++)
    		 {  
    			 if (a>(threshold.get(a2)).get(i)){
    				 continue;
    				 }
    			 else 
    			 {
    				 arg[al]=String.valueOf(i);
    				 discrete=true;
    				 break;
    				 }
    		 }
			 if (discrete==false)
			 {
				 arg[al]=String.valueOf(i);
			 }  
			a2++;
    		}
    		int count = 0;
    		for(String s: arg) 
    		{    
			   o += (count == arg.length-1) ? s: s + ",";
			   count++;
    		}
    		out=g.prename+"("+o+")."+"\n";
    		bw.write(out);
    	}
    	
    	}
    	br2.close();
    	bw.flush();
    	bw.close();
    	//count_pred=count_pred+1;
    	}
        
        BufferedWriter bw1 = new BufferedWriter(new FileWriter(new File(outpath)));
        String strLine3;
        for (String file : filenames) 
        {
            FileInputStream instream = new FileInputStream(mergefile+file);
            BufferedReader br3 = new BufferedReader(new InputStreamReader(instream));
        	while ((strLine3 = br3.readLine()) != null)   
        	{  
        		bw1.write(strLine3+"\n");
        	}
        	br3.close();
        	        
        }
        for (String file : filenames) 
        {
            File tfile = new File(delfile+file);
            tfile.delete();
        }
        String strLine4;
        FileInputStream instream2 = new FileInputStream(factspath);
        BufferedReader br4 = new BufferedReader(new InputStreamReader(instream2));
        while ((strLine4 = br4.readLine()) != null && !(strLine4.contains("//")))   
    	{  
        	String[] temp=strLine4.split("\\(");
        	if (!prednames.contains(temp[0]))
        	{
        		bw1.write(strLine4+"\n");
        	}
        	
    	}
        br4.close();
        bw1.close();
        
    }
}
