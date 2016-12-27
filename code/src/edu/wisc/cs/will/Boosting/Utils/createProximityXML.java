/**
 * 
 */
package edu.wisc.cs.will.Boosting.Utils;

    
import java.io.BufferedWriter;
import edu.wisc.cs.will.Utils.condor.CondorFileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.wisc.cs.will.DataSetUtils.Example;
import edu.wisc.cs.will.FOPC.Literal;
import edu.wisc.cs.will.ILP.ILPMain;
import edu.wisc.cs.will.Utils.StringPair;
import edu.wisc.cs.will.stdAIsearch.SearchInterrupted;

/**
 * @author Tushar Khot
 *
 */
public class createProximityXML {

	/**
	 * @param args
	 * @throws SearchInterrupted 
	 * @throws IOException 
	 */
	public static void main(String[] args) throws SearchInterrupted, IOException {
		// TODO Auto-generated method stub
		String[] args1 = {args[0]};
		ILPMain main = new ILPMain();
		main.setup(args1);
		Iterable<Literal> lits = main.outerLooper.getContext().getClausebase().getFacts();
		Set<String> users = new HashSet<String>();
		Set<String> movies = new HashSet<String>();
		HashMap<String, HashMap<String, String>> movie_att = new HashMap<String, HashMap<String,String>>();
		ArrayList<StringPair> genre_att = new ArrayList<StringPair>();
		HashMap<String, HashMap<String, String>> user_att = new HashMap<String, HashMap<String,String>>();
		ArrayList<StringPair> tmp_ratings = new ArrayList<StringPair>();
		ArrayList<StringPair>  ratings = new ArrayList<StringPair>();
		ArrayList<String> rating_values = new ArrayList<String>();
		for (Literal lit : lits) {
			String pname = lit.predicateName.name;
			if (pname.equals("year")) {
				movies.add(lit.getArgument(0).toString());
				addToMap("year", lit.getArgument(0).toString(), lit.getArgument(1).toString(), movie_att);
			}
			if (pname.equals("genre")) {
				String movie = lit.getArgument(0).toString();
				String genre = lit.getArgument(1).toString();
				movies.add(movie);
				// Multiple genre
				// addToMap("genre", lit.getArgument(0).toString(), lit.getArgument(1).toString(), movie_att);
				genre_att.add(new StringPair(movie, genre));
			}
			if (pname.equals("age")) {
				users.add(lit.getArgument(0).toString());
				addToMap("age", lit.getArgument(0).toString(), lit.getArgument(1).toString(), user_att);

			}
			if (pname.equals("gender")) {
				users.add(lit.getArgument(0).toString());
				addToMap("gender", lit.getArgument(0).toString(), lit.getArgument(1).toString(), user_att);

			}
			if (pname.equals("occupation")) {
				users.add(lit.getArgument(0).toString());
				addToMap("occupation", lit.getArgument(0).toString(), lit.getArgument(1).toString(), user_att);

			}
			if (pname.equals("tmp_ratings")) {
				String usr = lit.getArgument(0).toString();
				String mov = lit.getArgument(1).toString();
				String rat = lit.getArgument(2).toString();
				users.add(usr);
				movies.add(mov);
				tmp_ratings.add(new StringPair(usr, mov));
				rating_values.add(rat);
			}
		}
		
		
		// Go through the positive examples for ratings
		List<Example> posex = main.outerLooper.getPosExamples();
		for (Example lit : posex) {
			String usr = lit.getArgument(0).toString();
			String mov = lit.getArgument(1).toString();
			String rat = lit.getArgument(2).toString();
			users.add(usr);
			movies.add(mov);
			ratings.add(new StringPair(usr, mov));
			rating_values.add(rat);
		}
		BufferedWriter writer = new BufferedWriter(new CondorFileWriter("test0.xml", false)); // Create a new file.
		writer.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>");
		writer.newLine();
		writer.write("<!DOCTYPE PROX3DB SYSTEM \"prox3db.dtd\">");
		writer.newLine();
		writer.write("<PROX3DB>");
		writer.newLine();
		int count=0;
		// Create links
		writer.write("<OBJECTS>");
		for(;count<rating_values.size();count++) {
			writer.write("\t<OBJECT ID=\"" + (count)+ "\"/>");
			writer.newLine();
		}
		//count++;
		HashMap<String, Integer> id_to_counter = new HashMap<String, Integer>();
		//writer.write("<OBJECTS>");
		writer.newLine();
		for (String mov : movies) {
			id_to_counter.put(mov,count);
			writer.write("\t<OBJECT ID=\"" + (count++)+ "\"/>");
			writer.newLine();
		}
		for (String mov : users) {
			id_to_counter.put(mov,count);
			writer.write("\t<OBJECT ID=\"" + (count++)+ "\"/>");
			writer.newLine();
		}
		writer.write("</OBJECTS>");
		writer.newLine();
		
		writer.write("<LINKS>");
		writer.newLine();
		int l=0;
		for (int i = 0; i < rating_values.size(); i++) {
			StringPair res = null;
			if (i >= tmp_ratings.size()) {
				res = ratings.get(i-tmp_ratings.size());
			} else {
				res = tmp_ratings.get(i);
			}
			String usr = res.getFirst();
			String mov = res.getSecond();
			// String link = "<LINK ID=\"" + i + "\" O1-ID=\"" + id_to_counter.get(usr) + "\" O2-ID=\"" + id_to_counter.get(mov) +"\"/>\n";
			String link = "<LINK ID=\"" + (l++) + "\" O1-ID=\"" + i + "\" O2-ID=\"" + id_to_counter.get(usr) +"\"/>\n";
			link = link + "<LINK ID=\"" + (l++) + "\" O1-ID=\"" + i + "\" O2-ID=\"" + id_to_counter.get(mov) +"\"/>\n";
			writer.write(link);
		}
		writer.write("</LINKS>");
		writer.newLine();
		
		writer.write("<ATTRIBUTES>");
		writer.newLine();
		// MOVIE
		for (String attr : movie_att.keySet()) {
			 writer.write("<ATTRIBUTE NAME=\"" + attr + "\" ITEM-TYPE=\"O\" DATA-TYPE=\"STR\">\n");

			HashMap<String, String> attr_vals = movie_att.get(attr);
			for (String att : attr_vals.keySet()) {
				Integer id = id_to_counter.get(att);
				writer.write(" <ATTR-VALUE ITEM-ID=\"" + id + "\">\n");
				writer.write("          <COL-VALUE>" + attr_vals.get(att)+"</COL-VALUE>\n");
				writer.write(" </ATTR-VALUE>\n");
			}
			writer.write(" </ATTRIBUTE>\n");
		}
		// GENRE
		 writer.write("<ATTRIBUTE NAME=\"" + "genre" + "\" ITEM-TYPE=\"O\" DATA-TYPE=\"STR\">\n");
		for (StringPair mg : genre_att) {
			String mov = mg.getFirst();
			String gen = mg.getSecond();
			Integer id = id_to_counter.get(mov);
			writer.write(" <ATTR-VALUE ITEM-ID=\"" + id + "\">\n");
			writer.write("          <COL-VALUE>" + gen +"</COL-VALUE>\n");
			writer.write(" </ATTR-VALUE>\n");
		}
		writer.write(" </ATTRIBUTE>\n");
		// USERS
		for (String attr : user_att.keySet()) {
			 writer.write("<ATTRIBUTE NAME=\"" + attr + "\" ITEM-TYPE=\"O\" DATA-TYPE=\"STR\">\n");

			HashMap<String, String> attr_vals = user_att.get(attr);
			for (String att : attr_vals.keySet()) {
				Integer id = id_to_counter.get(att);
				writer.write(" <ATTR-VALUE ITEM-ID=\"" + id + "\">\n");
				writer.write("          <COL-VALUE>" + attr_vals.get(att)+"</COL-VALUE>\n");
				writer.write(" </ATTR-VALUE>\n");
			}
			writer.write(" </ATTRIBUTE>\n");
		}
		
		// LINKS
		// writer.write("<ATTRIBUTE NAME=\"" + "tmp_ratings" + "\" ITEM-TYPE=\"L\" DATA-TYPE=\"STR\">\n");
		//writer.write("<ATTRIBUTE NAME=\"" + "ratings" + "\" ITEM-TYPE=\"L\" DATA-TYPE=\"STR\">\n");
		writer.write("<ATTRIBUTE NAME=\"" + "ratings" + "\" ITEM-TYPE=\"O\" DATA-TYPE=\"STR\">\n");
		for (int i = 0; i < rating_values.size(); i++) {
			//String res = null;
			if (i == tmp_ratings.size()) {
				//writer.write(" </ATTRIBUTE>\n");
				//writer.write("<ATTRIBUTE NAME=\"" + "ratings" + "\" ITEM-TYPE=\"L\" DATA-TYPE=\"STR\">\n");
				//res = "ratings";
			} else {
				//res = "tmp_ratings";
			}
			
			writer.write(" <ATTR-VALUE ITEM-ID=\"" + i + "\">\n");
			writer.write("          <COL-VALUE>" + rating_values.get(i)+"</COL-VALUE>\n");
			writer.write(" </ATTR-VALUE>\n");
			
		}
		writer.write(" </ATTRIBUTE>\n");
		
		
		writer.write("</ATTRIBUTES>");
		writer.newLine();
		
		writer.write("</PROX3DB>");
		writer.newLine();
		writer.close();
	}

	private static void addToMap(String key, String key2, String val,
			HashMap<String, HashMap<String, String>> movieAtt) {
		if (!movieAtt.containsKey(key)) {
			movieAtt.put(key, new HashMap<String, String>());
		}
		movieAtt.get(key).put(key2, val);
	}

    private createProximityXML() {
    }

}
