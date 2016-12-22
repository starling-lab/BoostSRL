package graphdbInt;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import org.apache.commons.collections4.MultiMap;
import org.apache.commons.collections4.map.MultiValueMap;
import org.apache.commons.lang3.StringUtils;
import org.apache.log4j.PropertyConfigurator;

import com.hp.hpl.jena.graph.Graph;
import com.hp.hpl.jena.graph.GraphUtil;
import com.hp.hpl.jena.graph.Node;
import com.hp.hpl.jena.graph.NodeFactory;
import com.hp.hpl.jena.graph.Triple;
import com.hp.hpl.jena.query.Dataset;
import com.hp.hpl.jena.query.Query;
import com.hp.hpl.jena.query.QueryExecution;
import com.hp.hpl.jena.query.QueryExecutionFactory;
import com.hp.hpl.jena.query.QueryFactory;
import com.hp.hpl.jena.query.QuerySolution;
import com.hp.hpl.jena.query.ReadWrite;
import com.hp.hpl.jena.query.ResultSet;
import com.hp.hpl.jena.query.ResultSetFormatter;
import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.ModelFactory;
import com.hp.hpl.jena.rdf.model.Property;
import com.hp.hpl.jena.rdf.model.RDFNode;
import com.hp.hpl.jena.rdf.model.RDFWriter;
import com.hp.hpl.jena.rdf.model.Resource;
import com.hp.hpl.jena.rdf.model.Statement;
import com.hp.hpl.jena.rdf.model.StmtIterator;
import com.hp.hpl.jena.shared.AddDeniedException;
import com.hp.hpl.jena.tdb.TDBFactory;

import edu.wisc.cs.will.FOPC.Literal;

public class GraphDB {

	// Directory where the graph structures are stored
		private static final String storage_dir = System.getProperty("user.dir");
		public static final double delta = 1;
		// The namespace
		String[] gvarlst;
		String[] vallst;
		private static final String ns = "http://example.org/";
		//private static final String nsp = "http://example.org/prop/";
		public static double totalSize = 1;
		// The model
		private Model m;
		private Model mIn, mOut, mIn_1order,mOut_1order;
		private Dataset ds;
		
		//datastructs for metadata
		Hashtable<String,String> grnd = new Hashtable<String,String>();
		Hashtable<String,ArrayList<String>> argtypes = new Hashtable<String,ArrayList<String>>();
		Hashtable<String,Integer> typeCounts = new Hashtable<String,Integer>();
		Hashtable<String,Integer> qrySign = new Hashtable<String,Integer>();
		Set<String> vars = new TreeSet<String>();
		HashMap<String,Double> countTable = new HashMap<String,Double>();
		HashMap<String,Boolean> predSense = new HashMap<String,Boolean>();
		HashMap<String,Double> predcountTableIn = new HashMap<String,Double>();
		HashMap<String,Double> predcountTableOut = new HashMap<String,Double>();
		HashMap<String,Double> predcountTableInNum = new HashMap<String,Double>();
		HashMap<String,Double> predcountTableOutNum = new HashMap<String,Double>();
		//summary tables
		HashMap<String,HashMap<String,Double>> InCount = new HashMap<String,HashMap<String,Double>>();
		HashMap<String,HashMap<String,Double>> OutCount = new HashMap<String,HashMap<String,Double>>();
		String final_var = null;
		static {
			//Setting up the config file for the logger
			PropertyConfigurator.configure("./log4j.properties");
		}

		/**
		 * Constructor for the graph database
		 * @param EFpath - path for the evidence file
		 * @param dbName - name of the database
		 * @param overwrite - decision for overwrite of the graph file if already present,
		 * 			if false the old copy of the graph is loaded (faster);
		 * @throws IOException 
		 * @throws AddDeniedException 
		 */
		public GraphDB(String EFpath, String dbSc, String dbName, boolean overwrite) throws Exception {
			
			argtypes = getMLN.getPredArgtypes(dbSc);
			//System.out.println(argtypes);
			File f = new File(EFpath);
			ds = TDBFactory.createDataset(storage_dir + dbName);

			//If the database was saved already and no overwrite is desired, then simply load it
			if(f.exists() && !f.isDirectory() && !overwrite) {
				ds.begin(ReadWrite.READ);
				m = ds.getNamedModel("evigraph");
				mIn = ds.getNamedModel("evigraphIN");
				mOut = ds.getNamedModel("evigraphOUT");
						
			}
			else{
				ds.begin(ReadWrite.WRITE);

				m = ds.getNamedModel("evigraph");

				Graph eviG = m.getGraph();

				BufferedReader in = new BufferedReader(new FileReader(EFpath));
				int l=1;
				String line;
				while((line=in.readLine())!=null){
					
					if(line.contains("//"))
						continue;
					else
					{
						System.out.println(l);
						l++;
					}
						
					line = line.replace('.', ' ').trim();
					if(line.isEmpty())
						continue;
					String[] tokens = line.split("\\(|,\\s*|\\)");
					for(int i=0;i<tokens.length;i++)
						tokens[i] = tokens[i].replace('"', ' ').trim();
					
					
					Resource subj  = m.createResource(ns + tokens[1].replace('"', ' ').trim());
					Property pred  = m.createProperty(ns + tokens[0].replace('!', '_'));
					Resource obj   = m.createResource(ns + (tokens.length > 2 ? tokens[2].replace('"', ' ').trim():tokens[1]).replace('"', ' ').trim());
					Statement stmt = m.createStatement(subj, pred, obj);
					Triple tG      = stmt.asTriple();
					eviG.add(tG);
					//System.out.println(tG);
					
					//assigning to type
					String predName = tokens[0].replace('!', ' ').trim();
					
					ArrayList<String> args = argtypes.get(predName);
					Resource s1  = m.createResource(ns + tokens[1]);
					Property p1  = m.createProperty(ns + "type");
					Resource o1   = m.createResource(ns + args.get(0));
					
					Triple typeG1      = new Triple(s1.asNode(),p1.asNode(),o1.asNode());
					if(!eviG.contains(typeG1))
					{	
						eviG.add(typeG1);
					}
					if(tokens.length>2)
					{
						Resource s2  = m.createResource(ns + tokens[2]);
						Property p2  = m.createProperty(ns + "type");
						Resource o2   = m.createResource(ns + args.get(1));
						
						Triple typeG2      = new Triple(s2.asNode(),p2.asNode(),o2.asNode());
						if(!eviG.contains(typeG2))
							eviG.add(typeG2);
					}
				}
				in.close();
				ds.commit();
				//String fileName = "example.rdf";
				//FileWriter out = new FileWriter( fileName );
				//m.write( out, "RDF/XML-ABBREV" );
				//out.close();
				summarize(dbName);
				//System.out.println(InCount);
				//System.in.read();
				calcTypeCnts();
				
				System.out.println(typeCounts);
			}
			close();
		}
		
		void calcTypeCnts()
		{
			String qry = "PREFIX nmspc: <http://example.org/> SELECT  ?o  (count(?s) as ?cnt)  WHERE {?s nmspc:type ?o} GROUP BY ?o";
			Query query = QueryFactory.create(qry);
			QueryExecution qexec = QueryExecutionFactory.create(query, m);
			ResultSet results = qexec.execSelect();
			//ResultSetFormatter.out(results);
			while(results.hasNext())
			{
				QuerySolution qs = results.next();
				String type = qs.get("o").asResource().getLocalName();
				int cnt = qs.get("cnt").asLiteral().getInt();
				typeCounts.put(type, cnt);
			}
		}

		/**
		 * Closes the database
		 */
		public void close(){
			ds.close();
		}
		
		

		/**
		 * 
		 * @param Gvar
		 * @param val
		 * @param preds
		 * @param rvar
		 * @return
		 */
		public Hashtable<String,Integer> getCount(String Gvar, String val, String preds, String rvar){
			String[] PredArr = preds.split("\\|");
			String[] retvar = rvar.split(",");

			StringBuilder sb = new StringBuilder();
			StringBuilder grpSb = new StringBuilder();
			grpSb.append(" GROUP BY ");
			sb.append(String.format("PREFIX nmspc: <%s> SELECT ", ns));

			if(retvar==null){
				sb.append("(count(*) as ?cnt)");
			}
			else{
				for(int j = 0; j < retvar.length; ++j){
					sb.append(String.format("?%s (count(?%s) as ?%s) ",retvar[j], retvar[j], "cnt_"+retvar[j]));
					grpSb.append(String.format("?%s ", retvar[j]));
				}
			}

			sb.append(" WHERE {");

			for(int i = 0; i < PredArr.length; ++i){
				String p = PredArr[i];

				String predLabel = (p.split(":"))[0];
				String argstr = (p.split(":"))[1];

				String[] arg = argstr.split(",");

				String arg1 = arg[0];
				String arg2 = arg.length==1 ? arg[0] : arg[1];

				if(i != 0){
					sb.append(". ");
				}
				sb.append(String.format(i == 0 ? "{?%s nmspcP:%s ?%s}" : "optional{?%s nmspcP:%s ?%s}", arg1, predLabel, arg2));
				
			}
			
			//Adding list filter
			if(Gvar != null)
			{
				String[] vals = val.split(",");
				String str = convert(vals);
				//System.out.println(str);
				sb.append(". ");
				sb.append(String.format("VALUES ?%s {%s}", Gvar,str));
			}
			
			sb.append("}");
			//adding group by
			sb.append(grpSb.toString());
			
			//System.out.println(sb.toString());
			
			
			
			Query query = QueryFactory.create(sb.toString());
			//String f = "PREFIX nmspc: <http://example.org/> SELECT ?a1 WHERE {?a1 nmspc:_Smokes ?a1} GROUP BY ?a1";
			//Query query = QueryFactory.create(f);
			QueryExecution qexec = QueryExecutionFactory.create(query, m);

			ResultSet results = qexec.execSelect();
			//int count  = results.next().get("cnt_b").asLiteral().getInt();
			//return count;*/
			//ResultSetFormatter.out(results) ;
			
			Hashtable<String,Integer> retTable = new Hashtable<String,Integer>();
			QuerySolution qs=null;
			
			while(results.hasNext())
			{
				qs = results.next();
				retTable.put(qs.get(rvar)!=null?qs.get(rvar).asResource().getLocalName():"..", qs.get("cnt_"+rvar).asLiteral().getInt());
			}
			//System.out.println(retTable);
			return retTable;
		}
		
		public static String convert(String[] name) { 
		    StringBuilder sb = new StringBuilder();
		    for (String st : name) { 
		        sb.append("nmspc:").append(st).append(' ');
		    }
		    if (name.length != 0) sb.deleteCharAt(sb.length()-1);
		    return sb.toString();
		}
		
		public void summarize(String dbName)
		{
			ds = TDBFactory.createDataset(storage_dir + dbName);
			ds.begin(ReadWrite.WRITE);
			mIn = ds.getNamedModel("evigraphIN");
			mOut = ds.getNamedModel("evigraphOUT");
			//Model m = ds.getNamedModel("evigraph");
			
			Graph mInG = mIn.getGraph();
			Graph mOutG = mOut.getGraph();
			
			
			//start summarize
			String qrytot = "PREFIX nmspc: <http://example.org/> SELECT  (count(?s) as ?cnt) WHERE {?s ?p ?o. FILTER(?p != nmspc:type)}";
			Query querytot = QueryFactory.create(qrytot);
			QueryExecution qexectot = QueryExecutionFactory.create(querytot, m);
			ResultSet resultstot = qexectot.execSelect();
			while(resultstot.hasNext())
			{
				QuerySolution qs = resultstot.next();
				totalSize = qs.get("cnt").asLiteral().getDouble();
			}
			//In degrees
			String qry = "PREFIX nmspc: <http://example.org/> SELECT  (count(DISTINCT ?s) as ?cnt) ?p ?o  WHERE {?s ?p ?o} GROUP BY ?p ?o";
			Query query = QueryFactory.create(qry);
			QueryExecution qexec = QueryExecutionFactory.create(query, m);
			ResultSet results = qexec.execSelect();
			
			
			while(results.hasNext())
			{
				QuerySolution qs = results.next();
				mInG.add(new Triple(qs.get("cnt").asNode(),qs.getResource("p").asNode(),
						qs.getResource("o").asNode()));
				HashMap<String,Double> temp = null;
				temp = InCount.get(qs.get("o").asResource().getLocalName().isEmpty()?qs.get("o").asResource().toString().replace(ns, ""):qs.get("o").asResource().getLocalName());
				//System.out.println(qs.get("cnt").asLiteral().getDouble()+" | "+qs.get("p").asResource().getLocalName()+" | "+qs.get("o").asResource().getLocalName());
				if(temp==null)
				{
					temp = new HashMap<String,Double>();
				}
				System.out.println("----IN");
				System.out.println(qs.get("cnt").asLiteral().getDouble()+" | "+qs.get("p").asResource().getLocalName()+" | "+(qs.get("o").asResource().getLocalName().isEmpty()?qs.get("o").asResource().toString().replace(ns, ""):qs.get("o").asResource().getLocalName()));
				temp.put(qs.get("p").asResource().getLocalName(),qs.get("cnt").asLiteral().getDouble());
				InCount.put(qs.get("o").asResource().getLocalName().isEmpty()?qs.get("o").asResource().toString().replace(ns, ""):qs.get("o").asResource().getLocalName(), temp);
				//predcountTableIn.put(qs.get("p").asResource().getLocalName(), predcountTableIn.getOrDefault(qs.get("p").asResource().getLocalName(), 0.0)+qs.get("cnt").asLiteral().getDouble());
				predcountTableInNum.put(qs.get("p").asResource().getLocalName(), 
						predcountTableInNum.getOrDefault(qs.get("p").asResource().getLocalName(), 0.0)+1.0);
				
			}
			//ResultSetFormatter.out(results);
			
			//Out Degrees
			qry = "PREFIX nmspc: <http://example.org/> SELECT  ?s ?p  (count(DISTINCT ?o) as ?cnt)  WHERE {?s ?p ?o} GROUP BY ?s ?p";
			query = QueryFactory.create(qry);
			qexec = QueryExecutionFactory.create(query, m);
			ResultSet results1 = qexec.execSelect();
			
			//ResultSetFormatter.out(results1);
			
			while(results1.hasNext())
			{
				QuerySolution qs = results1.next();
				mOutG.add(new Triple(qs.get("s").asNode(),
						qs.get("p").asNode(),qs.get("cnt").asNode()));
				HashMap<String,Double> temp = null;
				temp = OutCount.get(qs.get("s").asResource().getLocalName().isEmpty()?qs.get("s").asResource().toString().replace(ns, ""):qs.get("s").asResource().getLocalName());
				//System.out.println(qs.get("s").asResource().getLocalName()+" | "+qs.get("p").asResource().getLocalName()+" | "+qs.get("cnt").asLiteral().getDouble());
				if(temp==null)
				{
					temp = new HashMap<String,Double>();
				}
				temp.put(qs.get("p").asResource().getLocalName(),qs.get("cnt").asLiteral().getDouble());
				OutCount.put(qs.get("s").asResource().getLocalName().isEmpty()?qs.get("s").asResource().toString().replace(ns, ""):qs.get("s").asResource().getLocalName(), temp);
				//predcountTableOut.put(qs.get("p").asResource().getLocalName(), predcountTableOut.getOrDefault(qs.get("p").asResource().getLocalName(),0.0)+qs.get("cnt").asLiteral().getDouble());
				//predcountTableOutNum.put(qs.get("p").asResource().getLocalName(), predcountTableOutNum.getOrDefault(qs.get("p").asResource().getLocalName(),0.0)+1.0);
				predcountTableOutNum.put(qs.get("p").asResource().getLocalName(), 
						predcountTableOutNum.getOrDefault(qs.get("p").asResource().getLocalName(), 0.0)+1.0);
			}
			//ds.commit();
			
			
			//build first order summary
			qry = "PREFIX nmspc: <http://example.org/> SELECT  ?p  (count(?o) as ?a) WHERE  {?s ?p ?o} GROUP BY ?p";
			query = QueryFactory.create(qry);
			qexec = QueryExecutionFactory.create(query, mOut);
			ResultSet results2 = qexec.execSelect();
			//ResultSetFormatter.out(results2);
			while(results2.hasNext())
			{
				QuerySolution qs = results2.next();
				String p = qs.get("p").asResource().getLocalName();
				Double a = qs.get("a").asLiteral().getDouble();
				predcountTableOut.put(p, a);
			}
			
			
			qry = "PREFIX nmspc: <http://example.org/> SELECT  ?p  (count(?s) as ?a) WHERE {?s ?p ?o} GROUP BY ?p";
			query = QueryFactory.create(qry);
			qexec = QueryExecutionFactory.create(query, mIn);
			ResultSet results3 = qexec.execSelect();
			//ResultSetFormatter.out(results2);
			while(results3.hasNext())
			{
				QuerySolution qs = results3.next();
				String p = qs.get("p").asResource().getLocalName();
				Double a = qs.get("a").asLiteral().getDouble();
				System.out.println("+++avg--"+a);
				predcountTableIn.put(p, a);
			}
			/*for(String k:predcountTableOut.keySet())
			{
				predcountTableOut.put(k, predcountTableOut.getOrDefault(k, 0.0)/predcountTableOutNum.get(k));
			}
			for(String k:predcountTableIn.keySet())
			{
				predcountTableIn.put(k, predcountTableIn.getOrDefault(k, 0.0)/predcountTableInNum.get(k));
			}*/
			mIn.close();
			mOut.close();
			mIn = null;
			mOut = null;
		}
		
		public int getExists(String Gvar, String value, String[] preds, int num)
		{
			int unique=0;
			String[] gvarlst = Gvar.split(",");
			String[] vallst = value.split(",");
			//String val = value.replace('"', ' ').trim();
			//System.out.println(val);
			Model qryModel = ModelFactory.createDefaultModel();
			Graph qryGraph = qryModel.getGraph();
			
			String qry = "PREFIX nmspc:"+ns+" SELECT ";
			StringBuilder sb = new StringBuilder();
			StringBuilder filter = new StringBuilder();
			//filter.append("FILTER (NOT EXISTS {");
			sb.append(String.format("PREFIX nmspc: <%s> SELECT (count(*) as ?cnt) WHERE {", ns));
			int neg=0;
			for(int i = 0 ; i<preds.length; i++)
			{
				if(!(i==0 || i==preds.length-1))
					continue;
				String p = preds[i];
				
				
				String predLabel = p.split("\\(")[0];
				String argstr = p.split("\\(")[1].replace(')', ' ').trim();

				String[] arg = argstr.split(",");
				
				String arg1 = arg[0];
				String arg2 = arg.length==1 ? arg[0].toString() : arg[1];
				/*if(predLabel.startsWith("_"))
				{
					predLabel = predLabel.replace('_', ' ').trim();
					String t = arg2;
					arg2 = arg1;
					arg1=t;
				}*/
				
				String a1="",a2="";
				for(int j = 0; j<gvarlst.length;j++)
				{
					if(gvarlst[j].equalsIgnoreCase(arg1))
					{
						a1 = "nmspc:"+vallst[j];
						break;
					}
					else
						a1 = "?"+arg1;
				}
				for(int j = 0; j<gvarlst.length;j++)
				{
						
					if(gvarlst[j].equalsIgnoreCase(arg2))
					{
						a2 = "nmspc:"+vallst[j];
						break;
					}
					else
						a2 = "?"+arg2;
				}
					
				sb.append(String.format("%s nmspc:%s %s. ", a1, predLabel, a2));
					
				
					
			}
			
			for(int i = 0 ; i<preds.length; i++)
			{
				if(i==0 || i==preds.length-1)
					continue;
				String p = preds[i];
				
				
				String predLabel = p.split("\\(")[0];
				String argstr = p.split("\\(")[1].replace(')', ' ').trim();

				String[] arg = argstr.split(",");

				String arg1 = arg[0];
				String arg2 = arg.length==1 ? arg[0].toString() : arg[1];
				/*if(predLabel.startsWith("_"))
				{
					predLabel = predLabel.replace('_', ' ').trim();
					String t = arg2;
					arg2 = arg1;
					arg1=t;
				}*/
				
				String a1="",a2="";
				for(int j = 0; j<gvarlst.length;j++)
				{
					if(gvarlst[j].equalsIgnoreCase(arg1))
					{
						a1 = "nmspc:"+vallst[j];
						break;
					}
					else
						a1 = "?"+arg1;
				}
				for(int j = 0; j<gvarlst.length;j++)
				{
						
					if(gvarlst[j].equalsIgnoreCase(arg2))
					{
						a2 = "nmspc:"+vallst[j];
						break;
					}
					else
						a2 = "?"+arg2;
				}
					
				sb.append(String.format("%s nmspc:%s %s. ", a1, predLabel, a2));
					
				
					
			}
			
			
			//--------------
//			String gvarL = "";
//			String valL = "";
//			for(int g=0;g<gvarlst.length;g++)
//			{
//				if(g!=0)
//				{
//					gvarL = gvarL+" ?"+gvarlst[g];
//					valL = valL+ " nmspc:"+vallst[g].replace('"', ' ').trim();
//				}
//				else
//				{
//					gvarL = gvarL+"?"+gvarlst[g];
//					valL = valL+ "nmspc:"+vallst[g].replace('"', ' ').trim();
//				}
//				
//			}
			//--------------
			//System.out.println(gvarL+"=============="+valL);
			sb.setLength(sb.length() - 2);
			//sb.append(String.format(" VALUES (%s) {(%s)}", gvarL, valL));
			sb.append("}");
			//System.out.println(Gvar);
			//if(num==96)
				//System.out.println(sb.toString());
			Query query = QueryFactory.create(sb.toString());
			//Query query = QueryFactory.create(exQ);
			QueryExecution qexec = QueryExecutionFactory.create(query, m);
			try{
			qexec.setTimeout(40000);
			//boolean results = qexec.execAsk();
			ResultSet results = qexec.execSelect();
			//ResultSetFormatter.out(System.out, results, query) ;
			int count  = results.next().get("cnt").asLiteral().getInt();
			//System.out.println(count);
			//return count;
			/*if(results)
				return 1;*/
			if(count>0)
				return count;
			}
			catch(Exception e)
			{
				return 0;
			}
			return 0;
		}
		
		
		public long getExactCount(String Gvar, String value, String[] preds, String bitrep)
		{
			int unique=0;
			String[] gvarlst = Gvar.split(",");
			String[] vallst = value.split(",");
			//String val = value.replace('"', ' ').trim();
			//System.out.println(val);
			Model qryModel = ModelFactory.createDefaultModel();
			Graph qryGraph = qryModel.getGraph();
			
			String qry = "PREFIX nmspc:"+ns+" SELECT ";
			StringBuilder sb = new StringBuilder();
			StringBuilder filter = new StringBuilder();
			filter.append("FILTER (NOT EXISTS {");
			sb.append(String.format("PREFIX nmspc: <%s> SELECT (count(*) as ?cnt) WHERE {", ns));
			int neg=0;
			for(int i = 0 ; i<preds.length; i++)
			{
				String p = preds[i];
				
				
				String predLabel = p.split("\\(")[0];
				String argstr = p.split("\\(")[1].replace(')', ' ').trim();

				String[] arg = argstr.split(",");

				String arg1 = arg[0];
				String arg2 = arg.length==1 ? arg[0].toString() : arg[1];
				
				
				
				if(bitrep.charAt(i)=='1')
				{
					
					sb.append(String.format("?%s nmspc:%s ?%s. ", arg1, predLabel, arg2));
					
				}
				else
				{
					filter.append(String.format("?%s nmspc:%s ?%s. ", arg1, predLabel, arg2));
					//sb.append(String.format("?%s nmspc:%s ?var%s. ", arg1, predLabel, unique));
					//unique++;
					//sb.append(String.format("?var%s nmspc:%s ?%s. ", unique, predLabel, arg2));
					//unique++;
					neg++;
					
				}
					
			}
			String exQ= "PREFIX nmspc: <http://example.org/> SELECT (count() as ?cnt) WHERE {?person1 nmspc:personineconomicsector ?sector1. ?a1 nmspc:academicfieldusedbyeconomicsector ?sector1. FILTER (NOT EXISTS {?field1 nmspc:academicfieldusedbyeconomicsector ?sector1}). VALUES (?sector1) {(nmspc:financial_services)} }";
			filter.setLength(filter.length() - 2);
			filter.append("})");
			if(neg>0)
			{
				sb.append(filter.toString());
			}
			else
				sb.setLength(sb.length()-2);
			
			//--------------
			String gvarL = "";
			String valL = "";
			for(int g=0;g<gvarlst.length;g++)
			{
				if(g!=0)
				{
					gvarL = gvarL+" ?"+gvarlst[g];
					valL = valL+ " nmspc:"+vallst[g].replace('"', ' ').trim();
				}
				else
				{
					gvarL = gvarL+"?"+gvarlst[g];
					valL = valL+ "nmspc:"+vallst[g].replace('"', ' ').trim();
				}
				
			}
			//--------------
			System.out.println(gvarL+"=============="+valL);
			
			sb.append(String.format(". VALUES (%s) {(nmspc:%s)}", gvarL, valL));
			sb.append("}");
			System.out.println(Gvar);
			System.out.println(sb.toString());
			//Query query = QueryFactory.create(sb.toString());
			Query query = QueryFactory.create(exQ);
			QueryExecution qexec = QueryExecutionFactory.create(query, m);

			ResultSet results = qexec.execSelect();
			ResultSetFormatter.out(System.out, results, query) ;
			//int count  = results.next().get("cnt").asLiteral().getInt();
			//System.out.println(count);
			//return count;
			return 0;
			
		}
		
		@SuppressWarnings("deprecation")
		public Double getApproxCount(String Gvar, String value, List<Literal> preds, String bitrep)
		{
			System.out.println("preds"+preds);
			grnd = new Hashtable<String,String>();
			System.out.println(Gvar);
			if(preds.size()==0)
				return 0.0;
			countTable = new HashMap<String,Double>();
			String[] gvarlst = Gvar.split(",");
			String[] vallst = value.split(",");
			for(int i = 0;i<gvarlst.length;i++)
			{
				grnd.put(gvarlst[i], vallst[i]);
			}
			System.out.println(grnd);
			MultiMap<String,String> qryModelIn = new MultiValueMap<String,String>();
			MultiMap<String,String> qryModelOut = new MultiValueMap<String,String>();
			
			//String[] PredArr = preds.split("\\|");
			//String[] retvar = rvar.split(",");
			//StringBuilder sb = new StringBuilder();
			String val = value.replace('"', ' ').trim();
			//System.out.println(val);
			Model qryModel = ModelFactory.createDefaultModel();
			Graph qryGraph = qryModel.getGraph();
			double totalcount = 0;
			for(int i = 0; i < preds.size(); ++i)
			{
				double c =0;
				int sign =1;
				Literal p = preds.get(i);
				
				
				String predLabel = p.predicateName.toString();
				String argstr = p.getArguments().toString();


				String[] arg = argstr.split(",");

				String arg1 = arg[0].trim();
				String arg2 = arg.length==1 ? arg[0].trim() : arg[1].trim();
				
				String pLabel = predLabel.replace('!', ' ').trim();
				
//				if(pLabel.startsWith("_"))
//				{
//					pLabel = pLabel.replace('_', ' ').trim();
//					String t = arg2;
//					arg2 = arg1;
//					arg1=t;
//				}
				if(bitrep.charAt(i)=='0')
					this.predSense.put(pLabel, false);
				else
					this.predSense.put(pLabel, true);
				Resource subj  = qryModel.createResource(ns + arg1);
				Property pred  = qryModel.createProperty(ns + pLabel);
				Resource obj   = qryModel.createResource(ns + arg2);
				qryGraph.add(new Triple(subj.asNode(),pred.asNode(),obj.asNode()));
				
				//--------------------- new optimization ------------
				//populate In --
				qryModelIn.put(arg2, pLabel+"-::-"+arg1);
				qryModelOut.put(arg1, pLabel+"-::-"+arg2);
				//System.out.println(typeCounts);
				ArrayList<String> a = argtypes.get(pLabel);
				if(a.size()==1)
				{
					countTable.put(arg1, 0.0+typeCounts.get(a.get(0)));
				}
				else
				{
					countTable.put(arg1, 0.0+typeCounts.getOrDefault(a.get(0),0));
					System.out.println(pLabel);
					System.out.println(pLabel+ " " +a.get(1));
					countTable.put(arg2, 0.0+typeCounts.getOrDefault(a.get(1),0));
				}
				
				if(Gvar!=null)
				{
					for(int gv=0;gv<gvarlst.length;gv++)
					countTable.put(gvarlst[gv], 1.0);
				}
				
			}
			
			Set<String> temp = countTable.keySet();
			vars.addAll(temp);
			
			System.out.println(countTable);
			
			String currvar = gvarlst[0];
			induce_count(currvar,vallst[0],qryModelIn,qryModelOut);
			//induce_countV2(Gvar,val,qryModelIn,qryModelOut);
			//System.out.println("Final var - "+final_var);
			//System.out.println(countTable);
			//System.out.println("Final count - "+countTable.get(final_var));
			
			//return ((countTable.get(final_var).longValue()==0?(long)delta:countTable.get(final_var).longValue()));
			//System.out.println(countTable);
			System.out.println(countTable);
			return countTable.get(final_var);
		}
		
		void induce_count(String var, String val,MultiMap<String,String> qryModelIn, MultiMap<String,String> qryModelOut)
		{
			if(!vars.contains(var))
				return;
			vars.remove(var);
			//System.out.println(countTable);
			Integer totalOut=1,totalIn=1;
			
			List<String> tempIn = (List<String>) qryModelIn.get(var);
			
			Double sum = 1.0; //change
			int i =0;
			if(tempIn!=null)
			{	for(String pair:tempIn)
				{
					i++;
					//QuerySolution qs = rs.next();
					//String sub = qs.get("s").asResource().getLocalName();
					//String pr = qs.get("p").asResource().getLocalName();
					String[] pairArr = pair.split("-::-");
					String sub = pairArr[1];
					String pr = pairArr[0];
					if(vars.contains(sub))
					{
						//System.out.println(var + "===============#==" +true);
						induce_count(sub,val,qryModelIn,qryModelOut);
					}
						
					
					//--------------
					totalOut = typeCounts.get(argtypes.get(pr).size()>1?argtypes.get(pr).get(1):argtypes.get(pr).get(0));
					totalIn = typeCounts.get(argtypes.get(pr).get(0));
					Double expIn, expOut;
					Double subcnt = countTable.get(sub);
					Double outedge = 0.0;
					if(subcnt == 1 && grnd.containsKey(sub))
					{
						//System.out.println(grnd.get(sub));
						if(OutCount.get(grnd.get(sub))!=null)
							outedge = OutCount.get(grnd.get(sub)).get(pr);
						//System.out.println(OutCount);
						//System.out.println("----"+outedge);
						if(outedge==null)
							outedge = 0.0;
						//expOut = outedge;
						
					}
					else
					{
						outedge = predcountTableOut.get(pr);
						//expOut = outedge/totalOut.doubleValue();
						//System.out.println(outedge+"#####"+predcountTableOutNum.getOrDefault(pr, 1.0));
						//outedge = outedge/predcountTableOutNum.getOrDefault(pr, 1.0);
					}
					if(sub.equalsIgnoreCase(var))
						outedge=1.0;
					
					
					Double inedge = 0.0;
					if(countTable.get(var)==1.0 && grnd.containsKey(var))
					{
						//System.out.println(grnd.get(var));
						if(InCount.get(grnd.get(var))!= null)
						{
							inedge=InCount.get(grnd.get(var)).get(pr);
						}
						else
							inedge = 0.0;
						//System.out.println(inedge);
						//expIn = inedge;
					}
					else
					{
						
						inedge = predcountTableIn.get(pr);
						//System.out.println(inedge+"******"+predcountTableInNum.getOrDefault(pr, 1.0));
						//inedge = inedge/predcountTableInNum.getOrDefault(pr, 1.0);
						//expIn = inedge/totalIn.doubleValue();
						
					}
					
					//System.out.println(predcountTableIn);
					//System.out.println(inedge);
					if(inedge==null)
						inedge=0.0;
					else if(sub.equalsIgnoreCase(var))
						inedge=1.0;
					//---- for neg preds
					//Integer totalOut=1,totalIn=1;
					if(predSense.get(pr)==false)
					{
						//totalOut = typeCounts.get(argtypes.get(pr).size()>1?argtypes.get(pr).get(1):argtypes.get(pr).get(0));
						//System.out.println("here----"+outedge);
						outedge = totalOut - outedge;
						
						//totalIn = typeCounts.get(argtypes.get(pr).get(0));
						inedge = totalIn - inedge;
					}
					//--------------------
					
					if(inedge==0.0)
						sum *= 0.0; //change
					else{
						//sum *= subcnt * predcountTableOut.get(pr)/((double)totalOut*(double)totalIn) * (inedge*outedge/(double)totalIn);
						//System.out.println(var+"===="+subcnt);
						//System.out.println(((outedge/(double)totalOut)*(inedge/(double)totalIn)));
						//sum *= subcnt * predcountTableOut.get(pr)/((double)totalOut*(double)totalIn) * (inedge*outedge/(double)totalIn);
						//sum *= subcnt/(outedge*totalOut.doubleValue());
						//sum *= subcnt*((outedge/(double)totalOut)*(inedge/(double)totalIn)); //change
						//System.out.println(+subcnt+"=====$$$ ====" + outedge +":"+inedge+":"+totalOut.doubleValue()+":"+totalIn.doubleValue());
						sum *= subcnt*(outedge*inedge*inedge/(totalOut.doubleValue()*totalIn.doubleValue()*predcountTableOut.get(pr))); //change
					}
					if(sub.equalsIgnoreCase(var))
							sum = 1.0;
				}
			}
			//System.out.println(sum+"^^^^"+countTable.get(var));
			Double cnt = sum*countTable.get(var);
			if(i!=0)
				countTable.put(var, cnt);
			this.final_var = var;
			
			List<String> tempOut = (List<String>) qryModelOut.get(var);
			if(tempOut!=null)
			{
				for(String pair:tempOut)
				{
					String[] pairArr = pair.split("-::-");
					String pr = pairArr[0];
					String o = pairArr[1];
					//System.out.println(vars + "-----" + vars.contains(o));
					if(vars.contains(o))
					{
						//System.out.println("outward");
						induce_count(o,val,qryModelIn,qryModelOut);
						//Double temp = countTable.get(var)*countTable.get(final_var);
						//countTable.put(var, temp);
					}
				}
			}
			return;
		}
		
		/*void induce_count(String var, String val,MultiMap<String,String> qryModelIn, MultiMap<String,String> qryModelOut)
		{
			if(!vars.contains(var))
				return;
			vars.remove(var);
			//System.out.println(countTable);
			Integer totalOut=1,totalIn=1;
			
			List<String> tempIn = (List<String>) qryModelIn.get(var);
			
			Double sum = 1.0; //change
			int i =0;
			if(tempIn!=null)
			{	for(String pair:tempIn)
				{
					i++;
					//QuerySolution qs = rs.next();
					//String sub = qs.get("s").asResource().getLocalName();
					//String pr = qs.get("p").asResource().getLocalName();
					String[] pairArr = pair.split("-::-");
					String sub = pairArr[1];
					String pr = pairArr[0];
					if(vars.contains(sub))
						induce_count(sub,val,qryModelIn,qryModelOut);
					
					//--------------
					totalOut = typeCounts.get(argtypes.get(pr).size()>1?argtypes.get(pr).get(1):argtypes.get(pr).get(0));
					totalIn = typeCounts.get(argtypes.get(pr).get(0));
					Double expIn, expOut;
					Double subcnt = countTable.get(sub);
					Double outedge = 1.0;
					if(subcnt == 1 && grnd.containsKey(sub))
					{
						//System.out.println(grnd.get(sub));
						if(OutCount.get(grnd.get(sub))!=null)
							outedge = OutCount.get(grnd.get(sub)).get(pr);
						//System.out.println(OutCount);
						//System.out.println("----"+outedge);
						if(outedge==null)
							outedge = 0.0;
						//expOut = outedge;
						
					}
					else
					{
						outedge = predcountTableOut.get(pr);
						//expOut = outedge/totalOut.doubleValue();
						//System.out.println(outedge+"#####"+predcountTableOutNum.getOrDefault(pr, 1.0));
						//outedge = outedge/predcountTableOutNum.getOrDefault(pr, 1.0);
					}
					
					
					Double inedge = 1.0;
					if(countTable.get(var)==1.0 && grnd.containsKey(var))
					{
						//System.out.println(grnd.get(var));
						if(InCount.get(grnd.get(var))!= null)
						{
							inedge=InCount.get(grnd.get(var)).get(pr);
						}
						else
							inedge = 0.0;
						//System.out.println(inedge);
						//expIn = inedge;
					}
					else
					{
						
						inedge = predcountTableIn.get(pr);
						//System.out.println(inedge+"******"+predcountTableInNum.getOrDefault(pr, 1.0));
						//inedge = inedge/predcountTableInNum.getOrDefault(pr, 1.0);
						//expIn = inedge/totalIn.doubleValue();
						
					}
					
					//System.out.println(predcountTableIn);
					//System.out.println(inedge);
					if(inedge==null)
						inedge=0.0;
					//---- for neg preds
					//Integer totalOut=1,totalIn=1;
					if(predSense.get(pr)==false)
					{
						//totalOut = typeCounts.get(argtypes.get(pr).size()>1?argtypes.get(pr).get(1):argtypes.get(pr).get(0));
						//System.out.println("here----"+outedge);
						outedge = totalOut - outedge;
						
						//totalIn = typeCounts.get(argtypes.get(pr).get(0));
						inedge = totalIn - inedge;
					}
					//--------------------
					
					if(inedge==0.0)
						sum *= 0.0; //change
					else
						sum *= subcnt * predcountTableIn.get(pr)/((double)totalOut*(double)totalIn) * (inedge*outedge/(double)totalIn);
						//sum *= subcnt/(outedge*totalOut.doubleValue());
						//sum *= subcnt*((outedge/(double)totalOut)*(inedge/(double)totalIn)); //change
						//sum *= subcnt*(outedge*inedge/(totalOut.doubleValue()*totalIn.doubleValue())); //change
				}
			}
			//System.out.println(this.countTable);
			Double cnt = sum*countTable.get(var);
			if(i!=0)
				countTable.put(var, cnt);
			this.final_var = var;
			
			List<String> tempOut = (List<String>) qryModelOut.get(var);
			if(tempOut!=null)
			{
				for(String pair:tempOut)
				{
					String[] pairArr = pair.split("-::-");
					String pr = pairArr[0];
					String o = pairArr[1];
					//System.out.println(vars + "-----" + vars.contains(o));
					if(vars.contains(o))
					{
						//System.out.println("outward");
						induce_count(o,val,qryModelIn,qryModelOut);
						//Double temp = countTable.get(var)*countTable.get(final_var);
						//countTable.put(var, temp);
					}
				}
			}
			return;
		}*/
	
	/*public long getApproxCount(String Gvar, String value, List<Literal> preds, String bitrep)
	{
		//System.out.println("preds"+preds);
		if(preds.size()==0)
			return 0;
		String[] gvarlst = Gvar.split(",");
		String[] vallst = value.split(",");
		MultiMap<String,String> qryModelIn = new MultiValueMap<String,String>();
		MultiMap<String,String> qryModelOut = new MultiValueMap<String,String>();
		
		//String[] PredArr = preds.split("\\|");
		//String[] retvar = rvar.split(",");
		//StringBuilder sb = new StringBuilder();
		String val = value.replace('"', ' ').trim();
		//System.out.println(val);
		Model qryModel = ModelFactory.createDefaultModel();
		Graph qryGraph = qryModel.getGraph();
		double totalcount = 0;
		for(int i = 0; i < preds.size(); ++i)
		{
			double c =0;
			int sign =1;
			Literal p = preds.get(i);
			
			
			String predLabel = p.predicateName.toString();
			String argstr = p.getArguments().toString();

			Object[] arg = p.getArguments().toArray();

			String arg1 = arg[0].toString();
			String arg2 = arg.length==1 ? arg[0].toString() : arg[1].toString();
			
			String pLabel = predLabel.replace('!', ' ').trim();
			if(bitrep.charAt(i)=='0')
				this.predSense.put(pLabel, false);
			else
				this.predSense.put(pLabel, true);
			Resource subj  = qryModel.createResource(ns + arg1);
			Property pred  = qryModel.createProperty(ns + pLabel);
			Resource obj   = qryModel.createResource(ns + arg2);
			qryGraph.add(new Triple(subj.asNode(),pred.asNode(),obj.asNode()));
			
			//--------------------- new optimization ------------
			//populate In --
			qryModelIn.put(arg2, pLabel+"::"+arg1);
			qryModelOut.put(arg1, pLabel+"::"+arg2);
			//System.out.println(typeCounts);
			ArrayList<String> a = argtypes.get(pLabel);
			if(a.size()==1)
			{
				countTable.put(arg1, 0.0+typeCounts.get(a.get(0)));
			}
			else
			{
				countTable.put(arg1, 0.0+typeCounts.get(a.get(0)));
				countTable.put(arg2, 0.0+typeCounts.get(a.get(1)));
			}
			
			if(Gvar!=null)
			{
				for(int gv=0;gv<gvarlst.length;gv++)
				countTable.put(gvarlst[gv], 1.0);
			}
			
		}
		
		Set<String> temp = countTable.keySet();
		vars.addAll(temp);
		
		//System.out.println(countTable);
		
		String currvar = gvarlst[0];
		induce_count(currvar,vallst[0],qryModelIn,qryModelOut);
		//induce_countV2(Gvar,val,qryModelIn,qryModelOut);
		//System.out.println("Final var - "+final_var);
		//System.out.println(countTable);
		//System.out.println("Final count - "+countTable.get(final_var));
		
		return ((countTable.get(final_var).longValue()==0?(long)delta:countTable.get(final_var).longValue()));
		
		//return 0;
	}
	
	void induce_count(String var, String val,MultiMap<String,String> qryModelIn, MultiMap<String,String> qryModelOut)
	{
		if(!vars.contains(var))
			return;
		vars.remove(var);
		
		List<String> tempIn = (List<String>) qryModelIn.get(var);
		
		double sum = 1.0; //change
		int i =0;
		if(tempIn!=null)
		{	for(String pair:tempIn)
			{
				i++;
				//QuerySolution qs = rs.next();
				//String sub = qs.get("s").asResource().getLocalName();
				//String pr = qs.get("p").asResource().getLocalName();
				String[] pairArr = pair.split("::");
				String sub = pairArr[1];
				String pr = pairArr[0];
				if(vars.contains(sub))
					induce_count(sub,val,qryModelIn,qryModelOut);
				
				//--------------
				Double subcnt = countTable.get(sub);
				Double outedge = 0.0;
				if(subcnt == 1)
				{
					
					if(OutCount.get(sub)!=null)
						outedge = OutCount.get(sub).get(pr);
				}
				else
					outedge = predcountTableOut.get(pr);
				if(outedge==null)
					outedge = 0.0;
				
				Double inedge = 1.0;
				if(countTable.get(var)==1)
				{
					
					if(InCount.get(val)!= null)
					{
						inedge=InCount.get(val).get(pr);
					}
					else
						inedge = 0.0;
				}
				else
				{
					
					inedge = predcountTableIn.get(pr);
					
				}
				if(inedge==null)
					inedge=0.0;
				//---- for neg preds
				Integer totalOut=1,totalIn=1;
				if(predSense.get(pr)==false)
				{
					totalOut = typeCounts.get(argtypes.get(pr).size()>1?argtypes.get(pr).get(1):argtypes.get(pr).get(0));
					//System.out.println("here----"+outedge);
					outedge = totalOut - outedge;
					
					totalIn = typeCounts.get(argtypes.get(pr).get(0));
					inedge = totalIn - inedge;
				}
				//--------------------
				
				if(inedge==0)
					sum *= 0.0; //change
				else
					sum *= subcnt*((outedge/totalOut)*(inedge/totalIn)); //change
			}
		}
		//System.out.println(this.countTable);
		Double cnt = sum*countTable.get(var);
		if(i!=0)
			countTable.put(var, cnt);
		this.final_var = var;
		
		List<String> tempOut = (List<String>) qryModelOut.get(var);
		if(tempOut!=null)
		{
			for(String pair:tempOut)
			{
				String[] pairArr = pair.split("::");
				String pr = pairArr[0];
				String o = pairArr[1];
				//System.out.println(vars + "-----" + vars.contains(o));
				if(vars.contains(o))
				{
					//System.out.println("outward");
					induce_count(o,val,qryModelIn,qryModelOut);
					Double temp = countTable.get(var)*countTable.get(final_var);
					countTable.put(var, temp);
				}
			}
		}
		return;
	}*/
	

}
