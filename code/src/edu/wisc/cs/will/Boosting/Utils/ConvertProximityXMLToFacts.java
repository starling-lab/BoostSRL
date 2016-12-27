/**
 * 
 */
package edu.wisc.cs.will.Boosting.Utils;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.print.attribute.HashAttributeSet;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.omg.CORBA.OBJ_ADAPTER;
import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import edu.wisc.cs.will.Utils.Utils;
import edu.wisc.cs.will.Utils.condor.CondorFile;
import edu.wisc.cs.will.Utils.condor.CondorFileWriter;

/**
 * @author shark
 *
 */
public class ConvertProximityXMLToFacts {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		// TODO Auto-generated method stub

		String filename = "C:\\Documents and Settings\\shark\\My Documents\\Downloads\\proximity-4.3\\proximity\\proxwebkb.xml";
		for (int i = 0; i < 4; i++) {
			ConvertProximityXMLToFacts converter = new ConvertProximityXMLToFacts();
			converter.setContainerName("1d-clusters/testf/" + i);
			converter.parse(filename);
			try {
			BufferedWriter writer = new BufferedWriter(new CondorFileWriter("webkb_test" + i + ".txt"));
			converter.writeFactsToWriter(writer);
			writer.close();
			}
			catch(IOException e) {
				e.printStackTrace();
				Utils.reportStackTrace(e);
			}
		}
		
	}
	private String containerName = "1d-clusters/train/0";
	public String getContainerName() {
		return containerName;
	}


	public void setContainerName(String containerName) {
		this.containerName = containerName;
	}
	private List<String> objIds;
	private List<String> linkIds;
	private List<String> fromIds;
	private List<String> toIds;
	private Map<String, Map<String, List<String>>> objectAttrs;
	private Map<String, Map<String, List<String>>> linkAttrs;
	private Set<String> container_objIds;
	private Set<String> container_linkIds;

	public ConvertProximityXMLToFacts() {
		objIds = new ArrayList<String>();
		linkIds = new ArrayList<String>();
		fromIds = new ArrayList<String>();
		toIds = new ArrayList<String>();
		objectAttrs = new HashMap<String, Map<String,List<String>>>();
		linkAttrs = new HashMap<String, Map<String,List<String>>>();
		container_objIds = new HashSet<String>();
		container_linkIds = new HashSet<String>();
	}


	public void writeFactsToWriter(Writer op) throws IOException {
		for (String objAtt : objectAttrs.keySet()) {
			Map<String, List<String>> y = objectAttrs.get(objAtt);
			for (String key : y.keySet()) {
				if (isValidObject(key)) {
					for (String atts : y.get(key)) {
						System.out.print(".");
						op.write(objAtt+"(" + key+","+atts+").\n");
					}
				}
			} 
		}
		System.out.println(".");
		for (int pos = 0; pos < fromIds.size(); pos++) {
			String from = fromIds.get(pos);
			String to = toIds.get(pos);
			if (isValidLink(linkIds.get(pos))) {
				op.write("link"+"(" + from + "," + to + ").\n");
			}
		}
		for (String objAtt : linkAttrs.keySet()) {
			Map<String, List<String>> y = linkAttrs.get(objAtt);
			for (String key : y.keySet()) {
				int pos = linkIds.indexOf(key);
				if (pos == -1) {
					Utils.error("Didnt find " + key + " in links for " + objAtt);
				}
				if (isValidLink(key)) {
					String from = fromIds.get(pos);
					String to = toIds.get(pos);
					for (String atts : y.get(key)) {
						System.out.print(".");
						op.write(objAtt+"(" + from + "," + to +","+atts+").\n");
					}
				}
			} 
		}
		System.out.println(".");
	}




	private boolean isValidLink(String string) {
		return container_linkIds.contains(string);
	}


	private boolean isValidObject(String key) {
		return container_objIds.contains(key);
	}

	private final static String XML_HEAD = "PROX3DB";
	private final static String ID_ATTR = "ID";
	private final static String FROM_ID_ATTR = "O1-ID";
	private final static String TO_ID_ATTR = "O2-ID";

	public void parse(String filename) {

		Document doc = getXMLDoc(filename);
		if (doc == null) {
			Utils.waitHere("Didnt read the file or filename absent:" + filename);
		}
		String file_head = doc.getDocumentElement().getNodeName();
		if (!file_head.equals(XML_HEAD)) {
			Utils.waitHere("Expecting '" + XML_HEAD + "' as the head of the xml file. But found '" + file_head + "'");
		}

		// Go through each node
		NodeList nodes = doc.getDocumentElement().getChildNodes();
		if (nodes == null)
			return;

		for (int i = 0; i < nodes.getLength(); i++) {
			String nodename = nodes.item(i).getNodeName();
			if (nodename.equals("OBJECTS")) {
				handleObjects(nodes.item(i));
			}
			if (nodename.equals("LINKS")) {
				handleLinks(nodes.item(i));
			}
			if (nodename.equals("ATTRIBUTES")) {
				handleAttrs(nodes.item(i));
			}
			if (nodename.equals("CONTAINERS")) {
				handleContainers(nodes.item(i));
			}
		}
	}


	private void handleContainers(Node item) {
		Node container = getContainerChild(item, containerName);
		if (container == null) {
			Utils.error("Didn't find container: " + containerName);
		}
		NodeList children = container.getChildNodes();
		for (int i = 0; i < children.getLength(); i++) {
			Node child = children.item(i);
			if (child.getNodeName().equals("SUBG-ITEMS")) {
				NodeList subg_children = child.getChildNodes();
				for (int j = 0; j < subg_children.getLength(); j++) {
					Node subg_child = subg_children.item(j);
					if (subg_child.getNodeName().equals("ITEM")) {
						String itemid = getItemId(subg_child);
						String itemtype = getItemType(subg_child);
						if (itemtype.equals("L")){
							container_linkIds.add(itemid);
						}
						if (itemtype.equals("O")){
							container_objIds.add(itemid);
						}
					}
				}
			}
		}
	}

	private Node getContainerChild(Node item, String cont) {
		String[] container_path = cont.split("/");
		int cont_path_index = 0;
		return getContainerChildRecursive(item, container_path, cont_path_index);
	}
	private Node getContainerChildRecursive(Node item, String[] container_path, int cont_path_index) {
		NodeList children = item.getChildNodes();
		for (int i = 0; i < children.getLength(); i++) {
			Node child = children.item(i);
			if (child.getNodeName().equals("CONTAINER")) {
				String name = getName(child);
				if (name.equals(container_path[cont_path_index])) {
					if (cont_path_index == (container_path.length-1)) {
						return child;
					}
					Node result = getContainerChildRecursive(child, container_path, cont_path_index+1);
					if (result != null) {
						return result;
					}
				}
			}
		}
		// Didn't find it
		return null;
	}


	private void handleAttrs(Node item) {
		NodeList nodes = item.getChildNodes();
		if (nodes == null)
			return;

		for (int i = 0; i < nodes.getLength(); i++) {
			String nodename = nodes.item(i).getNodeName();
			if (nodename.equals("ATTRIBUTE")) {
				Node node = nodes.item(i);
				String name = getName(node);
				String type = getItemType(node);
				NodeList childnodes = node.getChildNodes();
				HashMap<String, List<String>> attributeValue = new HashMap<String, List<String>>();

				for (int j = 0; j < childnodes.getLength(); j++) {
					String childname = childnodes.item(j).getNodeName();
					if (childname.equals("ATTR-VALUE")) {
						Node childnode = childnodes.item(j);
						String id = getItemId(childnode);
						ArrayList<String> attrValues = getColValues(childnode);
						//for (String attr : attrValues) {
						//System.out.println(name +"("+type + id+"," + attr+").");
						//}
						attributeValue.put(id, attrValues);
					}
				}
				
				if (type.equals("O")) { 
					objectAttrs.put(name, attributeValue);
				} 
				if (type.equals("L")) {
					linkAttrs.put(name, attributeValue);
				}


			}
		}

	}

	private ArrayList<String> getColValues(Node item) {
		NodeList nodes = item.getChildNodes();
		ArrayList<String> result = new ArrayList<String>();
		if (nodes == null)
			return result;

		for (int i = 0; i < nodes.getLength(); i++) {
			String nodename = nodes.item(i).getNodeName();
			if (nodename.equals("COL-VALUE")) {
				Node node = nodes.item(i);
				result.add("\"" + node.getTextContent() + "\"" );
			}
		}
		return result;
	}

	private String getItemId(Node node) {
		return node.getAttributes().getNamedItem("ITEM-ID").getNodeValue();
	}

	private String getItemType(Node node) {
		return node.getAttributes().getNamedItem("ITEM-TYPE").getNodeValue();
	}

	private String getName(Node node) {
		return node.getAttributes().getNamedItem("NAME").getNodeValue();
	}

	private void handleLinks(Node item) {
		NodeList nodes = item.getChildNodes();
		if (nodes == null)
			return;

		for (int i = 0; i < nodes.getLength(); i++) {
			String nodename = nodes.item(i).getNodeName();
			if (nodename.equals("LINK")) {
				Node node = nodes.item(i);
				String id = getID(node);
				String from = getFrom(node);
				String to = getTo(node);
				linkIds.add(id);
				fromIds.add(from);
				toIds.add(to);
			}
		}	
	}

	private String getTo(Node node) {
		return node.getAttributes().getNamedItem(TO_ID_ATTR).getNodeValue();
	}

	private String getFrom(Node node) {
		return node.getAttributes().getNamedItem(FROM_ID_ATTR).getNodeValue();
	}

	private void handleObjects(Node item) {
		// Go through each node
		NodeList nodes = item.getChildNodes();
		if (nodes == null)
			return;

		for (int i = 0; i < nodes.getLength(); i++) {
			String nodename = nodes.item(i).getNodeName();
			if (nodename.equals("OBJECT")) {
				Node node = nodes.item(i);
				String id = getID(node);
				objIds.add(id);
			}
		}

	}

	private String getID(Node node) {
		return node.getAttributes().getNamedItem(ID_ATTR).getNodeValue();
	}

	public Document getXMLDoc(String filename) {
		DocumentBuilderFactory docBuilderFactory = DocumentBuilderFactory.newInstance();
		DocumentBuilder docBuilder=null;
		Document doc = null;
		File f = new CondorFile(filename);
		if(f.length() == 0)
			return null;
		try {
			docBuilder = docBuilderFactory.newDocumentBuilder();
		} catch (ParserConfigurationException e) {
			Utils.reportStackTrace(e);
			Utils.error("Encountered a problem: " + e);
		}
		try {
			doc = docBuilder.parse(f);
		} catch (SAXException e) {
			Utils.reportStackTrace(e);
			Utils.error("Encountered a problem: " + e);
		} catch (IOException e) {
			Utils.reportStackTrace(e);
			Utils.error("Encountered a problem: " + e);
		}

		// normalize text representation
		doc.getDocumentElement().normalize();
		return doc;
	}

}
