package edu.wisc.cs.will.FOPC;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

import edu.wisc.cs.will.Utils.Utils;

public class IsaHetrarchy {	
	/*
	 * Written by shavlik.
	 */
	
	
	protected final static int debugLevel = 0; // Used to control output from this project (0 = no output, 1=some, 2=much, 3=all).
	
	private HandleFOPCstrings stringHandler; // Have a back pointer to the owner of this ISA hetrarchy.
	
	public static final String WILL_ANYTHING_TYPE_NAME = "willAnything";
	public static final String WILL_LIST_TYPE_NAME     = "willList";
	public static final String WILL_NUMBER_TYPE_NAME   = "willNumber";
	public static final String WILL_BOOLEAN_TYPE_NAME  = "willBoolean";
	public static final String WILL_TOKEN_TYPE_NAME    = "willToken";
	public static final String WILL_ATOMIC_TYPE_NAME   = "willAtomic";	
	private Type willListType, willAtomicType, willNumberType, willBooleanType, willTokenType;
	
	private   Type                        rootOfISA;
	private   Map<Type,List<Type>>        isaHetrarchy; // Only LEAF nodes can be ISA more than one type.  EXTENDED (7/09) TO A HETRARCHY.
	private   Map<Type,List<Type>>        reverseIsaHetrarchy;  // Allow quick lookup of the CHILDREN nodes.
	protected Map<String,Type>            isaTypeHash; // Used to convert strings to types.  THIS IS NOT USED TO STORE PARENTS POINTERS IN THE ISA Hetrarchy (isaHetrarchy is used for this).
	
	protected IsaHetrarchy(HandleFOPCstrings stringHandler) {
		
		this.stringHandler  = stringHandler;

		isaTypeHash         = new HashMap<String,Type>(16);
		isaHetrarchy        = new HashMap<Type,List<Type>>(4);  // Might not have any of these, but go ahead and make the hash map.
		reverseIsaHetrarchy = new HashMap<Type,List<Type>>(4);  // Ditto.
		rootOfISA           = getIsaType(WILL_ANYTHING_TYPE_NAME); // Be sure to use getIsaType() so the proper case is used.
		reverseIsaHetrarchy.put(rootOfISA, new ArrayList<Type>(32));
		willListType    = getIsaType(WILL_LIST_TYPE_NAME);
		willAtomicType  = getIsaType(WILL_ATOMIC_TYPE_NAME);
		willNumberType  = getIsaType(WILL_NUMBER_TYPE_NAME);
		willBooleanType = getIsaType(WILL_BOOLEAN_TYPE_NAME);
		willTokenType   = getIsaType(WILL_TOKEN_TYPE_NAME);
		addISA(willListType,    rootOfISA);
		addISA(willAtomicType,  rootOfISA);
		addISA(willNumberType,  getIsaType(WILL_ATOMIC_TYPE_NAME));
		addISA(willBooleanType, getIsaType(WILL_ATOMIC_TYPE_NAME));
		addISA(willTokenType,   getIsaType(WILL_ATOMIC_TYPE_NAME));
		
		if (debugLevel > 2) {
			Utils.println("%         isa: " + Utils.limitLengthOfPrintedList(isaHetrarchy,        25));
			Utils.println("% reverse isa: " + Utils.limitLengthOfPrintedList(reverseIsaHetrarchy, 25));
			Utils.waitHere();
		}
	}
	
	public Type getWillListType()    { 	return willListType;	}
	public Type getWillAtomicType()  {	return willAtomicType;	}
	public Type getWillNumberType()  {  return willNumberType;	}
	public Type getWillBooleanType() {	return willBooleanType;	}
	public Type getWillTokenType()   {	return willTokenType;	}
	
	public List<Type> getAllKnownTypesForThisTerm(Term term) {
		if (term instanceof Variable) { return null; }
		if (term instanceof Function) { return null; }
		if (term instanceof StringConstant) { // TODO - should we check if we know this is a willTokenType (eg, as done for numbers)?  Seems unnecessary.
			StringConstant sc = (StringConstant) term;
			String      value = sc.getName();
			Type lookup = isaTypeHash.get(value);
			if (lookup == null) { return null; }
			return isaHetrarchy.get(lookup);
		}
		if (term instanceof NumericConstant) {
			NumericConstant nc = (NumericConstant) term;
			String      value = nc.getName();
			Type lookup = isaTypeHash.get(value);
			if (lookup == null) { 
				List<Type> result = new ArrayList<Type>(1);
				result.add(willNumberType);
				return result;
			}
			List<Type> result = isaHetrarchy.get(lookup);
			if (result != null) {
				if (result.contains(willNumberType)) { return result; }
				// Else see if this is already known via an ISA.
				for (Type knownType : result) {
					if (isa(knownType, willNumberType)) { return result; }
				}
			}
			List<Type> result2 = new ArrayList<Type>(Utils.getSizeSafely(result) + 1);
			if (result != null) { result2.addAll(result); }
			result2.add(willNumberType);
			return result2;
		}
		return null;
	}
	
	public boolean okToAddToIsa(Type child, Type parent) {
		if (isa(child, parent)) { /* Utils.println("TEMP: isa(" + child +  "," + parent + ")"); */ return false; }
		if (isa(parent, child)) { /* Utils.println("TEMP: isa(" + parent + "," + child  + ")"); */ return false; } // TODO indicate somehow this is circular?
		return true;
	}
	
	public void addISA(Type child, Type parent) {
		if (debugLevel > 1) { Utils.println("addISA(" + child + ", " + parent + ")."); }
		if (isa(child, parent)) { return; }  // Some callers check this and the following line, but not all do, so play it safe.
		if (isa(parent, child)) { Utils.error("Cannot add '" + child + " ISA " + parent + "' because the reverse is already the case."); }
		// Utils.println("Add isa(" + child + "," + parent + ").");
		List<Type> otherParents = isaHetrarchy.get(child);
		
		if (otherParents != null) {
			ListIterator<Type> parentIter = otherParents.listIterator();
			while (parentIter.hasNext()) { // Need to do this for ALL parents.
				Type otherParent = parentIter.next();
				if        (isa(otherParent, parent)) {
					// Want to add isa(A,C) but already have isa(A,B) and isa(B,C).
					Utils.waitHere("This should not occur since then would already be ISA.");
					return;
				} else if (isa(parent, otherParent)) {
					// Want to add isa(A,C) but already have isa(A,B) and isa(C,B),
					// so can remove the A-B link.  HOWEVER CAN ONKY DO THIS BECAUSE A-B IS A *DIRECT* LINK.  OTHERWISE MIGHT LOSE SOME ISA's.
					if (debugLevel > 1) { Utils.println("removeISA(" + child + ", " + otherParent + ") because isa(" + parent + ", " + otherParent + ")."); }
					parentIter.remove(); // Need to use this instead of removeISA() due to the way Java iteration works.
					removeFromReverseISA(otherParent, child);
				}
			}
		}
		else {
			otherParents = new ArrayList<Type>(1);
		}
		isaHetrarchy.put(child, otherParents);
		otherParents.add(parent);		
		addToReverseISA(parent, child);	
		if (!isaHetrarchy.containsKey(parent)) { addISA(parent, rootOfISA); }
		if (debugLevel > 1) { Utils.println("addISA(" + child + ", " + parent + "): isa = " + Utils.limitLengthOfPrintedList(isaHetrarchy, 25)); }
	}
	
	/**
         * @param parent
         * @return All the children of this type in the type Hetrarchy.
         */
	protected List<Type> reverseIsa(Type parent) {
		return reverseIsaHetrarchy.get(parent);
	}
	public Type getIsaType(Term constant) {	// TODO - clean up and put interfaces to all public's in the string handler?
		return getIsaType(constant.toString());
	}
	public Type getIsaType(String name) {	// Might want to require types to be the same case as constants, but seems OK to deal with these in a case-independent manner.	
		String stdName     = (stringHandler.getStringsAreCaseSensitive() ? name : name.toLowerCase()); // Hash case-independently if that is how strings are handled..
		Type   hashedValue = isaTypeHash.get(stdName);
		
		// Utils.println("  getIsaType: stdName=" + stdName + " hashed=" + hashedValue);
		if (hashedValue != null) { return hashedValue; }
		
		Type result = new Type(name, stringHandler); // Store using the first version seen.
		isaTypeHash.put(stdName, result);
		// Utils.println("  getIsaType, put in isaTypeHash: " + stdName + " -> " + result);
		return result;		
	}
	protected void addISA(String child, String parent) {
		if (child == null || parent == null) { Utils.error("Cannot have null's in isa(" + child + ", " + parent + ")"); }
		if (child.equals(parent)) { 
			if (HandleFOPCstrings.debugLevel > 2) { Utils.println("Ignoring " + child + " ISA " + parent + "."); }
			return;
		}
		
		Type childType  = getIsaType(child);
		Type parentType = getIsaType(parent);
		addISA(childType, parentType); 
	}
	protected void addISA(Term child, Type parentType ) {
		stringHandler.addConstantToISA(child, getIsaType(child), parentType); // Need to register this constant.
	}
	protected List<Type> reverseISA(String parent) {
		return reverseIsaHetrarchy.get(getIsaType(parent));
	}
	
	protected void addToReverseISA(Type parent, Type child) {
		List<Type> children = reverseIsa(parent);
		
		if (children != null) {
			if (children.contains(child)) { return; } // Already there.
			children.add(child);
			}
		else {
			List<Type> newChildren = new ArrayList<Type>(1);
			newChildren.add(child);
			reverseIsaHetrarchy.put(parent, newChildren);
		}
	}

	// Only works for DIRECT child-parent links.
	private boolean removeFromReverseISA(Type parent, Type child) {
		Collection<Type> children = reverseIsa(parent);
		
		if (children != null) {
			if (children.contains(child)) {
				if (!children.remove(child)) { Utils.error("Could not remove '" + child + "' from " + Utils.limitLengthOfPrintedList(children, 10) + " of '" + parent + "'."); }
				return true;
			}
		}
		Utils.println("%         isa: " + Utils.limitLengthOfPrintedList(isaHetrarchy));
		Utils.println("% reverse isa: " + Utils.limitLengthOfPrintedList(reverseIsaHetrarchy));
		Utils.println("% reverse children of '" + parent + "' are " + children);
		Utils.error("Cannot remove '" + child + "' from the reverse ISA of '" + parent + "'.");
		return false;
	}
	
	// Only works for DIRECT child-parent links.
	protected void removeISA(String child, String parent) {
		if (child == null || parent == null) { Utils.error("Cannot have null's in remove isa(" + child + ", " + parent + ")"); }
		if (child.equals(parent))            { Utils.error("Cannot remove isa(" + child + ", " + parent + ")"); }
		
		Type childType  = getIsaType(child);
		Type parentType = getIsaType(parent);
		removeISA(childType, parentType);
	}
	protected void removeISA(Type childType, Type parentType) {
		List<Type> currentParents = isaHetrarchy.get(childType);
		
		if (!currentParents.remove(parentType)) { 
			Utils.error("Cannot find isa(" + childType + ", " + parentType + ").  Currently isa(" + childType + ", " + Utils.limitLengthOfPrintedList(currentParents, 10) + ")."); // Could simply fail silently here?
		}	
		removeFromReverseISA(parentType, childType);
	}
	
	// See if child ISA parent.
	public boolean isa(String child, String parent) {
		return isa(getIsaType(child), getIsaType(parent));
	}
	public boolean isa(Type child, String parent) {
		return isa(child, getIsaType(parent));
	}
	public boolean isa(String child, Type parent) {
		return isa(getIsaType(child), parent);
	}
	public boolean isa(Type child, Type parent) {
		// if (parent == rootOfISA) { return true; } // Save some time.  THIS MESSES UP THE INITIALIZATION.  IF REALLY NEEDED, ADD A 'done' FLAG.
		if (false) {
			boolean temp = isa(child, parent, 0);
			Utils.println(" isa(" + child + ", " + parent + ") = " + temp);
			return temp;
		}
		return isa(child, parent, 0);
	}
	private boolean isa(Type child, Type parent, int depth) {
		if (depth > 100) { Utils.error("isa depth too deep? checking isa(" + child + "," + parent + ")  depth=" + depth); }
		if (child == parent) { return true; }
		List<Type> ancestors = isaHetrarchy.get(child);
		if (depth >  50) {
			for (int i = 0; i < depth; i++) { Utils.print(""); }
			Utils.println("  checking isa(" + child + "," + parent + ")  depth=" + depth + " ancestors=" + ancestors);
		}
		if (ancestors == null) {return false; }
		int depthPlus1 = depth + 1;
		for (Type ancestor : ancestors) if (isa(ancestor, parent, depthPlus1)) { return true; }
		return false;
	}

	// This deals with hetrarchies by using breadth-first search.
	// This code assumes no loops in the ISA's, though there is a counter to catch odd behavior.
	public Type nearestCommonParent(String typeA, String typeB, boolean complainIfNoParentFound) {
		return nearestCommonParent(getIsaType(typeA), getIsaType(typeB), complainIfNoParentFound);
	}
	public Type nearestCommonParent(Type typeA, Type typeB, boolean complainIfNoParentFound) {
		if (debugLevel > 1) { Utils.println("% nearestCommonParent(" + typeA + ", " + typeB + ")."); }
		if (typeA == null) { Utils.waitHere("TypeA should not be null (TypeB = " + typeB + ")"); return null; }
		if (typeB == null) { Utils.waitHere("TypeB should not be null (TypeA = " + typeA + ")"); return null; }
		if (isa(typeA, typeB)) { return typeB; }
		if (isa(typeB, typeA)) { return typeA; }
		
		Type typeAorig = typeA; // Hold for reporting.
		Type typeBorig = typeB;
		
		Set<Type> parentsOfOriginalA = new HashSet<Type>(4);
		Set<Type> parentsOfOriginalB = new HashSet<Type>(4);
		
		List<Type> typeAinIsa = isaHetrarchy.get(typeA);
		List<Type> typeBinIsa = isaHetrarchy.get(typeB);
		if (typeAinIsa == null) { Utils.warning("Cannot find '" + typeA + "' in the isa: " + Utils.limitLengthOfPrintedList(isaHetrarchy)); return rootOfISA; }
		if (typeBinIsa == null) { Utils.warning("Cannot find '" + typeB + "' in the isa: " + Utils.limitLengthOfPrintedList(isaHetrarchy)); return rootOfISA; }
		Set<Type> ancestorsA = new HashSet<Type>(typeAinIsa);
		Set<Type> ancestorsB = new HashSet<Type>(typeBinIsa);
		
		int counter = 0;
		
		while (Utils.getSizeSafely(ancestorsA) > 0 ||  Utils.getSizeSafely(ancestorsB) > 0) {
			
			if (Utils.getSizeSafely(ancestorsA) > 0) { 
				Set<Type> newAncestorsA = new HashSet<Type>(4); // TODO - should be able to write without needing new memory cells.  Just have two OPEN lists and append at END.  But how to alternate between them?  The current implementation explicitly does level-by-level.
				for (Type ancestor : ancestorsA) { // Go through the current level and collect all new nodes.
					if (parentsOfOriginalB.contains(ancestor)) { 
						if (debugLevel > 1) { Utils.println("% The closest common parent of '" + typeAorig + "' and '" + typeBorig + "' is '" + ancestor + "."); }
						return ancestor; 
					}
					if (isaHetrarchy.get(ancestor) != null) {
						newAncestorsA.addAll(isaHetrarchy.get(ancestor));
					}
				}
				ancestorsA = newAncestorsA;
			}
			if (Utils.getSizeSafely(ancestorsB) > 0) {
				Set<Type> newAncestorsB = new HashSet<Type>(4);
				for (Type ancestor : ancestorsB) {
					if (parentsOfOriginalA.contains(ancestor)) { 
						if (debugLevel > 1) { Utils.println("% The closest common parent of '" + typeAorig + "' and '" + typeBorig + "' is '" + ancestor + "."); }
						return typeB; 
					}
					parentsOfOriginalA.add(ancestor);
					if (isaHetrarchy.get(ancestor) != null) {
						newAncestorsB.addAll(isaHetrarchy.get(ancestor));
					}
				}
				ancestorsB = newAncestorsB;
			}
			if (counter++ > 1000) { Utils.error("Infinite loop?  AncestorsA = " + ancestorsA + ", ancestorsB = " + ancestorsB); }
		}
		if (complainIfNoParentFound) { Utils.error("Cannot find a common parent of '" + typeAorig + "' and '" + typeBorig + "'."); }
		return null;
	}
	
	protected List<Type> getTypeAndSuperTypes(Type child) {
		List<Type> ancestors = isaHetrarchy.get(child);
		List<Type> result    = null;
		if (ancestors == null) { 
			result = new ArrayList<Type>(1); 
			if (child != rootOfISA) { result.add(rootOfISA); }
		} else { 
			for (Type ancestor : ancestors) { 
				List<Type> results2 = getTypeAndSuperTypes(ancestor);
				if (result == null) { result = results2; }
				else                { result.addAll(results2); }
			}
		}
		result.add(0, child); // Add to front so list is in order from child to root. 
		return result;		
	}	
	
	public void dumpIsaHier() {  // TODO need to pretty print.
		Utils.println("\n% The isa hetrarchy: " + isaHetrarchy);
	}
	
	// Collect all the instances of this type AND OF ITS CHILDREN.  A FRESH list is returned.
	public Set<Term> getAllInstances(Type thisType) {
		// Utils.println("getAllInstances of " +EntryType);
		if (debugLevel > 3) { Utils.println("% knownConstantsOfThisType = " + Utils.limitLengthOfPrintedList(stringHandler.knownConstantsOfThisType, 50)); }
		
		// First get all the instances at this node.
		Set<Term> results = stringHandler.getConstantsOfExactlyThisTypeAsList(thisType);
		// Next collect all the instances beneath this node.
		Collection<Type> children = reverseIsa(thisType);  // Notice we need the REVERSE isa Hetrarchy here.	
		if (children != null) for (Type child : children) { 
			Set<Term> childrenInstances = getAllInstances(child);
			if (childrenInstances == null) { continue; }
			if (results == null) { results = new HashSet<Term>(4); }
			results.addAll(childrenInstances);
		}
		return results;
	}
//	public static void main(String[] args)  {
//		args = Utils.chopCommentFromArgs(args);
//
//		// Test ISA to see if a hetrarchy works.
//		HandleFOPCstrings stringHandler = new HandleFOPCstrings();
//		IsaHetrarchy      isaHandler    = stringHandler.isaHandler;
//
//		Type h = new Type("h");
//		Type i = new Type("i");
//		Type j = new Type("j");
//		Type k = new Type("k");
//		Type l = new Type("l");
//		Type m = new Type("m");
//		Type a = new Type("a");
//		Type b = new Type("b");
//		Type c = new Type("c");
//		Type d = new Type("d");
//		Type e = new Type("e");
//		Type f = new Type("f");
//		Type g = new Type("g");
//
//		isaHandler.addISA(a, d);
//		isaHandler.addISA(a, e);
//		isaHandler.addISA(a, f);
//		isaHandler.addISA(b, d);
//		isaHandler.addISA(b, e);
//		isaHandler.addISA(b, f);
//		isaHandler.addISA(c, d);
//		isaHandler.addISA(c, e);
//		isaHandler.addISA(c, f);
//		isaHandler.addISA(f, g);
//		isaHandler.addISA(f, h);
//		isaHandler.addISA(f, i);
//		isaHandler.addISA(i, j);
//		isaHandler.addISA(a, j);
//
//		isaHandler.addISA(k, j);
//		isaHandler.addISA(a, k);
//		isaHandler.addISA(l, c);
//		isaHandler.addISA(m, a);
//
//		Utils.println(" isa(a,b) = " + isaHandler.isa(a,b));
//		Utils.println(" isa(a,f) = " + isaHandler.isa(a,f));
//		Utils.println(" isa(a,h) = " + isaHandler.isa(a,h));
//		Utils.println(" isa(b,j) = " + isaHandler.isa(b,j));
//		Utils.println(" isa(c,i) = " + isaHandler.isa(c,i));
//		Utils.println(" isa(l,j) = " + isaHandler.isa(l,j));
//		Utils.println(" isa(l,b) = " + isaHandler.isa(l,b));
//
//		isaHandler.dumpIsaHier();
//
//		Utils.println(" reverseISA(j) = " + isaHandler.reverseIsa(j));
//		Utils.println(" reverseISA(a) = " + isaHandler.reverseIsa(a));
//		Utils.println(" reverseISA(d) = " + isaHandler.reverseIsa(d));
//
//	}
	
}
