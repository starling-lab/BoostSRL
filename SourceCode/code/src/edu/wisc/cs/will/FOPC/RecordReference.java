package edu.wisc.cs.will.FOPC;

//Written by Trevor Walker.

@SuppressWarnings("serial")
public class RecordReference extends Constant {

	protected String key;
	protected RecordEntry recordEntry;
	
	/** Index to provide nice printing and debugging.
	 * 
	 * This index can be removed if memory becomes important.
	 */
	protected int index;
	
	/** Index counter to assign each Reference a unique index.
	 * 
	 * Can be remove along with index if desired.
	 */
	private static int nextDBIndex = 0; 
	
	/** Creator for weak references.
	 * 
	 * These should not be created directly.  The RecordReferenceMap
	 * should be used to obtain canonical references to the appropriate
	 * RecordReference.
     *
     * @param key
     * @param recordEntry
     */
	protected RecordReference(String key, RecordEntry recordEntry) {
		this.key = key;
		this.recordEntry = recordEntry;
		this.index = nextDBIndex++;
	}
	
	public boolean freeVariablesAfterSubstitution(BindingList theta) {
		return false;
	}

    @Override
    public BindingList isEquivalentUptoVariableRenaming(Term that, BindingList bindings) {
        throw new UnsupportedOperationException("Not supported yet.");
    }
	
    

	@Override
	public String getName() {
		return "'$REF:" + key + "@" + index + "'";
	}

	@Override
	public String toPrettyString(String newLineStarter, int precedenceOfCaller, BindingList bindingList) {
		return getName();
	}

	@Override
	public String toString(int precedenceOfCaller, BindingList bindingList) {
		return getName();
	}


}
