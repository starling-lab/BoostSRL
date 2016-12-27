package edu.wisc.cs.will.DataSetUtils;

import edu.wisc.cs.will.FOPC.Constant;
import edu.wisc.cs.will.FOPC.Term;
import edu.wisc.cs.will.FOPC.Variable;

/**
 * @author shavlik
 *
 */
public class WorldState {
	private Constant world;
	private Constant state;
	
	public WorldState(Constant world, Constant state) {
		this.world = world;
		this.state = state;
	}
	public Constant getWorld() {
		return world;
	}
	public void setWorld(Constant world) {
		this.world = world;
	}
	public Constant getState() {
		return state;
	}
	public void setState(Constant state) {
		this.state = state;
	}
	
	@Override
	public int hashCode() { // Need to have equal objects produce the same hash code.
		final int prime = 31;
		int result = 1;
		result = prime * result + ((state == null) ? 0 : state.hashCode());
		result = prime * result + ((world == null) ? 0 : world.hashCode());
		return result;
	}
	public boolean equals1(Object other) {
		if (this  == other) { return true; }
		if (other == null)  { return false; }
		
		if (other instanceof WorldState) {
			WorldState otherAsWorldState = (WorldState) other;
			return (world == otherAsWorldState.world && state == otherAsWorldState.state);
		}
		return false;
	}
	
	public boolean equals(Term otherWorld, Term otherState) {
		if (otherWorld instanceof Variable && otherState instanceof Variable) {
			return otherWorld != otherState;
		}
		if (otherWorld instanceof Variable) {
			return state == otherState;
		}
		if (otherState instanceof Variable) {
			return world == otherWorld;
		}
		return (world == otherWorld && state == otherState);
	}

	public boolean isaNullWorldState() {
		return (world == null && state == null);
	}
	
	public String toString() {
		return world + "." + state;
	}
	
	
}
