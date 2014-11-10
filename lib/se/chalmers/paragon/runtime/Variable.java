package se.chalmers.paragon.runtime;

public class Variable extends Argument {
	
	private final int var;
	
	public Variable(int var) {
		this.var = var;
	}

	public int getVar() {
		return var;
	}
	
	public boolean equals (Object o) {
		if (o instanceof Variable) {
			return ((Variable) o).var == this.var;
		}
		return false;
	}
	
	public String toString() {
		return "#" + this.var;
	}

	public int hashCode() {
		return var;
	}
}
