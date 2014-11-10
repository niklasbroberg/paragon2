package se.chalmers.paragon.runtime;

import java.util.Arrays;
import java.util.HashMap;

public class Atom {

	private final LockID lockID;

	private final Argument[] arguments;

	public Atom(LockID lockID, Argument... arguments) {
		this.lockID = lockID;
		this.arguments = arguments;
	}

	public LockID getLockID() {
		return lockID;
	}

	public Argument[] getArguments() {
		return arguments;
	}

	public boolean equals(Object o) {
		if (o instanceof Atom) {
			Atom a = (Atom) o;
			return a.lockID == this.lockID
					&& Arrays.equals(a.arguments, this.arguments);
		} else {
			return false;
		}
	}

	public HashMap<Variable, Actor> substituteTo(Class<?>[] sets, Lock l) {
		HashMap<Variable, Actor> res = new HashMap<Variable, Actor>();
		for (int i = 0; i < arguments.length; i++) {
			if (arguments[i] instanceof Variable) {
				if (res.containsKey(arguments[i])) {
					Actor a = res.get(arguments[i]);
					if (!a.equals(l.getActors()[i]))
						return null;
				} else {
					Actor a = l.getActors()[i];
					Variable v = (Variable) arguments[i];
					// type safety
					if (sets[v.getVar()].isInstance(a.getActor()))
						res.put(v, a);
					else
						return null;
				}
			} else {
				Actor a = (Actor) arguments[i];
				if (!a.equals(l.getActors()[i]))
					return null;
			}
		}
		return res;
	}

	public Lock applyGroundSubstitution(HashMap<Variable, Actor> s) {
		Actor[] acts = new Actor[arguments.length];
		for (int i = 0; i < arguments.length; i++) {
			if (arguments[i] instanceof Variable) {
				// clause safety guarantees types are correct
				acts[i] = s.get(arguments[i]);
			} else {
				acts[i] = (Actor) arguments[i];
			}
		}
		return new Lock(this.lockID, acts);
	}

	public Atom applySubstitution(HashMap<Variable, Argument> s) {
		Argument[] args = new Argument[arguments.length];
		for (int i = 0; i < arguments.length; i++) {
			if (arguments[i] instanceof Variable && s.get(arguments[i]) != null) {
				args[i] = s.get(arguments[i]);
			} else {
				args[i] = arguments[i];
			}
		}
		return new Atom(this.lockID, args);
	}

	public boolean isGround() {
		for (Argument a : arguments)
			if (a instanceof Variable)
				return false;
		return true;
	}

	public String toString() {
		String res = lockID.getLockName();
		res += "(";
		for (int i = 0; i < arguments.length - 1; i++) {
			res += arguments[i].toString();
			res += ",";
		}
		if (arguments.length > 0)
			res += arguments[arguments.length - 1].toString();
		res += ")";
		return res;
	}

}
