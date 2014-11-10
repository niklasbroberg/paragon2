package se.chalmers.paragon.runtime;

import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;

public class Clause {

	private final Class<?>[] sets;
	private final Argument head;
	private final Atom[] body;

	public Clause(Class<?>[] sets, Argument head, Atom... body) {
		this.sets = sets;
		this.head = head;
		this.body = body;
	}

	public Class<?>[] getSets() {
		return sets;
	}

	public Argument getHead() {
		return head;
	}

	public Atom[] getBody() {
		return body;
	}

	public Clause join(Clause d) {

		// substitutions for the body
		HashMap<Variable, Argument> subC = new HashMap<Variable, Argument>();
		HashMap<Variable, Argument> subD = new HashMap<Variable, Argument>();

		// New set / body of resulting clause
		LinkedList<Class<?>> newSet = new LinkedList<Class<?>>();
		LinkedList<Atom> newBody = new LinkedList<Atom>();

		// Try to join the head:
		Argument newHead = null;
		Class<?> headVar = null;
		if (head instanceof Variable) {
			int vC = ((Variable) head).getVar();
			if (d.getHead() instanceof Variable) {
				int vD = ((Variable) d.getHead()).getVar();
				if (sets[vC].isAssignableFrom(d.getSets()[vD]))
					headVar = d.getSets()[vD];
				else if (d.getSets()[vD].isAssignableFrom(sets[vC]))
					headVar = sets[vC];
				else
					return null; // failed to join
			} else { // Other is concrete
				newHead = d.getHead();
				if (!sets[vC].isInstance(newHead))
					return null;
				subC.put((Variable) head, d.getHead());
			}
		} else {
			if (d.getHead() instanceof Variable) {
				int vD = ((Variable) d.getHead()).getVar();
				newHead = head;
				if (!d.getSets()[vD].isInstance(newHead))
					return null;
				subD.put((Variable) d.getHead(), head);
			} else {
				if (d.getHead().equals(this.head))
					newHead = head;
				else
					return null; // Failed to join
			}
		}
		if (headVar != null) {
			newHead = new Variable(0);
		}

		// ///
		// Body of this clause:
		// ///

		newSet.addAll(Arrays.asList(this.sets));
		if (headVar != null) {
			newSet.set(((Variable) head).getVar(), headVar);
		} else if (head instanceof Variable) {
			int vi = ((Variable) head).getVar();
			newSet.remove(vi);
			for (int i = vi; i < newSet.size(); i++)
				subC.put(new Variable(i + 1), new Variable(i));
		}

		// In this-part, only substitute possible head variable to concrete:
		for (Atom a : this.body)
			newBody.add(a.applySubstitution(subC));

		// ///
		// Body of other clause:
		// ///

		LinkedList<Class<?>> others = new LinkedList<Class<?>>(Arrays.asList(d
				.getSets()));
		if (d.getHead() instanceof Variable) {
			Variable vd = (Variable) d.getHead();
			int j = 0;
			for (int i = 0; i < others.size(); i++) {
				if (vd.getVar() == i)
					continue;
				subD.put(new Variable(i), new Variable(j + newSet.size()));
				j++;
			}
			others.remove(vd.getVar());
			subD.put(vd, head);
		} else {
			for (int i = 0; i < others.size(); i++) {
				subD.put(new Variable(i), new Variable(i + newSet.size()));
			}
		}
		newSet.addAll(others);

		for (Atom a : d.getBody())
			newBody.add(a.applySubstitution(subD));

		return new Clause(newSet.toArray(new Class<?>[0]), newHead,
				newBody.toArray(new Atom[0]));

	}

	public String toString() {
		String res = "[";
		for (int i = 0; i < sets.length - 1; i++) {
			res += sets[i].getSimpleName();
			res += ",";
		}
		if (sets.length > 0)
			res += sets[sets.length - 1].getSimpleName();
		res += "] ";
		res += head.toString();
		res += " : ";
		for (int i = 0; i < body.length - 1; i++) {
			res += body[i].toString();
			res += ",";
		}
		if (body.length > 0)
			res += body[body.length - 1].toString();

		return res;
	}

}
