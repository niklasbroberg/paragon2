package se.chalmers.paragon.runtime;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

public class LockProperty {

	private final Class<?>[] sets;
	private final Atom head;
	private final Atom[] body;

	public LockProperty(Class<?>[] sets, Atom head, Atom... body) {
		this.sets = sets;
		this.head = head;
		this.body = body;
	}

	public Class<?>[] getSets() {
		return sets;
	}

	public Atom getHead() {
		return head;
	}

	public Atom[] getBody() {
		return body;
	}

	/**
	 * Expands the provided database by applying this property once
	 * 
	 * @param database
	 */
	public void expand(HashSet<Lock> database) {

		// Collect all grounding substitutions
		LinkedList<HashMap<Variable, Actor>> substitutions = new LinkedList<HashMap<Variable, Actor>>();
		substitutions.add(new HashMap<Variable, Actor>());
		for (Atom b : body) {

			// Collect correct substitutions for this atom
			LinkedList<HashMap<Variable, Actor>> nsubs = new LinkedList<HashMap<Variable, Actor>>();
			for (Lock l : database) {

				HashMap<Variable, Actor> s = b.substituteTo(sets, l);
				if (s != null)
					nsubs.add(s);

			}

			// Expand the substitutions so far, but only if the new ones do not
			// conflict.
			LinkedList<HashMap<Variable, Actor>> nsubstitutions = new LinkedList<HashMap<Variable, Actor>>();
			for (HashMap<Variable, Actor> s : nsubs) {
				nsubstitutions.addAll(expandCorrect(s, substitutions));
			}

			// Resulting set are the correct possible substitutions
			substitutions = nsubstitutions;

			// Short-circuit
			if (substitutions.size() == 0)
				return;
		}

		// Apply substitutions to get new facts:
		for (HashMap<Variable, Actor> s : substitutions) {
			database.add(head.applyGroundSubstitution(s));
		}
	}

	/**
	 * 
	 * @param s
	 *            substitution to extend
	 * @param nsubs
	 *            Substitutions to extend it with
	 * @return cloned versions of s with each nsub added, if that nsub agrees on
	 *         variable substitutions
	 */
	private LinkedList<HashMap<Variable, Actor>> expandCorrect(
			HashMap<Variable, Actor> s,
			LinkedList<HashMap<Variable, Actor>> nsubs) {

		LinkedList<HashMap<Variable, Actor>> res = new LinkedList<HashMap<Variable, Actor>>();
		for (HashMap<Variable, Actor> ns : nsubs) {
			boolean ok = true;
			for (Variable v : ns.keySet())
				if (s.containsKey(v))
					if (!s.get(v).equals(ns.get(v))) // Do no agree on variable
														// mapping
						ok = false;
			if (ok) {
				@SuppressWarnings("unchecked")
				HashMap<Variable, Actor> clone = (HashMap<Variable, Actor>) s
						.clone();
				clone.putAll(ns);
				res.add(clone);
			}
		}
		return res;
	}
}
