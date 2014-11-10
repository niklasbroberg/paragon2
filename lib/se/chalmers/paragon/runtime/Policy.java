package se.chalmers.paragon.runtime;

import java.util.LinkedList;

public class Policy {

	private final Clause[] clauses;

	public Policy(Clause... clauses) {
		this.clauses = clauses;
	}

	public Clause[] getClauses() {
		return clauses;
	}

	public Policy meet(Policy p) {
		Clause[] res = new Clause[clauses.length + p.getClauses().length];
		System.arraycopy(this.clauses, 0, res, 0, this.clauses.length);
		System.arraycopy(p.getClauses(), 0, res, this.clauses.length,
				p.getClauses().length);
		return new Policy(res);
	}

	public Policy join(Policy p) {
		LinkedList<Clause> res = new LinkedList<Clause>();
		for (Clause c : clauses)
			for (Clause d : p.getClauses()) {
				Clause joined = c.join(d);
				if (joined != null)
					res.add(joined);
			}
		return new Policy(res.toArray(new Clause[0]));
	}

	public String toString() {
		String res = "{ ";
		for (int i = 0; i < clauses.length - 1; i++) {
			res += clauses[i].toString();
			res += ";";
		}
		if (clauses.length > 0)
			res += clauses[clauses.length - 1].toString();
		res += " }";
		return res;

	}

}
