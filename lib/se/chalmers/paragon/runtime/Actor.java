package se.chalmers.paragon.runtime;

public class Actor extends Argument {

	private final Object actor;

	public Actor(Object actor) {
		this.actor = actor;
	}

	public Object getActor() {
		return actor;
	}

	public boolean equals(Object o) {

		if (o instanceof Actor) {
			// Pointer equality!!
			return ((Actor) o).actor == this.actor;
		}
		return false;
	}
	
	public String toString() {
		return "A" + actor.hashCode();
	}

}
