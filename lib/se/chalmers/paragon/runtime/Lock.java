package se.chalmers.paragon.runtime;

import java.util.Arrays;

public class Lock {

	private final LockID lockID;

	private final Actor[] actors;

	public Lock(LockID lockID, Actor... actors) {
		this.lockID = lockID;
		if (actors.length != lockID.getArity().length)
			throw new ParagonException("Lock " + lockID.getLockName()
					+ " created with wrong arity");
		for (int i = 0; i < actors.length; i++) {
			if (!lockID.getArity()[i].isInstance(actors[i].getActor()))
				throw new ParagonException("Lock " + lockID.getLockName()
						+ " created with wrong argument on location " + i);
		}
		this.actors = actors;
	}

	public LockID getLockID() {
		return lockID;
	}

	public Actor[] getActors() {
		return actors;
	}

	public boolean equals(Object o) {
		if (o instanceof Lock) {
			Lock l = (Lock) o;
			return l.lockID == this.lockID
					&& Arrays.equals(l.actors, this.actors);
		} else {
			return false;
		}
	}

	public int hashCode() {
		// Force hash-set to use equals-method - dirty;
		// TODO: change to something dependend on fields
		return 0;
	}

}
