package se.chalmers.paragon.runtime;

public class LockID {

	private final String lockName;
	private final Class<?>[] arity;

	public LockID(String lockName, Class<?> ...  arity) {
		this.lockName = lockName;
		this.arity = arity;
	}

	public String getLockName() {
		return lockName;
	}

	public Class<?>[] getArity() {
		return arity;
	}

}
