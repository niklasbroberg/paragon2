package se.chalmers.paragon.runtime;

import java.util.HashSet;

public class LockState {

	private static HashSet<Lock> lockState = new HashSet<Lock>();

	public static void open(Lock lock) {
		lockState.add(lock);
	}

	public static void close(Lock lock) {
		lockState.remove(lock);
	}

	/**
	 * 
	 * @param lock
	 *            Requested lock is open
	 * @return True if this lock is open in the explicit lock state, or can
	 *         derived to be open using the lock properties.
	 */
	public static boolean isOpen(Lock lock) {
		if (lockState.contains(lock))
			return true;
		// Derive all locks that are open and check if requested lock is in
		// there -- efficiency could be improved greatly by using something
		// like magic sets. Unfortunately we cannot just translate to some
		// Datalog module.
		HashSet<Lock> database = lockState;
		int nfacts;
		do {
			nfacts = database.size();
			for (LockProperty p : GlobalPolicy.getProperties()) {
				p.expand(database);
			}
		} while (database.size() > nfacts); // while new facts are derived
		return database.contains(lock);
	}

}
