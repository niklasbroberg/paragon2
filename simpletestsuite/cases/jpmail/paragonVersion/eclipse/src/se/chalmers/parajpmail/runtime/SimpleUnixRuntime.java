package se.chalmers.parajpmail.runtime;

import java.io.InputStream;
import java.io.PrintStream;
import java.nio.charset.Charset;
import java.util.HashMap;

import se.chalmers.paragon.Actor;
import se.chalmers.paragon.ConcreteActor;

/**
 * Native Java file for handling the mapping between unix users and paragon
 * actors. In addition it provides one very simple function for reading the
 * content of a file.
 * 
 * @author Bart van Delft
 * 
 */
public class SimpleUnixRuntime {

	// Poor man's bidirectional hashmap:
	private static HashMap<UnixUserID, ConcreteActor> unixToParagon = new HashMap<UnixUserID, ConcreteActor>();
	private static HashMap<ConcreteActor, UnixUserID> paragonToUnix = new HashMap<ConcreteActor, UnixUserID>();

	/**
	 * Stores the actor representing the unix user running the application.
	 * 
	 * @pi public static final actor currentUser;
	 */
	public static final ConcreteActor currentUser = getActorOf(new UnixUserID(
			System.getProperty("user.name")));

	/**
	 * Looks up, or creates if not exists, the paragon actor for this unix user.
	 * It ensures that you always get the same actor back for the same unix id
	 * within the same paragon run.
	 * 
	 * @param id
	 *            The unix user id for which you want to have the actor
	 * @return The previously created actor for this id, or a fresh one if it
	 *         didn't exist.
	 * @pi public static final actor getActorOf(UnixUserID id);
	 */
	public static final ConcreteActor getActorOf(UnixUserID id) {
		ConcreteActor res = unixToParagon.get(id);
		if (res == null) {
			res = Actor.freshActor(id.getId());
			unixToParagon.put(id, res);
			paragonToUnix.put(res, id);
			// Debug.println("Created new Unix actor " + id.getId());
		}
		return res;
	}

	/**
	 * @pi public static final ?{currentUser:} PrintStream<{currentUser:}> out;
	 */
	public static final PrintStream out = System.out;

	/**
	 * @pi public static final ?{'x:} InputStream<{'x:}> in;
	 */
	public static final InputStream in = System.in;

	public static void exit(int code) {
		System.exit(code);
	}

	public static final Charset UTF8 = initCharset();

	private static Charset initCharset() {
		try {
			return Charset.forName("UTF8");
		} catch (Exception e) {
		}
		System.out.println("UTF8 charset not found, exiting.");
		System.exit(-1);
		return null;
	}

}