package se.chalmers.parajpmail.runtime;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.NoSuchFileException;
import java.nio.file.Paths;
import java.nio.file.attribute.PosixFilePermission;
import java.nio.file.attribute.PosixFilePermissions;
import java.security.KeyStore;
import java.util.HashMap;
import java.util.Set;

import se.chalmers.paragon.Actor;
import se.chalmers.paragon.ConcreteActor;

public class JPMailRuntime {

	private static HashMap<JPMailUserID, ConcreteActor> jpmailToParagon = new HashMap<JPMailUserID, ConcreteActor>();

	/**
	 * Looks up, or creates if not exists, the actor for this jpmail user. It
	 * ensures that you always get back the same actor for the same jpmail id
	 * during one paragon run.
	 * 
	 * @param id
	 *            The JPMail user ID
	 * @return The paragon actor representing this id.
	 * @pi public static final actor getActorOf(JPMailUserID id);
	 */
	public static final ConcreteActor getActorOf(JPMailUserID id) {
		ConcreteActor res = jpmailToParagon.get(id);
		if (res == null) {
			res = Actor.freshActor(id.getId());
			jpmailToParagon.put(id, res);
			// Debug.println("Created new JP actor " + id.getId());
		}
		return res;
	}

	/**
	 * Look up user, look up public key in keystore
	 * 
	 * @param actor
	 *            actor for which to relate the public key
	 * @param keystore
	 *            store in which to look for the key
	 * @throws SecurityException
	 *             If key was not signed by the trusted CA.
	 * @pi public static <actor jpmailUser> void loadPublicKey(Keystore
	 *     keystore);
	 */
	public static void relatePublicKey(ConcreteActor actor, KeyStore keystore)
			throws SecurityException {
		// TODO
		System.err.println("TODO:: Call to unimplemented function "
				+ "JPMailRuntime.relatePublicKey");
	}

	/**
	 * Get the unix-style permissions on a file -- if this wasn't clear yet,
	 * this is not cross-platform!
	 * 
	 * @param file
	 *            File from which to get the permissions.
	 * @return The unix permissions of this file (rw-r--r-- etc) represented as
	 *         string.
	 * @throws NoSuchFileException
	 *             If the file is not found 
	 * @pi public static ?policyof(file) String getFilePermissions(String file);
	 */
	public static String getFilePermissions(String file)
			throws NoSuchFileException {
		Set<PosixFilePermission> filePerm = null;
		try {
			filePerm = Files.getPosixFilePermissions(Paths.get(file));
		} catch (IOException e) {
			e.printStackTrace();
		}
		return PosixFilePermissions.toString(filePerm);
	}

}