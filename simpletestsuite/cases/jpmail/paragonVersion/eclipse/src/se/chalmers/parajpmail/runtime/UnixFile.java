package se.chalmers.parajpmail.runtime;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.attribute.UserPrincipal;
import java.util.Scanner;

import se.chalmers.paragon.Actor;
import se.chalmers.paragon.ConcreteActor;
import se.chalmers.paragon.Lock;

public class UnixFile {

	private String fileContent;

	/**
	 * Represents this file.
	 * 
	 * @pi public final actor fd;
	 */
	public final ConcreteActor fd = Actor.freshActor("UnixFile");

	/**
	 * @pi public static final lock FileOwner(fileDescriptor, fileOwner);
	 */
	public static final Lock FileOwner = Lock.newLock(
			"se.chalmers.parajpmail.runtime.UnixFile.FileOwner", 2);

	/**
	 * @pi public static final lock ShareContent(fileDescriptor, fileOwner,
	 *     otherActor);
	 */
	public static final Lock ShareContent = Lock.newLock(
			"se.chalmers.parajpmail.runtime.UnixFile.ShareContent", 3);

	/**
	 * Reads file into content string and opens locks according to file owner
	 * 
	 * @param file
	 *            File to be read
	 * @throws IOException
	 *             If file does not exist / owner cannot be determined
	 * @pi public UnixFile(?policyof(this) String file) throws !policyof(file)
	 *     IOException { }
	 */
	public UnixFile(String file) throws IOException {

		// Read in file
		Scanner scan = new Scanner(new File(file));
		scan.useDelimiter("\\Z");
		this.fileContent = scan.next();
		scan.close();

		// Get file owner
		Path path = Paths.get(file);
		UserPrincipal owner = Files.getOwner(path);
		String username = owner.getName();
		ConcreteActor actOwner = SimpleUnixRuntime.getActorOf(new UnixUserID(
				username));

		// Open lock UnixFile.ReadPermission(thisfile, actOwner)
		FileOwner.open(this.fd, actOwner);
	}

	/**
	 * Can be read by anyone allowed to read the file, and anyone who the owner
	 * of the file wants to share it to
	 * 
	 * @return The content of this file
	 * @pi public ?{ 'x : FileOwner(fd, 'x) ; 'y : FileOwner(fd, 'x),
	 *     ShareContent(fd, 'x, 'y) } String getContent();
	 */
	public String getContent() {
		return this.fileContent;
	}

}
