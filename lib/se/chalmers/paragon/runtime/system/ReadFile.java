package se.chalmers.paragon.runtime.system;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.nio.file.attribute.UserPrincipal;
import java.util.Scanner;

import se.chalmers.paragon.runtime.Actor;
import se.chalmers.paragon.runtime.Atom;
import se.chalmers.paragon.runtime.Clause;
import se.chalmers.paragon.runtime.Policy;

public class ReadFile {

	public final Policy filePolicy;

	public final Scanner scan;

	private ReadFile(String filename) throws IOException {
		UserPrincipal up = Files.getOwner(Paths.get(filename));
		String owner = up.getName();
		RuntimeActor ownerActor = RuntimeActor
				.lookUpOrCreate(new RuntimeIdentifier(owner));
		filePolicy = new Policy(new Clause(new Class<?>[] {}, new Actor(
				ownerActor), new Atom[] {}));
		scan = new Scanner(filename);
	}

	public String getContent() {
		scan.useDelimiter("\\Z");
		return scan.next();
	}
}