package se.chalmers.paragon.runtime.system;

import java.util.HashMap;

public class RuntimeActor {

	private static HashMap<RuntimeIdentifier, RuntimeActor> knownActors = new HashMap<RuntimeIdentifier, RuntimeActor>();

	private RuntimeIdentifier user;

	public static final RuntimeActor runtimeUser = getInvokingUser();

	private RuntimeActor(RuntimeIdentifier user) {
		this.user = user;
	}

	public static RuntimeActor lookUpOrCreate(RuntimeIdentifier user) {
		RuntimeActor res = knownActors.get(knownActors);
		if (res != null)
			return res;
		return new RuntimeActor(user);
	}

	private static RuntimeActor getInvokingUser() {
		String uname = System.getProperty("user.name");
		return RuntimeActor.lookUpOrCreate(new RuntimeIdentifier(uname));
	}

	public RuntimeIdentifier getUser() {
		return user;
	}

}
