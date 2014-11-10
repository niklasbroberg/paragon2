package se.chalmers.paragon.runtime;

import java.util.LinkedList;

public class GlobalPolicy {

	private static final LinkedList<LockProperty> properties = new LinkedList<LockProperty>();

	public static void addProperty(LockProperty property) {
		properties.add(property);
	}

	public static LinkedList<LockProperty> getProperties() {
		return properties;
	}

}
