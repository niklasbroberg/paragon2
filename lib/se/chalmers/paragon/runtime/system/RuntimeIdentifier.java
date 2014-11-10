package se.chalmers.paragon.runtime.system;

public class RuntimeIdentifier {

	private String username;

	public RuntimeIdentifier(String username) {
		this.username = username;
	}

	public String getUsername() {
		return this.username;
	}

	public String toString() {
		return this.username;
	}

	public boolean equals(Object o) {
		if (!(o instanceof RuntimeIdentifier))
			return false;
		return ((RuntimeIdentifier) o).username == this.username;
	}
	
	public int hashCode() {
		return this.username.hashCode();
	}

}
