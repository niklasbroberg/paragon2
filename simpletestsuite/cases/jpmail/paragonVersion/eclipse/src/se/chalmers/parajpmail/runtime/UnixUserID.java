package se.chalmers.parajpmail.runtime;

public class UnixUserID {

	private final String id;

	public UnixUserID(String id) {
		if (id == null)
			throw new NullPointerException("id may not be null.");
		this.id = id;
	}

	public String getId() {
		return this.id;
	}

	public boolean equals(Object o) {
		if (!(o instanceof UnixUserID))
			return false;
		String _id = ((UnixUserID) o).id;
		return _id != null && _id.equals(this.id);
	}
	
	public int hashCode() {
		return id.hashCode();
	}

}
