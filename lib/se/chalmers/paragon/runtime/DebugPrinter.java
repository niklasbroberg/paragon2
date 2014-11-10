package se.chalmers.paragon.runtime;

public class DebugPrinter {
	public void println(String s) {
	  // TODO use stack trace to print class, method and line.
	  System.out.println("DEBUG: " + s);
	}
}
