package se.chalmers.parajpmail.runtime;

import java.sql.Timestamp;

public class Debug {
	
	public static final boolean debug = true;

	public static void println(String msg) {
		if (!debug) return;

		java.util.Date date = new java.util.Date();
		String ts = (new Timestamp(date.getTime())).toString();
		String method = getMethod();
		String clazz = getClazz();
		int line = getLine();
		System.out.println(ts + ": " + clazz + "." + method + "(" + line + "): " + msg);
	}
	
	private static int getLine() {
		try {
			throw new Exception();
		} catch (Exception e) {
			return e.getStackTrace()[2].getLineNumber();
		}
	}

	public static void printstack(Exception e) {
		if (!debug) return;

		java.util.Date date = new java.util.Date();
		String ts = (new Timestamp(date.getTime())).toString();
		String method = getMethod();
		String clazz = getClazz();
		System.out.println(ts + ": " + clazz + "." + method + ": ");
		e.printStackTrace();
	}

	private static String getClazz() {
		try {
			throw new Exception();
		} catch (Exception e) {
			return e.getStackTrace()[2].getClassName();
		}
	}

	private static String getMethod() {
		try {
			throw new Exception();
		} catch (Exception e) {
			return e.getStackTrace()[2].getMethodName();
		}
	}

}