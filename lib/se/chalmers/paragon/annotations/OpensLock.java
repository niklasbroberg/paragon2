package se.chalmers.paragon.annotations;

public @interface OpensLock {

	String lock();

	String[] actors() default { };

}
