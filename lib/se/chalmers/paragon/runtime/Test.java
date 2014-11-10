package se.chalmers.paragon.runtime;

public class Test {

	// Testing simple lock property
	public static void foo() {
		Object alice = new Object();
		String bob = "Je m'appelle Bob";

		LockID paid = new LockID("paid", Object.class);

		// { Paid(alice) : Paid(bob) }
		LockProperty bobPaysForAlice = new LockProperty(new Class<?>[] {},
				new Atom(paid, new Actor(alice)), new Atom[] { new Atom(paid,
						new Actor(bob)) });
		GlobalPolicy.addProperty(bobPaysForAlice);

		System.out.println("Paid(Alice) = "
				+ LockState.isOpen(new Lock(paid, new Actor(alice))) + "\t"
				+ "Paid(Bob) = "
				+ LockState.isOpen(new Lock(paid, new Actor(bob))));
		System.out.println("opening Paid(bob)");
		LockState.open(new Lock(paid, new Actor(bob)));
		System.out.println("Paid(Alice) = "
				+ LockState.isOpen(new Lock(paid, new Actor(alice))) + "\t"
				+ "Paid(Bob) = "
				+ LockState.isOpen(new Lock(paid, new Actor(bob))));

	}

	// Testing subtyping
	public static void foo2() {
		LockID a = new LockID("A", Object.class);
		LockID b = new LockID("B", Object.class);

		// { A ( String ) : B ( String ) }
		LockProperty bToA = new LockProperty(new Class<?>[] { String.class },
				new Atom(a, new Variable(0)), new Atom[] { new Atom(b,
						new Variable(0)) });
		GlobalPolicy.addProperty(bToA);

		Object alice = new Object();
		String bob = "Je m'appelle Bob";
		System.out.println("a(Alice) = "
				+ LockState.isOpen(new Lock(a, new Actor(alice))) + "\t"
				+ "a(Bob) = " + LockState.isOpen(new Lock(a, new Actor(bob))));

		System.out.println("b(Alice) = "
				+ LockState.isOpen(new Lock(b, new Actor(alice))) + "\t"
				+ "b(Bob) = " + LockState.isOpen(new Lock(b, new Actor(bob))));

		System.out.println("opening b(Alice), b(Bob)");
		LockState.open(new Lock(b, new Actor(alice)));
		LockState.open(new Lock(b, new Actor(bob)));

		System.out.println("a(Alice) = "
				+ LockState.isOpen(new Lock(a, new Actor(alice))) + "\t"
				+ "a(Bob) = " + LockState.isOpen(new Lock(a, new Actor(bob))));

		System.out.println("b(Alice) = "
				+ LockState.isOpen(new Lock(b, new Actor(alice))) + "\t\t"
				+ "b(Bob) = " + LockState.isOpen(new Lock(b, new Actor(bob))));

	}

	// Testing transitivity
	public static void foo3() {
		LockID a = new LockID("A", Object.class, Object.class);

		// { A ( x , y ) : A (x, z), A(z, y) }
		LockProperty trans = new LockProperty(new Class<?>[] { Object.class,
				Object.class, Object.class }, new Atom(a, new Variable(0),
				new Variable(1)), new Atom[] {
				new Atom(a, new Variable(0), new Variable(2)),
				new Atom(a, new Variable(2), new Variable(1)), });
		GlobalPolicy.addProperty(trans);

		Object alice = new Object();
		Object bob = new Object();
		Object charlie = new Object();

		System.out.println("a(Alice, Bob) = "
				+ LockState
						.isOpen(new Lock(a, new Actor(alice), new Actor(bob)))
				+ "\t"
				+ "a(Bob, Charlie) = "
				+ LockState.isOpen(new Lock(a, new Actor(bob), new Actor(
						charlie)))
				+ "\t"
				+ "a(Alice, Charlie) = "
				+ LockState.isOpen(new Lock(a, new Actor(alice), new Actor(
						charlie))));

		System.out.println("opening a(Alice, Bob), b(Bob, Charlie)");
		LockState.open(new Lock(a, new Actor(alice), new Actor(bob)));
		LockState.open(new Lock(a, new Actor(bob), new Actor(charlie)));

		System.out.println("a(Alice, Bob) = "
				+ LockState
						.isOpen(new Lock(a, new Actor(alice), new Actor(bob)))
				+ "\t"
				+ "a(Bob, Charlie) = "
				+ LockState.isOpen(new Lock(a, new Actor(bob), new Actor(
						charlie)))
				+ "\t"
				+ "a(Alice, Charlie) = "
				+ LockState.isOpen(new Lock(a, new Actor(alice), new Actor(
						charlie))));

	}

	// Test policy join operations
	public static void foo4() {
		Object alice = new Object();
		// { Object x : }
		Policy bottom = new Policy(new Clause(new Class<?>[] { Object.class },
				new Variable(0)));
		// { String x : }
		Policy strBottom = new Policy(new Clause(
				new Class<?>[] { String.class }, new Variable(0)));
		// { alice : }
		Policy toAlice = new Policy(new Clause(new Class<?>[] {}, new Actor(
				alice)));
		System.out.println("Bottom    : " + bottom.toString());
		System.out.println("strBottom : " + strBottom.toString());
		System.out.println("toAlice   : " + toAlice.toString());
		System.out.println("bottom * toAlice    : "
				+ bottom.join(toAlice).toString());
		System.out.println("toAlice * bottom    : "
				+ toAlice.join(bottom).toString());
		System.out.println("strBottom * toAlice : "
				+ strBottom.join(toAlice).toString());
		System.out.println("toAlice * strBottom : "
				+ toAlice.join(strBottom).toString());
		System.out.println("strBottom * bottom  : "
				+ strBottom.join(bottom).toString());
		System.out.println("bottom * strBottom  : "
				+ bottom.join(strBottom).toString());
	}

	// More complicated joins
	public static void foo5() {
		// p = Object x, String y . x : F(x,y)
		// q = Object x, Object y . x : F(x,y)
		LockID F = new LockID("F",
				new Class<?>[] { Object.class, Object.class });
		Policy p = new Policy(new Clause(new Class<?>[] { Object.class,
				String.class }, new Variable(0), new Atom[] { new Atom(F,
				new Variable(0), new Variable(1)) }));
		Policy q = new Policy(new Clause(new Class<?>[] { Object.class,
				Object.class }, new Variable(0), new Atom[] { new Atom(F,
				new Variable(0), new Variable(1)) }));
		System.out.println("p   : " + p.toString());
		System.out.println("q   : " + q.toString());
		System.out.println("p*q : " + p.join(q).toString());
		System.out.println("q*p : " + q.join(p).toString());
		System.out.println("p*p : " + p.join(p).toString());
		System.out.println("q*q : " + q.join(q).toString());

		System.out.println("------------------------------");
		
		// l = Object x, Object y, Object z . x : F(x,z), G(y)
		// m = Object x . alice : F(alice, x)
		LockID G = new LockID("G", new Class<?>[] { Object.class });
		Policy l = new Policy(new Clause(new Class<?>[]{Object.class, Object.class,
				Object.class }, new Variable(0), new Atom[]{
			new Atom(F, new Variable(0), new Variable(1)),
			new Atom(G, new Variable(2))
		}));
		String alice = new String("cooper");
		Policy m = new Policy(new Clause(new Class<?>[]{Object.class}, new Actor(alice),
				new Atom[]{new Atom(F, new Actor(alice), new Variable(0))}));

		System.out.println("l   : " + l.toString());
		System.out.println("m   : " + m.toString());
		System.out.println("l*m : " + l.join(m).toString());
		System.out.println("m*l : " + m.join(l).toString());
		System.out.println("l*l : " + l.join(l).toString());
		System.out.println("m*m : " + m.join(m).toString());
	}

	public static void main(String[] arg) {
		foo5();
	}

}
