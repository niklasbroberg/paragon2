package se.chalmers.paragon.bidsystem;

import java.io.BufferedReader;
import java.io.InputStreamReader;

import se.chalmers.paragon.Actor;

public class Channel {

	private static BufferedReader in = new BufferedReader(
			new InputStreamReader(System.in));

	private Actor id;

	public Channel(Actor id) {
		this.id = id;
	}

	public int get() throws NoBidExc {
		System.out.print("Bid for actor " + id.toString() + " ");
		while (true)
			try {
				return (new Integer(in.readLine()).intValue());
			} catch (Exception e) {
				throw new NoBidExc();
			}
	}

	public void put(int winBid) {
		System.out.println("Sending to bidder " + id.toString()
				+ " that the winning bid is " + winBid);
	}

	public void put(String data) {
		System.out.println("Sending to bidder " + id.toString());
		System.out.println(data);
	}

}
