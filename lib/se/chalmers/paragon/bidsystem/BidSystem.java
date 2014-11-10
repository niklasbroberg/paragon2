package se.chalmers.paragon.bidsystem;

import se.chalmers.paragon.Actor;
import se.chalmers.paragon.Atom;
import se.chalmers.paragon.ConcreteActor;
import se.chalmers.paragon.Lock;
import se.chalmers.paragon.Policy;
import se.chalmers.paragon.annotations.ArgumentPolicy;
import se.chalmers.paragon.annotations.ExceptionPolicy;
import se.chalmers.paragon.annotations.ExpectsOpen;
import se.chalmers.paragon.annotations.OpensLock;
import se.chalmers.paragon.annotations.ReadPolicy;
import se.chalmers.paragon.annotations.WritePolicy;

public class BidSystem {

	final Lock AuctionClosed = Lock.newLock("AuctionClosed", 0);
	final Lock HasBid = Lock.newLock("HasBid", 1);
	final Lock Winner = Lock.newLock("Winner", 1);

	final Policy allBidders = Policy.newPolicy(
			"allBidders",
			Policy.newPClause(Actor.newActorVariable(0),
					Atom.newAtom(AuctionClosed),
					Atom.newAtom(HasBid, Actor.newActorVariable(0))));

	Bidder[] bidders;

	BidSystem(int nbidders) {
		generateBidders(nbidders);
		collectBids();
		Bidder winner = determineWinner();
		if (winner != null) {
			Winner.open(winner.id);
			reportResult(winner.bid);
			sendSpoils(winner);
		}
	}

	void sendSpoils(Bidder winner) {
		winner.chan.put("                               o==)_\\ \n"
				+ "                                 ',====_ \n"
				+ "      _-~_                         \\ \\  \\_____ \n"
				+ " \\ _-~_-~_),-._____..______         \\ \\  `\\  || \n"
				+ "  ~_-~_-~\\_|_______||______|         \\ \\   `\\|| \n"
				+ "  (_-~\\,-'_--~~~~___~~~\\    \\        |  |    `\\_ \n"
				+ "  ())=/ /~      (_~_)   | _ /        / /        `-_ \n"
				+ "     / (           __  / ==/        / /            \\ \n"
				+ "    (___\\_________===_/___/________/_/___==O=====O==O \n"
				+ "   _//|  ( () )/ |~`-----------------'  |  ( ()')  | \n"
				+ "  '-'  \\_ `--' _/                        \\_ `--' _/ \n"
				+ "         `----'        The Spoils          `----'");
	}

	void generateBidders(int nbidders) {
		bidders = new Bidder[nbidders];
		for (int id = 0; id < nbidders; id++)
			bidders[id] = new Bidder(id + 1);
	}

	@WritePolicy("bottom")
	void collectBids() {
		for (Bidder b : bidders) {
			try {
				b.getBid();
			} catch (NoBidExc e) {

			}
		}
	}

	@OpensLock(lock = "AuctionClosed")
	@ReadPolicy("allBidders")
	Bidder determineWinner() {
		Bidder winner = null;
		for (Bidder b : bidders) {
			if (HasBid.isOpen(b.id)) {
				if (winner == null || b.bid > winner.bid) {
					winner = b;
				}
			}
		}
		AuctionClosed.open();
		return winner;
	}

	@WritePolicy("bottom")
	@ArgumentPolicy(argument = "winBid", policy = "allBidders")
	@ExpectsOpen(Lock = "AuctionClosed")
	void reportResult(int winBid) {
		for (Bidder b : bidders) {
			if (HasBid.isOpen(b.id)) {
				b.chan.put(winBid);
			}
		}
	}

	class Bidder {
		final ConcreteActor id = Actor.freshActor("bidder");
		final Channel chan = new Channel(id);
		final Policy bidpol = Policy.newPolicy(
				"bidpol",
				Policy.newPClause(id),
				Policy.newPClause(Actor.newActorVariable(0),
						Atom.newAtom(AuctionClosed),
						Atom.newAtom(HasBid, Actor.newActorVariable(0)),
						Atom.newAtom(Winner, id)));
		@ReadPolicy("bidpol")
		int bid;

		Bidder(int bid) {
			this.bid = bid;
		}

		@OpensLock(lock = "HasBid", actors = { "id" })
		@WritePolicy("bidpol")
		@ExceptionPolicy(Exception = "NoBidExc", Write = "bidpol")
		void getBid() throws NoBidExc {
			bid = chan.get();
			HasBid.open(id);
		}
	}

	public static void main(String[] arg) {
		new BidSystem(3);
	}

}
