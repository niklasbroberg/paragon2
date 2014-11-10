all: build

build: *.para java/lang/* extra/*
	cp extra/Channel.* .
	parac BidLocks.para
	parac NoBidExc.para
	parac Bidder.para
	parac BidSystem.para

clean:
	rm -f *.pi *.java *~

java: *.java
	 javac -Xlint:-options -cp .:paragonRT.jar BidSystem.java
