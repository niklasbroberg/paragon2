all: build

build: mp/*.para extra/* java/lang/* java/io/* java/math/* java/util/* java/security/*
	parac mp/MPException.para 
	parac mp/DataFieldAttribute.para
	parac mp/DABigInteger.para
	parac mp/BigIntPair.para
	parac mp/BigIntVector.para
	parac mp/CRT.para
	parac mp/Digest.para
	parac mp/PermutationMatrix.para
	parac mp/CardVector.para
	parac mp/DataField.para
	parac mp/DAVector.para
	parac mp/DNCLink.para
	parac mp/PHInteger.para
	parac mp/PHIntVector.para
	parac mp/PHEPermutationMatrix.para
	parac mp/EncryptedCardVector.para
	parac mp/PHCrypto.para
	parac mp/SerializeWriteHelper.para
	parac mp/SerializeReadHelper.para
	parac mp/DNCChain.para
	parac mp/TrustedDeclassifier.para
	parac mp/GameState.para
	parac mp/UpgradeAssist.para
	cp extra/Channel.* mp/
	parac mp/Player.para
	parac mp/Communicator.para
	parac mp/Main.para

clean:
	rm -f mp/*.pi mp/*.java mp/*~

java: mp/*.java
	javac mp/MPException.java 
	javac mp/DataFieldAttribute.java
	javac mp/DABigInteger.java
	javac mp/BigIntPair.java
	javac mp/BigIntVector.java
	javac mp/CRT.java
	javac mp/Digest.java
	javac mp/PermutationMatrix.java
	javac mp/CardVector.java
	javac mp/DataField.java
	javac mp/DAVector.java
	javac mp/DNCLink.java
	javac mp/PHInteger.java
	javac mp/PHIntVector.java
	javac mp/PHEPermutationMatrix.java
	javac mp/EncryptedCardVector.java
	javac mp/PHCrypto.java
	javac mp/SerializeWriteHelper.java
	javac mp/SerializeReadHelper.java
	javac mp/DNCChain.java
	javac mp/TrustedDeclassifier.java
	javac mp/GameState.java
	javac mp/UpgradeAssist.java
