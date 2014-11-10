all: pipath
	parac jif/DLM.para 
	parac jif/lang/Closure.para
	parac crypto/MD5Closure.para
	parac smtp/DigestMD5.para

clean:
	rm -rf crypto/*.pi
	rm -rf crypto/*.java
	rm -rf jif/*.pi
	rm -rf jif/*.java
	rm -rf jif/lang/*.pi
	rm -rf jif/lang/*.java
	rm -rf smtp/*.pi
	rm -rf smtp/*.java
	rm -rf policyp/*.pi
	rm -rf policyp/*.java

pipath:
ifndef PIPATH
  $(error Set environment variable PIPATH to [pathOfPiFiles:.])
endif

