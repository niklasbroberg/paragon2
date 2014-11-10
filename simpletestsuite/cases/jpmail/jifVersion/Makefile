all: check-home
	unzip jif-2.0.1.zip
	patch jif-2.0.1/build.xml < patches/jifbuild_patch
	cd jif-2.0.1 ; ant configure
	cd jif-2.0.1 ; ant jif-runtime
	cd jif-2.0.1 ; ant
	tar xzf jpmail-full-latest.tgz
	patch jpmail-full-*/build.xml < patches/jpmailbuild_patch
	patch jpmail-full-*/jifpol/src/policy/KeyPrincipal.jif < patches/KeyPrincipal_patch
	patch jpmail-full-*/jpmail/src/pop3/JPMailMessage.jif < patches/JPMailMessage_patch
	cd jpmail-full-* ; ant jif-update
	cd jpmail-full-* ; ant jpmail
	cd jpmail-full-* ; ant demo

download:
	wget http://siis.cse.psu.edu/jpmail/downloads/jpmail-full-latest.tgz
	wget http://www.cs.cornell.edu/jif/releases/jif-2.0.1.zip

clean:
	rm -rf jif-2.0.1
	rm -rf jpmail-full-0.3.1

check-home:
ifndef JAVA_HOME
  $(error Set environment variable JAVA_HOME to the root of your JDK)
endif

