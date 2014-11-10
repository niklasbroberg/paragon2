#!/bin/bash

echo "Assuming you have default stuff installed"
echo "(i.e. wget, jdk, ant, sed, etc)"

if [ -e jif-1.1.1.zip ]
then
  echo "Jif 1.1.1 detected"
else
  echo "Downloading Jif 1.1.1"
  wget http://www.cs.cornell.edu/jif/releases/jif-1.1.1.zip
fi

echo "Extracting Jif Mental Poker"
unzip -o jifpoker.zip > /dev/null

echo "Extracting Jif 1.1.1"
unzip -o jif-1.1.1.zip > /dev/null

path=`pwd`
export JIF=$path/jif-1.1.1

cd $JIF
ant configure

echo ":: PATCHES ::"
mkdir tmp

echo ""
echo "Patch 1: jif.types.ParamInstance"
cat src/jif/types/ParamInstance.java | \
    sed 's/extends\ Enum/extends\ polyglot.util.Enum/' \
    > tmp/ParamInstance.java
mv tmp/ParamInstance.java src/jif/types/ParamInstance.java

echo ""
echo "Patch 2: jif.types.Path"
cat src/jif/types/Path.java | \
    sed 's/extends\ Enum/extends\ polyglot.util.Enum/' \
    > tmp/Path.java
mv tmp/Path.java src/jif/types/Path.java

echo ""
echo "Patch 3: jif.visit.ArrayIndexChecker"
cat src/jif/visit/ArrayIndexChecker.java | \
    sed 's/Bound).compareTo(/Bound).compareTo((Integer)/' \
    > tmp/ArrayIndexChecker.java
mv tmp/ArrayIndexChecker.java src/jif/visit/ArrayIndexChecker.java

echo ""
echo "Patch 4: build.xml"
cat build.xml | \
    sed 's/<arg\ value=\"\-I\.\"\/>/<arg\ value=\"\-fPIC\"\/>\n\ \ \ \ \ \ <arg\ value=\"\-I\.\"\/>/' \
    > tmp/build.xml
mv tmp/build.xml build.xml

rm -rf tmp

echo ""
echo "Finished patching. Running ant."
ant
ant jif-runtime

echo ""
echo "Compiling Alice and Bob."
cd $JIF/tests
javac -d . -classpath $JIF/rt-classes jif/principal/Alice.java jif/principal/Bob.java

cd $path


cd jifpoker
mkdir bin
cd src

echo ""
echo "Patching Mental Poker"

mkdir tmp

cat binder.py | \
    sed 's/jif\ mp\/Main/jif\ \-cp\ \.\:\.\.\/\.\.\/jif\-1\.1\.1\/rt\-classes\:\.\.\/\.\.\/jif\-1\.1\.1\/lib\-classes \-Djava\.library\.path=\.\.\/\.\.\/jif\-1\.1\.1\/lib  mp\/Main/' | \
    sed 's/print\ \"[^\+^\:]/\#\ print\ \"/' \
    > tmp/binder.py
mv tmp/binder.py binder.py

rm -rf tmp

echo ""
echo "Compiling Mental Poker"
chmod +x compile.sh
./compile.sh mp/*.jif

echo ""
echo "Running Mental Poker (might take some time!)"
cd ../bin

export PATH=$PATH:$JIF/bin
chmod +x start.sh
chmod +x binder.py
./start.sh

cd $path

echo ""
echo "Done."
echo ""
echo "Don't forget to set the following env. variables each time (or in .bashrc):"
echo "export JIF=$JIF"
echo "export PATH=\$PATH:$JIF/bin"
