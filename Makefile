nesrev:
	javac NESrev.java -Xlint:unchecked

test:
	javac NESrev.java NESrevTest.java -Xlint:unchecked
	java NESrevTest
