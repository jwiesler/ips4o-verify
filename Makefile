KEY_JAR=tools/key-2.11.0-exe.jar
KEY_OVERFLOW_JAR=tools/key-2.11.0-o-exe.jar
CI_TOOL=tools/citool-1.4.0-mini.jar

checkCommand=java -Dlogback.configurationFile=./gradle/disablelogging.xml -Dkey.contractOrder="contract-order.txt" -cp "$(KEY_JAR):$(CI_TOOL)" de.uka.ilkd.key.CheckerKt --no-auto-mode --proof-path src/main/key

checkOverflowCommand=java -Dlogback.configurationFile=./gradle/disablelogging.xml -Dkey.contractOrder="contract-order.txt" -cp "$(KEY_OVERFLOW_JAR):$(CI_TOOL)" de.uka.ilkd.key.CheckerKt -v --no-auto-mode --proof-path src/main/key-overflow

default:
	@echo Available targets:
	@sed -n 's/^\([a-zA-Z_-]\+\):.*/   \1/p' Makefile

proofSettings:
	mkdir -p $${HOME}/.key
	cp proofIndependentSettings.props $${HOME}/.key

run:
	@echo Consider loading one of the following files:
	@find -iname "project*.key"
	java -Dkey.contractOrder="contract-order.txt" -jar $(KEY_JAR)

compile:
	find -name "*.java" > sources.txt
	javac @sources.txt

constr-src:
	rm -rf src/main/java-constr
	cp -r src/main/java src/main/java-constr
	sed -i 's/no_state int bucketStart/int bucketStart/' src/main/java-constr/de/wiesler/BucketPointers.java
	sed -i 's/no_state int bucketSize/int bucketSize/' src/main/java-constr/de/wiesler/BucketPointers.java

constr-overflow-src:
	rm -rf src/main/java-constr-overflow
	cp -r src/main/java src/main/java-constr-overflow
	sed -i 's/no_state int bucketStart/int bucketStart/' src/main/java-constr-overflow/de/wiesler/BucketPointers.java
	sed -i 's/no_state int bucketSize/int bucketSize/' src/main/java-constr-overflow/de/wiesler/BucketPointers.java

check: check-methods check-constructors check-overflow-methods check-overflow-constructors

check-methods: proofSettings
	$(checkCommand) --forbid-contracts-file "contracts/ignore.txt" --forbid-contracts-file "contracts/constructors.txt" -s statistics-methods.json src/main/key/project.key

check-constructors: constr-src
	$(checkCommand) --contracts-file contracts/constructors.txt -s statistics-constructors.json  src/main/key/project-constr.key

check-overflow-methods:
	$(checkOverflowCommand) --contracts-file "contracts/overflow.txt" --forbid-contracts-file "contracts/constructors.txt" -s statistics-overflow-methods.json  src/main/key-overflow/project.key

check-overflow-constructors: constr-overflow-src
	$(checkOverflowCommand) --contracts-file "contracts/constructors.txt" -s statistics-overflow-constructors.json  src/main/key-overflow/project-constr.key
