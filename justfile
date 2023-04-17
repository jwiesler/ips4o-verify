KEY_JAR := "tools/key-2.11.0-exe.jar"
KEY_OVERFLOW_JAR := "tools/key-2.11.0-o-exe.jar"
CI_TOOL := "tools/citool-1.4.0-mini.jar"

checkCommand := 'java -Dkey.contractOrder="contract-order.txt" -cp "' + KEY_JAR + ';' + CI_TOOL + '" de.uka.ilkd.key.CheckerKt --no-auto-mode --proof-path proofs/ project.key'
checkOverflowCommand := 'java -Dkey.contractOrder="contract-order.txt" -cp "' + KEY_OVERFLOW_JAR + ';' + CI_TOOL + '" de.uka.ilkd.key.CheckerKt -v --no-auto-mode --proof-path proofs-overflow/ project.key'
checkTreeCommand := 'java -Dkey.contractOrder="contract-order.txt" -cp "' + KEY_OVERFLOW_JAR + ';' + CI_TOOL + '" de.uka.ilkd.key.CheckerKt -v --no-auto-mode --proof-path proofs/ project.key'

default:
	@just --list

run:
	java -Dkey.contractOrder="contract-order.txt" -jar {{KEY_JAR}}

compile:
	find -name "*.java" > sources.txt
	javac @sources.txt

check:
	{{checkCommand}} --forbid-contracts-file "contracts/ignore.txt" -s statistics.json

check-methods:
	{{checkCommand}} --forbid-contracts-file "contracts/ignore.txt" --forbid-contracts-file "contracts/constructors.txt" -s statistics-methods.json

check-constructors:
	{{checkCommand}} --contracts-file contracts/constructors.txt -s statistics-constructors.json

check-class target:
	{{checkCommand}} --forbid-contracts-file "contracts/ignore.txt" --contracts-filter "^de\.wiesler\.{{target}}\[.*" -s statistics.json

check-overflow-class target:
	{{checkOverflowCommand}} --forbid-contracts-file "contracts/ignore.txt" --contracts-filter "^de\.wiesler\.{{target}}\[.*"

check-tree:
    {{checkTreeCommand}} --forbid-contracts-file "contracts/ignore.txt" --contracts-filter "^de\.wiesler\.Tree\[.*"

check-overflow-methods:
	{{checkOverflowCommand}} --contracts-file "contracts/overflow.txt" --forbid-contracts-file "contracts/constructors.txt" -s statistics-overflow-methods.json

check-overflow-constructors:
	{{checkOverflowCommand}} --contracts-file "contracts/constructors.txt" -s statistics-overflow-constructors.json
