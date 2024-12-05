build:
	./updatebackend.sh
	echo "rebuilding dafny extensions to dafny compiler"
	cd dafny/Source/DafnyCore && ./DafnyGeneratedFromDafny.sh --no-verify
	echo "rebuilding dafny compiler"
	cd dafny && make exe

backend: 
	./copybackendstodafny.sh
	cd dafny/Source/DafnyCore && ./DafnyGeneratedFromDafny.sh --no-verify
	echo "rebuilding dafny compiler"
	cd dafny && make exe


test:
	./dafny/Scripts/dafny translate dpt --no-verify:true consts.dfy

dns:
	./dafny/Scripts/dafny translate dpt --no-verify:true --allow-warnings DNSprotect5.dfy




.PHONY: build test