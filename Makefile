all:
	#cd mlton-parmem && $(MAKE)
	cd priml && $(MAKE)
	echo "#!/bin/sh" > primlc
#	echo "export MLTON_PARMEM=$(shell pwd)/mlton-parmem/build/bin/mlton-parmem" >> primlc
	echo "export OCAMLC=ocamlc" >> primlc
#	echo "export PRIML_LIB=$(shell pwd)/stdlib" >> primlc
	echo "$(shell pwd)/priml/c72s \$$@" >> primlc
	chmod +x primlc

clean:
	cd mlton-parmem && $(MAKE) clean
	cd priml && $(MAKE) clean
	rm -f primlc
