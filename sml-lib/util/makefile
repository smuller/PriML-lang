default : test.exe

MLTON=/c/mlton/bin/mlton.bat

test.exe : *.cm *.sml
	$(MLTON) -output $@ -const 'Exn.keepHistory true' test.cm
