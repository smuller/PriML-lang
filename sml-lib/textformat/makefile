
default : tftest.exe test

MLTON=/c/mlton/bin/mlton.bat

tfcompiler.exe : tfcompiler.cm tfcompiler.sml description-parser.sml
	${MLTON} -output $@ tfcompiler.cm

test-tf.sml : test.tfdesc tfcompiler.exe
	./tfcompiler.exe test.tfdesc

tftest.exe : test-tf.sml test.sml test.cm
	${MLTON} -output $@ test.cm

test : tftest.exe
	./tftest.exe
