all:
#	mlton -const 'Exn.keepHistory true' -default-ann 'allowFFI true' -cc-opt "-g" -link-opt "-lz3 -Wl,--whole-archive -lrt -lpthread -Wl,--no-whole-archive " -mlb-path-map lib7-map c72s.mlb z3ml.c
	mlton -default-ann 'allowFFI true' -link-opt "-lz3 -Wl,--whole-archive -lrt -lpthread -Wl,--no-whole-archive " -mlb-path-map lib7-map c72s.mlb z3ml.c

clean:
	rm -f c72s
	rm -f temp.mlb
	rm -f temp.sml
