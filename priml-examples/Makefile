PRIML=../primlc

all: bank email fibserv fibserv-fair fib_term web

sync_ex_dfc: sync_ex_dfc.prm
	$(PRIML) sync_ex_dfc.prm sync_ex_dfc

var_ex_dfc: var_ex_dfc.prm
	$(PRIML) var_ex_dfc.prm var_ex_dfc

prapp_ex_dfc: prapp_ex_dfc.prm
	$(PRIML) prapp_ex_dfc.prm prapp_ex_dfc

prapp_ex: prapp_ex.prm
	$(PRIML) prapp_ex.prm prapp_ex


cmd_ex_dfc: cmd_ex_dfc.prm
	$(PRIML) cmd_ex_dfc.prm cmd_ex_dfc

cmd_ex: cmd_ex.prm
	$(PRIML) cmd_ex.prm cmd_ex




uh: uh.prm
	$(PRIML) uh.prm uh

badmail2: email-src/badmail2.prm
	$(PRIML) email-src/badmail2.prm badmail2

badmail: email-src/badmail.prm
	$(PRIML) email-src/badmail.prm badmail

fib_fc: fib_fc.prm
	$(PRIML) fib_fc.prm fib_fc

fib: fib.prm
	$(PRIML) fib.prm fib

bank_simp: bank_simp.prm
	$(PRIML) bank_simp.prm bank_simp

bank: bank.prm
	$(PRIML) bank.prm bank

email: email-src/email.prm
	$(PRIML) email-src/email.prm email

fibserv: fibserv.prm
	$(PRIML) fibserv.prm fibserv

fibserv-fair: fibserv-fair.prm
	$(PRIML) fibserv-fair.prm fibserv-fair

fib_term: fib_term.prm
	$(PRIML) fib_term.prm fib_term

web: web-src/web.prm
	$(PRIML) web-src/web.prm web

clean:
	rm -f bank email fibserv fibserv-fair fib_term web
