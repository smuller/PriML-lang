PRIML=../primlc

all: bank email fibserv fibserv-fair fib_term web

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
