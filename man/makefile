TROFF=psroff -Tpsc
DEST=>cprolog.doc

cprolog.doc: app.me cprolog.me
	tbl cprolog.me app.me | $(TROFF) -me 
