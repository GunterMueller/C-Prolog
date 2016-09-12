PLSTARTUP=/usr/local/lib/pstartup1.5
GRIND=igrind

# Replace VAX by IEEE for IEEE floating point machines (e.g. Sun)
FLOATING=IEEE

# Replace the right-end side by the empty string to get
# -1 as end of file character

EOF=

CC=cc
CFLAGS=-w -g $(EOF) -D$(FLOATING) -DSTARTUPFILE=\"$(PLSTARTUP)\"
# change define in parms.c - no mistakes then!
BIN=/usr/local/bin/prolog
OBJECTS=main.o unify.o rewrite.o dbase.o sysbits.o space.o \
	parms.o arith.o compare.o auxfn.o trace.o

prolog : $(OBJECTS)
	$(CC) -o prolog $(OBJECTS) -lm

main.o : arithop.h evalp.h trace.h

$(OBJECTS) : pl.h
arith.o : arithop.h
trace.o : trace.h

clean : /tmp
	rm -f $(OBJECTS) prolog startup

startup : prolog pl/init
	./prolog -b pl/init <bootcmd

install : prolog startup
	cp prolog $(BIN)
	chmod 755 $(BIN)
	cp startup $(PLSTARTUP)
	chmod 755 $(PLSTARTUP)

grind:
	$(GRIND) pl.h evalp.h arithop.h main.c rewrite.c dbase.c auxfn.c \
		arith.c unify.c compare.c sysbits.c space.c parms.c
	$(GRIND) -x index

TROFF=nroff -Tlp
DEST=>cprolog.doc

cprolog.doc: app.me cprolog.me
	tbl cprolog.me app.me | $(TROFF) -me $(DEST)


