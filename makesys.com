$ cc arith
$ cc auxfn
$ cc compare
$ cc dbase
$ cc main
$ cc parms
$ cc rewrite
$ cc space
$ cc sysbits
$ cc trace
$ cc unify
$ link/executable:prolog arith,auxfn,compare,dbase,main,parms,rewrite,space,-
$ trace,sysbits,unify
! The line below should be changed to whatever is appropriate at
! your installation
$ prolog :== $usr$:prolog.exe
$ prolog -b [.pl]init
['[.pl]vmsall'].
:-save(startup).
end_of_file.
! The file 'startup' should be moved to its final place as defined in
! parms.c

