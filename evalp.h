/**********************************************************************
*                                                                     *
*                  C Prolog     evalp.h                               *
*                  ========                                           *
*                                                                     *
*  By Fernando Pereira, July 1982.                                    *
*  EdCAAD, Dept. of Architecture, University of Edinburgh.            *
*                                                                     *
*  Based on the Prolog system written in IMP by Luis Damas            *
*  for ICL 2900 computers, with some contributions by                 *
*  Lawrence Byrd.                                                     *
*                                                                     *
*  Copyright (C) 1982 Fernando Pereira, Luis Damas and Lawrence Byrd  *
*                                                                     *
**********************************************************************/

/* Internal codes for the evaluable predicates.
   These connect the definitions in the bootstrap file(s) to the
   big case statement following the label EvalPted: in main.c.
   The definitions in the bootstrap file are clauses of the form
   
       p(A1,...,Ak) :- n.
       
   or calls of the form
   
       :- $sysp(p(A1,...,Ak),n).

   where p is the evaluable predicate being defined, and n
   is its internal code (Prolog doesn't know about the
   symbolic definitions below, the actual numbers must be used).
   The difference between the first and second forms of definition
   is that in the first a stack frame is build for a call to the
   predicate, containing the arguments, which can be accessed
   in the standard way via the 'x' pointer. In other words,
   the C code for the evaluable predicate will execute as
   if the definition clause was its parent. In contrast,
   evaluable predicates defined in the second way have no
   frame pushed for them, it is up to them to find their
   arguments and xecution environment.
*/

#define _call		  1
#define _cut		  2
#define _repeat		  3
#define _abort		  4
#define _call1		  5
#define _and		  6
#define _see		 10
#define _seeing		 11
#define _seen		 12
#define _tell		 13
#define _telling	 14
#define _told		 15
#define _close		 16
#define _read		 17
#define _write		 18
#define _nl		 19
#define _get0		 20
#define _get		 21
#define _skip		 22
#define _put		 23
#define _tab		 24
#define _fileerrors	 25
#define _nofileerrors	 26
#define _rename		 27
#define _writeq		 28
#define _sh		 29
#define _system		 30
#define _prompt		 31
#define _exists		 32
#define _save		 33
#define _is		 40
#define _ncompare	 41
/* ncompare_+NE
            +LT
	    +GT
	    +LE
	    +GE: RESERVED */
#define _var		 50
#define _nonvar		 51
#define _integer	 52
#define _atomic		 53
#define _eq		 54
#define _ne		 55
#define _functor	 56
#define _arg		 57
#define _univ		 58
#define _atom		 59
#define _erase		 60
#define _asst1	 61
#define _assta1	 62
#define _asst2	 63
#define _assta2	 64
#define _clause		 65
/* clause_+1 : RESERVED */
#define _rcrded	 67
/* _rcrd_+1 : RESERVED */
#define _instance	 69
#define _NOLC		 70
#define _LC		 71
#define _trace		 72
#define _rcrda	 73
#define _rcrdz	 74
#define _name		 75
#define _op		 76
#define _leash		 78
#define _debug		 79
#define _catom		 80
/* catom_+1: RESERVED */
#define _cfunctor	 82
/* cfunctor_+1: RESERVED */
#define _flags		 84
#define _compare	 85
#define _alpLT	 86
#define _alpGT	 87
#define _alpLE	 88
#define _alpGE	 89
#define _all_float	 90
#define _number		 91
#define _erased		 92
#define _statistics	 93
#define _sysp		100
#define _sysflgs	101
#define _brk		102
#define _exit_break	103
#define _xprompt	104
#define _user_exec	105
#define _save_vars	106
#define _reset_vars	107
#define _repply		108
#define _recons		109
#define _brkstart	110
#define _brkend	111
#define _asstr	112
#define _RIP		113
#define _user_call	114
#define _xrepeat	115
#define _yes		116
#define _no		117
#define _primitive	118
#define _db_reference	119
#ifdef GRAPHICS
#define _graphics	120
#endif
#define _hidden_call	121
#define _unary		130
/* 131-149: reserved for unary arithmetic operators */
#define _binary		150
/* 151-169: reserved for binary arithmetic operators */
#define _carith		170
#define _hideat		171
#define _isop		172
#define _abolish	173
#define _append		174
