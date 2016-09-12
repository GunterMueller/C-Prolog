/**********************************************************************
*                                                                     *
*                  C Prolog      pl.h                                 *
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

#include <stdio.h>

#define TRUE	1
#define FALSE	0

#define K	1024

/* the representable integers are in the interval [MinInt,MaxInt] */

#define MaxInt	268435455	/* largest integer = 2^28-1 */
#define MinInt	-268435456	/* smallest integer = -2^28 */


/* SIGNED must be defined as the type of integers with the same width
   as a pointer (int on a VAX). This type is used to interpret pointers
   as signed numbers in comparisons related to the internal representation
   of terms (see picture below). Despite attempts to parameterise as
   much as possible, the sistem still depends on pointers being 32 bits
   wide and numbers being held in two's-complement.
*/

typedef int SIGNED;

/* The original EMAS Prolog in IMP relies too much on pointers being
   just addresses, independently of the type pointed to, for me to be
   able to do anything about it. To help satisfy the compiler's view
   of typing, addresses are objects of type PTR, which are then cast
   into the appopriate types.
*/

typedef unsigned **PTR;

#define CellP(p)	((PTR*)(p))
#define AtomP(p)	((ATOM*)(p))
#define FunctorP(p)	((FUNCTOR*)(p))
#define FrameP(p)	((FRAME*)(p))
#define ClauseP(p)	((CLAUSEREC*)(p))
#define MolP(p)		((MOL*)(p))
#define SkelP(p)	((SKEL*)(p))
#define Signed(p)	((SIGNED)(p))
#define Unsigned(p)	((unsigned)(p))
#define CharP(p)	((char*)(p))

#define Addr(p)		((PTR)&(p))	/* PTRise an address */

/* Prolog registers as cell pointers */

/* Words(number) converts a number of bytes to a number of PTRs */

#define Words(v) (((v)+sizeof(PTR))/sizeof(PTR))

#define SC(x,o,y) (Signed(x) o Signed(y)) /* signed pointer comparison */

/* Origin of input variables */

#define VAR0	0x40000000	/* all variables */
#define LOCAL0	0x41000000	/* local variables */
#define VMASK	0xf0000000	/* variable bit mask */
#define LVMASK	0xff000000	/* local variable bit mask */

#ifdef COMMENT

    The definitions that follow depend crucially on the relative
    positions of stacks and other work areas. Values of type PTR
    whose most significant bit is 1 (negative as integers) are not
    pointers but values of some primitive type (integers or
    database pointers, floats sometime in the future). Positive
    PTRs are pointers into the stacks/work areas. Therefore, the
    top of the topmost area must be below address 2^30-1. If
    Unix could cope with widely scattered segments (promised for
    4.2 BSD), I might be able to implement these things more
    nicely in terms of tagged pointers. As it is, type checking
    is done by signed comparisons, and the stacks/work areas
    occupy a contiguous region in memory. This region is allocated
    by CreateStacks() (sysbits.c), and area sizes are defined in
    parms.c.
    
    The layout is as follows:

	atom0:  	*----------------------*
			|  Atoms               |
	auxstk0:	*----------------------*
			|  Auxiliary stack     |
	trbase:		*----------------------*
			|  Trail               |
	skel0:		*----------------------*
			|  Heap (input terms)  |
	glb0:		*----------------------*
			|  Global stack        |
	lcl0:		*----------------------*
			|  Local stack         |
			*----------------------*

#endif

#define NAreas	6	/* number of work areas/stacks */

#define IsRef(c)	SC(c,>=,glb0)	/* reference */
#define IsAtomic(c)	SC(c,<,skel0)	/* atomic term */
#define IsInp(c)	SC(c,<,glb0)	/* input term */
#define IsComp(c)	SC(c,>=,skel0)	/* compound or constructed term */
#define IsLocal(c)	SC(c,>=,lcl0)	/* local address */
#define IsPrim(c)	SC(c,<,0)	/* number or db reference */
#define IsDBRef(c)	((Unsigned(c)&NUM0) == DB_REF0) /* db reference */
#define IsNumber(c)	((Unsigned(c)&NUM0) == NUM0)	/* number */
#define IsInt(c)	((Unsigned(c)&INT0) == INT0)	/* integer */
#define IsFloat(c)	((Unsigned(c)&INT0) == FLOAT_TAG) /* float */
#define Undef(c)	(Unsigned(c) == 0)	/* undefined cell */
#define IsntName(c)	SC(c,<,atom0)	/* isn't atom or functor */
#define IsName(c)	SC(c,>=,atom0)	/* not primitive */
#define IsVar(c)	((Unsigned(c)&VMASK) == VAR0)	/* input variable */
#define IsLocalVar(c)	((Unsigned(c)&LVMASK) == LOCAL0)/* input local */
#define VarNo(x) (Signed(x)&0xffff)	/* var. offset */

#define FrameVar(v,n) ((PTR)(CharP(v)+(n)))	/* var. cell address */

/* skeleton representation of the nth local variable */

#define SkelLocal(n) ((PTR)((Addr(FrameP(LOCAL0)->v1ofcf)+(n))))

/* ditto global variable */

#define SkelGlobal(n) (((PTR)VAR0)+n)

/* extract and construct integer */

#define XtrInt(c)	((Signed(c)&SIGN) ? Signed(c) : Signed(c)&~INT0)
#define ConsInt(i)	((PTR)(INT0|(i)))

/* extract and construct database pointer */

#define XtrDBRef(c)	(skel0+(Unsigned(c)&~(NUM0|RECORD)))
#define DBType(c)	(Unsigned(c)&RECORD)
#define ConsDBRef(p,k)	((PTR)(((p)-skel0)|DB_REF0|(k)))

/* extract and construct float */

extern float XtrFloat();
extern PTR ConsFloat();

/* Grow pointer p by n agains limit l on area i. */

#define Grow(p,l,n,i)	{if ((p += (n)) > l) NoSpace(i); }

/* Grow atom space */

#define GrowAtom(n)	Grow(atomfp,atmax,n,AtomId)

/* Grow stacks. */

#define GrowLocal(n)	(v += (n))

#define GrowGlobal(n)	(v1 += (n))

#define InitGlobal(n,k)	{ register PTR p; \
			    p = v1+(n); \
			    k = v1; \
			    while (p > v1) *--p = NULL; \
			    GrowGlobal(n); }

/* construct molecule */

#define ConsMol(s,e,m)	{ MolP(v1)->Sk=(s); \
			  MolP(v1)->Env=(e); \
			  m = v1; \
			  GrowGlobal(MolSz); }

/* trail an assignment */

#define TrailPtr(t)	{if (tr > trmax) NoSpace(TrailId); else *tr++ = (t);}

#define TrailVar(t)	{ PTR tt; \
			  tt = (t); \
                          if (tt < vv1 || (lcl0 <= tt && tt < vv)) \
			    TrailPtr(tt); \
			}

/* Headers for doubly linked definition chains */

typedef struct {
    PTR First;
    PTR Last;
} Header;

/* atom entry */

#define infofae	AInfo.Infofae
#define arityofae AInfo.ABytes.Arityofae
#define flgsofae AInfo.Abytes.Flgsofae
#define infxofae AInfo.ABytes.InfixOfAE
#define defsofae AClauses.First
#define dbofae ARecords.First

typedef struct ATOM {
    PTR atofae;			/* self pointer */
    union {
	unsigned Infofae;	/* information */
	struct {
	    char Arityofae;	/* arity ( = 0 ) */
	    char Flgsofae;	/* flags field */
	    short InfixOfAE;	/* infix priority */
	} ABytes;
    } AInfo;
    Header AClauses;		/* chain of definitions */
    Header ARecords;		/* chain of records */
    PTR fcofae;			/* functor chain */
    PTR nxtofae;		/* hash chain */
    short prfxofae, psfxofae;	/* prefix and postfix priorities */
    char stofae[1];		/* string for atom */
} ATOM;

/* size of atom entry (excluding string) */

#define szofae sizeof(ATOM)

/* Size of hashtable */

#define HASHSIZE	269	/* a prime */

/* functor entry */

#define infoffe		FInfo.Infoffe
#define arityoffe	FInfo.FBytes.Arityoffe
#define flgsoffe	FInfo.FBytes.Flgsoffe
#define defsoffe	FClauses.First
#define dboffe		FRecords.First

typedef struct FUNCTOR {
    PTR atoffe;			/* atom for this functor */
    union {
	unsigned Infoffe;	/* general information field */
	struct {
	    char Arityoffe;	/* arity */
	    char Flgsoffe;	/* flags field */
	} FBytes;
    } FInfo;
    Header FClauses;		/* clauses for this functor */
    Header FRecords;		/* data base entries under functor */
    PTR nxtoffe;		/* chain of functors with same name */
    PTR gtoffe;			/* start of general skeleton for this */
				/* term. points to this entry. */
} FUNCTOR;

/* size of functor entry (+ arity) in PTRs */

#define szoffe	(sizeof(FUNCTOR)/sizeof(PTR))

/* clause */

#define MAX_VAR 255	/* highest variable number */

typedef struct CLAUSEREC {
    unsigned char ltofcl;		/* no. of local and temp. variables */
    unsigned char lvofcl;		/* no. of local vars */
    unsigned char gvofcl;		/* no. of global vars */
    char infofcl;		/* general inf. */
    int	 refcofcl;		/* reference count */
    PTR  hdofcl;		/* clause head */
    PTR  bdyofcl;		/* body of clause */
    PTR  altofcl;		/* alternatives */
    PTR  prevofcl;		/* previous clause */
} CLAUSEREC;

/* size of entry in PTRs */

#define szofcl	(sizeof(CLAUSEREC)/sizeof(PTR))

/* local frame */

typedef struct {
    PTR  Lcpofcf;		/* preyious choice point */
    PTR  Gofcf;			/* goal */
    PTR  Gfofcf;		/* goal's local frame */
    PTR  Gsofcf;		/* global frame associated with this frame */
    PTR  Trofcf;		/* tr at entry */
    unsigned Infofcf;		/* general information */
    PTR  Cofcf;			/* continuation on entry */
    PTR  Altofcf;		/* alternatives */
} FRAMECTL;

/* size in cells */

#define szofcf	sizeof(FRAMECTL)/sizeof(PTR)
#define MAX_FRAME szofcf+MAX_VAR+1

typedef struct FRAME {
    FRAMECTL FCTL;
    PTR  v1ofcf;		/* variables */
    PTR  v2ofcf;
    PTR  v3ofcf;
    PTR  v4ofcf;
    PTR  v5ofcf;
} FRAME;

/* Fields of the frame information word */

#define HIDDEN_FRAME	NUM_TAG	/* system frame, not traceable */
#define LEVEL_WIDTH	12	/* width of the level field */
#define CALL_NUMBER	0x3ffff	/* invocation number mask */
#define	LEVEL		0xfff	/* recursion level mask */

/* build the information for the current frame, faking a
   primitive object */

#define FrameInfo(i,l) (((i&CALL_NUMBER)<<LEVEL_WIDTH)|(l&LEVEL)|PRIM_TAG)

/* extract the frame information fields */

#define InvNo(info)	(((info)>>LEVEL_WIDTH)&CALL_NUMBER)
#define Level(info)	((info)&LEVEL)
#define SysFrame(info)	((info)&HIDDEN_FRAME)

/* Evaluable predicate arguments */

#define ARG1 (X->v1ofcf)
#define ARG2 (X->v2ofcf)
#define ARG3 (X->v3ofcf)
#define ARG4 (X->v4ofcf)
#define ARG5 (X->v5ofcf)

/* Frame locations */

#define lcpofcf	FCTL.Lcpofcf
#define gofcf	FCTL.Gofcf
#define gfofcf	FCTL.Gfofcf
#define gsofcf	FCTL.Gsofcf
#define trofcf	FCTL.Trofcf
#define infofcf	FCTL.Infofcf
#define cofcf	FCTL.Cofcf
#define altofcf	FCTL.Altofcf

/* Prolog registers as frame pointers */

#define	X		FrameP(x)
#define V		FrameP(v)
#define VV		FrameP(vv)

/*  skeleton layout - add argument fields as required by code
    (could define an arg. array instead, the generality is hardly worth
    the bother)
*/

typedef struct SKEL {
	PTR Fn;
	PTR Arg1;
	PTR Arg2;
    } SKEL;

#define SkelSz(n)	((n)+1)	/* size of n arg. skeleton */


/* molecule layout - the Sk field MUST be the first! */

typedef struct MOL {
	PTR Sk;
	PTR Env;
    } MOL;

#define MolSz	2	/* NB: size in PTRs, not in bytes */

/* entry is read's variable dictionary */

typedef struct VarEntry {
	struct VarEntry *NextVar;	/* must be the first */
	PTR VarValue;
	int VarLen;
	char VarName[1];
    } VarEntry;

typedef VarEntry *VarP;

/* Primitive objects (ints, floats and database pointers at present)
   are distinguished by tag bits. Any primitive object will have
   bit 31 (sign bit) set. The tags are as follows:

                 tag bits
                 31 30 29
   =============+==+==+==
   int           1  1  1
   float         1  1  0
   ptr to clause 1  0  0
   ptr to record 1  0  1

*/
#define PRIM_TAG	0x80000000	/* tag for primitive types */
#define NUM_TAG		0x40000000	/* tag for numbers */
#define NUM0		0xc0000000	/* origin of primitive types */
#define INT0		0xe0000000	/* origin of integers */
#define SIGN		0x10000000	/* sign bit on a constructed number */
#define FLOAT_TAG	NUM0		/* float tag bits */
#define DB_REF0		0x80000000	/* origin of database references */
#define RECORD		0x20000000	/* reference to a record */
#define CLAUSE		0		/* reference to a clause (clear) */

/* clause/record flags */

#define ERASED	1		/* erased but not yet removed */
#define IN_USE	2		/* in use in a proof, cannot be
				   deleted yet */

#define Erased(c) ((ClauseP(c)->infofcl)&ERASED)
#define InUse(c) ((ClauseP(c)->infofcl)&IN_USE)
#define RC(c) (ClauseP(c)->refcofcl)
#define Idle(c) (RC(c) == 0 && !InUse(c))

/* Flags in a functor entry - apply to the corresponding predicate */

#define RESERVED	0xe0	/* cannot be modified */
#define HIDDEN		0xc0	/* Protected or invisible */
#define PROTECTED	0x80	/* cannot be listed, traced, or modified */
#define INVISIBLE	0x40	/* invisible to tracing and recursion level */
#define UNTRACEABLE	0x20	/* cannot be traced */
#define SPY_ME		0x10	/* is a spypoint */

/* NB. The low order 4 bits of the flags field in a functor or
   atom entry, if non-zero, represent the internal code of that
   functor or atom as an arithmetic operator. This means that
   the maximum number of different arithmetic operators for each
   arity is 15 (see arith.c). This could be changed by redefining
   the layout of functor and atom entries, taking care with
   the way unions are used in them (left-overs from the original
   code in IMP).
*/

/* Internal event conditions */

#define COLD_START	0	/* first thing in the morning */
#define ABORT		1	/* 'abort' evaluable predicate */
#define IO_ERROR	2	/* every STDIO failure that is not */
#define END_OF_FILE	3	/* end of file on input */
#define ARITH_ERROR	4	/* incorrect args. to 'is", =:=, etc. */
#define GEN_ERROR	5	/* all others report here */

/* Initial state flags (set by switches: see parms.c) */

#define IN_BOOT	2
#define QUIET	3
#define DEBUG	4
#define TRACE	5

/* predefined I/O streams */

#define	STDIN	0
#define STDOUT	1
#define	STDERR	2

/* Work areas */

/* Indices of areas */

#define AtomId		0
#define AuxId		1
#define TrailId		2
#define HeapId		3
#define GlobalId	4
#define LocalId		5

/* origins of work areas */

#define atom0	(Origin[AtomId])
#define auxstk0	(Origin[AuxId])
#define trbase	(Origin[TrailId])
#define skel0	(Origin[HeapId])
#define glb0	(Origin[GlobalId])
#define lcl0	(Origin[LocalId])

/* limits of work areas */

#define atmax	Limit[AtomId]
#define auxmax	Limit[AuxId]
#define trmax	Limit[TrailId]
#define hpmax	Limit[HeapId]
#define v1max	Limit[GlobalId]
#define vmax	Limit[LocalId]

/* Tide marks */

#define HighTide(reg,mark) if (reg > mark) mark = reg

#define Auxtide Tide[AuxId]
#define TRtide	Tide[TrailId]
#define V1tide	Tide[GlobalId]
#define Vtide	Tide[LocalId]

/* initial atoms */

#define BATOMS	15

#define atomnil		BasicAtom[0]
#define commafunc	BasicAtom[1]
#define assertatom	BasicAtom[2]
#define EndOfFile	BasicAtom[3]
#define atomtrue	BasicAtom[4]
#define user		BasicAtom[5]
#define live		BasicAtom[6]
#define breakat 	BasicAtom[7]
#define LessThan	BasicAtom[8]
#define Equal		BasicAtom[9]
#define GreaterThan	BasicAtom[10]
#define Yes		BasicAtom[11]
#define No		BasicAtom[12]
#define Minus		BasicAtom[13]
#define semicatom	BasicAtom[14]

/* initial functors */

#define BFUNCS	8

#define calltag		BasicFunctor[0]
#define commatag	BasicFunctor[1]
#define assertfunc	BasicFunctor[2]
#define listfunc	BasicFunctor[3]
#define arrowtag	BasicFunctor[4]
#define provefunc	BasicFunctor[5]
#define HiddenCall	BasicFunctor[6]
#define PrivTerm	BasicFunctor[7]

/* basic terms */

#define BTERMS	2

#define List10		BasicTerm[0]	/* not read in from init file */
#define CsltUser	BasicTerm[1]

/* Magic sequence that starts saved states */

#define	SaveMagic	"PLGS"

/* Exit codes */

#ifdef unix
# define GOOD_EXIT 0
# define BAD_EXIT  1
#else
# define GOOD_EXIT 1
# define BAD_EXIT  0
#endif

/* public data */

extern PTR v, x, vv, v1, vv1, x1, v1f, tr, tr0,
	   atomfp, hasha, vra, vrz, varfp, lsp, brkp,
	   Origin[], Limit[], Tide[], BasicFunctor[], BasicAtom[],
	   BasicTerm[], FileAtom[];

extern char Switch[], StandardStartup[], Parameter[],
            *ErrorMess, OutBuf[], PlPrompt[], *AreaName[], version[];

extern VarP varchain;

extern int crit, running, debug, sklev, quoteia, nvars, lc, errno,
           saveversion, Switches,  Size[], State[], NParms,
	   Input, Output, AllFloat;

/* public functions */

extern int See(), Tell(), CSee(), CTell(), gunify(), instance(),
           intval(), Statistics(), Safe(), Unsafe();
extern PTR fentry(), apply(), makelist(), deref(), arg(), argv(), recorded(),
           lookup(), lookupvar(), pread(), record(), getsp(), Telling(),
           Seeing(), NoSpace(), Unary(), Binary(), scanstack(), findinv();

extern char Get(), ToEOL(), *SysError(), *AtomToFile();

extern float CPUTime();
