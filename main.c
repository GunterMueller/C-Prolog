/**********************************************************************
*                                                                     *
*                  C Prolog     main.c                                *
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

#include "pl.h"
#include "evalp.h"
#include "arithop.h"
#include "trace.h"
#include <errno.h>
#include <setjmp.h>

extern int  sys_nerr;
extern char *sys_errlist[];
extern PTR HeapTop();

#define TEST(c,s,f)	{if (c) goto s; else goto f;}
#define TRY(c)		TEST(c,continuation,efail)
#define FlOffset	(Addr(ClauseP(0)->altofcl)-(PTR)0)

/* initial atoms */

PTR BasicAtom[BATOMS];

/* initial functors */

PTR BasicFunctor[BFUNCS];

/* initial terms */

PTR BasicTerm[BTERMS];

/* Variables for comunication with read, write and symbol table */

PTR hasha, lsp, atomfp, varfp, atprompt;
int lc, quoteia, nvars, fileerrors, reading, InBoot;
VarP varchain;

/* start-up flag */

int running = FALSE;

/* variables for communication with dbase */

PTR vra, vrz;

/*  general error message passing string */

char *ErrorMess;

/* emergency exit */

typedef struct {
    jmp_buf buf;
} JumpBuf;

extern  JumpBuf ZeroState;

/*  Heap management block */

extern char Heap[];
extern int  HeapHeader;

/* Names of work areas */

char   *AreaName[] = {
    "atom space", "aux. stack", "trail", "heap",
    "global stack", "local stack"
};

/* Prolog machine registers */

PTR x, x1, v, v1, vv, vv1, v1f, tr, tr0;

/*  main loop variables */

static int info;
PTR pg, c, bg;
static PTR g, fl;

#define FL	ClauseP(fl)	/* failure label */

/*  miscellaneous */

int brklev;

static int  n;
static  PTR f, d, b, k, k1, y, p, l, arg1;
static int  i, j, i1, i2, bb, modeflag;
static char ch, ch2, *bn, *plparm;

/* Input/output diversion */

#define IfInput(flag,code) { \
    int     savedstream = Input; \
    JumpBuf catch; \
    catch = ZeroState; \
    if (!setjmp (ZeroState.buf)) {    \
	if (flag) Input = STDIN;    \
	code;    \
	if (flag) Input = savedstream;    \
	ZeroState = catch;    \
    } else {    \
	if (flag) Input = savedstream; \
	ZeroState = catch;  \
	longjmp (ZeroState.buf, 1);    \
    } \
}

#define IfOutput(flag,code) { \
    int     savedstream = Output; \
    JumpBuf catch; \
    catch = ZeroState; \
    if (!setjmp (ZeroState.buf)) {    \
	if (flag) \
	Output = STDOUT;    \
	code;    \
	if (flag) \
	Output = savedstream;    \
	ZeroState = catch;    \
    } else {    \
	if (flag) \
		Output = savedstream;    \
	ZeroState = catch;    \
	longjmp (ZeroState.buf, 1);    \
    } \
}

/* Variables for the basic debugging package */

int debug = FALSE, lev, sklev, spy, leash = 10 /* half */,
    dotrace, breakret, invokno, execsys;

static int recons, cmparith = 0, InStat, OutStat;
static VarP vchain;
static PTR pvrz, *savead;
PTR brkp;

/*  variables to be saved on a break */

static  PTR * BreakVars[] = {
    &breakret, &brkp, &vchain, &recons, &pvrz,
    &vra, &vrz,
    &x, &x1, &v, &v1, &vv, &vv1, &v1f, &tr, &tr0,
    &debug, &execsys, &pg, &g, &info, &lev, &c, &invokno, &fl,
    &lc,
    &f, &d, &b, &k, &k1, &n, &y, &p, &l, &bb,
    &spy, &sklev, &dotrace,
    &Input, &Output, &InStat, &OutStat
};

/* There must be a one-to-one correspondence between elements of
   BreakVars and VarType. The VarType of a BreakVars is REMAP if
   the BreakVars is a PTR, otherwise it is FIX. FIXes are converted
   to Prolog integers when they are saved, therefore they cannot be
   more than 29 bits.

*/

#define FIX 0
#define REMAP 1

static char VarType[] = {
    FIX, REMAP, REMAP, FIX, REMAP,
    REMAP, REMAP,
    REMAP, REMAP, REMAP, REMAP, REMAP, REMAP, REMAP, REMAP, REMAP,
    FIX, REMAP, REMAP, REMAP, REMAP, FIX, REMAP, FIX, REMAP,
    FIX,
    REMAP, REMAP, REMAP, REMAP, REMAP, REMAP, REMAP, REMAP, REMAP, FIX,
    FIX, FIX, FIX,
    FIX, FIX, FIX, FIX
};

/*  Number of locations in the Prolog environment */

#define BrkEnvSize	(sizeof(BreakVars)/sizeof(PTR *))

static
savev (p, n)
PTR *p; int n;
/*  saves n vars starting with p */
{
    while (n-- > 0)
	*savead++ = *p++;
}

static
rstrv(p,n)
PTR *p; int n;
/*  restores n vars starting with v */
{
    while (n-- > 0)
	*p++ = *savead++;
}

static
savevars()
/*  to enter a break */
{
    PTR nbrkp, **p; char *tp;

    nbrkp = v+MAX_FRAME;
    if (nbrkp > vmax) NoSpace(LocalId);
    for (p = BreakVars, tp = VarType, savead = nbrkp;
         p-BreakVars < BrkEnvSize; p++, tp++, savead++)
	*savead = (*tp == FIX) ? ConsInt(Signed(**p)) : **p;
    vra = vrz; v = savead; brkp = nbrkp;
}

static
popbreak()
/*  to continue from a break */
{
    PTR **p; char *tp;

    for (p = BreakVars, tp = VarType, savead = brkp;
         p-BreakVars < BrkEnvSize; p++, tp++, savead++)
	**p = (*tp == FIX) ? (PTR)XtrInt(*savead) : *savead;
}

#define latS	LSave[AtomId]
#define lauxS	LSave[AuxId]
#define ltrS	LSave[TrailId]
#define lskelS	LSave[HeapId]
#define lglbS	LSave[GlobalId]
#define llclS	LSave[LocalId]
#define savepS	LSave[NAreas]

static int
save()
/*  save current prolog state */
{
    int i;
    unsigned LSave[NAreas+1];
    unsigned *pl; PTR ps;
    FILE *fa;
    int oldin, oldout;

    /* open file */
    if (!(fa = fopen(AtomToFile(ARG1),"w"))) return FALSE;
    errno = 0;		/* no errors right now */
    /*  save state */
    oldin = Input; oldout = Output;
    Input = STDIN; Output = STDOUT;
    savevars();		/* create a break environ */
    savepS = savead-lcl0;
    savev(BasicAtom,BATOMS);
    savev(BasicFunctor,BFUNCS);
    savev(BasicTerm,BTERMS);
    savev(&atprompt,1);
    savev(&brklev,1);
    savev(&atomfp,1);
    /*  compute length of different stacks */
    latS = atomfp-atom0;
    lauxS = vrz-auxstk0;
    ltrS = tr-trbase;
    lskelS = HeapTop()-skel0;
    lglbS = v1-glb0;
    llclS = savead-lcl0+2;
    fwrite(SaveMagic,1,4,fa);	/* mark with tag and version no. */
    fwrite(&saveversion,sizeof saveversion,1,fa);
    fwrite(LSave,sizeof LSave,1,fa);
    fwrite(Origin,sizeof(PTR),NAreas,fa);
    fwrite(Limit,sizeof(PTR),NAreas,fa);
    fwrite(Heap,HeapHeader,1,fa);
    fwrite(&brkp,sizeof brkp,1,fa);
    fwrite(&fileerrors,sizeof fileerrors,1,fa);
    pl = LSave; ps = Origin;
    for (i = 0; i< NAreas; i++)
	fwrite(*ps++,sizeof(PTR),*pl++,fa);
    fclose(fa);
    popbreak();
    Input = oldin; Output = oldout;
    if (errno) ErrorMess = SysError();
    return (errno == 0);	/* TRUE if no errors, FALSE otherwise */
}

/*---------------------------------------------------------------

	restore Prolog state

---------------------------------------------------------------*/

static PTR PArea[2*NAreas];
static int RArea[NAreas];
static unsigned LArea[NAreas];

#define patom	PArea[AtomId]
#define pauxstk	PArea[AuxId]
#define ptr	PArea[TrailId]
#define pskel	PArea[HeapId]
#define pglb	PArea[GlobalId]
#define plcl	PArea[LocalId]

#define ratom	RArea[AtomId]
#define rauxstk	RArea[AuxId]
#define rtr	RArea[TrailId]
#define rskel	RArea[HeapId]
#define rglb	RArea[GlobalId]
#define rlcl	RArea[LocalId]

static
remap(tp)
PTR tp;
/*  remap source term pointed to by tp */
{
    PTR t; int n;
    t = *tp;
    if (IsVar(t)) return;
    if (SC(t,<,patom)) return;
    if (SC(t,<,pskel)) {
	*tp = t+ratom;
	return;
    }
    *tp = t+rskel;
    tp = *tp; t = *tp+rskel; *tp = t;
    n = FunctorP(t)->arityoffe;
    while (n-- > 0)
	remap(++tp);
}

static int
restore(sfile)
char *sfile;
{
    FILE *fa;
    int i, l;
    unsigned savep; int *p; PTR *p1, *p2, s, t, r;
    char magic[5];

    /*  open file */
    if (!(fa = fopen(sfile,"r"))) {
	ErrorMess = SysError();
	return FALSE;
    }
    /*  check it is a saved Prolog state */
    fread(magic,1,4,fa); magic[4] = 0;
    if (strcmp(magic,SaveMagic)) { 
	sprintf(OutBuf,"! File %s is not a saved Prolog state",sfile);
	ErrorMess = OutBuf;
	return FALSE;
    }
    /*  check version */
    fread(&i,sizeof(int),1,fa);
    if (i != saveversion) { 
	sprintf(OutBuf,
	"! File %s is not compatible with this version of Prolog",
        sfile);
	ErrorMess = OutBuf;
	return FALSE;
    }
    fread(LArea,sizeof LArea,1,fa);
    {
	int newsize;

	for(i = 0; i < NAreas; i++) {
	    newsize = (1+(LArea[i]*sizeof(PTR))/K);
	    newsize = K*(int)(1.33*newsize);	/* 33% margin */
	    if (Size[i] < newsize) {	
		fprintf(stderr,
		    "[ Expanding %s from %dK to %dK ]\n",
		    AreaName[i], Size[i]/K, newsize/K);
		Size[i] = newsize;
	    }
	}
    }
    CreateStacks();
    fread(&savep,sizeof savep,1,fa);
    fread(PArea,sizeof PArea,1,fa);
    fread(Heap,HeapHeader,1,fa);
    fread(&brkp,sizeof brkp,1,fa);
    fread(&fileerrors,sizeof fileerrors,1,fa);
    /*  compute relocation constants */
    p1 = Origin; p2 = PArea; p = RArea;
    for (i = 0; i < NAreas; i++)
	*p++ = *p1++ - *p2++;
    /*  extract stacks from file */
    p = LArea; p2 = Origin;
    for (i = 0; i < NAreas; i++, p++, p2++) {
	l = *p; s = *p2;
	fread(s,sizeof(PTR),l,fa);
	if (i != AtomId && i != HeapId && i != AuxId)
	/* relocate stack contents */
	while (l-- > 0) {
	    k = *s;
	    if (SC(k,<,ptr)) {
		if (SC(k,>=,pauxstk)) k += rauxstk;
		else if (SC(k,>=,patom)) k += ratom;
	    } else {
		if (SC(k,>=,pglb))
		    k += SC(k,>=,plcl) ? rlcl : rglb;
		else
		    k += (SC(k,>=,pskel)) ? rskel : rtr;
	    }
	    *s++ = k;
	}
    }
    savead = savep+lcl0;
    rstrv(BasicAtom,BATOMS);
    rstrv(BasicFunctor,BFUNCS);
    rstrv(BasicTerm,BTERMS);
    rstrv(&atprompt,1);
    rstrv(&brklev,1);
    rstrv(&atomfp,1);
    brkp += rlcl;
    popbreak();
    /* NB: the various registers in the Prolog machine (those
       referred to in BreakVars) have already been remapped
       because savevars() saves the environment in the local
       stack, whose contents have been remapped above (tricky,
       this one!)
    */
    /*  remap free space chains */
    RelocHeap(rskel);

    /* fix prompt (may have been remapped) */
    SetPlPrompt(AtomP(atprompt)->stofae);

    /*  remap auxiliary stack  */
    for (k = auxstk0; k < vrz;) {
    /*	the auxiliary stack can only contain variable records (from 'read')
	or functor and atom pointers (from 'reconsult'). Variable records
	are distinguished by having either NULL or an aux. stack pointer in
	their first word (NextVar); they are variable length,
	with the length in VarLen. */
	if (k->NextVar == NULL ||
	    (SC(k->NextVar,>=,pauxstk) && SC(k->NextVar,<,ptr))) {
	    k->VarValue += rglb;
	    if (k->NextVar) k->NextVar += rauxstk;
	    k += k->VarLen;
	}
	else {
	    if (SC(*k,>=,pskel)) *k += rskel;
	    else *k += ratom;
	    k++;
	}
    }
    /* Remap atom and heap areas */

    /* Start from the hash table. The test in the loop is <= rather
       than < because we want to remap hidden atoms as well, whose
       chain is stored at hasha+HASHSIZE */

    for (k = hasha = atom0; k <= hasha+HASHSIZE; k++) {
	p = k;
    	/* remap hash chain */
	while (*p) {
	    /* remap arity chain */
	    p1 = p;
	    while (*p1) {
		t = *p1;
		t += SC(t,<,pskel) ? ratom : rskel;
		*p1 = t;	/* remap pointer to entry */
		p1 = *p1;
		FunctorP(p1)->atoffe += ratom; /* remap pointer to atom */
		if (FunctorP(p1)->FClauses.Last)
		    FunctorP(p1)->FClauses.Last += rskel;
		if (FunctorP(p1)->FRecords.Last)
		    FunctorP(p1)->FRecords.Last += rskel;
		/* remap chain of definitions */
		p2 = Addr(FunctorP(p1)->defsoffe);
		while (SC(*p2,>=,pskel)) {
		    p2 = *p2 += rskel;
		    /*  check for circularity */
		    if (ClauseP(p2)->altofcl == p2) break;
		    remap(&(ClauseP(p2)->hdofcl));
 		    remap(&(ClauseP(p2)->bdyofcl));
		    if (ClauseP(p2)->prevofcl)
			ClauseP(p2)->prevofcl += rskel;
		    p2 = Addr(ClauseP(p2)->altofcl);
		}
		/* remap data base chain */
		p2 = Addr(FunctorP(p1)->dboffe);
		while (SC(*p2,>=,pskel)) {
		    p2 = *p2 +=rskel;
		    t = ClauseP(p2)->hdofcl;	/* remap key pointer */
		    t += (SC(t,<,pskel)) ? ratom : rskel;
		    ClauseP(p2)->hdofcl = t;
		    remap(&(ClauseP(p2)->bdyofcl));
		    if (ClauseP(p2)->prevofcl)
			ClauseP(p2)->prevofcl += rskel;
		    p2 = Addr(ClauseP(p2)->altofcl);
		}
		if (SC(p1,>=,skel0)) {
		    t = Addr(FunctorP(p1-rskel)->gtoffe);
		    remap(&t);
		}
		p1 = Addr(FunctorP(p1)->nxtoffe);
	    }
	    p = Addr(AtomP(*p)->nxtofae);
	}
    }
    fclose(fa);
    return TRUE;
}

static
ResetTrail(t)
register PTR t;
{
    register PTR k, xtr; register char *status;

    xtr = tr;
    while (xtr-- != t) { 
	k = *xtr;
	if (IsRef(k)) *k = NULL;
	else {
	    status = &(ClauseP(XtrDBRef(k))->infofcl);
	    if (!((*status)&ERASED)) *status &= ~IN_USE;
	    else hide(k);
	}
    }
    tr = xtr;
}

static PTR
bread()
/*  read initialization terms */
{
    PTR r;

    do {
	v = lcl0; v1 = glb0;
	SetPlPrompt("    >> ");  PromptIfUser("boot>> ");
	varfp = vrz; lsp = v;
	reading = FALSE;
    } while (!(r = pread()));
    return r;
}

/*===============================================================

    Prolog execution starts here

===============================================================*/

int PrologEvent;

main(ArgC,ArgV)
int ArgC; char *ArgV[];
{
    /* our first Prolog event will be a cold start */
    Safe();
    PrologEvent = COLD_START;
    /* Prolog events cause execution to resume fom here */
    setjmp(ZeroState.buf);
    CatchSignals();	/* prepare to handle signals etc. */
    switch (PrologEvent) {
	/* Prolog event handling
	   Unix signals are mapped to Prolog events,
	   Event(..) can also be used to force
	   a Prolog event to occur. */
	case ABORT:  /* abort */
	    aborting:
	    fprintf(stderr,"\n\n[ execution aborted ]\n\n");
	    ResetTrail(trbase); CloseFiles(); InitIO();
	    goto restart;
	case IO_ERROR:	/* files error */
	    IoFailure:
	    if (fileerrors) goto efail;
	    debug = TRUE;
	    fprintf(stderr,"\n\n%s\n",ErrorMess);
	    goto aborting;
	case END_OF_FILE:	/* input ended */
	    Seen();
	    if (reading) {
		reading = FALSE;
		goto readend;
	    }
	    ErrorMess = "! Input ended";
	    goto IoFailure;
	case ARITH_ERROR:	/* error in arithmetic expression */
	    fprintf(stderr,"\n! Error in arithmetic expression: %s\n",
		ErrorMess);
	    debug = TRUE; sklev = NEVER_SKIP; goto efail;
	case GEN_ERROR:	/* general error with message requiring abort */
	    fprintf(stderr,"\n%s",ErrorMess);
	    goto aborting;
	case COLD_START:	/* cold start */
	    break;
    }

    printf("%s\n",version);

    /*  process parameters */

    for (i = 0; i < Switches; i++)
	State[i] = FALSE;
    plparm = NULL;
    while (--ArgC > 0)
	if (**++ArgV == '-') {
	    for (i = 0; i < NParms; i++)
		if (Parameter[i] == (*ArgV)[1]) {
		    ArgV++; ArgC--;
		    if (*ArgV) Size[i] = atoi(*ArgV)*K;
		}
	    for (i1 = 1; (*ArgV)[i1]; i1++) {
		for (i = 0; i < Switches; i++)
		    if (Switch[i] == (*ArgV)[i1]) {
			State[i] = TRUE;
			break;
		}
		if (i > Switches)
		    fprintf(stderr,
		    "! Unknown switch: %c\n",(*ArgV)[i1]);
	    }
	} else {
	    plparm = *ArgV;
	    break;
	}
    InBoot = FALSE;
    if (!State[IN_BOOT]) {
	if (!plparm) {
	    plparm = UserStartup();
	    if (!Exists(plparm)) {
		plparm = StandardStartup;
		State[QUIET] = TRUE;
	    }
	}
	if (!Exists(plparm)) {
	    fprintf(stderr,"! File %s does not exist\n",plparm);
	    exit(BAD_EXIT);
	}
	if (!State[QUIET]) {
	    printf("[ Restoring file %s ]\n",plparm);
	}
	if (restore(plparm)) {
	    InitIO();
	    Vtide = v; V1tide = v1; TRtide = tr; Auxtide = vrz;
	    running = TRUE;
            /* the system is now up and running */
	    if (brklev > 0) 
		printf("[ Restarting break (level %d) ]\n",brklev);
	    TRY(unifyarg(Addr(ARG2),ConsInt(1),0));
	}
	fprintf(stderr,"%s\n",ErrorMess);
	exit(BAD_EXIT);
    }

    if ((!plparm) || (!Exists(plparm))) {
	fprintf(stderr,"** File %s does not exist\n",plparm);
	exit(BAD_EXIT);
    }
    printf("[ Bootstrapping session. Initializing from file %s ]\n",
           plparm);

    /* create stacks */

    CreateStacks();

    /* initialize atom area */

    hasha = atom0; atomfp = atom0;
    for (i = 0; i <= HASHSIZE; i++) *atomfp++ = NULL;
   /* hasha+HASHSIZE points to atoms that have been hidden by $hide_atom */

    /*  initialize read/print vars */

    lc = TRUE; quoteia = FALSE; 

    /*  initialize heap */

    InitHeap();

    /*  initialise i/o system */

    InitIO();
    fileerrors = FALSE;
    InBoot = TRUE;		/* We are booting */

    /* junk (otherwise unititialised) */

    brkp = l = n = recons = spy = 0;

    /*  now load bootstrap file information */

    CSee(plparm);

    /*  read required atoms */

    for (i = 0; i < BATOMS; i++)
	BasicAtom[i] = bread();

    /*  read required functors */

    for (i = 0; i <BFUNCS; i++)
	BasicFunctor[i] = SkelP(MolP(bread())->Sk)->Fn;

    /* read required terms */

    pg = getsp(27); k = pg;
    for (i = 9; i > 0; i--) {
	SkelP(k)->Fn = listfunc;
	SkelP(k)->Arg1 = SkelGlobal(i);
	SkelP(k)->Arg2 = k+3;
        k += 3;
    }
    *(pg+26) = SkelGlobal(i);
    List10 = pg;

    for (i = 0; i < BTERMS; i++) {	/* first term is the special List10 */
	if (i == 0)
	    pg = ConsInt(0);		/* a dummy term */
	else
	    pg = bread();		/* read a term */
	x1 = v1;
	*v1++ = pg;		/* push it into global stack */
	ConsMol(Addr(FunctorP(PrivTerm)->gtoffe),x1,pg); /* encapsulate it */
	if (!(g = record(CLAUSE,pg,0,0))) { /* assert encapsulated term */
	    fprintf(stderr,"Cannot create basic term: ");
	    Output = STDERR;
	    pwrite(pg,0,1200);
	    Put('\n');
	    exit(BAD_EXIT);
	}
	if (i == 0)		/* major hack for List10 */
	    SkelP(ClauseP(XtrDBRef(g))->hdofcl)->Arg1 = List10;
	else
	    BasicTerm[i] = SkelP(ClauseP(XtrDBRef(g))->hdofcl)->Arg1;
    }

/* Set top level termination */

/* On success */

    FunctorP(Yes)->defsoffe = _yes;

/* On failure - clause $no :- _no */

    k = v1 = glb0;
    *v1++ = No;
    *v1++ = ConsInt(_no);
    ConsMol(Addr(FunctorP(arrowtag)->gtoffe),k,pg);
    if (!record(CLAUSE,pg,0,0)) {
	fprintf(stderr,"\n! Fatal error in startup - consult guru\n");
	Stop(TRUE);
    }
    k = FunctorP(No)->defsoffe;	/* Fail to itself */
    ClauseP(k)->altofcl = k;

    atprompt = atomnil;
    running = TRUE;	/* boot is now running */

    /* restart here after an abort etc. */

    restart:
    vrz = auxstk0;
    v = lcl0;
    v1 = glb0;
    tr = trbase;
    FileAtom[STDIN] = FileAtom[STDOUT] = user;
    ResetStreams();
    dotrace = FALSE;
    execsys = PRIM_TAG|HIDDEN_FRAME;
    brklev = 0;
    if (!State[IN_BOOT]) {
    	pg = live;
	goto go;
    }

    /* main loop during bootstrap session */

    mainloop:
    pg = bread();
    if (IsRef(pg) && *pg) g = *pg; else g = pg;
    if (g == EndOfFile) {
	Seen();
	State[IN_BOOT] = FALSE;
	goto restart;
    }

    if (IsAtomic(g) || SkelP(g)->Fn != provefunc) { 
	if (!record(CLAUSE,pg,0,0)) {
	    int telling;

	    fprintf(stderr,"%s\n",ErrorMess);
	    telling = Output;
	    Output = STDERR;
	    pwrite(pg,0,1200);
	    Put('\n');
	    Output = telling;
	}
	goto mainloop;
    }

    SetPlPrompt("| ");
    pg = arg(Addr(SkelP(g)->Arg1),pg->Env);

    /* go - run the goal pg */

    go:
    brkp = 0;	/* no break points so far */
    tr = trbase; vv = x = lcl0; vv1 = x1 = glb0; c = Yes;
    VV->gofcf = No;
    VV->altofcf = Addr(FunctorP(No)->defsoffe->altofcl);
    VV->gfofcf = VV->lcpofcf = vv;
    VV->gsofcf = vv1;
    VV->trofcf = tr0 = tr;
    VV->infofcf = PRIM_TAG|HIDDEN_FRAME;
    VV->cofcf = c;
    GrowLocal(szofcf);
    dotrace = FALSE;
    lev = 1; invokno = 0; execsys = HIDDEN_FRAME;
    sklev = NEVER_SKIP;

/********************************************************************

          interpreter main loop

********************************************************************/

    icall:
    if (IsInp(pg)) g = pg;
    else { 
	x1 = MolP(pg)->Env;
	g = MolP(pg)->Sk;
    }
    f = SkelP(g)->Fn;
    d = FunctorP(f)->defsoffe;
    if (execsys)
	info = PRIM_TAG|HIDDEN_FRAME;
    else {
	bb = FunctorP(f)->flgsoffe;
	if (!(bb&INVISIBLE)) invokno++;
	info = FrameInfo(invokno,lev);
    brokencall:
	Trace((debug && !(bb&(INVISIBLE|UNTRACEABLE))),
	      v,pg,x,info,CALL_PORT);
    }
    if (Signed(d) > 0 && Signed(d) < 255) {
	i = Signed(d);
	goto EvalPred;
    }
    while (d && Erased(d)) d = ClauseP(d)->altofcl;
    if (!d) goto efail;

    V->lcpofcf = vv;
    V->gofcf = pg;
    V->gfofcf = x;
    V->gsofcf = v1;
    V->trofcf = tr0 = tr;
    V->infofcf = info;
    V->cofcf = c;
    vv = v; vv1 = v1;

    /* try one clause */
    alt:
    n = SkelP(g)->Fn->arityoffe;
    fl = Addr(ClauseP(d)->altofcl);
    v1f=v1;
    if ((!debug) && !*fl) {
	vv = V->lcpofcf;
	vv1 = VV->gsofcf;
    }
    InitGlobal(ClauseP(d)->gvofcl,k);
    k = Addr(V->v1ofcf);
    i = ClauseP(d)->ltofcl;
    while (i-- > 0) *k++ = 0;
    V->altofcf = fl;
    if (IsComp(g)) {
	register PTR ta, tb, a, b, pa, pb; int arity;

	/* in-line top level for unification */

	ta = ClauseP(d)->hdofcl;
	tb = g;
	arity = SkelP(ta)->Fn->arityoffe;

	/* main loop  */

	while (arity-- > 0) {
	    a = *++ta;
	    if (IsVar (a)) {
		pa = FrameVar (IsLocalVar (a) ? v : v1f, VarNo (a));
		a = *pa;
		while (IsRef (a)) {
		    pa = a;
		    a = *a;
		}
		b = *++tb;
		if (IsVar (b)) {
		    pb = FrameVar (IsLocalVar (b) ? x : x1, VarNo (b));
		    b = *pb;
		    while (IsRef (b)) {
			pb = b;
			b = *b;
		    }
		    if (pa == pb)
			continue;
		    if (Undef (b)) {
			if (Undef (a)) {
			    if (pa > pb) {
				*pa = pb;
				TrailVar (pa);
				continue;
			    }
			    *pb = pa;
			    TrailVar (pb);
			    continue;
			}
			if (IsComp (a))
			    *pb = pa;
			else
			    *pb = a;
			TrailVar (pb);
			continue;
		    }
    
		    if (Undef (a)) {
			if (IsComp (b))
			    *pa = pb;
			else
			    *pa = b;
			TrailVar (pa);
			continue;
		    }
    
		    if (IsAtomic (a)) {
			if (a == b)
			    continue;
			else
			    goto fail;
		    }
		    if (IsAtomic (b) ||
			!gunify (a, MolP (pa) -> Env, b, MolP (pb) -> Env))
			goto fail;
		    continue;
		}
		if (IsAtomic (b)) {
		    if (Undef (a)) {
			*pa = b;
			TrailVar (pa);
			continue;
		    }
		    if (a == b)
			continue;
		    goto fail;
		}
		if (Undef (a)) {
		    ConsMol (b, x1, *pa);
		    TrailVar (pa);
		    continue;
		}
		if (IsAtomic (a) ||
		    !gunify (a, MolP (pa) -> Env, b, x1))
		    goto fail;
		continue;
	    }
	    b = *++tb;
	    if (IsInp (b)) {
		if (IsComp (a)) {
		    if (IsAtomic (b) || !gunify (a, v1f, b, x1))
			goto fail;
		    continue;
		}
		if (b != a)
		    goto fail;
		continue;
	    }
	    pb = FrameVar (IsLocalVar (b) ? x : x1, VarNo (b));
	    b = *pb;
	    while (IsRef (b)) {
		pb = b;
		b = *b;
	    }
	    if (Undef (b)) {
		if (IsAtomic (a))
		    *pb = a;
		else
		    ConsMol (a, v1f, *pb);
		TrailVar (pb);
		continue;
	    }
	    if (IsComp (b)) {
		if (IsAtomic (a) ||
		    !gunify (a, v1f, b, MolP (pb) -> Env))
		    goto fail;
		continue;
	    }
	    if (b != a)
		goto fail;
	    continue;
	}
    }

    if (v > vmax) NoSpace(LocalId);
    if (v1 > v1max) NoSpace(GlobalId);
    bn = &(ClauseP(d)->infofcl);
    if (!((*bn)&IN_USE)) {
	*bn |= IN_USE;
	TrailPtr(ConsDBRef(d,CLAUSE));
    }
    x = v; x1 = v1f;
    GrowLocal(szofcf+ClauseP(d)->lvofcl);
    if (c = ClauseP(d)->bdyofcl) {
	if (!execsys && !(bb&INVISIBLE)) {
	    if (bb&PROTECTED) execsys = HIDDEN_FRAME;
	    else lev++;
	}
	if (IsInt(c)) {
	    i = XtrInt(c)&255;
	    modeflag = XtrInt(c)>>8;
	    c = NULL;
	    goto EvalPred;
	}
    }
continuation:
    while (!c) {
	HighTide(v,Vtide);
	if (x > vv) v = x;
    fromcut:
	c = X->cofcf;
	pg = X->gofcf;
	info = X->infofcf;
	execsys = SysFrame(info);
	if (!execsys) lev = Level(info);
    brokenexit:
	Trace((debug && (!execsys)),x,pg,X->gfofcf,info,EXIT_PORT);
	x = X->gfofcf;
	x1 = X->gsofcf;
    }

    /* nonempty continuation */

    notfoot:
    x1 = X->gsofcf;
    if (IsPrim(c)) goto efail;
    if (SkelP(c)->Fn != commatag) {
	pg = c; c = NULL;
	goto icall; 
    }
    pg = SkelP(c)->Arg1;
    c = SkelP(c)->Arg2;
    if (IsPrim(pg)) goto efail;
    goto icall;

    
    /*  shallow backtracking */

    fail:
    d = *fl;
    while (tr != tr0) **--tr = NULL;
    while (d && Erased(d)) d = ClauseP(d)->altofcl;
    if (d) {
	v1 = v1f;
	goto alt;
    }
    vv = V->lcpofcf;
    
    /*  deep backtracking */

    efail:
    HighTide(v,Vtide);
    HighTide(v1,V1tide);
    HighTide(tr,TRtide);
    if (!debug) {
	while(TRUE) {
	    for (d = *(VV->altofcf); d && Erased(d); d = ClauseP(d)->altofcl);
	    if (d) break;
	    vv = VV->lcpofcf;
	}
    } else {
    brokenfail:
	Trace((!execsys),v,pg,x,info,FAIL_PORT);
	for (d = *(VV->altofcf); d && Erased(d); d = ClauseP(d)->altofcl);
    }
    {
	int fail_parent = vv == x && !c;

	v = vv; vv1 = v1 = V->gsofcf;
	x = V->gfofcf;
	x1 = X->gsofcf;
	pg = V->gofcf;
	c = V->cofcf;
	info = V->infofcf;
	execsys = SysFrame(info);
	tr0 = V->trofcf;
	while (tr != tr0) { 
	    k = *--tr;
	    if (IsRef(k)) *k = NULL;
	    else {
		bn = &(ClauseP(XtrDBRef(k))->infofcl);
		if (!((*bn)&ERASED)) *bn &= ~IN_USE;
		else hide(k);
	    }
	}
    brokenback:
	Trace((debug&&(!execsys)&&(!fail_parent)),v,pg,x,info,BACK_PORT);
    }
    if (!d) {
	vv = VV->lcpofcf;
	goto efail;
    } else {
	if (IsInp(pg))
	    g = pg,  x1 = X->gsofcf;
	else
	    g = MolP(pg)->Sk, x1 = MolP(pg)->Env;
	bb = FunctorP(SkelP(g)->Fn)->flgsoffe;
	goto alt;
    }

/****************************************************************
*                                                               *
*		evaluable predicates				*
*                                                               *
****************************************************************/

    EvalPred:
    switch (i) {

/*   control predicates */

	case _and:		/* conjunction a,b      a6 */
	    k = arg(Addr(SkelP(g)->Arg2),x1);
	    if (IsInp(k) && IsComp(k))
		ConsMol(k,x1,k);
	    *v1 = k; *(v1+1) = &(FunctorP(HiddenCall)->gtoffe);
	    *(v1+2) = v1;
	    k = v1+1; GrowGlobal(3);
	    if (!c) c = k;
	    else {
		*v1 = commatag; *(v1+1) = k; *(v1+2) = c;
		c = v1; GrowGlobal(3);
	    }
	case _hidden_call:
	    pg = arg(Addr(SkelP(g)->Arg1),x1);
	    if (IsPrim(pg) || Undef(*pg)) goto efail;
	    if (IsInp(pg) && IsComp(pg))
		ConsMol(pg,x1,pg);
	    goto icall;
	case _user_call:	/* revive tracing (for setof, etc.) */
	    lev++;
	    execsys = FALSE;
	case _call:			/* call(a) */
	    pg = ARG1;
	    TEST(IsPrim(pg) || Undef(*pg),efail,icall);
	case _cut:			/* cut operator */
	cut:
	    if (x > vv) goto continuation;
	    HighTide(v,Vtide);
	    v = x+szofcf+((X->altofcf)-FlOffset)->ltofcl;
	    vv = X->lcpofcf;
	    vv1 = VV->gsofcf;
	    HighTide(tr,TRtide);
	    if (X->trofcf != tr) {
	        register PTR kept, old, entry ; PTR globound, locbound;

/* If debugging, trail entries pointing to frames not being discarded
   cannot be removed, otherwise  the retry option would not work.
   The variables globound and locbound contain the lowest discardable
   entries for the global and local stack respectively */

		if (debug)
		    globound = v1, locbound = v;
		else
		    globound = vv1, locbound = vv;
		kept = old = X->trofcf;
		do {
		    entry = *old++;
		    if ((!IsRef(entry))
		    ||  entry < globound
		    ||  (lcl0 <= entry && entry < locbound))
			*kept++ = entry;
		} while (old != tr);
		tr = kept;
	    }
	    TEST(c, notfoot, fromcut);
	case _repeat:			/* repeat           b3 */
	    repeat:
	    vv = x;
	    vv1 = x1;
	    *fl = d;
	    goto continuation;
	case _abort:			/* abort             a4 */
	    goto aborting;
	case _call1:			/*  $call(x) */
	    pg = arg(Addr(SkelP(g)->Arg1),x1);
	    c = X->cofcf; x = X->gfofcf;
	    if (IsPrim(pg) || Undef(*pg)) goto efail;
	    if (IsInp(pg) && IsComp(pg))
		ConsMol(pg,x1,pg);
	    goto icall;

/*----------------------------------------------------------------

           I/O predicates  

----------------------------------------------------------------*/
	case _see:		/* see(f) */
	    See(ARG1);
	    goto continuation;
	case _seeing:		/* seeing(x) */
	    k = Seeing();
	    goto unifyatom;
	case _seen:		/* seen */
	    Seen();
	    goto continuation;
	case _tell:		/* tell(f) */
	    Tell(ARG1,"w");
	    goto continuation;
	case _append:		/* append(f) */
	    Tell(ARG1,"a");
	    goto continuation;
	case _telling:		/* telling(x) */
	    k = Telling();
	    unifyatom:		/* unify atom k with arg in v1ofcf */
	    k1 = ARG1;
	    if (IsRef(k1) && Undef(*k1)) {
		*k1 = k;
		TrailVar(k1);
		goto continuation;
	    }
	    TRY(k == k1);
	case _told:		/* told            b15 */
	    Told();
	    goto continuation;
	case _close:		/* close(f)	   b16 */
	    PClose(ARG1);
	    goto continuation;
	case _read:		/*  read(x) */
	    varfp = vrz;
	    lsp = v+3;
	    varchain = NULL; reading = TRUE;
	    IfInput(modeflag,k = pread());
	    readunify:
	    reading = FALSE; 
	    if (!k) goto efail;
	    TRY(unifyarg(Addr(ARG1),k,0));
	    readend:	/* input ended trapped while reading */
	    k = EndOfFile;
	    goto readunify;
	case _write:		/* write(x)        b18 */
	    quoteia = FALSE;
	    IfOutput(modeflag,pwrite(ARG1,x1,1200));
	    goto continuation;
	case _writeq:		/* writeq(x)        b28 */
	    quoteia = TRUE;
	    IfOutput(modeflag,pwrite(ARG1,x1,1200));
	    goto continuation;
	case _nl:		/* nl         b19 */
	    IfOutput(modeflag,Put('\n'));
	    goto continuation;
	case _get0:		/* get0(n)     b20 */
	    IfInput(modeflag,k = ConsInt(Get()));
	    goto unifyatom;
	case _get:		/* get(n)   b21 */
	    IfInput(modeflag,
		do ch = Get(); while (ch <= ' ' || ch >= 127);
	    )
	    k = ConsInt(ch);
	    goto unifyatom;
	case _skip:		/* skip(n)  b22 */
	    ch2 = intval(&(ARG1));
	    IfInput(modeflag,
	    do ch = Get(); while (ch != ch2);
	    )
	    goto continuation;
	case _put:		/* put(n)      b23 */
	    IfOutput(modeflag,Put(intval(&(ARG1))));
	    goto continuation;
	case _tab:		/* tab(n)          b24 */
	    i = intval(&(ARG1));
	    IfOutput(modeflag,while (i-- > 0) Put(' '));
	    goto continuation;
	case _fileerrors:		/* fileerrors      b25 */
	    fileerrors = FALSE;
	    goto continuation;
	case _nofileerrors:		/* nofileerrors     b26 */
	    fileerrors = TRUE;
	    goto continuation;
	case _rename:		/* rename(f,f1)     b27 */
	    if (ARG2 == atomnil)
		Remove(AtomToFile(ARG1));
	    else
		Rename(AtomToFile(ARG1),AtomToFile(ARG2));
	    goto continuation;
	case _sh:		/* sh		 b29 */
	    TRY(Sh());
	case _system:		 /* system(_) b30 */
	    TRY(CallSystem(ARG1));
	case _prompt:		 /* prompt(_,_) b31 */
	    if (!unifyarg(Addr(ARG1),atprompt,0)) goto efail;
	    k = vvalue(Addr(ARG2),&l);
	    if (IsntName(k) || !IsAtomic(k)) goto efail;
	    atprompt = k;
	    SetPlPrompt(AtomP(atprompt)->stofae);
	    goto continuation;
	case _carith:		/* $carith(_,_) */
	    if (!(unifyarg(Addr(ARG1),ConsInt(cmparith),0))) goto efail;
	    k = vvalue(Addr(ARG2),&l);
	    if (!IsInt(k)) goto efail;
	    cmparith = XtrInt(k);
	    goto continuation;
	case _exists:		/* exists(f)  b32 */
	    TRY(Exists(AtomToFile(ARG1)));
	case _save:		/* $save(f,i) a33 */
	    if (save()) {
		TRY(unifyarg(Addr(ARG2),ConsInt(0),0));
	    } else goto IoFailure;

/*---------------------------------------------------------------

        arithmetic predicates

---------------------------------------------------------------*/
	case _is:		/*  is         b40 */
	    k = numeval(&(ARG2));
	    goto unifyatom;
	case _ncompare+EQ:
	case _ncompare+NE:
	case _ncompare+LT:
	case _ncompare+GT:
	case _ncompare+LE:
	case _ncompare+GE:
	    TRY(numcompare(i-_ncompare,&(ARG1),&(ARG2)));

	/* expanded arithmetic predicates */

	/* unary */

	case _unary+ID:
	case _unary+UMINUS:
	case _unary+NOT:
	case _unary+EXP:
	case _unary+LOG:
	case _unary+LOG10:
	case _unary+SQRT:
	case _unary+SIN:
	case _unary+COS:
	case _unary+TAN:
	case _unary+ASIN:
	case _unary+ACOS:
	case _unary+ATAN:
	case _unary+FLOOR:
	    TRY(unifyarg(Addr(ARG2),Unary(i-_unary,Addr(ARG1)),0));

	/* binary */
	
	case _binary+PLUS:
	case _binary+MINUS:
	case _binary+TIMES:
	case _binary+DIVIDE:
	case _binary+MOD:
	case _binary+AND:
	case _binary+OR:
	case _binary+LSHIFT:
	case _binary+RSHIFT:
	case _binary+IDIV:
	case _binary+POW:
	    TRY(unifyarg(Addr(ARG3),
		Binary(i-_binary,Addr(ARG1),Addr(ARG2)),0));

/*--------------------------------------------------------------*/

	case _var:		/* var(x)   b50 */
	    k = ARG1;
	    TRY(IsRef(k) && Undef(*k));
	case _nonvar:/* nonvar(x)   b51 */
	    k = ARG1;
	    TRY(!IsRef(k) || !Undef(*k));
	case _integer:		/* integer(x)   b52 */
	    TRY(IsInt(ARG1));
	case _number:		/* number(x) b91 */
	    TRY(IsNumber(ARG1));
	case _primitive:	/* primitive(x) */
	    TRY(IsPrim(ARG1));
	case _db_reference:	/* db_reference(x) */
	    TRY(IsDBRef(ARG1));
	case _atomic:		/* atomic(x)   b53 */
	    TRY(IsAtomic(ARG1));
	case _atom:		/* atom(x) b59 */
	    k = ARG1;
	    TRY(!IsPrim(k) && IsAtomic(k));
	case _eq:	/* == b54 */
	    TRY(!compare(&(ARG1),&(ARG2)));
	case _ne:	/* \==  b55 */
	    TRY(compare(&(ARG1),&(ARG2)));
	case _functor:	/* functor(t,f,n)  b56 */
	    k = ARG1;
	    if (IsAtomic(k)) {
		k1 = ConsInt(0);
		goto unifyfn;
	    }
	    if (IsRef(k) && !Undef(*k)) {
		k = SkelP(MolP(k)->Sk)->Fn;
		k1 = ConsInt(FunctorP(k)->arityoffe);
		k = FunctorP(k)->atoffe; goto unifyfn;
	    }
	    i1 = intval(&(ARG3));
	    if (i1 == 0) {
		k = ARG2;
		goto unifyt;
	    }
	    if (i1 < 0 || i1 > 100) goto efail;
	    InitGlobal(i1,k1);
	    k = ARG2;
	    if (IsPrim(k) || IsComp(k)) goto efail;
	    k = Addr(FunctorP(fentry(k,i1))->gtoffe);
	    unifyt:
	    TRY(unifyarg(Addr(ARG1),k,k1));
	    unifyfn:
	    TRY(unifyarg(Addr(ARG2),k,0) &&
	    	 unifyarg(Addr(ARG3),k1,0));
	case _arg:		/* arg(n,t,a) b57 */
	    i1 = intval(&(ARG1));
	    k1 = ARG2;
	    if (IsInp(k1) || Undef(*k1)) goto efail;
	    y = MolP(k1)->Env; k1 = MolP(k1)->Fn;
	    if ( i1 <= 0 ||
                     i1 > FunctorP(SkelP(k1)->Fn)->arityoffe)
		 goto efail;
	    k = argv(k1+i1,y,&y);
	    TRY(unifyarg(Addr(ARG3),k,y));
	case _univ:		/*  x=..l   b58 */
	    k = ARG1;
	    if (IsRef(k) && Undef(*k)) goto tcons;
	    k1 = v+2;
	    n = 2;
	    if (IsInp(k)) {
		*k1 = k;
		goto mklst;
	    }
	    y = MolP(k)->Env; k = MolP(k)->Sk;
	    *k1 = FunctorP(SkelP(k)->Fn)->atoffe;
	    i = FunctorP(SkelP(k)->Fn)->arityoffe;
	    n += i;
	    while (i-- > 0) {
		b = arg(++k,y);
		if (IsComp(b) && IsInp(b))
		    ConsMol(b,y,b);
		*++k1 = b;
	    }
	    mklst: *(k1+1) = atomnil;
	    k = makelist(n,v+2); v1 -= 2;
	    TRY(unifyarg(Addr(ARG2),MolP(k)->Sk,MolP(k)->Env));
	    tcons:
	    k = ARG2;
	    if (IsInp(k) || Undef(*k)) goto efail;
	    y = MolP(k)->Env; k = MolP(k)->Sk;
	    l = v+2; n = 0;
	    while (k != atomnil) {
		if (IsAtomic(k) ||
                    IsVar(k) || SkelP(k)->Fn != listfunc)
		    goto efail;
		if (n++ > 100) {
		    ErrorMess = "! Too many arguments in =..";
		    goto aborting;
		}
		k1 = arg(Addr(SkelP(k)->Arg1),y);
		if (IsComp(k1) && IsInp(k1))
		    ConsMol(k1,y,k1);
		*l++ = k1;
		k = argv(Addr(SkelP(k)->Arg2),y,&y);
	    }
	    k = *(v+2);
	    if (IsComp(k)) goto efail;
	    if (n == 1)
		TRY(unifyarg(Addr(ARG1),k,0));
	    if (IsPrim(k)) goto efail;
	    k = apply(k,n-1,v+3);
	    v1 -= 2;
	    TRY(unifyarg(Addr(ARG1),MolP(k)->Sk,MolP(k)->Env));
	case _asst1:		/* assert(c) */
	    TEST(record(CLAUSE,ARG1,0,FALSE),continuation,dbfail);
	case _assta1:		/* asserta(c) */
	    TEST(record(CLAUSE,ARG1,0,TRUE),continuation,dbfail);
	case _asst2:		/* assert(c,r) */
	    i1 = FALSE;
	    assertr:
	    k = record(CLAUSE,ARG1,0,i1);
	    y = &(ARG2);
	    unfref:
	    if (!k) goto dbfail;
	    k1 = XtrDBRef(k);
	    ClauseP(k1)->infofcl |= IN_USE;
	    TrailPtr(k);
	    TRY(unifyarg(y,k,0));
	case _assta2:		/* asserta(c,r) */
	    i1 = TRUE;
	    goto assertr;
	case _rcrda:		/* recorda(k,t,r) */
	    i1 = TRUE; goto recordr;
	case _rcrdz:		/* recordz(k,t,r) */
	    i1 = FALSE;
	    recordr:
	    k = record(RECORD,ARG2,ARG1,i1);
	    y = &(ARG3);
	    goto unfref;
	case _clause:		/* $clause(p,r,_) */
	    k = *fl;
	    fl = Addr(ClauseP(k)->altofcl);
	    *fl = k;
	    k = ARG3;
	    if (IsRef(k)) k = MolP(k)->Sk;
	    if ((FunctorP(SkelP(k)->Fn)->flgsoffe)&PROTECTED) goto cutfail;
	    ARG4 = Addr(FunctorP(SkelP(k)->Fn)->defsoffe);
	case _clause+1:
	    k = recorded(CLAUSE);
	    if (!k) goto cutfail;
	    TRY(instance(k,Addr(ARG1)));
	case _rcrded:		/* $recorded(t,r,k) */
	    k = *fl;
	    fl = Addr(ClauseP(k)->altofcl);
	    *fl = k;
	    k = ARG3; 
	    if (IsRef(k)) k = MolP(k)->Sk;
	    ARG4 = Addr(FunctorP(SkelP(k)->Fn)->dboffe);
	case _rcrded+1:
	    k = recorded(RECORD);
	    TEST(k,continuation,cutfail);
	dbfail:
	    fprintf(stderr,"\n%s\n",ErrorMess);
	    debug = TRUE; sklev = NEVER_SKIP;
	cutfail:
	    if (vv >= x) vv = X->lcpofcf;
	    goto efail;
	case _instance:		/* instance(r,t) */
	    k = instance(ARG1,&(ARG2));
	    if (!k) goto efail;
	    if (k == 1) goto continuation;
	    ErrorMess = 
            "! First argument of instance must be a reference";
	    goto dbfail;
	case _erase:		/* erase(r) */
	    TEST(erase(ARG1),continuation,dbfail);
	case _abolish:		/* abolish(a,n) */
	    TRY(IsAtomic(ARG1) && (!IsPrim(ARG1)) &&
		IsInt(ARG2) && (i = XtrInt(ARG2)) >= 0 &&
		    abolish(i == 0 ? ARG1 : fentry(ARG1,i)));
	case _erased:		/* erased(r) */
	    if ((i1 = erased(ARG1)) < 0) goto dbfail;
	    TRY(i1);
	case _NOLC:		/* 'NOLC' */
	    lc = FALSE;
	    goto continuation;
	case _LC:		/* 'LC' */
	lc = TRUE;
	goto continuation;
	case _trace:		/* trace */
	    debug = dotrace = TRUE;
	    goto continuation;
	case _op:		/* op(p,t,a) */
	    TRY(op(ARG1,ARG2,Addr(ARG3)));
	case _leash:		/* $leash(x,n) */
	    if (!unifyarg(Addr(ARG1),ConsInt(leash),0))
		goto efail;
	    leash = intval(Addr(ARG2));
	    goto continuation;
	case _debug:		/*  $debug(p,n) */
	    if (!unifyarg(Addr(ARG1),ConsInt(debug),0))
		goto efail;
	    spy = debug = intval(&(ARG2));
	    goto continuation;
	case _name:		/*  name(x,l) */
	    k = ARG1; 
	    if (IsRef(k) && Undef(*k)) goto namecons;
	    if (IsComp(k)) goto nameerr;
	    if (IsName(k)) bn = AtomP(k)->stofae;
	    else {
		if (!IsNumber(k)) goto nameerr; 
		if (IsInt(k))
		    sprintf(OutBuf,"%d",XtrInt(k));
		else
		    sprintf(OutBuf,"%f",XtrFloat(k));
		bn = OutBuf;
	    }
	    i = strlen(bn);
	    if (i > 0) {
		k1 = v+1; n = i+1;
		while (i-- > 0)
		    *++k1 = ConsInt(*bn++);
		goto mklst;
	    } else
		TRY(unifyarg(Addr(ARG2),atomnil,0));

	    namecons:
	    if (!list_to_string(ARG2,OutBuf,255)) goto nameerr;
	    bn = OutBuf;
	    if (NumberString(&bn,&k,FALSE)) {
		TRY(unifyarg(Addr(ARG1),k,0));
	    }
	    mkname:
	    TRY(unifyarg(Addr(ARG1),lookup(OutBuf),0));
	    nameerr:
	    ErrorMess = "! Illegal arguments name(atomic,list)";
	    goto dbfail;
	case _catom: /* current_atom(a) */
	    k = ARG1;
	    if (IsAtomic(k) && !IsPrim(k)) goto cut;
	    if (IsInp(k) || !Undef(*k)) goto cutfail;
	    ARG2 = 0; ARG3 = NULL;
	    fl = *fl; FL->altofcl = fl;
	case _catom+1:
	    GrowLocal(3);
	    i = ARG2; k1 = ARG3;
	    while (k1 == NULL) {
		if (i >= HASHSIZE) goto cutfail;
	    	k1 = *(hasha+i++);
	    }
	    ARG2 = i; ARG3 = AtomP(k1)->nxtofae;
	    unifyarg(Addr(ARG1),k1,0);
	    goto continuation;
	case _cfunctor:		/*  $current_functor(a,n,key,mask)
				    mode_(+,?,+,+) */
	    ARG5 = ARG1;
	    fl = *fl; FL->altofcl = fl;
	case _cfunctor+1:
	    GrowLocal(5);
	    k1 = ARG5;
	    nextfunc:
	    if (!k1) goto cutfail;
	    k = k1; k1 = FunctorP(k)->nxtoffe;
	    i = XtrInt(ARG3)&255;
	    if ((XtrInt(ARG4)&(FunctorP(k)->flgsoffe)) != i)
		goto nextfunc; 
	    if ((XtrInt(ARG3)&256) && !FunctorP(k)->defsoffe)
		goto nextfunc;
	    if (!unifyarg(Addr(ARG2),
                          ConsInt(FunctorP(k)->arityoffe),0))
		goto nextfunc;
	    ARG5 = k1;
	    goto continuation;
	case _flags:		/*  $flags(p,old,new) */
	    bn = &(SkelP(FunctorP(MolP(ARG1)->Sk)->Fn)->flgsoffe);
	    if (!unifyarg(Addr(ARG2),ConsInt(*bn),0)) goto efail;
	    *bn = (char)intval(&(ARG3));
	    goto continuation;

	case _compare:		/* compare(Op,T1,T2) */
	    i = compare(&(ARG2),&(ARG3));
	    k = (i < 0) ? LessThan : ((i > 0) ? GreaterThan : Equal);
	    goto unifyatom;

	case _alpLT:		/* T1 @< T2 */
	    TRY(compare(&(ARG1),&(ARG2)) < 0);
	    
	case _alpGT:		/* T1 @> T2 */
	    TRY(compare(&(ARG1),&(ARG2)) > 0);

	case _alpLE:		/* T1 @=< T2 */
	    TRY(compare(&(ARG1),&(ARG2)) <= 0);
	    
	case _alpGE:		/* T1 @>= T2 */
	    TRY(compare(&(ARG1),&(ARG2)) >= 0);
	case _all_float:		/* $all_float(x,y) */
	    if (!unifyarg(Addr(ARG1),ConsInt(AllFloat),0)) goto efail;
	    k = vvalue(Addr(ARG2),&l);
	    if (!IsPrim(k) || !IsInt(k)) goto efail;
	    AllFloat = XtrInt(k);
	    goto continuation;
	case _statistics:		/* statistics. */
	    Statistics();
	    goto continuation;

/*------------------------------------------------------------------

    system private predicates

------------------------------------------------------------------*/

	case _sysp:		/*  $sysp(f,n) */
	   FunctorP(SkelP(MolP(ARG1)->Sk)->Fn)->defsoffe =
		XtrInt(ARG2)&255;
	    goto continuation;
	case _sysflgs:		/*  $sysflgs(p,n) */
	    FunctorP(SkelP(MolP(ARG1)->Sk)->Fn)->flgsoffe =
		(char)XtrInt(ARG2);
	    goto continuation;
	case _hideat:		/*  $hide_atom(a) */
	    TRY((IsAtomic(ARG1) && (!IsPrim(ARG1)) &&
		 hide_atom(ARG1)));
	case _brk:		/* $break(g) a102 */
	    bg = arg(g+1,x1);
	    if (IsPrim(bg) || Undef(*bg)) goto efail;
	    if (IsComp(bg) && IsInp(bg)) ConsMol(bg,x1,bg);
	    breakret = CONT;
	enterbreak:
	    InStat = SaveStream(Input);
	    OutStat = SaveStream(Output);
	    savevars();
	    Output = STDOUT;
	    Input = STDIN;
	    pg = bg;
	    goto icall;
	case _exit_break:		/* $exit_break a103 */
	    popbreak();
	    RestStream(Input,InStat);
	    RestStream(Output,OutStat);
	    switch(breakret) {
		case CALL_PORT: goto brokencall;
		case EXIT_PORT: goto brokenexit;
		case BACK_PORT: goto brokenback;
		case FAIL_PORT: goto brokenfail;
		default: goto continuation;
	    }
	case _xprompt:		/* $prompt(p) b104 */
	    PromptIfUser(AtomP(ARG1)->stofae);
	    goto continuation;
	case _user_exec:		/* $user_exec(_) b105 */
	    c = ARG1;
	    if (IsPrim(c) || Undef(*c)) goto efail;
	    GrowLocal(1); lev = 1; invokno = 0;
	    if (debug) {
		spy = TRUE;
		if (dotrace) {
		    sklev = NEVER_SKIP;
		    dotrace = FALSE;
		} else sklev = 0;
	    } else sklev = 0;
	    execsys = FALSE;
	    goto continuation;
	case _save_vars:		/* $save_read_vars a106 */
	    vchain = varchain; pvrz = vrz; vrz = varfp;
	    goto continuation;
	case _reset_vars:		/* $reset_read_vars a107 */
	    vrz = pvrz;
	    goto continuation;
	case _repply:		/* $repply a108 */
	    if (!vchain) goto continuation;
	    {
		VarP var; int telling;

		telling = Output;
		Output = STDOUT;
		for (var = vchain; var; var = var->NextVar) {
		    Put('\n');
		    PutString(var->VarName); PutString(" = ");
		    k = vvalue(var->VarValue,&k1);
		    pwrite(k,k1,1200);
		}
		PutString(" ");
		Output = telling;
	    }
	    ch = ToEOL(0,0);
	    TRY(ch != ';' && ch != 'y' && ch != 'Y');
	case _recons:		/* $recons(_) b109 */
	    recons = XtrInt(ARG1);
	    goto continuation;
	case _brkstart:		/* $break_start a110 */
	    printf("[ Break (level %d) ]\n",++brklev);
	    goto continuation;
	case _brkend:		/* $break_end a111 */
	    printf("[ End break (level %d) ]\n",brklev--);
	    goto continuation;
	case _asstr:		/* $assertr(_) b112 */
	    k = record(CLAUSE,ARG1,recons,FALSE);
	    if (k) goto continuation;
	    fprintf(stderr,"\n%s\n",ErrorMess);
	    goto efail;
	case _isop:		/* $isop(_,_,_,_,_) */
	    TRY((IsAtomic(ARG1) && (!IsPrim(ARG1)) &&
		IsInt(ARG2) &&
	        isop(ARG1,XtrInt(ARG2),&i,&i1,&i2) &&
		unifyarg(Addr(ARG3),ConsInt(i),NULL) &&
		unifyarg(Addr(ARG4),ConsInt(i1),NULL) &&
		unifyarg(Addr(ARG5),ConsInt(i2),NULL)));
	case _RIP:		/* $rest_in_peace  a113 */
	    CloseFiles();
	    printf("\n[ Prolog execution halted ]\n");
	    exit(GOOD_EXIT);
	case _xrepeat:           /* b115  $repeat */
	    goto repeat;
	case _yes:		/* top level success in bootstrap */
	    ResetTrail(trbase);
	    goto mainloop;
	case _no:		/* top level failure in bootstrap */
	    PutString("no\n");
	    goto mainloop;
#ifdef GRAPHICS:
	case _graphics:
	    TRY(plgraphics());
#endif
	default:
	    fprintf(stderr,"\n! Undefined built-in predicate : %d\n",i);
	    goto efail;
    }
}
