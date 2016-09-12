/**********************************************************************
*                                                                     *
*                  C Prolog     sysbits.c                             *
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

/*
  Interface with Unix -- apart from trivial STDIO calls, other
  modules do not call Unix directly.
*/

#include "pl.h"
#include <errno.h>
#include <setjmp.h>
#include <signal.h>

#ifdef vms
#   include <types.h>
#   include "times.h"

#   define TIMESCALE (0.001)	/* 10 msec. per times() unit in VMS */

#else
#  include <sys/types.h>
#  include <sys/times.h>
/* #  include <sys/param.h> */
#   define HZ 	60

#   define TIMESCALE (1.0/HZ)	/* times() units in 1/HZ sec. */

#endif

#ifdef vms
  
#  include stdio
#  include ssdef
#  include descrip

#  define AsDEC10

#endif

#define READ	1
#define WRITE	2
#define DIR	3
#define PROT	4
#define LOCK	8
#define FREE	0

#define PromptSize	81

#define MaxFile	15
#define NSigs	16

#define SAFE	0
#define UNSAFE	1
#define ABORTED	2

#ifdef AsDEC10

/* end of file character -- ^Z to simulate DEC-10 Prolog */

#define	PlEOF	'\032'

#else

/* -1 to be like STDIO */

#define PlEOF (-1)

#endif

char PlPrompt[PromptSize];
static int NewLine, crit;
static int (*OldSignal[NSigs])();

typedef struct { jmp_buf buf; } JumpBuf;

JumpBuf	ZeroState;

extern int sys_nerr, PrologEvent;
extern char *sys_errlist[];

/* stream information */

FILE *File[MaxFile];
PTR FileAtom[MaxFile];
int FileStatus[MaxFile];

int Input, Output;		/* current I/O streams */

char OutBuf[256];		/* general purpose buffer */

InitIO()
{
    int i;
    
    for (i = 0; i < MaxFile; i++) {
	File[i] = NULL;
	FileAtom[i] = NULL;
	FileStatus[i] = FREE;
    }
    File[STDIN] = stdin;
    File[STDOUT] = stdout;
    File[STDERR] = stderr;
    FileStatus[STDIN] = READ|PROT;
    FileStatus[STDOUT] = WRITE|PROT;
    FileStatus[STDERR] = WRITE|PROT;
    FileAtom[STDIN] = FileAtom[STDOUT] = user;
    Input = STDIN; Output = STDOUT;
    NewLine = FALSE;
}

char *
AtomToFile(file)
PTR file;
{
    if (IsntName(file) || IsComp(file))
	IODie("Invalid file specification");
    return AtomP(file)->stofae;
}

int
See(file)
PTR file;
{
    int i;
    
    if (file == user)
	return Input = STDIN;
    for (i = 0; i < MaxFile; i++)
	if (FileAtom[i] == file) break;
    if (i >= MaxFile) {			/* not already open */
	i = CSee(AtomToFile(file));
	FileAtom[i] = file;
    }
    else if ((FileStatus[i]&DIR) != READ) {/* open but not right */
	if (i == Output)
	    Told();
	else
	    CClose(i);	    
	i = CSee(AtomToFile(file));
	FileAtom[i] = file;
    } else Input = i;
    return i;
}

int
Tell(file,mode)
PTR file; char *mode;
{
    int i;
    
    if (file == user)
	return Output = STDOUT;
    for (i = 0; i < MaxFile; i++)
	if (FileAtom[i] == file) break;
    if (i >= MaxFile) {			/* not already open */
	i = CTell(AtomToFile(file),mode);
	FileAtom[i] = file;
    }
    else if ((FileStatus[i]&DIR) != WRITE) {	/* open but not right */
	if (i == Input)
	    Seen();
	else
	    CClose(i);	    
	i = CTell(AtomToFile(file),mode);
	FileAtom[i] = file;
    } else Output = i;
    return i;
}

int
CSee(s)
char *s;
{
    return Input = COpen(s,"r",READ);
}

int
CTell(s, mode)
char *s, *mode;
{
    return Output = COpen(s,mode,WRITE);
}

static int
COpen(s,m,st)
char *s, *m; int st;
{
    int i;
    
    for (i = 0; i < MaxFile; i++)
	if (FileStatus[i] == FREE) break;
    if (i >= MaxFile)
	IODie("Too many open files");
    if (!(File[i] = fopen(s,m)))
	IOError();
    FileStatus[i] = st;
    return i;
}

Seen()
{
    int inp;

    CClose(Input);
    Input = STDIN;
}

Told()
{
    if (Output == STDOUT || Output == STDERR) return;
    CClose(Output);
    Output = STDOUT;
}

PClose(file)
PTR file;
{
    int i;

    if (file == user) return;
    for (i = 0; i < MaxFile; i++)
	if (FileAtom[i] == file) {
	    CClose(i);
	    if (Input == i)
		Input = STDIN;
	    else if (Output == i)
		Output = STDOUT;
	    break;
    }
}

CloseFiles()
{
int i;

    for (i = 0; i < MaxFile; i++)
	if (!(FileStatus[i]&PROT) && (FileStatus[i]&DIR)) {
	    CClose(i);
	    if (Input == i)
		Input = STDIN;
	    else if (Output == i)
		Output = STDOUT;
	}
}

static
CClose(i)
int i;
{
    if (!(FileStatus[i]&PROT)) {
	fclose(File[i]);
	FileStatus[i] = FREE;
	File[i] = NULL;
	FileAtom[i] = NULL;
    } else clearerr(File[i]);
}

PTR
Seeing()
{
    return FileAtom[Input];
}

PTR
Telling()
{
    return FileAtom[Output];
}

SetPlPrompt(s)
char *s;
{
    if (s) strncpy(PlPrompt,s,PromptSize-1);
    PlPrompt[PromptSize-1] = 0;
}

Put(c)
char c;
{
    if (Output == STDOUT) NewLine = (c == '\n');
    putc(c,File[Output]);
}

PutString(s)
char *s;
{
    register char c;

    while (c = *s++) Put(c);
}

char
Get()
{
int c;

    if (feof(File[Input])) {
	Seen();
	Event(END_OF_FILE);
}
    if (NewLine)
	PromptIfUser(PlPrompt);
    c = getc(File[Input]);
    if (c == EOF) c = PlEOF;
    else if (Input == STDIN) NewLine = (c == '\n');
    return c;
}

Prompt(s)
char *s;
{
    fputs(s,stdout);
    fflush(stdout);
    NewLine = FALSE;
}

PromptIfUser(s)
char *s;
{
    if (Input == STDIN)
	Prompt(s);
}

char
ToEOL(reply,count)
register char *reply; int count;
{
    char c0, c;
    
    while ((c0 = getchar()) <= ' ' && c0 != '\n');
    c = c0;
    while (c0 != '\n') {
	c0 = getchar();
	if (reply && --count>0) *reply++ = c0;
    }
    if (reply) *reply = '\0';
    if (c >= 'A' && c <= 'Z') c += 'a'-'A';
    return c;
}

Exists(s)
char *s;
{
    return (access(s,0) == 0);
}

Rename(f1,f2)
char *f1, *f2;
{
int r;
#ifdef unix
    if ((r = link(f1,f2)) == 0) {
	if ((r = unlink(f1)) != 0)
	    unlink(f2);
    }
#endif
#ifdef vms
    fprintf(stderr,"! Rename not supported in this version of CProlog\n");
    r = -1;
#endif
    if (r) IOError();
}

Remove(f)
char *f;
{
#ifdef unix
    if (unlink(f) != 0)
        IOError();
#endif
#ifdef vms
    if (delete(f) !=0)
	IOError();
#endif
}

/* create stacks */

CreateStacks()
{
    char *r;
    int i, s = 0; 

    for (i = 0; i < NAreas; i++)
	s += Size[i];
    if ((r = malloc(s)) == NULL) {
	perror("Prolog");
	exit(BAD_EXIT);
    }
    for (i = 0; i < NAreas; i++) {
	Origin[i] = (PTR)r;
	r += Size[i];
    }
    Origin[NAreas] = r;
    atmax = auxstk0-100;
    auxmax = trbase-1;
    trmax = skel0-1;
    hpmax = glb0-100;
    v1max = lcl0-500;
    vmax  = ((PTR)r)-500;
}
    
/* Signals and events */
    
Event(n)
int n;
{
    if (State[TRACE])
	fprintf(stderr,"\n Prolog event %d\n",n);
    if (!running) {
	if (errno)
	    perror("Prolog");
	fputs("\nError while starting up Prolog -- cannot continue\n",stderr);
	exit(BAD_EXIT);
    }
    if (crit != SAFE) {
	fprintf(stderr,"%s\n",OutBuf);
	fputs("\nCan't recover from this error - bye\n",stderr);
	Stop(State[DEBUG]);
    }
    PrologEvent = n;
    Unwind();
}

/* Signals */

TakeSignal(s)
int s;
{
    if (State[TRACE])
	fprintf(stderr,"\nSignal %d\n");
    switch (s) {
	case SIGINT:
	    Interrupt();
	    break;
	case SIGQUIT:
	    Stop(FALSE);
	case SIGFPE:
	    signal(SIGFPE,TakeSignal);
	    ArithError("Floating point exception");
	case SIGSEGV:
	    NoSpace(-1);
	default:
	    fprintf(stderr,"\nUnexpected signal: %d\n",s);
	    Stop(TRUE);
    }
}

Stop(dump)
int dump;
{
    if (dump || State[DEBUG]) {
	fputs("\nDisaster! Dumping core...\n",stderr);
	abort();
    }
    exit(GOOD_EXIT);
}

Safe()
{
    if (crit == ABORTED) {
	crit = SAFE;
	Event(ABORT);
    }
    crit = SAFE;
}


Unsafe()
{
    crit = UNSAFE;
}

Interrupt()
{
    while (TRUE) {
	Prompt("Action (h for help): ");
	switch(ToEOL(0,0)) {
	    case 'a':
		if (crit == SAFE)
		    Event(ABORT);
		crit = ABORTED;
		goto cont;
	    case 't':
		debug = TRUE;
		sklev = 1000000;
		goto cont;
	    case 'd':
		debug = TRUE;
		goto cont;
	    case 'h':
		puts("a\tabort\nc\tcontinue\nd\tdebug\nt\ttrace\n");
		break;
	    case 'c':
		goto cont;
	    default:
		puts("Unknown option\n");
	}
    }
    cont:
    signal(SIGINT,TakeSignal);
}

PTR
NoSpace(s)
int s;
{
    char *n;

    n = (s >= 0 && s < NAreas) ?  AreaName[s] : "?";
    sprintf(OutBuf,"\n! Out of %s during execution\n",AreaName[s]);
    ErrorMess = OutBuf;
    Event(GEN_ERROR);
    return NULL;
}


CatchSignals()
{
    signal(SIGINT,TakeSignal);
    signal(SIGFPE,TakeSignal);
/*  signal(SIGSEGV,TakeSignal);    
    signal(SIGBUS,TakeSignal); */
} 

/* Emergency exit */

Unwind()
{
    longjmp(ZeroState.buf,1);
}

/* Errors */

static IOError()
{
    IODie(SysError());
}

static
IODie(s)
char *s;
{
    ErrorMess = s;
    Event(IO_ERROR);
}

char *
SysError()
{
    return errno < sys_nerr ? sys_errlist[errno] : "Unknown Unix error";
}

int
Sh()
{
#ifndef vms
    char *shell; int p;
    if (!(shell=getenv("SHELL")))
	shell = "/bin/sh";
    if ((p=fork())==0) {
    	if (execl(shell,shell,0)<0)
	    return FALSE;
    } else if (p<0) return FALSE;
    wait(0);
    return TRUE;
#else
    return lib$spawn();
#endif
}

int
CallSystem(cmd)
PTR cmd;
{
    char command[256];
#ifdef vms
    struct dsc$descriptor_s s_d;
#endif

    if (!list_to_string(cmd,command,255))
	return FALSE;
#ifdef unix
    return !system(command);
#else
#ifdef vms
    s_d.dsc$w_length	= strlen(command);
    s_d.dsc$b_dtype	= DSC$K_DTYPE_T;
    s_d.dsc$b_class	= DSC$K_CLASS_S;
    s_d.dsc$a_pointer	= command;
    return lib$spawn(&s_d);
#endif
#endif
}

suspend()
{
    signal(SIGINT,SIG_DFL);
    kill(0,SIGINT);
    signal(SIGINT,TakeSignal);
}

float
CPUTime()
{
    struct tms Time; float t;

    times(&Time);
    t = Time.tms_utime;
    return t*TIMESCALE;
}

int
SaveStream(stream)
int stream;
{
    int oldstate;

    if (!((oldstate = FileStatus[stream])&PROT))
	FileStatus[stream] |= PROT|LOCK;
    return oldstate;
}

RestStream(stream,oldstate)
int stream, oldstate;
{
    FileStatus[stream] = oldstate;
}

ResetStreams()
{
	register int stream;

	for (stream = 0; stream < MaxFile; stream++)
	    if (FileStatus[stream]&LOCK)
		FileStatus[stream] &= ~(LOCK|PROT);
}
