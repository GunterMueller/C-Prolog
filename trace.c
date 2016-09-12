#include "pl.h"
#include "trace.h"

static char *portname[] = {
    "Call: ", "Exit: ", "Back to: ", "Fail: "
};

int trace(frame,goal,goalenv,info,port)
PTR frame, goal, goalenv; unsigned info; int port;
{
    PTR realx = x, realx1 = x1, target;
    char flags, arg[10];
    int level, telling, iarg;

    level = Level(info);
    x = goalenv;
    x1 = X->gsofcf;
    if (IsRef(goal))
	 x1 = MolP(goal)->Env, goal = MolP(goal)->Sk;
    flags = FunctorP(SkelP(goal)->Fn)->flgsoffe;
    if (port == CALL_PORT) {
	if (dotrace) {
	    dotrace = FALSE;
	    sklev = NEVER_SKIP;
	}
	FrameP(frame)->infofcf = info;
    }
    if ((level > sklev-(port==BACK_PORT) && !(spy && (flags&SPY_ME))) ||
        (flags&(INVISIBLE|UNTRACEABLE))) {
	x = realx; x1 = realx1;
	return NORMAL;
    }
    message:
    if (flags&SPY_ME) putchar('*'); else putchar(' ');
    if (level == sklev) putchar('>'); else putchar(' ');
    printf(" (%d) %d %s",InvNo(info),level,portname[port-1]);
    telling = Output;
    Output = STDOUT;
    pwrite(goal,x1,999);
    if (!(leash&(1<<(4-port)))) {	
	Put('\n');
	Output = telling;
	x = realx; x1 = realx1;
	return NORMAL;
    } else PutString(" ? ");
    Output = telling;
    switch (ToEOL(arg,10)) {
	case '\n':
	case  'c':	/* creep */
	    sklev = NEVER_SKIP; spy = FALSE;
	    break;
	case 'l':	/* leap */
	    sklev = 0; spy = TRUE;
	    break;
	case 's':	/* skip */
	    if (port == EXIT_PORT || port == FAIL_PORT) goto notapp;
	    sklev = level; spy = FALSE;
	    break;
	case 'q':	/* quasi-skip */
	    if (port == EXIT_PORT || port == FAIL_PORT) goto notapp;
	    sklev = level; spy = TRUE;
	    break;
	case 'r':	/* retry */
	    spy = FALSE; sklev = NEVER_SKIP;
	    if (sscanf(arg,"%d",&iarg) == 1
             && iarg != InvNo(info)
	     && (target = findinv(iarg,frame,vv)) != frame) {
		fprintf(stderr,"[** JUMP **]\n");
		failto(target); 	/* long retry */
	    } else {
		fprintf(stderr,"[ retry ]\n");
		if (port != EXIT_PORT) {
		    x = realx;
		    x1 = realx1;
		    lev = level;
		    invokno = InvNo(info);
		    if (port == BACK_PORT)
			vv = VV->lcpofcf; /* this is essential !!! */
		} else failto(frame); /*  fail to frame */
	    }
	    invokno--;		/* the Call port increments this again */
	    return ICALL;
	case 'f':	/* fail */
	    if (port == FAIL_PORT) goto notapp;
	    x = realx;
	    x1 = realx1;
	    lev = level;
	    invokno = InvNo(info);
	    if (port == EXIT_PORT) failto(frame);
	    else if (port == BACK_PORT) vv = VV->lcpofcf; /* essential */
	    spy = FALSE; sklev = NEVER_SKIP;
	    return EFAIL;
	case 'a':	/* abort */
	    return ABORTING;
	case 'b':	/* break */
	    x = realx;
	    x1 = realx1;
	    breakret = port; bg = breakat;
	    return BREAK;
	case '[':	/* consult user */
	    x = realx;
	    x1 = realx1;
	    breakret = port; ConsMol(CsltUser,x1,bg);
	    return BREAK;
	case 'g':       /* backtrace */
	    backtrace(x);
	    goto message;
	case 'e':
	    suspend();
	    goto message;
	default:
	    printf("Unknown option; these are the known ones: ");
	case 'h':
	    puts("\
\n<cr>  creep           a  abort\
\nc     creep           f  fail\
\nr	retry		r <n> retry call <n>\
\nl     leap            b  break\
\ns     skip            h  help\
\nq     quasi-skip      n  nodebug\
\ng     goal stack      [  consult user\
\ne	exit Prolog\n");
	    goto message;
	case 'n':	/* turn debug mode off */
	    debug = FALSE;
	    break;
    }
    x1 = realx1; x = realx;
    return NORMAL;

    notapp:
    printf("Option not applicable at this port\n");
    goto message;
}

int
clausenumber(fr)
PTR fr;
{
    PTR g, cp, np, onp, fp; int pos = 1;

    g = FrameP(fr)->gofcf;
    if (!IsInp(g)) g = MolP(g)->Sk;
    cp = FunctorP(SkelP(g)->Fn)->defsoffe;
    fp = fr->altofcf; onp = NULL;
    for (;(np = Addr(ClauseP(cp)->altofcl)) != fp; cp = *np) {
	if (!*np) return 0;
	if (onp == np) return 0;
	onp = np;
	if (!Erased(cp)) pos++;
    }
    return pos;
}

backtrace(fr)
PTR fr;
{ PTR ofr, frg, fre, out, oldx; unsigned info; int clno;

    oldx = x; ofr = NULL;
    out = Output; Output = STDOUT;
    for (; fr != ofr; fr = x) {
	ofr = fr;
	x = fr->gfofcf;
	info = fr->infofcf;
	if (info== (PRIM_TAG|NUM_TAG)) continue;
	frg = fr->gofcf;
	if (IsInp(frg))
	    fre = x->gsofcf;
	else {
	    fre = MolP(frg)->Env; frg = MolP(frg)->Sk;
	}
	printf("%4d (%d)->",Level(info),InvNo(info));
        clno = clausenumber(fr);
	if (clno)
	    printf("%d: ",clno);
	else
	    printf("?: ");
	pwrite(frg,fre,999);
	printf("\n");
    }
    x = oldx;
    Output = out;
}

/* scanstack(frame,choice,fun,all) scans stack frames backwards from frame
   and last choice point choice calling fun with each as an argument until
   fun returns TRUE or the stack for the current execution is exhausted.
   If all is true, the entire stack is scanned; otherwise, only the stack
   since the last breakpoint.
   Return the last frame scanned or 0 if stack exhausted.
*/

PTR
scanstack(frame,choice,fun,all)
FRAME *frame, *choice; int (*fun)();
{
    register FRAME *alt, *par; int result;
    
    par = frame;
    alt = choice;
    while ((alt != FrameP(alt->lcpofcf)) &&
            (all || (PTR)alt > brkp)) {
	while (par > alt) {
	    if ((*fun)(par)) return (PTR)par;
	    par = FrameP(par->gfofcf);
	}
	if((*fun)(alt)) return (PTR)alt;
	par = FrameP(alt->gfofcf);
	alt = FrameP(alt->lcpofcf);
    }
    return (PTR)0;
}

/* findinv(invno,frame,choice) finds the most recent user frame with
   invocation number =< invno in the current execution (that is, it
   does not search past break points). If no such frame is found,
   findinv returns the oldest user frame in the execution.
*/

static PTR theframe;
static int target;

static
invoked(frame)
FRAME *frame;
{
    unsigned int info = frame->infofcf; int frameno;

    if (SysFrame(info)) return FALSE;
    theframe = frame;
    frameno = InvNo(info);	/* helps debugging */
    return frameno <= target;
}

PTR
findinv(invno,frame,choice)
int invno; FRAME *frame, *choice;
{
    PTR found;
    
    target = invno;
    theframe = frame;
    found = scanstack(frame,choice,invoked,FALSE);
    return (found ? found : theframe);
}

/* failto(frame) simulates a failure back to frame. */   

static failto(frame)
PTR frame;
{ register PTR p; register char *flagp; unsigned info;

    v = frame;
    x = V->gfofcf;
    v1 = V->gsofcf;
    x1 = X->gsofcf;
    vv = V->lcpofcf;
    vv1 = VV->gsofcf;
    pg = V->gofcf;
    c = V->cofcf;
    info = V->infofcf;
    lev = Level(info);
    invokno = InvNo(info);
    execsys = SysFrame(info);
    tr0 = V->trofcf;
    while (tr != tr0) { 
	p = *--tr;
	if (IsRef(p)) *p = NULL;
	else {
	    flagp = &(ClauseP(XtrDBRef(p))->infofcl);
	    if (!((*flagp)&ERASED)) *flagp &= ~IN_USE;
	    else hide(p);
	}
    }
}
