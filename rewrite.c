/**********************************************************************
*                                                                     *
*                  C Prolog     rewrite.c                             *
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

#define Isatoz(a) ('a' <= (AtomP(a)->stofae)[1] && \
                          (AtomP(a)->stofae)[1] <= 'z')

#define PREFIX	0
#define INFIX	1
#define POSTFIX	2

/* decrease left priority flag */

#define dlprflg	0x2000

/* decrease rigth priority flag */

#define drprflg	0x1000

/* priority field */

#define mskprty 0x0fff

/* Character types for tokeniser */

#define UC	1		/* Upper case alphabetic */
#define UL	2		/* Underline */
#define LC	3		/* Lower case alphabetic */
#define N	4		/* Digit */
#define QT	5		/* Single quote */
#define DC	6		/* Double quote */
#define SY	7		/* Symbol character */
#define SL	8		/* Solo character */
#define BK	9		/* Brackets & friends */
#define BS	10		/* Blank space */

static char chtyp[] = {
/* nul soh stx etx eot enq ack bel  bs  ht  nl  vt  np  cr  so  si */
    BS, BS, BS, BS, BS, BS, BS, BS, BS, BS, BS, BS, BS, BS, BS, BS,

/* dle dc1 dc2 dc3 dc4 nak syn etb can  em sub esc  fs  gs  rs  us */
    BS, BS, BS, BS, BS, BS, BS, BS, BS, BS, BS, BS, BS, BS, BS, BS,

/*  sp   !   "   #   $   %   &   '   (   )   *   +   ,   -   .   /  */
    BS, SL, DC, SY, LC, SL, SY, QT, BK, BK, SY, SY, BK, SY, SY, SY,

/*  0   1   2   3   4   5   6   7   8   9   :   ;   <   =   >   ? */
    N,  N,  N,  N,  N,  N,  N,  N,  N,  N, SY, SL, SY, SY, SY, SY,

/*  @   A   B   C   D   E   F   G   H   I   J   K   L   M   N   O */
   SY, UC, UC, UC, UC, UC, UC, UC, UC, UC, UC, UC, UC, UC, UC, UC,

/*  P   Q   R   S   T   U   V   W   X   Y   Z   [   \   ]   ^   _ */
   UC, UC, UC, UC, UC, UC, UC, UC, UC, UC, UC, BK, SY, BK, SY, UL,

/*  `   a   b   c   d   e   f   g   h   i   j   k   l   m   n   o */
   SY, LC, LC, LC, LC, LC, LC, LC, LC, LC, LC, LC, LC, LC, LC, LC,

/*  p   q   r   s   t   u   v   w   x   y   z   {   |   }   ~  del */
   LC, LC, LC, LC, LC, LC, LC, LC, LC, LC, LC, BK, BK, BK, SY,  BS };

PTR term();


int
isop(atom,optype,p,lp,rp)
PTR atom; int optype, *p, *lp, *rp;
{
    short oe;

    switch (optype) {
	case PREFIX:
	    oe = AtomP(atom)->prfxofae;
	    break;
	case INFIX:
	    oe = AtomP(atom)->infxofae;
	    break;
	case POSTFIX:
	    oe = AtomP(atom)->psfxofae;
	    break;
	default:
	    return FALSE;
    }
    if (oe < 0) return FALSE;
    *p = oe&mskprty;
    *lp = !(oe&dlprflg) ? *p : *p-1;
    *rp = !(oe&drprflg) ? *p : *p-1;
    return TRUE;
}

op(prio,optype,spec)
PTR prio, optype, spec;
/*  processes op declarations */
{
    int c, i, pr, typ; PTR spf, at;
    static char
    *OpTypes[] = { "xfx", "xfy", "yfx",    "xf",    "yf",   "fx",   "fy" };
    static int
    optyp[] =    { INFIX, INFIX, INFIX, POSTFIX, POSTFIX, PREFIX, PREFIX };
    char *ops;

    if (!IsInt(prio)) return FALSE;
    pr = XtrInt(prio);
    if (pr > 1200 || pr <= 0) return FALSE;
    if (!IsAtomic(optype) || IsPrim(optype)) return FALSE;
    ops = AtomP(optype)->stofae;
    c = -1;
    for (i = 0;i < 7; i++)
	if (!strcmp(ops,OpTypes[i])) {
	    c = i;
	    break;
	}
    if (c < 0) return FALSE;
    typ = optyp[c];
    c = 1<<(c+1);
    if (c&0x16) pr |= dlprflg;
    if (c&0x4a) pr |= drprflg;
    spec = vvalue(spec,&spf);
    do {
	if (IsntName(spec) || IsRef(spec)) return FALSE;
	if (IsComp(spec)) {
	    if (SkelP(spec)->Fn != listfunc) return FALSE;
	    at = arg(Addr(SkelP(spec)->Arg1),spf);
	    if (IsntName(at) || IsRef(at)) return FALSE;
	    spec = argv(Addr(SkelP(spec)->Arg2),spf,&spf);
	} else
	    at = spec, spec = atomnil;
	switch (typ) {
	    case PREFIX:
		AtomP(at)->prfxofae = pr;
		break;
	    case INFIX:
		AtomP(at)->infxofae = pr;
		break;
	    case POSTFIX:
		AtomP(at)->psfxofae = pr;
	}
    } while (spec != atomnil);
    return TRUE;
}

static
legalatom(s)
char *s;
{
    char c;

    c = chtyp[*s];
    if (c == LC) {
	while (c = chtyp[*s], *s++) if (c > N) return FALSE;
	return TRUE;
    }
    if (c == SL) return (s[0] != '%' && !s[1]);
    if (c != SY) return FALSE;
    if (!strcmp(s,"/*") || !strcmp(s,".")) return FALSE;
    while (c = chtyp[*s], *s++) if (c != SY) return FALSE;
    return TRUE;
}

static
patom(at)
PTR at;
{
    char ch, *s;
    s = AtomP(at)->stofae;
    if (!quoteia || legalatom(s)) {
	PutString(s);
	return;
    }
    Put('\'');
    while ((ch = *s++)) {
	if (ch == '\'') Put(ch);
	Put(ch);
    }
    Put('\'');
}

/*  pwrite - write a prolog term  */

pwrite(t,g,p)
PTR t, g; int p;
/*  write term t in context of priority p
    with global frame g
*/
{
    int i, m, mr, ml; PTR ax, f, a;
    if (IsPrim(t)) {
	if (IsInt(t)) {
	    sprintf(OutBuf,"%d",XtrInt(t)); PutString(OutBuf);
	    return;
	}
	if (IsFloat(t)) {
	    sprintf(OutBuf,"%g",XtrFloat(t)); PutString(OutBuf);
	    return;
	}
	sprintf(OutBuf,"%x",t);
	PutString(OutBuf);
	return;
    }
    if (IsAtomic(t)) {
	patom(t);
	return;
    }
    if (Undef(*t)) {
	sprintf(OutBuf,"_%d",t-glb0); PutString(OutBuf);
	return;
    }
    if (IsRef(t))
	g = MolP(t)->Env, t = MolP(t)->Sk;
    if (SkelP(t)->Fn == listfunc) {
	Put('[');
	do {
	    ax = argv(Addr(SkelP(t)->Arg1),g,&a);
	    pwrite(ax,a,999);
	    t = argv(Addr(SkelP(t)->Arg2),g,&g);
	} while (IsComp(t) && (MolP(t)->Sk == listfunc) && (Put(','),TRUE));
	if (t != atomnil) {
	    Put('|');
	    pwrite(t,g,999);
	}
	Put(']');
	return;
    }
    if (MolP(t)->Sk == assertfunc) {
	Put('{');
	ax = argv(Addr(SkelP(t)->Arg1),g,&g); pwrite(ax,g,1200);
	Put('}');
	return;
    }
    f = SkelP(t)->Fn;
    i = FunctorP(f)->arityoffe;
    a = FunctorP(f)->atoffe;
    if (i == 1) {
	if (isop(a,PREFIX,&m,&ml,&mr)) {
	    if (m > p) Put('(');
	    patom(a);
	    if (Isatoz(a)) Put(' ');
	    ax = argv(Addr(SkelP(t)->Arg1),g,&f);
	    pwrite(ax,f,mr);
	    if (m > p) Put(')');
	    return;
	}
	if (isop(a,POSTFIX,&m,&ml,&mr)) {
	    if (m > p) Put('(');
	    ax = argv(Addr(SkelP(t)->Arg1),g,&f);
	    pwrite(ax,f,ml);
	    if (Isatoz(a)) Put(' ');
	    patom(a);
	    if (m > p) Put(')');
	    return;
	}  
    }
    if (i == 2 && isop(a,INFIX,&m,&ml,&mr)) {
	if (m > p) Put('(');
	ax = argv(Addr(SkelP(t)->Arg1),g,&f);
	pwrite(ax,f,ml);
	if (Isatoz(a)) Put(' ');
	patom(a);
	if (Isatoz(a)) Put(' ');
	ax = argv(Addr(SkelP(t)->Arg2),g,&f); pwrite(ax,f,mr);
	if (m > p) Put(')');
	return;
    }
    patom(a);
    Put('(');
    while (i-- > 0) {
	ax = argv(++t,g,&f); pwrite(ax,f,999);
	if (i > 0) Put(',');
    }
    Put(')');
    return;
}


/*-------------------------------------------------------------------

   pread - read a prolog term
   (this function has lots of auxiliary functions, which are listed first)

*/

static int e;

/* Token types */

#define NAME		1
#define PRIMITIVE	2
#define VAR		3
#define STRING		4
#define PUNCTUATION	5
#define FULLSTOP	6

static int retoken, tokentype, rechar, chtype, errflg;
static char *line, *lp, *lpmax, ch;
static char nam[255];
static PTR slsp;

union {
    PTR		AsPTR;
    char	AsChar;
    char *	AsString;
} tokeninfo;

/*  next character from input buffer (in read)
/*  allows for single char lookahead */

static char
nextch()
{
    if (rechar) {
	rechar = FALSE;
	return chtype;
    }
    chtype = chtyp[ch = *++lp];
    if (lp >= lpmax) lp = lpmax-2;
    return chtype;
}


/*  look up variable name in variable table (in read) */

PTR
lookupvar(id)
char *id;
{
    PTR p; VarP r, q; int l;

    if (!strcmp(id,"_")) {
	p = v1; *v1 = NULL; GrowGlobal(1);
	return p;
    }
    for (q = varchain, r = NULL; q; r = q, q = q->NextVar)
	if (!strcmp(q->VarName,id)) return q->VarValue;
    l = Words(sizeof(VarEntry)+strlen(id))+1;
    q = (VarP)varfp;
    varfp += l;
    HighTide(varfp,Auxtide);
    if (varfp > auxmax) NoSpace(AuxId);
    Unsafe();
    nvars++;
    if (r)
	r->NextVar = q;
    else
	varchain = q;
    strcpy(q->VarName,id);
    q->NextVar = NULL;
    q->VarValue = p = v1; *v1 = NULL;
    q->VarLen = l;
    Safe();
    GrowGlobal(1);
    return p;
}


/*  report a syntax error and wind things up (in read) */

static
SyntaxError()
{
    char *i;

    rechar = FALSE; retoken = FALSE;;
    if (errflg) {
	lp = lpmax-2;
	return;
    }
    fprintf(stderr,"\n***Syntax error***\n");
    for (i = line; i <= lpmax; i++) {
	if (i == lp)
	    fprintf(stderr,"\n**here**\n");
	putc(*i,stderr);
    }
    lp = lpmax-2; errflg = TRUE;
}


/*  token - tokeniser (in read) */

static int
token()
{
    int v, l;

    if (retoken) {
	retoken = FALSE;
	return tokentype;
    }
    start:
    switch (nextch()) {
	case BS: goto start;

	case UC:		/* uppercase letter */
	    v = lc; goto id;

	case UL:		/* underline */
	    v = 1; goto id;
	case LC:		/* lowercase letter */
	    v = 0;
	id: 		/* common to both variables and atoms */
	    rechar = TRUE; l = 0;
	    while (nextch() <= N) {
		if ((!lc) && (!v) && ch>='A' && ch<='Z') ch += 32;
		nam[l++]=ch;
	    }
	    nam[l] = 0;
	    rechar = TRUE;
	    if (v) {
		tokentype = VAR;
		tokeninfo.AsPTR = lookupvar(nam);
		return VAR;
	    }
	    tokentype = NAME;
	    tokeninfo.AsPTR = lookup(nam);
	    return NAME;
	case N: 	/* digit */
	    if (*(lp+1) == '\'') {
		lp++; v = ch-'0'; l = 0;
		while (nextch() == N)
		    l = l*v+ch-'0';
		tokeninfo.AsPTR = ConsInt(l);
		rechar = TRUE;
		return tokentype = PRIMITIVE;
	    }
	if (!NumberString(&lp,&tokeninfo.AsPTR,TRUE))
	    SyntaxError();
	    return tokentype = PRIMITIVE;
	case QT:		/* single quote */
	    v = QT; goto quoted;

	case DC:		/* double quote */
	    v = DC;
	quoted:
	    l = 0;
	    while (nextch() != v || nextch() == v) {
		nam[l++] = ch;
		if (l >= 228) SyntaxError();
	    }
	    nam[l] = 0;
	    rechar = TRUE;
	    if (v == QT) {
		tokentype = NAME; tokeninfo.AsPTR = lookup(nam);
		return NAME;
	    }
	    tokentype = STRING; tokeninfo.AsString = nam;
	    return STRING;

	case SY:		/* symbol char */
	    if (ch =='/' && *(lp+1) == '*') {
		do
		    chtype = nextch();
		while (ch != '*' || *(lp+1) != '/');
		lp++; goto start;
	    }
	    l = 1; nam[0] = ch;
	    if (ch == '.') {		/* full stop is a special case */
		if (nextch() == BS ) {
		    tokentype = FULLSTOP; lp--;
		    return FULLSTOP;
		}
		rechar = TRUE;
	    }
	    while (nextch() == SY)
		nam[l++] = ch;
	    nam[l] = 0;
	    rechar = TRUE;
	    tokentype = NAME; tokeninfo.AsPTR = lookup(nam);
	    return NAME;

	case SL:		/* solo char */
	    nam[0] = ch; nam[1] = 0;
	    tokentype = NAME; tokeninfo.AsPTR = lookup(nam);
	    return NAME;

	case BK:		/*  ponctuation char */
	    if (ch == '[' && *(lp+1) == ']') {
		tokentype = NAME; strcpy(nam,"[]"); lp++;
		if (atomnil)
		    tokeninfo.AsPTR = atomnil;
		else tokeninfo.AsPTR = lookup(nam);
		return NAME;
	    }
	    tokentype = PUNCTUATION; tokeninfo.AsChar = ch;
	    return PUNCTUATION;
    }
}		/* end of tokeniser */

/*  readargs - parse arguments of a term (in read) */

static PTR
readargs(atom)
PTR atom;
{
    PTR savelsp, e; int a;

    savelsp = lsp; a = 0;
    chtype = nextch();		/* pass over ( */
    do {
	*lsp++ = term(999); a++;
    } while (token() == PUNCTUATION && tokeninfo.AsChar == ',');
    if (tokentype != PUNCTUATION || tokeninfo.AsChar != ')')
	SyntaxError();
    e = apply(atom,a,savelsp);
    lsp = savelsp;
    return e;
}


/*  stringtolist - string to list of chars (in read) */

static PTR
stringtolist()
{
    PTR savelsp; int n; register char c, *l;

    if (nam[0]==0) return atomnil;
    savelsp = lsp;
    for (l = nam; c = *l; l++)
	*lsp++ = ConsInt(c);
    n = l-nam;
    *lsp = atomnil; lsp = savelsp;
    return makelist(n+1,savelsp);
}

/*  readlist - parse a prolog list (in read) */

PTR
readlist()
{
    PTR savelsp, e; int n;

    savelsp = lsp; n = 1;
    while (TRUE) {
	*lsp++ = term(999); n++;
	if (token() == PUNCTUATION && tokeninfo.AsChar == ',') {
	    if (token() == NAME && !strcmp(nam,"..")) {
		e = term(999);
		break;
	    }
	    else retoken = TRUE;
	}
	else {
	    if (tokentype == PUNCTUATION && tokeninfo.AsChar == '|')
		e = term(999);
	    else {
		e = atomnil; retoken = TRUE;
		}
	    break;
	}
    }
    *lsp = e; lsp = savelsp;
    return makelist(n,savelsp);
}


/* term - parse token stream to get term (in read) */

static PTR
term(n)
int n;
{
    int m, m1, ml, mr; PTR e[2], s;

    if (errflg) return NULL;
    m = 0;
    switch (token()) {
	case NAME:			/* a name */
	    if (*lp == '(') {
		e[0] = readargs(tokeninfo.AsPTR);
		break;
	    }
	    if (isop(tokeninfo.AsPTR,PREFIX,&m,&ml,&mr)) {
		e[0] = s = tokeninfo.AsPTR;
		if (token() == PUNCTUATION && 
                   (tokeninfo.AsChar != '(' &&
		    tokeninfo.AsChar != '{' &&
		    tokeninfo.AsChar != '[')
		    || tokentype == FULLSTOP) {
		    if (m > n) SyntaxError();
		    retoken = TRUE;
		    break;
		}
		retoken = TRUE;
		e[0] = term(mr);
		e[0] = (s == Minus && IsNumber(e[0])) ?
			(IsFloat(e[0]) ? ConsFloat(-(XtrFloat(e[0])))
				       : ConsInt(-(XtrInt(e[0])))) :
			apply(s,1,e);
		break;
	    }
	    e[0] = tokeninfo.AsPTR;
	    break;
	
	case PRIMITIVE:		/* a primitive type (already encoded) */
	    e[0] = tokeninfo.AsPTR;
	    break;
	    
	case VAR:			/* a variable */
	    e[0] = tokeninfo.AsPTR;
	    break;
	
	case STRING:			/* a string */
	e[0] = stringtolist();
	break;
	
	case PUNCTUATION:		/*  ponctuation char */
	    if (tokeninfo.AsChar == '(') {
		e[0] = term(1200);
		if (token() != PUNCTUATION || tokeninfo.AsChar != ')')
			SyntaxError();
		break;
	    }
	    if (tokeninfo.AsChar == '[') {
		e[0] = readlist();
		if (token() != PUNCTUATION ||
		    tokeninfo.AsChar != ']') SyntaxError();
		break;
	    }
	    if (tokeninfo.AsChar == '{') {
		e[0] = term(1200);
		if (token() != PUNCTUATION || tokeninfo.AsChar != '}')
		    SyntaxError();
		e[0] = apply(assertatom,1,e);
		break;
	    }
	
	case FULLSTOP:		/*  other poctuation chars or fullstop */
	    SyntaxError(); return NULL;

    }
    on:
    if (errflg) return NULL;
    if (token() == NAME) {
	if (isop(tokeninfo.AsPTR,INFIX,&m1,&ml,&mr)) {
	    if (m1 <= n && ml >= m) {
		s = tokeninfo.AsPTR;
		e[1] = term(mr);
		e[0] = apply(s,2,e);
		m = m1;
		goto on;
	    }
	}
	if (isop(tokeninfo.AsPTR,POSTFIX,&m1,&ml,&mr)) {
	    if (m1 <= n && ml >= m) {
		s = tokeninfo.AsPTR;
		e[0] = apply(s,1,e);
		m = m1;
		goto on;
	    }
	}
	retoken = TRUE;
	return e[0];
    }
    
    if (tokentype == FULLSTOP) {
	retoken = TRUE;
	return e[0];
    }
    if (tokentype != PUNCTUATION  ||
        tokeninfo.AsChar == '(' || tokeninfo.AsChar == '[') {
	SyntaxError();
	return NULL;
    }
    if (tokeninfo.AsChar == ',' &&  n >= 1000 && m <= 999) {
	e[1] = term(1000);
	e[0] = apply(commafunc,2,e);
	m = 1000;
	if (m < n) goto on;
	return e[0];
    }
    retoken = TRUE;
    return e[0];

}		/* end of term */


/* the read predicate */

PTR
pread()
{
    varchain = NULL; errflg = FALSE; nvars = 0;
    lpmax = line = CharP(lsp);
    slsp = lsp;
    
    loop:
    ch = Get();
    l1:
    chtype = chtyp[ch];
    if (chtype == BS) {
	do ch = Get(); while(chtyp[ch] == BS);
	*lpmax++ = ' ';
	goto l1;
    }
    if (ch == '%') {
	ch = Get();
	if (ch == '(') {
	    ch = '{'; goto l1;
	}
	if (ch == ')') {
	    ch = '}'; goto l1;
	}
	while (ch != '\n') ch = Get();
	goto loop;
    }
    *lpmax++ = ch;
    if (chtype == QT && lpmax-line > 1 && chtyp[*(lpmax-2)] == N)
	chtype = N;
    if (ch == '*' && lpmax-line > 1 && *(lpmax-2) == '/') {
	lpmax -= 2;
	ch = Get();
	do {
	    while (ch != '*') ch = Get();
	    ch = Get();
	    while (ch == '*') ch = Get();
	} while (ch != '/');
	goto  loop;
    }
    if ((CharP(vmax)) < lpmax) {
	fprintf(stderr,
	    "! Term too long to read (%d characters)\n",lpmax-CharP(lsp));
	Event(ABORT);
    }
    if (chtype == QT || chtype == DC) {
	do {
	    ch = Get(); *lpmax++ = ch;
	} while(chtyp[ch] != chtype);
	goto loop;
    }
    if (ch == '.' && lpmax-line >= 2 && chtyp[*(lpmax-2)] != SY) {
	ch = Get();
	if (chtyp[ch] == BS) goto end; else goto l1;
    }
    goto loop;
    
    end:
    *lpmax = '\n'; *(lpmax+1) = 0;
    lp = line-1;
    rechar = retoken = FALSE;
    lsp += Words(lpmax-line+1);
    e = term(1200);
    if (token() != FULLSTOP) SyntaxError();
    if (errflg) e = NULL;
/*  for (lp = line; lp <= lpmax; lp++) putchar(*lp); */
    lsp = slsp;
    return e;
}

int
NumberString(s,p,free)
/* Scans the string *s to see if it is a number. If yes, *p takes
   the constructed number, and TRUE is returned, otherwise FALSE.
   If free is FALSE, the number must reach the end of the string
   to be accepted. In all cases, *s is updated to point to the
   last character used for the number (oddity courtesy of nextch())
*/

char **s; PTR *p; int free;
{
    double d; int i; char *t, *u, c;
    
    u = t = *s;
    if (*t == '-' || *t == '+') t++;
    if (!digits(&t)) goto no;
    if (*t == '.') {
	t++;
	if (!digits(&t)) {
	    t--;
	    goto stop;
	}
    }
    if (!*t) goto yes;
    if (*t != 'e' && *t != 'E') goto stop;
    if (*++t == '-' || *t == '+') t++;
    if (!digits(&t)) goto no;
    yes:
    *s = t-1;
    c = *t;
    *t = ' ';
    sscanf(u,"%F",&d);
    *t = c;
    if (Narrow(d,&i))
	*p = ConsInt(i);
    else
	*p = ConsFloat(d);
    return TRUE;
    stop:
    if (free || !*t) goto yes;
    no:
    *s = t-1;
    return FALSE;
}

static
digits(s)
char **s;
{
    char *t;
    
    t = *s;
    if (chtyp[*t] != N) return FALSE;
    while (chtyp[*++t] == N);
    *s = t;
    return TRUE;
}
