/**********************************************************************
*                                                                     *
*                  C Prolog     dbase.c                               *
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

#define Twice 1
#define OnHead 2
#define OnBody 4
#define Global 8

extern int InBoot;

static PTR vid[MAX_VAR+2], vn[MAX_VAR+2];
static int nvars, lev, nt, nl, ng, toomany, refsflg, onhead;
static PTR i, f, g, k, r, head, body, argx;

static int
LookVar(vi)
PTR vi;
/* lookup a variable */
{
    int i;
    
    for (i = 0; i < nvars; i++)
	if (vid[i] == vi) return i;
    if (nvars > MAX_VAR) {
	toomany = TRUE;
	return MAX_VAR;
    }
    vid[nvars] = vi; vn[nvars] = 0;
    return nvars++;
}

PTR
heapify(t,g)
PTR t, g;
{
    int n; PTR p1, p3, f; unsigned p2;
    if (IsPrim(t) && IsDBRef(t)) /* if database reference */
	XtrDBRef(t)->refcofcl++; /* increment ref count of refed term */
    if (IsAtomic(t))
	return t;		/* nothing to store for atomic terms */
    if (Undef(*t)) {		/* if variable */
	n = LookVar(t);		/* look it up in variable table */
	p2 = vn[n];		/* get variable properties */
	if (p2)			/* if previously used */
	    p2 |= Twice;	/* mark as multiple occurrence */
	if (onhead)		/* if processing clause head */
	    p2 |= OnHead;	/* mark as such */
	else
	    p2 |= OnBody;	/* else mark as body variable */
	if (lev > 1)		/* if not at outer level */
	    p2 |= Global;	/* mark as global */
	    vn[n] = p2;		/* store updated properties */
	    p2 = SkelGlobal(n);	/* make variable prototype (global n) */
	    if ((!lev) && !onhead) { /* handle variable goal */
		p1 = getsp(SkelSz(1)); /* by converting into call(X) */
		SkelP(p1)->Fn = calltag; SkelP(p1)->Arg1 = p2;
		return p1;
	    }
	return p2;		/* return variable prototype */
    }
    if(IsRef(t))		/* compound term */
	g = MolP(t)->Env, t = MolP(t)->Sk;	/* extract skel and env */
    n = FunctorP(*t)->arityoffe;	/* arity of functor */
    p1 = getsp(SkelSz(n));		/* make term vector */
    SkelP(p1)->Fn = SkelP(t)->Fn; p3 = Addr(SkelP(p1)->Arg1); lev++;
    for (; n>0; n--)	/* do term arguments */
	argx = argv(++t,g,&f), *p3++ = heapify(argx,f);
    lev--;
    return p1;			/* return heapified term */
}

PTR
heapifybody(t,g)
PTR t, g;
{
    PTR p1, f;

    if (IsAtomic(t) || Undef(*t))
	return heapify(t,g);
    if (IsRef(t))
	g = MolP(t)->Env, t = MolP(t)->Sk;
    if (SkelP(t)->Fn == commatag) {
	p1 = getsp(SkelSz(2));
	SkelP(p1)->Fn = commatag;
	argx = argv(Addr(SkelP(t)->Arg1),g,&f);
	SkelP(p1)->Arg1 = heapify(argx,f);
	argx = argv(Addr(SkelP(t)->Arg2),g,&f);
	SkelP(p1)->Arg2 = heapifybody(argx,f);
	return p1;
    }
    return heapify(t,g);
}

static
scan(c)
PTR c;
{
    int n;

    if (IsVar(*c)) {
    *c = *CellP(CharP(vn)+VarNo(*c));
	return;
    }
    if (IsAtomic(*c))
	return;
    c = *c; n = FunctorP(SkelP(c)->Fn)->arityoffe;
    for (; n > 0; n--)
	scan(++c);
}
PTR
record(key, t, rk, aorz)
PTR t, rk; int key, aorz;
{
    int j; PTR proclist;

    nvars = 0; toomany = FALSE; refsflg = FALSE;
    if(IsRef(t) && !Undef(*t))
	g = MolP(t)->Env, t = MolP(t)->Sk;
    if (key == RECORD)
	goto dbase;
    /* asserting a clause */
    lev = 0; onhead = TRUE;
    if (IsComp(t) && (SkelP(t)->Fn == arrowtag)) {
	argx = argv(Addr(SkelP(t)->Arg1),g,&f), head = heapify(argx,f);
	onhead = FALSE;
	argx = argv(Addr(SkelP(t)->Arg2),g,&f), body = heapifybody(argx,f);
    } else {
	head = heapify(t,g);
	body = NULL;
    }
    if (IsVar(head)) {
	ErrorMess ="! Clause head is a variable (assert)";
	goto errorexit;
    }
    if (IsPrim(head)) {
	ErrorMess = "! Clause head is an integer (assert)";
	goto  errorexit;
    }
    if (IsPrim(body) && !InBoot) {
	ErrorMess = "! Clause body is an integer (assert)";
	goto errorexit;
    }
    r = SkelP(head)->Fn;
    if ((FunctorP(r)->flgsoffe)&RESERVED) {
	ErrorMess = "! Attempt to redefine a system predicate";
	goto errorexit;
    }
    if (rk && (!toomany) && !refsflg) {
	/* reconsulting */
	for (proclist = vra; proclist < vrz; proclist++)
	    if(*proclist == r) goto found;
	abolish(r);
	*vrz++ = r;
	HighTide(vrz,Auxtide);
	if (vrz > auxmax) NoSpace(AuxId);
    }
    found: rk = r;

    goto insert;

    dbase:  /* inserting a item on the data base */
    if (IsRef(rk)) {
	rk = *rk;
	if(IsComp(rk))
	    rk = SkelP(rk)->Fn;
    }
    if (IsntName(rk) || IsRef(rk)) {
	ErrorMess = "! Illegal key (record)";
	return NULL;
    }
    head = rk;
    lev = 2;
    body = heapify(t,g);

    insert:
    if (toomany) {
	ErrorMess = "! Too many variables in term or clause being recorded";
	goto errorexit;
    }
    if (refsflg) {
	ErrorMess = "! Term or clause being recorded contains references";
	goto errorexit;
    }
    r = getsp(szofcl);
    Unsafe();
    ClauseP(r)->hdofcl = head; ClauseP(r)->bdyofcl = body;
    ng = nl = nt = 0;
    for (j = 0; j < nvars; j++)
	if (Unsigned(vn[j])&Global)
	    vn[j] = SkelGlobal(ng++);
	else if (OnBody&Unsigned(vn[j]))
	    vn[j] = SkelLocal(nl++);
	else vn[j] = ((PTR)0)+nt++;
    if (nt > 0) {
	k = SkelLocal(nl);
	for (j = 0; j < nvars; j++)
	    if (Unsigned(vn[j]) < 1024)
		vn[j] = Unsigned(k)+Unsigned(vn[j]);
    }
    ClauseP(r)->altofcl = ClauseP(r)->prevofcl = NULL;
    ClauseP(r)->infofcl = 0;
    ClauseP(r)->ltofcl = nl+nt;
    ClauseP(r)->lvofcl = nl;
    ClauseP(r)->gvofcl = ng;
    if (body)
	scan(&body);
    if (key == CLAUSE)
	scan(&head);
    rk = key == CLAUSE ? &(FunctorP(rk)->FClauses)
                       : &(FunctorP(rk)->FRecords);

    if (aorz) {			/* store at the beginning */
	r->prevofcl = NULL;
	r->altofcl = rk->First;
	if (rk->First)
	    rk->First->prevofcl = r;
	rk->First = r;
	if (!(rk->Last))
	    rk->Last = r;
    } else {			/* store at the end */
	r->prevofcl = rk->Last;
	r->altofcl = NULL;
	if (rk->Last)
	    rk->Last->altofcl = r;
	rk->Last = r;
	if (!(rk->First))
	    rk->First = r;
    }
    Safe();
    return ConsDBRef(r,key);
    errorexit:
    Safe();
    freeterm(head);
    freeterm(body);
    return NULL;
}

int
erased(r)
PTR r;
{
    PTR c;

    if (!IsDBRef(r)) {
	ErrorMess = "! Erased argument is not a reference";
	return -1;
    }
    c = XtrDBRef(r);
    return((ClauseP(c)->infofcl&ERASED) != 0);
}

erase(r)
PTR r;
/* erase term pointed by reference r */
{
    int key; PTR c, d;

    if (!IsDBRef(r)) {
	ErrorMess = "! Erase argument is not a reference";
	return FALSE;
    }
    key = DBType(r);
    c = XtrDBRef(r);
/*    fprintf(stderr,"Erasing: %c %x\n",key ? 'R' : 'C',c); */
    if (ClauseP(c)->infofcl&ERASED) return TRUE;
    d = ClauseP(c)->hdofcl;
    if (key == CLAUSE)
	d = SkelP(d)->Fn;
    if ((FunctorP(d)->flgsoffe)&RESERVED) {
	ErrorMess = "! Attempt to erase a system object";
	return FALSE;
    }
    ClauseP(c)->infofcl |= ERASED;
    if (!InUse(c)) unchain(r);
/* At this point, if c is idle it will have been unchained, so there
   will be no junk in the chain if we dispose of it */
    if (Idle(c)) {
	dispose(c);
/*	fprintf(stderr,"Gone\n"); */
    }
    return TRUE;
}

/* release space occupied by source term c */

freeterm(c)
PTR c;
{
    int n, k; PTR p;

/* c may be 0, in which case it will be caught by IsAtomic below */

    if (IsPrim(c) && IsDBRef(c)) {
	p = XtrDBRef(c);
	if (--RC(p) == 0 && Erased(p) && !InUse(p))
/* If these conditions are true, p will no longer be in a chain,
   because it will have been removed either by erase or by hide when
   untrailing
*/
	    dispose(p);
	return;
    }
    if (IsAtomic(c) || IsVar(c) || IsAtomic(*c))
	return;
    k = FunctorP(SkelP(c)->Fn)->arityoffe;
    for (p = c, n = k; n>0; n--)
	freeterm(*++p);
    freeblock(c,k+1);
}

/* unchain(p), where p is a database reference, removes the record
   or clause referred to by p from its backtracking CHAIN.
   Unchain is only called for things that are not in use 
   (either when they are erased or on backtracking by hide).
*/
unchain(p)
PTR p;
{
    PTR c, r;
    int key;

    c = XtrDBRef(p);
    key = DBType(p);
    r = ClauseP(c)->hdofcl;
    if (key == CLAUSE)
	r = SkelP(r)->Fn;
			/* Choose chain header */
    r = key == CLAUSE ? Addr(FunctorP(r)->FClauses)
                      : Addr(FunctorP(r)->FRecords);
    Unsafe();
    if (c->prevofcl)
	c->prevofcl->altofcl = c->altofcl;
    else 			/* first in chain */
	r->First = c->altofcl;
    if (c->altofcl)		/* not last in chain */
	c->altofcl->prevofcl = c->prevofcl;
    else			/* last in chain */
	r->Last = c->prevofcl;
    Safe();
}

/* dispose(c), where c is the address of a clause (record) gets rid
   of the space occupied by the clause; freeterm will recover the
   space used by the terms, and update reference counts of clauses
   (records) pointed to from those terms, possibly causing recursive
   calls to dispose.
*/
dispose(c)
PTR c;
{
    freeterm(ClauseP(c)->bdyofcl);
    freeterm(ClauseP(c)->hdofcl);
    freeblock(c,szofcl);
}

/* hide(r), where r is a database reference, is called when an ERASED
   object leaves the in-use state (on backtracking).
   First, the IN_USE flag is reset.
   At this point, we
   know that the object's backtrack chain is not being used.
   If the object is idle at this point, we can dispose of it.
*/
hide(r)
PTR r;
{
    PTR c;

    c = XtrDBRef(r);
/*    fprintf(stderr,"Hiding: %c %x\n", key ? 'R': 'C',c); */
    ClauseP(c)->infofcl &= ~IN_USE;
    unchain(r);
    if (RC(c)==0) dispose(c);
}

abolish(r)
FUNCTOR *r;
{
    CLAUSEREC *oldcl, *nextold;

    if ((r->flgsoffe)&RESERVED)	return FALSE;
    for (oldcl = r->defsoffe; oldcl; oldcl = nextold) {
	nextold = ClauseP(oldcl->altofcl);
	oldcl->infofcl |= ERASED;
	if (!InUse(oldcl)) unchain(ConsDBRef((PTR)oldcl,CLAUSE));
	if (Idle(oldcl)) dispose(oldcl);
    }
    return TRUE;
}

PTR
recorded(key)
int key;
{
/*  key should be RECORD for the data base
    or CLAUSE for clauses;
    The local stack is expected to contain
      ARG1    term to be matched
      ARG2    var to be unified with reference into data base
      ARG3    
      ARG4    indirect pointer to next term to be tried for match
*/
    PTR p, sv1, v1f, t, h, b, sx, tr0;
    int n;

    p = *(ARG4);
    if (Signed(p) < 255) return FALSE; /* this is a $sysp */
    /* since args of $record(_,_,_) are classified as temp. */
    GrowLocal(4);
    sv1 = v1f = v1; tr0 = tr;
    for (; TRUE; p = ClauseP(p)->altofcl) {
	if (Undef(p)) return NULL;
	if (Erased(p)) continue;
	sx = x; x = v-4;
	if (key == RECORD) {
	    n = ClauseP(p)->gvofcl;
	    InitGlobal(n,t);
	    t = ClauseP(p)->bdyofcl;
	    n = unifyarg(Addr(FrameP(sx)->v1ofcf),t,v1f);
	} else n = 1;
	n &= unifyarg(Addr(FrameP(sx)->v2ofcf),ConsDBRef(p,key),v1f);
	x = sx;
	if (n) break;
	v1 = sv1;
	while (tr != tr0) **--tr = NULL;
    }
    ARG4 = Addr(ClauseP(p)->altofcl);
    if (!InUse(p)) {
	ClauseP(p)->infofcl |= IN_USE;
	TrailPtr(ConsDBRef(p,key));
    }

    return ConsDBRef(p,key);
}

static int rl; static PTR tf;

static PTR
globalize(t,bodyflg)
PTR t; int bodyflg;
{
    PTR a, b, k; int n;
    if (IsAtomic(t)) return t;
    if (bodyflg && SkelP(t)->Fn == commatag) {
	a = globalize(SkelP(t)->Arg1,FALSE);
	b = globalize(SkelP(t)->Arg2,TRUE);
	*v1 = a; *(v1+1) = b; t = v1+2;
	MolP(t)->Sk = Addr(FunctorP(commatag)->gtoffe);
	MolP(t)->Env = v1;
	GrowGlobal(4);
	return t;
    }
    n = FunctorP(*t)->arityoffe;
    MolP(v1)->Sk = Addr(FunctorP(*t)->gtoffe);
    MolP(v1)->Env = v1+2;
    a = v1; b = v1+2; GrowGlobal(n+2);
    while (n-- > 0) {
	k = *++t;
	if (IsComp(k)) {
	    if (IsInp(k)) {
		ConsMol(k,tf,k);
	    }
	    else if (IsLocalVar(k))
		k = rl+FrameVar(tf,VarNo(k));
	    else
		k = FrameVar(tf,VarNo(k));
	}
	*b++ = k;
    }
    return a;
}

int
instance(r,argp)
PTR r, argp;
{
    PTR p, h, b;
    int g, l;

    if (!IsDBRef(r)) return -1;

    p = XtrDBRef(r);
    g = ClauseP(p)->gvofcl; l = ClauseP(p)->ltofcl;
    InitGlobal(g+l,tf);
    rl = g-szofcf;
    if (DBType(r) == RECORD) h = p->bdyofcl;
    else {
	h = ClauseP(p)->hdofcl; b = ClauseP(p)->bdyofcl;
	if (Undef(b)) b = atomtrue;
	if (l>0 ) {
	    h = globalize(h,FALSE);
	    b = globalize(b,TRUE);
	} else {
	    if (IsComp(h))
		ConsMol(h,tf,h);
	    if (IsComp(b))
		ConsMol(b,tf,b);
	}
	*v1 = h; *(v1+1) = b; 
	h = Addr(FunctorP(arrowtag)->gtoffe); tf = v1;
	GrowGlobal(2);
    }
    return unifyarg(argp,h,tf);
}

