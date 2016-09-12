/**********************************************************************
*                                                                     *
*                  C Prolog    auxfn.c                                *
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

PTR
fentry(atom,arity)
PTR atom; int arity;
{
    register PTR fe, ne, p; int i;

    for (fe = atom;; fe = FunctorP(fe)->nxtoffe)
	if (FunctorP(fe)->arityoffe == arity)
	    return fe;
	else if (Undef(FunctorP(fe)->nxtoffe))
	    break;
    ne = getsp(szoffe+arity);
    Unsafe();
    FunctorP(ne)->atoffe = atom; FunctorP(ne)->infoffe = 0;
    FunctorP(ne)->arityoffe = arity;
    FunctorP(ne)->FClauses.First = FunctorP(ne)->FClauses.Last = NULL;
    FunctorP(ne)->FRecords.First = FunctorP(ne)->FRecords.Last = NULL;
    FunctorP(ne)->nxtoffe = NULL;
    FunctorP(fe)->nxtoffe = ne;
    p = Addr(FunctorP(ne)->gtoffe);
    for (i = 0; i < arity; i++)
	*++p = SkelGlobal(i);
    FunctorP(ne)->gtoffe = ne;
    Safe();
    return ne;
}

PTR
apply(at,n,args)
PTR at; register PTR args; register int n;
{
    PTR sk, s; register PTR r;
    sk = Addr(FunctorP(fentry(at,n))->gtoffe);
    s = r = v1; GrowGlobal(n);
    while (n-- > 0)
	*r++ = *args++;
    ConsMol(sk,s,r);
    return r;
}

PTR
makelist(n,elms)
int n; PTR elms;
{
    register PTR p; PTR  f; register int i; register PTR r;
    p = elms+n-1;
    for (; n > 10; n -= 9) {
	f = r = v1; GrowGlobal(10);
	for (i = 0; i < 10; i++)
	    *r++ = *p--;
	ConsMol(List10,f,*++p);
    }
    f = r = v1; GrowGlobal(n);
    for (i = 0; i < n; i++)
	*r++ = *p--;
    ConsMol(List10+(10-n)*3,f,r);
    return r;
}

int
list_to_string(t,s,n)
PTR t;
char *s;
int n;
{
    int c;
    PTR e, a;

    if (t == atomnil) {
	*s = '\0';
	return TRUE;
    }
    if (IsInp(t) || Undef(*t)) return FALSE;
    e = MolP(t)->Env; t = MolP(t)->Sk;
    while (t != atomnil) {
	if (IsAtomic(t) || IsVar(t) || SkelP(t)->Fn != listfunc) return FALSE;
	if (n-- <= 0) return FALSE;
	a = arg(Addr(SkelP(t)->Arg1),e);
	t = argv(Addr(SkelP(t)->Arg2),e,&e);
	if (!IsInt(a)) return FALSE;
	c = XtrInt(a);
	if (c < 0 || c > 255) return FALSE;
	*s++ = c;
    }
    *s = 0;
    return TRUE;
}

/* Print execution statistics */

Statistics()
{
    int i; PTR p;


    for (i = 0; i < NAreas; i++)
	printf("%s: %dK (in use: %d, max. used: %d)\n",
              AreaName[i], Size[i]/K, used(i), tide(i));
    printf("Runtime: %8.2f sec.\n", CPUTime());
}

static int
used(a)
int a;
{
    int u;

    switch (a) {
	case AtomId: u = sizeof(PTR)*(atomfp-atom0); break;
	case AuxId: u = sizeof(PTR)*(vrz-auxstk0); break;
	case TrailId: u = sizeof(PTR)*(tr-trbase); break;
	case HeapId: u = HeapUsed(); break;
	case GlobalId: u = sizeof(PTR)*(v1-glb0); break;
	case LocalId: u = sizeof(PTR)*(v-lcl0); break;
	default: u = 0;
    }
    return u;
}    

static int
tide(a)
int a;
{
    int u;

    switch (a) {
	case HeapId: u = HeapTide(); break;
	case AtomId: u = sizeof(PTR)*(atomfp-atom0); break;
	case AuxId:
	case TrailId:
	case GlobalId:
	case LocalId: u = sizeof(PTR)*(Tide[a]-Origin[a]); break;
	default: u = 0;
    }
    return u;
}    

/* Atom hash function */

static PTR
string_to_atom(name,app)
char *name; PTR **app;
{
    register unsigned int h; register ATOM **ap; register char *s = name;

    h = strlen(s);
    while (*s) h += *s++;
    for (ap = (ATOM **)(hasha+h%HASHSIZE); *ap; 
				ap = (ATOM **)Addr((*ap)->nxtofae))
	if (strcmp((*ap)->stofae,name) == 0) break;
    *app = (PTR*)ap;
    return *ap;
}

/* Intern a string to get a prolog atom */

PTR
lookup(id)
char *id;
{
    PTR old, ptr, new;

    if (old = string_to_atom(id,&ptr)) return old;
    new = atomfp;
    GrowAtom(Words(szofae+strlen(id)));
    Unsafe();
    *ptr = new; ptr = new;
    AtomP(ptr)->atofae = ptr;
    AtomP(ptr)->infofae = 0;
    AtomP(ptr)->infxofae = 
    AtomP(ptr)->prfxofae = AtomP(ptr)->psfxofae = -1;
    AtomP(ptr)->AClauses.First = AtomP(ptr)->AClauses.Last  = NULL;
    AtomP(ptr)->ARecords.First = AtomP(ptr)->ARecords.Last  = NULL;
    AtomP(ptr)->fcofae = NULL;
    AtomP(ptr)->nxtofae = NULL;
    strcpy(AtomP(ptr)->stofae,id);
    Safe();
    return ptr;
}

int
hide_atom(a)
ATOM *a;
{
    PTR *aa; PTR *lostatoms = CellP(hasha+HASHSIZE);

    if (!string_to_atom(a->stofae,&aa)) return FALSE;
    *aa = a->nxtofae;
    a->nxtofae = *lostatoms;
    *lostatoms = (PTR)a;
    return TRUE;
}
