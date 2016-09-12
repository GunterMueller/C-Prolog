/**********************************************************************
*                                                                     *
*                  C Prolog     unify.c                               *
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

int
gunify(ta, ga, tb, gb)
        PTR ta,
        ga,
        tb,
        gb;
{
/*  Unifies term t1 with global frame g1 and local frame v
    with term t2 with global frame g2 and local frame x
    result is TRUE if unification succeeds and FALSE otherwise.
*/

    int     arity;
    PTR a,
	b,
	pa,
	pb;

/*  check same functor */
start: 
    if (*tb != (a = *ta))
	return FALSE;

    arity = FunctorP (a) -> arityoffe;

/*  main loop  */

    while (--arity > 0) {
	a = *++ta;
	if (IsVar (a)) {
	    pa = FrameVar (ga, VarNo (a));
	    a = *pa;
	    while (IsRef (a)) {
		pa = a;
		a = *a;
	    }
	    b = *++tb;
	    if (IsVar (b)) {
		pb = FrameVar ( gb, VarNo (b));
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
			return FALSE;
		}
		if (IsAtomic (b) ||
			!gunify (a, MolP (pa) -> Env, b, MolP (pb) -> Env))
		    return FALSE;
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
		return FALSE;
	    }
	    if (Undef (a)) {
		ConsMol (b, gb, *pa);
		TrailVar (pa);
		continue;
	    }
	    if (IsAtomic (a) || !gunify (a, MolP (pa) -> Env, b, gb))
		return FALSE;
	    continue;
	}
	b = *++tb;
	if (IsInp (b)) {
	    if (IsComp (a)) {
		if (IsAtomic (b) || !gunify (a, ga, b, gb))
		    return FALSE;
		continue;
	    }
	    if (b != a)
		return FALSE;
	    continue;
	}
	pb = FrameVar ( gb, VarNo (b));
	b = *pb;
	while (IsRef (b)) {
	    pb = b;
	    b = *b;
	}
	if (Undef (b)) {
	    if (IsAtomic (a))
		*pb = a;
	    else
		ConsMol (a, ga, *pb);
	    TrailVar (pb);
	    continue;
	}
	if (IsComp (b)) {
	    if (IsAtomic (a) || !gunify (a, ga, b, MolP (pb) -> Env))
		return FALSE;
	    continue;
	}
	if (b != a)
	    return FALSE;
	continue;
    }
    ta = *++ta;
    if (IsVar (ta)) {
	pa = FrameVar (ga, VarNo (ta));
	ta = *pa;
	while (IsRef (ta)) {
	    pa = ta;
	    ta = *ta;
	}
	tb = *++tb;
	if (IsVar (tb)) {
	    pb = FrameVar (gb, VarNo (tb));
	    tb = *pb;
	    while (IsRef (tb)) {
		pb = tb;
		tb = *tb;
	    }
	    if (pa == pb)
		return TRUE;
	    if (Undef (tb)) {
		if (Undef (ta)) {
		    if (pa > pb) {
			*pa = pb;
			TrailVar (pa);
			return TRUE;
		    }
		    *pb = pa;
		    TrailVar (pb);
		    return TRUE;
		}
		*pb = IsComp (ta) ? pa : ta;
		TrailVar (pb);
		return TRUE;
	    }
	    if (Undef (ta)) {
		*pa = IsComp (tb) ? pb : tb;
		TrailVar (pa);
		return TRUE;
	    }
	    if (IsAtomic (ta))
		return (ta == tb);
	    if (IsAtomic (tb))
		return FALSE;
	    ga = MolP (pa) -> Env;
	    gb = MolP (pb) -> Env;
	    goto start;
	}
	if (IsAtomic (tb)) {
	    if (Undef (ta)) {
		*pa = tb;
		TrailVar (pa);
		return TRUE;
	    }
	    return (ta == tb);
	}
	if (Undef (ta)) {
	    ConsMol (tb, gb, *pa);
	    TrailVar (pa);
	    return TRUE;
	}
	if (IsAtomic (ta))
	    return FALSE;
	ga = MolP (pa) -> Env;
	goto start;
    }
    tb = *++tb;
    if (IsInp (tb)) {
	if (IsComp (ta)) {
	    if (IsAtomic (tb))
		return FALSE;
	    goto start;
	}
	return (tb == ta);
    }
    pb = FrameVar (gb, VarNo (tb));
    tb = *pb;
    while (IsRef (tb)) {
	pb = tb;
	tb = *tb;
    }
    if (Undef (tb)) {
	if (IsAtomic (ta))
	    *pb = ta;
	else
	    ConsMol (ta, ga, *pb);
	TrailVar (pb);
	return TRUE;
    }
    if (IsComp (tb)) {
	if (IsAtomic (ta))
	    return FALSE;
	gb = MolP (pb) -> Env;
	goto start;
    }
    return (tb == ta);
}

int
unifyarg(a,t,tf)
PTR a, t; PTR tf;
{
    if(IsVar(t)) {
	t=FrameVar(tf,VarNo(t));
	while(IsRef(*t)) t = *t;
    }
    while (IsRef(*a)) a = *a;
    if (Undef(*a)) {
	if (IsInp(t) && IsComp(t)) {
	    ConsMol(t,tf,*a);
	    TrailVar(a);
	    return TRUE;
	}
	if (IsRef(t) && Undef(*t) && t >= a) {
	    if (t == a) return TRUE;
	    *t = a;
	    TrailVar(t);
	    return TRUE;
	}
	*a = t;
	TrailVar(a);
	return TRUE;
    }
    if (IsRef(t) && Undef(*t)) {
	*t = IsComp(*a) ? CellP(a) : CellP(*a);
	TrailVar(t);
	return TRUE;
    }
    if (t == *a && IsAtomic(t)) return TRUE;
    if (IsAtomic(t) || IsAtomic(*a)) return FALSE;
    if (!IsInp(t)) {
	tf = MolP(t)->Env;
	t = MolP(t)->Sk;
    }	
    return gunify(MolP(a)->Sk,MolP(a)->Env,t,tf);
}

PTR
deref(vp)
register PTR vp;
{
    while (IsRef(*vp)) vp = *vp;
    return vp;
}

PTR
vvalue(vp,tf)
register PTR vp; PTR *tf;
{
    vp = deref(vp);
    if (Undef(*vp)) return vp;
    if (IsComp(*vp)) *tf = MolP(vp)->Env;
    return *vp;
}

PTR
arg(argp,tf)
register PTR argp; PTR tf;
{
    register PTR a;
    a = *argp;
    if (IsVar(a)) {
	if (IsLocalVar(a))
	    argp = x;
	else
	    argp = tf;
	argp = deref(FrameVar(argp,VarNo(a)));
	a = *argp;
	if (Undef(a) || IsComp(a)) return argp;
    }
    return a;
}

PTR
argv(argp,tf,af)
register PTR argp; PTR tf, *af;
{
    register PTR a;
    a = arg(argp,tf);
    if (IsRef(a)) {
	if (Undef(*a)) return a;
	*af = MolP(a)->Env;
	return MolP(a)->Sk;
    }
    *af = tf;
    return a;
}
