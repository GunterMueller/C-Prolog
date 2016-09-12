/**********************************************************************
*                                                                     *
*                  C Prolog     compare.c                             *
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

/* Returns the compare code of t, where t is atomic, unasigned or
   a skeleton.
   The compare codes are:

	variable: -2, primitive: -1, atom: 0, skeleton: its arity
*/
#define code(t) (IsRef(t) ? -2 : (IsPrim(t) ? -1 : SkelP(t)->Fn->arityoffe))
	    
compare(T1,T2)
PTR T1, T2;
/* Returns the comparison value between T1 and T2 */
{
    PTR E1, E2;

    E1 = E2 = NULL;
    T1 = vvalue(T1,&E1);
    T2 = vvalue(T2,&E2);
    return comp(T1,E1,T2,E2);
}

static comp(T1,E1,T2,E2)
PTR T1, E1, T2, E2;
{
    PTR t1, e1, t2, e2; int d1, d;

    if (T1 == T2 && E1 == E2) return 0;
    d1 = code(T1);
    d = d1 - code(T2);
    if (d) return d;		/* If codes different return difference */
    if (d1 < 0) {		/* Both vars. or primitives */
	if (IsNumber(T1))	/* Both numbers */
	    return intsign(T1,T2);
	else
	    return T1-T2;	/* Both variables or pointers */
    }
    				/* both atoms or molecules */
    if (SkelP(T1)->Fn == SkelP(T2)->Fn) {
    				/* same functors (can't be atoms) */
	while (d1-- > 0) {
	    t1 = argv(++T1,E1,&e1);
	    t2 = argv(++T2,E2,&e2);
	    if (d = comp(t1,e1,t2,e2))
		break;
	}
	return d;
    }
				/* compare names */
    return strcmp(SkelP(T1)->Fn->atoffe->stofae,
		  SkelP(T2)->Fn->atoffe->stofae);
}

