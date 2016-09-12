/**********************************************************************
*                                                                     *
*                  C-Prolog: arith.c                                  *
*                                                                     *
*  By Fernando Pereira, July 1982.                                    *
*  EdCAAD, Dept. of Architecture, University of Edinburgh.            *
*                                                                     *
*  Based on the Prolog system written in IMP by Luis Damas            *
*  for ICL 2900 computers, with some contributions by                 *
*  Lawrence Byrd.                                                     *
*                                                                     *
*  Copyright (C) 1982, 1983,                                          *
*       Fernando Pereira, Luis Damas and Lawrence Byrd.               *
*                                                                     *
*  Improvements by Richard O'Keefe and Fernando Pereira, 1983         *
*                                                                     *
**********************************************************************/
/* Evaluate arithmetic expressions */

#include "pl.h"
#include "arithop.h"
#include <math.h>
#include <errno.h>

#define NEVER		0
#define SOMETIMES	1
#define	ALWAYS		2

double
ffail()
{
    ArithError("internal error - undefined operator");
}

extern	double	sin(), asin(), exp(), sqrt();
extern	double	cos(), acos(), log(), floor();
extern	double	tan(), atan(), log10();

extern int brklev;

static double (*UFloat[])() = {
    ffail,
    ffail,
    ffail,
    ffail,
    exp,
    log,
    log10,
    sqrt,
    sin,
    cos,
    tan,
    asin,
    acos,
    atan,
    floor,
    ffail
};

static char floatable[] = {	/* code arity function */
    NEVER,			/*    0     - UNUSABLE */
    NEVER,			/*    1     1       ID */
    SOMETIMES,			/*    2     1        - */
    NEVER,			/*    3     1        \ */
    ALWAYS,			/*    4     1      exp */
    ALWAYS,			/*    5     1      log */
    ALWAYS,			/*    6     1    log10 */
    ALWAYS,			/*    7     1     sqrt */
    ALWAYS,			/*    8     1      sin */
    ALWAYS,			/*    9     1      cos */
    ALWAYS,			/*   10     1      tan */
    ALWAYS,			/*   11     1     asin */
    ALWAYS,			/*   12     1     acos */
    ALWAYS,			/*   13     1     atan */
    SOMETIMES,			/*   14     1    floor */
    SOMETIMES,			/*   15     1    SPARE */
    ALWAYS,			/*   16     - UNUSABLE */
    SOMETIMES,			/*    1     2        + */
    SOMETIMES,			/*    2     2        - */
    SOMETIMES,			/*    3     2        * */
    ALWAYS,			/*    4     2        / */
    NEVER,			/*    5     2      mod */
    NEVER,			/*    6     2       /\ */
    NEVER,			/*    7     2       \/ */
    NEVER,			/*    8     2       << */
    NEVER,			/*    9     2       >> */
    NEVER,			/*   10     2       // */
    ALWAYS,			/*   11     2        ^ */
    NEVER,			/*   12     2    SPARE */
    NEVER,			/*   13     2    SPARE */
    NEVER,			/*   14     2    SPARE */
    NEVER			/*   15     2    SPARE */
};


typedef struct {
    char Float;
    union {
	int asInt;
	double asFloat;
    } val;
} Value;

#define AsInt	val.asInt
#define AsFloat	val.asFloat

int AllFloat = TRUE;

static Value unary(), binary();

static Value
eval(t,g)
PTR t, g;
/* traverses a term producing its val and type.
   t is the term (derefed and unwrapped),
   g is the associated global frame (if t is a skel)
*/
{
    int b, n, i, typ, fl; PTR f1, f2, arg1, arg2; Value v1, v2;
    FUNCTOR *fn;
    
    if (IsRef(t) && Undef(*t))		/* undefined cell */
	NotNumber();
    if (IsPrim(t)) {			/* primitive type */
	if (IsInt(t)) {			/* integer */
	    v1.Float = FALSE;
	    v1.AsInt = XtrInt(t);
	    return v1;
	}
	if (IsFloat(t)) {		/* float */
	    v1.Float = TRUE;
	    v1.AsFloat = XtrFloat(t);
	    return v1;
	}
	NotNumber();			/* non-number */
    }
					/* atom or skel */
					/* grab expression info field */
    fn = FunctorP(SkelP(t)->Fn);
    b = (fn->flgsoffe)&0x1f;
    if (!b) NotOp(fn);
    if (IsAtomic(t)) {			/* atom */
	switch (b) {
	    case TIME:
		v1.Float = TRUE;
		v1.AsFloat = CPUTime();
		return v1;
	    case HEAP:
		v1.Float = FALSE;
		v1.AsInt = HeapUsed();
		return v1;
	    case BREAKLEV:
		v1.Float = FALSE;
		v1.AsInt = brklev;
		return v1;
	    default:
		NotOp(fn);
	}
    }
					/* skel   (first check for [_]) */
    if (fn == FunctorP(listfunc)) {
	if (argv(Addr(SkelP(t)->Arg2),g,&f1) != atomnil)
	    ArithError("not a string");
	arg1 = argv(Addr(SkelP(t)->Arg1),g,&f1);
	return eval(arg1,f1);
    }
					/* skel   (general case) */
    n = fn->arityoffe;	/* grab arity */
    if (n > 2) NotOp(fn);
    switch (n) {
	case 1:				/* unary */
	    arg1 = argv(++t,g,&f1);
	    return unary(b,arg1,f1);
	case 2:				/* binary */
	    arg1 = argv(++t,g,&f1);
	    arg2 = argv(++t,g,&f2);
	    return binary(b, arg1, arg2, f1, f2);
	default:
	ffail();
    }
}

static Value
unary(op,arg,env)
int op; PTR arg, env;
{
    int fl = floatable[op], typ;
    Value v;

    typ = fl-(1-AllFloat) > 0;
    errno = 0;				/* no errors */
    v = eval(arg,env);
    if (fl == NEVER) {
	if (!ForceInt(&v)) NotInt();
    } else
    if (v.Float)
    	typ = TRUE;
    else if (typ) {
	v.AsFloat = (double)(v.AsInt);
	v.Float = TRUE;
    }
    switch (op) {
	case ID:
	    break;
	case UMINUS:
	    if (typ) v.AsFloat = -v.AsFloat;
	    else v.AsInt = -v.AsInt;
	    break;
	case NOT:
	    v.AsInt = ~v.AsInt;
	    break;
	default:		/* ALWAYS functions */
	    v.AsFloat = (*UFloat[op])(v.AsFloat);
    }
    if (errno != 0) ArithError(SysError());
    return v;
}

static Value
binary(op,arg1,arg2,env1, env2)
int op; PTR arg1, arg2, env1, env2;
{ 
    Value v1, v2;
    int fl = floatable[op+16], typ;

    v1 = eval(arg1,env1);
    v2 = eval(arg2,env2);
    typ = fl-(1-AllFloat) > 0;
    errno = 0;				/* no errors */
    if (fl == NEVER) {
	if (!ForceInt(&v1)) NotInt();
	if (!ForceInt(&v2)) NotInt();
    } else {
	typ |= v1.Float | v2.Float;
	if (typ) {		/* coerce both args. to float */
	    if (!v1.Float) v1.AsFloat = (double)(v1.AsInt);
	    if (!v2.Float) v2.AsFloat = (double)(v2.AsInt);
	}
	v2.Float = typ;
    }
    switch (op) {
    case PLUS:
	if (typ)
	    v2.AsFloat = v1.AsFloat+v2.AsFloat;
	else
	    v2.AsInt = v1.AsInt+v2.AsInt;
	break;
    case MINUS:
	if (typ)
	    v2.AsFloat = v1.AsFloat-v2.AsFloat;
	else
	    v2.AsInt = v1.AsInt-v2.AsInt;
	break;
    case TIMES:
	if (typ)
	    v2.AsFloat = v1.AsFloat*v2.AsFloat;
	else
	    v2.AsInt = v1.AsInt*v2.AsInt;
	break;
    case DIVIDE:
	if (typ)
	    v2.AsFloat = v1.AsFloat/v2.AsFloat;
	else
	    v2.AsInt = v1.AsInt/v2.AsInt;
	break;
    case MOD:
	v2.AsInt = v1.AsInt%v2.AsInt;
	return v2;
    case AND:
	v2.AsInt = v1.AsInt&v2.AsInt;
	return v2;
    case OR:
	v2.AsInt = v1.AsInt|v2.AsInt;
	return v2;
    case LSHIFT:
	v2.AsInt = v1.AsInt<<v2.AsInt;
	return v2;
    case RSHIFT:
	v2.AsInt = v1.AsInt>>v2.AsInt;
	return v2;
    case IDIV:
	v2.AsInt = v1.AsInt/v2.AsInt;
	return v2;
    case POW:
	v2.AsFloat = pow(v1.AsFloat,v2.AsFloat);
	return v2;
    default:
	ffail();
    }
    if (errno) ArithError(SysError());
    return v2;
}

int
intval(p)
PTR p;
/* Evaluates an expression as an integer, causes an event if
   the value is not an integer */
{
    PTR f, v; Value r;
    
    v = vvalue(p,&f);
    r =  eval(v,f);
    if (r.Float) {
	r.Float = !Narrow(r.AsFloat, &(r.AsInt));
	if (r.Float) ArithError("Integer expected");
    }
    return r.AsInt;
}

PTR
numeval(p)
PTR p;
/* Evaluates expression p and returns a number representation */
{
    PTR f, v;
    Value r;
    
    v = vvalue(p,&f);
    r = eval(v,f);
    if (r.Float)
	r.Float = !Narrow(r.AsFloat, &(r.AsInt));
    if (r.Float)
	return ConsFloat(r.AsFloat);
    else
	return ConsInt(r.AsInt);
}

PTR
Unary(op,v)
int op; PTR v;
/* Applies op to x and returns a number representation */
{
    Value r; PTR f;
    
    v = vvalue(v,&f);
    r = unary(op,v,f);
    if (r.Float)
	r.Float = !Narrow(r.AsFloat, &(r.AsInt));
    if (r.Float)
	return ConsFloat(r.AsFloat);
    else
	return ConsInt(r.AsInt);
}

PTR
Binary(op,v1,v2)
int op; PTR v1, v2;
/* Applies op to v1 and v2 and returns a number representation */
{
    Value r; PTR f1, f2;
    
    v1 = vvalue(v1,&f1);
    v2 = vvalue(v2,&f2);
    r = binary(op,v1,v2,f1,f2);
    if (r.Float)
	r.Float = !Narrow(r.AsFloat, &(r.AsInt));
    if (r.Float)
	return ConsFloat(r.AsFloat);
    else
	return ConsInt(r.AsInt);
}

int
numcompare(op,t1,t2)
int op;
PTR t1, t2;
/* Applies comparison operation op to expressions t1 and t2 */
{
    PTR f, t;
    Value v1, v2;
    
    t = vvalue(t1,&f);
    v1 = eval(t,f);
    t = vvalue(t2,&f);
    v2 = eval(t,f);
    if (v1.Float || v2.Float) {
	if (!v1.Float) v1.AsFloat = (double)(v1.AsInt);
	if (!v2.Float) v2.AsFloat = (double)(v2.AsInt);
	switch (op) {
	    case EQ:	return v1.AsFloat == v2.AsFloat;
	    case NE:	return v1.AsFloat != v2.AsFloat;
	    case LT:	return v1.AsFloat < v2.AsFloat;
	    case GT:	return v1.AsFloat > v2.AsFloat;
	    case LE:	return v1.AsFloat <= v2.AsFloat;
	    case GE:	return v1.AsFloat >= v2.AsFloat;
	    default:	return NEVER;
	}
    }
    switch (op) {
	case EQ:	return v1.AsInt == v2.AsInt;
	case NE:	return v1.AsInt != v2.AsInt;
	case LT:	return v1.AsInt < v2.AsInt;
	case GT:	return v1.AsInt > v2.AsInt;
	case LE:	return v1.AsInt <= v2.AsInt;
	case GE:	return v1.AsInt >= v2.AsInt;
	default:	return NEVER;
    }    
}

int
intsign(n1,n2)
PTR n1, n2;
/* returns the sign of the difference between numbers t1 and t2 */
{
    double v1, v2;
    
    v1 = IsInt(n1) ? (double)XtrInt(n1) : XtrFloat(n1);
    v2 = IsInt(n2) ? (double)XtrInt(n2) : XtrFloat(n2);
    return (v1 > v2) ? 1 : ((v1 < v2) ? -1 : 0);
}

/* ======================================================================

These two functions are totally dependant on the float representation
of the machine. The type tag for a constructed float is binary 110
in the most significant bits of a 32 bit word. To fit a machine
float into a constructed float, the 3 least significant bits of the
mantissa are dropped. In the VAX F_floating format, the lowest
significance bits are on the right in the second 16 bit word
of the value.

The code given here for the Perq appears to work.

In the IEEE single precision floating point, the lowest significant bits
are on the right.
  
*/

typedef union {
#ifdef vax
    struct {
	short loword;
	short hiword;
      } aswords;
#endif
#ifdef IEEE
	unsigned	asunsigned;
#endif
      float	asfloat;
      PTR		asPTR;
  } Mixed;

PTR
ConsFloat(f)
    float f;
    {
	Mixed m;
    
	m.asfloat = f;
#ifdef vax
	m.aswords.hiword = ((m.aswords.hiword>>3)&0x1fff)|(FLOAT_TAG>>16);
#endif
#ifdef IEEE
	m.asunsigned = (m.asunsigned>>3)|FLOAT_TAG;
#endif
	return m.asPTR;
    }

float
XtrFloat(p)
    PTR p;
    {
	Mixed m;
    
	m.asPTR = p;
#ifdef	Perq
	m.aslong <<= 3;
#endif
#ifdef vax
	m.aswords.hiword <<= 3;
#endif
#ifdef IEEE
	m.asunsigned <<= 3;
#endif
	return m.asfloat;
    }

/* ====================================================================== */

int
Narrow(f,i)
    double f; int *i;
    {
	register int k;

	if (f < MinInt || f > MaxInt)  return FALSE;
	if ((double)(k = (int)f) != f) return FALSE;
	*i = k;
	return TRUE;
    }

static int
ForceInt(v)
    register Value *v;
    {
	if (v->Float) v->Float = !Narrow(v->AsFloat, &(v->AsInt));
	return !v->Float;
    }

ArithError(s)
    char *s;
    {
	ErrorMess = s;
	Event(ARITH_ERROR);
    }

NotNumber()
    {
	ArithError("not a number");
    }

static
NotInt()
    {
	ArithError("arithmetic operation requires integers");
    }

static
NotOp(fn)
    FUNCTOR *fn;
    {
    sprintf(OutBuf,
		  fn->arityoffe
		? "%s is not an arithmetic operator"
		: "%s is not a number",
		AtomP(fn->atoffe)->stofae);
    ArithError(OutBuf);
    }

