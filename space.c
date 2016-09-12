/* C Prolog    space.c */

#include "pl.h"

#ifdef ERRCHECK
int ReleaseCheck = TRUE;
#endif

#define	CHAINS		16
#define	BUCKET_SIZE	1024

typedef struct BLOCK
{
    struct BLOCK *NextBlock;
    int BlockSize;
} Block, *BlockP;

typedef struct
{
    BlockP FirstBlock, LastBlock;
} GCPair, *GCPairP;

#define MIN_SIZE	sizeof(Block)/sizeof(PTR)

struct {
    BlockP free[CHAINS+1];
    PTR top, bottom;
    int used, maxused;
} Heap;

int HeapHeader = sizeof(Heap);

static int size;
static GCPairP Garbage;
static int Buckets;

#define FreeChain	Heap.free
#define Top		Heap.top
#define Bottom		Heap.bottom

#define FreeMisc FreeChain[CHAINS]

ClearMem(loc,num)
char *loc;
{
#ifdef vax
#ifdef unix
    asm(" movc5 $0,*4(ap),$0,8(ap),*4(ap) ");
#else
    register char *l = loc;
    register int n = num;

    while (n-- > 0) *l++ = NULL;
#endif
#else
    register char *l = loc;
    register int n = num;

    while (n-- > 0) *l++ = NULL;
#endif
}

CopyMem(from,to,cc)
char *from, *to;
{
#ifdef vax
#ifdef unix
    asm(" movc3 12(ap),*4(ap),*8(ap) ");
#else
    register char *f = from, *t = to;
    register int n = cc;
    
    if (f < t) {
	f += n;
	t += n;
	while (n-- > 0) *--t = *--f;
    }
    else while (n-- > 0) *t++ = *f++;
#endif
#else
    register char *f = from, *t = to;
    register int n = cc;
    
    if (f < t) {
	f += n;
	t += n;
	while (n-- > 0) *--t = *--f;
    }
    else while (n-- > 0) *t++ = *f++;
#endif
}

#define WDPtr(c)	((PTR)(c))

InitHeap()
/* Initialize space tables. Do it only once */
{
    Top = Bottom = skel0;
    ClearMem(FreeChain,(CHAINS+1)*sizeof(PTR));
    Heap.used = Heap.maxused = 0;
}

#ifdef ERRCHECK

#define NOOVERLAP	0
#define SAME		1
#define OVERLAP		2

static
overlap(a,b)
PTR a, b;
/* Check for overlap of space in error checking version */
{
    register BlockP n; int i;

    for (i = CHAINS; i >= 0; i--) {
	for (n = FreeChain[i]; n; n = n->NextBlock) {
	    if (b < (PTR)n)
		continue;
	    if (a >= ((PTR)n)+n->BlockSize)
		continue;
	    if (a == (PTR)n)
		return SAME;
	    return OVERLAP;
	}
    }
    return NOOVERLAP;
}

check_free()
{
    int i; BlockP b, a;
    for (i = 0; i <= CHAINS; i++) {
        a = &FreeChain[i];
	for (b = a->NextBlock; b; a = b, b = a->NextBlock)
	    if (b < Bottom || b > Top) {
		fprintf(stderr,"Invalid block %d: %x\n",i,a);
		abort();
	    }
    }
}

#endif

PTR
freeblock(base,size)
BlockP base; int size;
{
    BlockP *list;
#ifdef ERRCHECK
    if (ReleaseCheck) {
	if (size < MIN_SIZE) {
	    fprintf(stderr,"%s\n","size < MIN_SIZE");
	    abort();
	}
	else if (base < Bottom || WDPtr(base)+size > Top) {
	    fprintf(stderr,"%s\n","out of bounds");
	    abort();
	}
	else
	switch(overlap((PTR)base,((PTR)base)+size-1)) {
	case NOOVERLAP:
	    break;
	case SAME:
	    fprintf(stderr,"%s\n","space freed twice");
	    abort();
	case OVERLAP:
	    fprintf(stderr,"%s\n","space overlap");
	    abort();
	} 
    }
#endif
    list = (size < CHAINS+MIN_SIZE) ? &FreeChain[size-MIN_SIZE] : &FreeMisc;
    Unsafe();
    base->NextBlock = *list;
    base->BlockSize = size;
    *list = base;
    Heap.used -= size;
    Safe();
#ifdef ERRCHECK
    check_free();
#endif
}

static PTR
GetExact()
/* Get exact fit from specified list */
{
    register BlockP b;

    if (!(b = FreeChain[size-MIN_SIZE]))
	return NULL;
    FreeChain[size-MIN_SIZE] = b->NextBlock;
    Heap.used += size;
    if (Heap.used > Heap.maxused) Heap.maxused = Heap.used;
    return WDPtr(b);
}

static PTR
GetMixed()
/* Get first fit from misc list */
{
    register BlockP *l, n;

    l = &FreeMisc;
    while (n = *l) {
	if (n->BlockSize == size) {
	    *l = n->NextBlock;
	    Heap.used += size;
	    if (Heap.used > Heap.maxused) Heap.maxused = Heap.used;
	    return WDPtr(n);
	}
	else if (n->BlockSize >= size+MIN_SIZE) {
	    *l = n->NextBlock;
	    Heap.used += n->BlockSize;
	    freeblock(WDPtr(n)+size,n->BlockSize-size);
	    if (Heap.used > Heap.maxused) Heap.maxused = Heap.used;
	    return WDPtr(n);
	} else {
	    l = &(n->NextBlock);
	}
    }
    return NULL;
}

static PTR
GetTop()
/* Get space from top of table */
{
    PTR s;
    
    s = Top;
    if (s+size > hpmax)
	return NULL;
    else {
	Top += size;
	Heap.used += size;
	if (Heap.used > Heap.maxused) Heap.maxused = Heap.used;
	return s;
    }
}

#define try(rtn) if (x = rtn());

PTR
getsp(sz)
/* allocate space of size sz */
{
    PTR x; int gc = 0;

    if (sz < MIN_SIZE) {
	fprintf(stderr,"! Internal error: heap request too small");
	Stop(TRUE);
    }
    Unsafe();
    while (gc < 2) {
	size = sz;
	if (size < CHAINS+MIN_SIZE) {
	    try(GetExact) else
	    try(GetTop) else
	    try(GetMixed);
	}
	else {
	    try(GetMixed) else
	    try(GetTop);
	}
	Safe();
	if (x) {
	    ClearMem(x,size*sizeof(PTR));
#ifdef ERRCHECK
	    check_free();
#endif
	    return x;
	} else {
	    CollectGarbage();
	    gc++;
	} 
    }
    Safe();
    NoSpace(HeapId);
}

static
SortGarbage()
/*  Sort all free lists onto Garbage by address */
{
    register BlockP c, *p, q; register GCPairP s; int i;

    for (i = CHAINS; i >= 0; i--)
	while (c = FreeChain[i]) {
	    FreeChain[i] = c->NextBlock;
	    s = &Garbage[(WDPtr(c)-Bottom)/BUCKET_SIZE];
	    p = &(s->FirstBlock);
	    for (q = *p; q && q < c; q = *p)
		p = &(q->NextBlock);
	    if (!q) s->LastBlock = c;
	    c->NextBlock = q;
	    *p = c;
	    Heap.used += c->BlockSize;
	    if (Heap.used > Heap.maxused) Heap.maxused = Heap.used;
	}
}

static
MergeGarbage()
/* Merge adjacent pieces of space on the sorted list Garbage */
{
    register BlockP c, p; int i;

    for(i = Buckets-1; i >= 0; i--)
	if (!(Garbage[i].FirstBlock)) {
	    Garbage[i] = Garbage[i+1];
	    Garbage[i+1].FirstBlock = Garbage[i+1].LastBlock = NULL;
	}
	else if (Garbage[i+1].FirstBlock) {
	    Garbage[i].LastBlock->NextBlock = Garbage[i+1].FirstBlock;
	    Garbage[i+1].FirstBlock = Garbage[i+1].LastBlock = NULL;
	}
    p = Garbage[0].FirstBlock;
    while (p)
	if ((BlockP)(WDPtr(p)+(p->BlockSize)) != p->NextBlock)
	    p = p->NextBlock;
	else {
	    c = p->NextBlock;
	    p->BlockSize += c->BlockSize;
	    p->NextBlock = c->NextBlock;
	}
}

static
RelGarbage()
/* Release all items on the merged, sorted list Garbage */
{
    register BlockP c, p;
#ifdef ERRCHECK
    int t = ReleaseCheck;
	    
    ReleaseCheck = FALSE;
#endif
    p = Garbage[0].FirstBlock;
    while (p) {
	c = p->NextBlock;
	if (!c && WDPtr(p)+(p->BlockSize) == Top) {
		Top = WDPtr(p);
		Heap.used -= p->BlockSize;
	}
	freeblock(p,p->BlockSize);
	p = c;
    }
#ifdef ERRCHECK
    ReleaseCheck = t;
#endif
}

CollectGarbage()
/* The garbage collection driver */
{
    int i;

    Buckets = (Top-Bottom)/BUCKET_SIZE;
    if ((Top-Bottom)%BUCKET_SIZE) Buckets++;
    Garbage = (GCPairP)(vrz ? vrz : auxstk0);
    if (Garbage+Buckets+1 > auxmax)
	return;
    for (i = 0; i <= Buckets; i++)
	Garbage[i].FirstBlock = Garbage[i].LastBlock = NULL;
    SortGarbage();
    MergeGarbage();
    RelGarbage();
}

RelocHeap(delta)
int delta;
/* Relocates the free space chains, where the actual free space
   has already been moved.
*/   
{
    int i; PTR p;
    
    for (i = 0; i <= CHAINS; i++) {
	p = WDPtr(&FreeChain[i]);
	while (*p)
	    p = WDPtr(&(((BlockP)(*p += delta))->NextBlock));
    }
    Top += delta;
    Bottom += delta;
}

int
HeapUsed()
{
    return Heap.used*sizeof(PTR);
}

int HeapTide()
{
    return Heap.maxused*sizeof(PTR);
}

PTR
HeapTop()
{
    return Heap.top;
}

