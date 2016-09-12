/**********************************************************************
*                                                                     *
*                  C Prolog     parms.c                               *
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

/* Declaration and properties of work areas */

#define AtomSize	(128*K)
#define AuxSize		(8*K)
#define TrailSize	(64*K)
#define HeapSize	(256*K)
#define GlobalSize	(256*K)
#define LocalSize	(128*K)


int Size[] = { AtomSize, AuxSize, TrailSize,
	       HeapSize, GlobalSize, LocalSize };

PTR Origin[7];
PTR Limit[6];
PTR Tide[6];

/*
    Switches: b = boot, q = quiet start-up, d = dump on error, T = trace,
    a = atom area size,
    x = aux   "     " ,
    t = trail "     " ,
    h = heap  "     " ,
    g = global "    " ,
    l = local  "    "

*/

char Parameter[] = { 'a', 'x', 't', 'h', 'g', 'l' };
int NParms = 6;

char Switch[] = { 0,  0, 'b', 'q', 'd', 'T' };
int State[] =   { 0,  0,  0,   0,   0,   0 };

int Switches = 6;

#ifdef vms
#define STARTUPFILE "STARTUP"
#endif

char StandardStartup[] = STARTUPFILE;

char *
UserStartup()
{
    static char buf[256];
#ifdef unix
    static char format[] = "%s/prolog.bin";
    char *env = getenv("HOME");
#else
#ifdef vms
    static char format[] = "%sPROLOG.BIN";
    char *env = getenv("HOME");
#else
    static char format[] = "%sPROLOG.BIN";
    char *env = NULL;
#endif
#endif
    sprintf(buf,format,env);
    return buf;
}

char version[] = "C-Prolog version 1.5";
int saveversion = 26;


