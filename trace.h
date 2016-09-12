#define NEVER_SKIP	1000000

#define CONT		0
#define CALL_PORT	1
#define EXIT_PORT	2
#define BACK_PORT	3
#define FAIL_PORT	4

#define NORMAL		0
#define EFAIL		1
#define ICALL		2
#define ABORTING	3
#define BREAK		4
#define Trace(when,frame,goal,goalenv,info,port) if (when) { \
			    switch (trace(frame,goal,goalenv,info,port)) { \
				case EFAIL: goto efail; \
				case ICALL: goto icall; \
				case ABORTING: goto aborting; \
				case BREAK: goto enterbreak; \
				case NORMAL: break; \
			    } \
			}

extern int debug, lev, sklev, invokno,
           spy, leash, dotrace, breakret, execsys;
extern PTR pg, bg, c;
