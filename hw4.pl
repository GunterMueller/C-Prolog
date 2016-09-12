/*

Name:       HW4
Author:     Kenneth Ray Barnhouse
SSN:        245-29-5485
Date:       15-Apr-1988
Class:      CSE 511

Purpose:
        To build a simple forward chaining production system in PROLOG.
	The language will have two kind of statements, facts and rules. 
	Facts look just like PROLOG facts.  Rules are of the form:

		when condition(s) then action(s)

	where  condition(s) are one or more facts connected with 'and'.
	  and  action(s) are one and more actions connected with 'and'.

	Actions are basically any of six verbs: store, remove, output,
        input, newline, halt.

        The Top level interpreter will accept two command: run and load.
        The form of the load command is:

               load 'filename'.  (the single quotes are NOT optional).

	and the run command is just 

               run.

	The inner interpreter executes in a basic fetch/execute cycle from
        top to bottom in the rule database.  This cycle will continue until
        a halt statements is executed.

*/

/*

define some operators to make PROLOG do the work for me.

*/

?- op(300,xfx,then).
?- op(200,fy,when).
?- op(100,xfy,and).
?- op(50,fx,store).
?- op(50,fx,remove).
?- op(50,fx,output).
?- op(50,fx,input).
?- op(50,fx,load).

/*

This is the highest level interpreter in my little FCPS.  I display a
prompt, read a command and execute it.  I then call interpreter to
loop.  There are really only two good command here, "load" and "run".

*/

my_interpreter :- write(' My Simple FCPS V1.0 '),nl,
                  write(' by Ken Barnhouse '),nl,
                  write(' Valid Commands are '),nl,
                  write(' load ''filename'' and run '),nl,
                  unknown(_,fail),
                  interpreter.

interpreter :- write('=> '),
               read(Command),
               call(Command),
               interpreter.
/*

Here I implement the load command. I can't just use consult because the
PROLOG interpreter will not allow me to "retract" any initial facts read in by
"consult".  By asserting all the term myself, I can retract them at will.
A little more programming, but it was clean and easy.

*/

load Program :- see(Program),
                read_in_terms,
		seen.

read_in_terms :- read(Term),
                 assert_term(Term).
read_in_terms.

assert_term(end_of_file).
assert_term(Term) :- assert(Term),
                     read_in_terms.

/*

Here is the inner rule interpreter for my FCPS.  It basically implements a
fetch/execute cycle.  The first line of the first rule gets  a FCPS rule from
the PROLOG database, then the second try to execute it. I used fail to loop
through the database.  Then second rule of run just does a recursive call to
run to loop to the top of the database.

*/

run :- when Conditions then Actions,
       execute(Conditions,Actions),
       fail.
run :- run.

/*

the execute rule does the "if conditions met then fire" part of the rule 
interpreter.  It checks to see if the condition part of the rule is met.
if so, it fire the action part of the rule.  If not, it returns true.

*/

execute(Conditions,Actions) :- conditions_met(Conditions),!,
                               fire_actions(Actions).
execute(_,_).

/*

conditions_met/1 checks to see if the conditions are met.  We have to do
this recursively if we have several 'and'ed conditions.

*/

conditions_met(Firstcondition and Otherconditions) :- 
               Firstcondition,
               conditions_met(Otherconditions),!.

conditions_met(Singlecondition) :- Singlecondition.

/*

first_actions/1 is basically like condition_met/1 in form, since we must 
recursely execute actions that we connected with and's.

*/

fire_actions(Firstaction and Otheractions) :-
               call(Firstaction),
               fire_actions(Otheractions),!.

fire_actions(Singleaction) :- call(Singleaction).

/*

Here I define the verbs in this language.  

*/

store Fact :- assert(Fact).

remove Fact :- retract(Fact).

output Term :- write(Term).

input Term :- read(Term).

newline :- nl.
