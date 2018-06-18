# 
#              CALL FOR COMMENTS, BENCHMARKS, AND SOLVERS
#
#                              SL-COMP'18
##        2nd International Competition of Solvers on Separation Logic
##                        at ADSL@FLOC'18, Oxford, UK
#
##	  http://adsl.univ-grenoble-alpes.fr/index.html#SL-COMP
#
##                 https://github.com/sl-comp/SL-COMP18
# 


Separation Logic (SL) is an established and fairly popular Hoare logic
for imperative, heap-manipulating programs. Its high expressivity, its 
ability to generate compact proofs, and its support for local reasoning 
have motivated the development of tools for automatic reasoning about 
programs using SL. These tools intensively use (semi-)decision procedures 
for checking satisfiability and/or entailment problems in SL.

The first competition of SL solvers took place in 2014 as an unofficial 
event at FLoC Olympic Games. It was an opportunity to collect more than
600 benchmarks, to make available the participating solvers on a common 
platform (StarExec), and to obtain very useful insights about the techniques 
used by these solvers. The web site of this competition is available
at https://www.irif.fr/~sighirea/sl-comp/14 and 
the its repository is available at https://github.com/sl-comp/SL-COMP14.

For the second edition of this competition, we are looking for more 
benchmarks and participants.


## CALL FOR COMMENTS

The organizing committee is particularly interested by comments concerning:

* SL fragment: The 2014 edition focused on the symbolic heaps fragment of SL with 
  Inductive Definitions because it was the intersection of the fragments dealt by 
  the participating solvers. We might consider other fragments, e.g., extension 
  of SL with data and length constraints.
  
* Benchmarks: The current set of benchmarks was built based on contributions sent by 
  each solver. This may lead to an over-representation of some categories
  of problems that are efficiently dealt by the participants. We are interested 
  in comments on the existing benchmarks and their adequacy to the needs of the 
  SL-based tools.

* Scoring: The scoring system used is the one of SMT-COMP'14, i.e., it gives 
  priority to the soundness of the solver, then to the number of correctly solved 
  problems over the time taken in solving the correctly solved problems. The
  difficulty of the problems is ignored. Also, some tools may be concerned 
  with fast solutions of most problems rather than eventual solution of more 
  problems. We might reconsider the scoring metric for this competition.


## CALL FOR BENCHMARKS

The competition needs to enhance the existing benchmarks with one
issued from industrial applications and tools. The organizing committee 
is interested by having this material even if it is not in the format 
required by the competition.


## CALL FOR SOLVERS

The solvers participating at the first edition will be also present
to this year edition. It is useful for the organizing committee to
know in advance how many solvers may be entering.
Thus we request that you let us know as soon as possible (and before
the deadline) if you think you may submit a solver to SL-COMP'18.
The organizing committee is willing to provide support for preparing
the incoming solvers.


## KEY DATES

Benchmark proposal     15  June,      2018
Solver registration    24  June,      2018
Competition first run   1  July,      2018
Competition last run    8  July,      2018


## RESSOURCES

The competition web site is https://www.irif.fr/~sighirea/sl-comp/18/

and the development repository is https://github.com/sl-comp/SL-COMP18


## CONTACT 

For questions about the competition, the benchmarks, or the organization 
of the competition, please contact: Mihaela.Sighireanu@irif.fr

For comments on the above topics, please consider posting on our mailing list: 
sl-comp@googlegroups.com.
Web archive: https://groups.google.com/forum/#!forum/sl-comp

