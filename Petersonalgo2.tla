--------------------------- MODULE Petersonalgo2 ---------------------------
(***************************************************************************)
(* This is a specification following Peterson's algorithm as documented at *)
(* https://en.wikipedia.org/wiki/Peterson%27s_algorithm.  I also hope for  *)
(* this to be an intermediate introduction to how a TLA+ spec reads if     *)
(* you're already familiar with the basics of TLA+.                        *)
(*                                                                         *)
(* This is a loose translation of the original pseudo-code that attempts   *)
(* to preserve the intent of the algorithm rather than following the       *)
(* pseudo-code to the T.  This hopefully results in a more natural TLA+    *)
(* specification rather than a mechanical logical translation of           *)
(* imperative code.                                                        *)
(*                                                                         *)
(* Peterson's algorithm is an attempt to allow two concurrent processes to *)
(* access the same resource (alternatively enter a critical section)       *)
(* exclusively.  That is the resource should be only accessed by at most a *)
(* single process at any time.                                             *)
(*                                                                         *)
(* The central intuition behind Peterson's algorithm is to use three       *)
(* separate items to coordinate efforts between the processes: one item to *)
(* coordinate whose turn it is to access the resource and then an          *)
(* additional flag per process to indicate that a process wishes to access *)
(* the resource.  It might seem that the single item keeping track of      *)
(* whose turn it is is enough to mediate access to the resource.           *)
(* Unfortunately, this breaks down if one process wishes to repeatedly     *)
(* access the resource whereas the other process remains idle the entire   *)
(* time.  For more details see                                             *)
(* https://github.com/changlinli/bad-peterson-tlaplus for what goes wrong. *)
(*                                                                         *)
(* There is one meta-invariant here that I attempt to preserve here.       *)
(* Peterson's algorithm is meant to be used in an environment with few     *)
(* atomicity guarantees.  In particular it assumes you can atomically set  *)
(* those three items mentioned earlier and have their changes propagate    *)
(* instantly, but no more.                                                 *)
(*                                                                         *)
(* That means each step in a TLA+ behavior should only change at most one  *)
(* of the three aforementioned items (although the internal state of a     *)
(* process could change as well).  Each step should also only read from at *)
(* most item (in addition to reading a process's internal state).  Finally *)
(* no step should both read and write to one of the three items (although  *)
(* a step could read a process's internal state and then write to one of   *)
(* the three items and modify its own internal state all in one go).       *)
(***************************************************************************)

EXTENDS Integers

VARIABLES turn, processState, flag 

vars == <<turn, processState, flag>> 

TypeOK ==
    /\ \A p \in {0, 1} : flag[p] \in {TRUE, FALSE}
    /\ turn \in {0, 1}
    /\ \A p \in {0, 1} : processState[p] \in {"idle", "sentRequest", "waiting", "critical"}


Init ==
    /\ flag = [i \in {0, 1} |-> FALSE]
    /\ turn \in {0, 1}
    /\ processState = [i \in {0, 1} |-> "idle"]
      
ProcessRequestFlag(p) ==
    /\ processState[p] = "idle"
    /\ flag' = [flag EXCEPT ![p] = TRUE]
    /\ processState' = [processState EXCEPT ![p] = "sentRequest"]
    /\ UNCHANGED <<turn>>

ProcessBeginWaiting(p) ==
    /\ processState[p] = "sentRequest"
    /\ turn' = 1 - p
    /\ processState' = [processState EXCEPT ![p] = "waiting"]
    /\ UNCHANGED <<flag>>

ProcessEnterCritical(p) ==
    /\ processState[p] = "waiting"
    /\ (flag[(1 - p)] = FALSE \/ turn = p)
    /\ processState' = [processState EXCEPT ![p] = "critical"]
    /\ UNCHANGED <<flag, turn>>

ProcessExitCritical(p) ==
    /\ processState[p] = "critical"
    /\ processState' = [processState EXCEPT ![p] = "idle"]
    /\ flag' = [flag EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<turn>>

Next ==
    \E p \in {0, 1} :
        \/ ProcessRequestFlag(p)
        \/ ProcessBeginWaiting(p)
        \/ ProcessEnterCritical(p)
        \/ ProcessExitCritical(p)

Spec == Init /\ [][Next]_vars 

SpecWithFairness == Spec /\ WF_vars(Next) /\ \A p \in {0, 1} : WF_vars(ProcessRequestFlag(p))

MutualExclusion == ~(processState[0] = "critical" /\ processState[1] = "critical")

THEOREM Spec => []MutualExclusion

WillEventuallyEnterCritical == <>(processState[0] = "critical") /\ <>(processState[1] = "critical")

THEOREM SpecWithFairness => WillEventuallyEnterCritical


CanOnlyBeCriticalIfTurn == \A p \in {0, 1} : processState[p] = "critical" => turn = p
(*A process is only allowed to be in the critical section if it is currently its turn.*)
\*THEOREM Spec => []TypeOK

=============================================================================
\* Modification History
\* Last modified Tue May 20 22:14:22 IST 2025 by yashi
\* Created Sun May 18 23:25:58 IST 2025 by yashi
