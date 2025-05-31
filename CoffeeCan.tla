----------------------------- MODULE CoffeeCan -----------------------------

(***************************Problem set************************************

You are given a can that contains a finite number of black and white beans.
Let’s say:
    -> Black beans are denoted by B
    -> White beans are denoted by W

The process follows these rules:
 -> Randomly pick two beans from the can (without looking).
 -> Based on the colors of the two beans, do the following:
    -> If the two beans are the same color (both black or both white):
        -> Throw both away
        -> Put back one black bean
    -> If the two beans are different colors (one black, one white):
        -> Throw both away
        -> Put back one white bean
    -> Repeat this process until only one bean remains in the can.
    
******************************************************************************)
EXTENDS Naturals

CONSTANT MaxBeanCount

ASSUME MaxBeanCount \in Nat /\ MaxBeanCount >= 1

VARIABLES can

\* The set of all possible cans
Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]

\* Possible values the can variable can take on
TypeInvariant == can \in Can

\* Initialize can so it contains between 1 and MaxBeanCount beans
Init == can \in {c \in Can : c.black + c.white \in 1..MaxBeanCount}

\* Number of beans currently in the can
BeanCount == can.black + can.white

\* Pick two black beans; throw both away, put one black bean in
PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Pick two white beans; throw both away, put one black bean in
PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

\* Pick one bean of each color; put white back, throw away black
PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Termination action to avoid triggering deadlock detection
Termination ==
    /\ BeanCount = 1
    /\ UNCHANGED can

\* Next-state relation: what actions can be taken?
Next ==
    \/ PickSameColorWhite
    \/ PickSameColorBlack
    \/ PickDifferentColor
    \/ Termination

\* Action formula: every step decreases the number of beans in the can
MonotonicDecrease == [][BeanCount' < BeanCount]_can

\* Liveness property: we eventually end up with one bean left
EventuallyTerminates == <>(ENABLED Termination)

\* Loop invariant: every step preserves white bean count mod 2
LoopInvariant == [][can.white % 2 = 0 <=> can'.white % 2 = 0]_can

\* Hypothesis: If we start out with an even number of white beans, we end up
\* with a single black bean. Otherwise, we end up with a single white bean.
TerminationHypothesis ==
    IF can.white % 2 = 0
    THEN <>(can.black = 1 /\ can.white = 0)
    ELSE <>(can.black = 0 /\ can.white = 1)

\* Start out in a state defined by the Init operator and every step is one
\* defined by the Next operator. Assume weak fairness so the system can't
\* stutter indefinitely: we eventually take some beans out of the can.
Spec ==
    /\ Init
    /\ [][Next]_can
    /\ WF_can(Next)

\* What we want to show: that if our system follows the rules set out by the
\* Spec operator, then all our properties and assumptions will be satisfied.
THEOREM Spec =>
    /\ TypeInvariant
    /\ MonotonicDecrease
    /\ EventuallyTerminates
    /\ LoopInvariant
    /\ TerminationHypothesis



=============================================================================
\* Modification History
\* Last modified Sat May 31 16:38:29 IST 2025 by yashi
\* Created Sat May 31 15:26:29 IST 2025 by yashi
