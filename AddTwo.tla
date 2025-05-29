------------------------------- MODULE AddTwo -------------------------------
EXTENDS Naturals, TLAPS

VARIABLE x 

vars == <<x>>

TypeOK == x \in Nat

Init == x = 0

Next == x' = x+2

Spec == Init /\ [][Next]_vars 

(*****************************************************

| You write | It means                               |
| --------- | -------------------------------------- |
| `==`      | "This is a definition or a name."      |
| `THEOREM` | "This is a claim that must be proved." |

******************************************************)


THEOREM Spec => []TypeOK
    <1>a. Init => TypeOK
        BY DEF Init, TypeOK
    <1>b. TypeOK /\ UNCHANGED vars => TypeOK'
        BY DEF TypeOK, vars
    <1>c TypeOK /\ Next => TypeOK'
        BY DEF TypeOK, Next
    <1> QED BY PTL , <1>a, <1>b, <1>c DEF Spec
    
(**********************************************************************

This concludes the proof using PTL (Propositional Temporal Logic rule):

What this rule says:
If:
-> the invariant holds initially (<1>a)
-> it is preserved in every stuttering step (<1>b)
-> it is preserved in every normal step (<1>c)

Then: Spec => []TypeOK

Therefore, we have proved that x will always be a natural number in all 
behaviors defined by Spec.

************************************************************************)    

    
a|b == \E c \in Nat : a*c = b

Even == 2|x

THEOREM Spec => []Even
  <1>a. Init => Even
    BY DEF Init, Even, | (*divide sign defined above *)
  <1>b. Even /\ UNCHANGED vars => Even'
    BY DEF Even, vars
  <1>c. Even /\ Next => Even'
    BY \A c \in Nat : c+1 \in Nat /\ 2*(c+1) = 2*c + 2, Zenon
    DEF TypeOK, Even, Next, |
  <1> QED BY PTL, <1>a, <1>b, <1>c DEF Spec
  
(*************************** Zenon ***************************************

Zenon is an automatic theorem prover used by the TLA+ Proof System (TLAPS) 
to automatically prove certain logical and arithmetic facts.

Zenon handles:
-> Propositional logic
-> Basic set theory
-> Arithmetic over natural numbers
-> Quantifiers (∃, ∀)
It doesn’t understand TLA+ temporal logic (like [], <>, ~>), but it’s great 
   for local reasoning.

****************************************************************************)
  
  
(*********************************************************
This invokes the temporal logic rule (PTL), which says:

If:
-> Even holds at the beginning
-> and it's preserved in stuttering steps
-> and it's preserved in real steps

Then: Spec => []Even

QED =>  Quod Erat Demonstrandum — “the proof is done”

*********************************************************)

(****************************************************************************************
| Step   | Goal                              | Why it’s true                            |
| ------ | --------------------------------- | ---------------------------------------- |
| `<1>a` | `x = 0` implies even              | `0` is divisible by 2                    |
| `<1>b` | If `x` doesn’t change, still even | `x' = x` keeps the same value            |
| `<1>c` | `x + 2` is still even             | Even + Even = Even (shown using algebra) |
| `QED`  | Combine all above steps           | Standard PTL proof rule                  |

****************************************************************************************)

(**************************How to execute it ********************************************
It keeps running continuously, because there is no termination condition.
To limit this, you can put constraints that check only up to a certain limit.
For that, go to Model -> Additional Spec Options -> State Constraint, then write x <= 2000.
You can use any other number, maybe x <= 40, depending on your needs.
*****************************************************************************************)
=============================================================================
\* Modification History
\* Last modified Thu May 29 15:31:54 IST 2025 by yashi
\* Created Wed May 28 14:54:19 IST 2025 by yashi
