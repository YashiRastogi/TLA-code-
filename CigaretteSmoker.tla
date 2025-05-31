-------------------------- MODULE CigaretteSmoker --------------------------

(*************************** CigaretteSmoker ********************************
In this problem, there are four entities: an agent and three smokers.
# Agent: Possesses an infinite supply of three ingredients required to make a 
cigarette—tobacco, paper, and matches.

# Smokers: Each smoker has an infinite supply of one of the three ingredients:
1. Smoker A has tobacco.
2. Smoker B has paper.
3. Smoker C has matches.

The agent randomly places two of the three ingredients on a shared table. 
The smoker who has the third ingredient (the one not on the table) picks up 
the two ingredients, makes a cigarette, smokes it, and then signals the agent 
to place the next set of ingredients

******************************************************************************)
EXTENDS Integers, FiniteSets \* for subset

CONSTANTS Ingredients, Offers
VARIABLES smokers, dealer 

vars == <<smokers, dealer>>

ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1
       
\* Every element n in Offers must be a set of exactly 2 ingredients.
    
TypeOK ==  /\ smokers \in [Ingredients ->[smoking : BOOLEAN]] \* smoker has which Ingredient and it is currently not smoking 
           /\ \/ dealer \in Offers 
              \/ dealer = {}

ChooseOne (S, P(_)) == CHOOSE x \in S: P(x) /\ \A y \in S : P(y) => y = x

\* ChooseOne (S, P(_)) == CHOOSE (x \in S: P(x)) /\ (\A y \in S : P(y)) => y = x
(*The notation P(_) in TLA+ is a function signature — it declares that P is a 
   function with one argument, but doesn’t name the argument yet.*)

(************************** ChooseOne **********************************
This defines a helper operator called ChooseOne. Its purpose is to safely
pick exactly one element from a set S that satisfies a condition P.

CHOOSE x \in Ingredients : 
  smokers[x].smoking /\ 
  \A y \in Ingredients : smokers[y].smoking => y = x
Which picks the only smoker who is smoking.

smokers[paper]         \* gives [smoking |-> TRUE]
smokers[paper].smoking \* gives TRUE


************************************************************************)


Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers
        
startSmoking == /\ dealer # {}
                /\ smokers' = [r \in Ingredients |-> [smoking |-> {r} \union dealer = Ingredients]]
                /\ dealer' = {}
                
stopSmoking == /\ dealer = {} 
               /\ LET r == ChooseOne(Ingredients, LAMBDA x: smokers[x].smoking)
                  IN smokers' = [smokers EXCEPT ![r].smoking = FALSE]
               /\ dealer' \in Offers
               
(*
LAMBDA x : <expression involving x>
LAMBDA x : x * x
*)


             
Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars

FairsSpec == Spec /\ WF_vars(Next)

AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1 

(**************How to execute**************
What is behaviour spec?
Click on temporal formula -> FairsSpec
what is Model ?
Offers -> { {"tobacco", "paper"}, {"tobacco", "matches"}, {"paper", "matches"} }
Ingredients -> {"tobacco", "paper", "matches"}
Invariants : TypeOK
Properties : AtMostOne        
**********************************)

=============================================================================
\* Modification History
\* Last modified Sat May 31 14:28:29 IST 2025 by yashi
\* Created Fri May 30 14:43:25 IST 2025 by yashi
