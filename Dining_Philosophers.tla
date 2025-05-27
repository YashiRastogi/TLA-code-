------------------------ MODULE Dining_Philosophers ------------------------
EXTENDS Naturals
CONSTANT N  \* take n = 5
ASSUME N \in Nat
Procs == 0..N-1
 
VARIABLES fork, pc, state
vars == << fork, pc, state >>


forkAvailable(i) == fork[i]= N  \* initially all forks are available

\* fork 
LeftFork(i) == i 
RightFork(i) == IF (i=0) THEN (N-1) ELSE (i-1) 

 \* neighbor
Leftneighbor(i) == IF (i=N-1) THEN 0 ELSE i+1
Rightneighbor(i) == IF (i=0) THEN (N-1) ELSE (i-1)

TypeOK == \A i \in 0..N-1:
            /\ state[i] \in {"Thinking", "Hungry", "Eating"}
            /\ pc[i] \in {"J0", "H", "P", "T", "E", "E0", "R"}

Init == /\ fork = [k \in Procs |-> N]
        /\ state = [self \in Procs |-> "Thinking"]
        /\ pc = [self \in Procs |-> "J0"]


J0(self) == /\ pc[self] = "J0"
            /\ pc' = [pc EXCEPT ![self] = "H"]
            /\ UNCHANGED << fork, state >>

H(self) == /\ pc[self] = "H"
           /\ \/ /\ IF state[self]="Thinking"
                       THEN /\ state' = [state EXCEPT ![self] = "Hungry"]
                       ELSE /\ TRUE
                            /\ state' = state
                 /\ pc' = [pc EXCEPT ![self] = "J0"]
              \/ /\ pc' = [pc EXCEPT ![self] = "P"]
                 /\ state' = state
              \/ /\ pc' = [pc EXCEPT ![self] = "T"]
                 /\ state' = state
           /\ fork' = fork

P(self) == /\ pc[self] = "P"
           /\ IF self#0 /\ state[self]="Hungry"
                 THEN /\ (forkAvailable(RightFork(self)))
                      /\ fork' = [fork EXCEPT ![RightFork(self)] = self]
                      /\ pc' = [pc EXCEPT ![self] = "E"]
                 ELSE /\ IF self=0 /\ state[self]="Hungry"
                            THEN /\ (forkAvailable(LeftFork(self)))
                                 /\ fork' = [fork EXCEPT ![LeftFork(self)] = self]
                                 /\ pc' = [pc EXCEPT ![self] = "E0"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "J0"]
                                 /\ fork' = fork
           /\ state' = state

E(self) == /\ pc[self] = "E"
           /\ (forkAvailable(LeftFork(self)))
           /\ fork' = [fork EXCEPT ![LeftFork(self)] = self]
           /\ state' = [state EXCEPT ![self] = "Eating"]
           /\ pc' = [pc EXCEPT ![self] = "J0"]

E0(self) == /\ pc[self] = "E0"
            /\ (forkAvailable(RightFork(self)))
            /\ fork' = [fork EXCEPT ![RightFork(self)] = self]
            /\ state' = [state EXCEPT ![self] = "Eating"]
            /\ pc' = [pc EXCEPT ![self] = "J0"]

T(self) == /\ pc[self] = "T"
           /\ IF state[self]="Eating"
                 THEN /\ state' = [state EXCEPT ![self] = "Thinking"]
                      /\ fork' = [fork EXCEPT ![LeftFork(self)] = N]
                      /\ pc' = [pc EXCEPT ![self] = "R"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "J0"]
                      /\ UNCHANGED << fork, state >>

R(self) == /\ pc[self] = "R"
           /\ fork' = [fork EXCEPT ![RightFork(self)] = N]
           /\ pc' = [pc EXCEPT ![self] = "J0"]
           /\ state' = state

j(self) == J0(self) \/ H(self) \/ P(self) \/ E(self) \/ E0(self) \/ T(self)
              \/ R(self)

Next == (\E self \in Procs: j(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(j(self))



\* DEADLOCK is reached as all processes go to PREP, but none of them can proceed to HUNGRY waiting for the Left fork
ME == \A p \in Procs: (state[p]="Eating" => (state[Leftneighbor(p)]#"Eating" /\ state[Rightneighbor(p)]#"Eating"))
NoStarvation ==  \A p \in Procs: [] (state[p]="Hungry" => <> (state[p]="Eating"))


=============================================================================
\* Modification History
\* Last modified Tue May 27 17:57:22 IST 2025 by yashi
\* Created Tue May 27 17:03:58 IST 2025 by yashi
