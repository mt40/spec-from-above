---- MODULE MutualExclusion ----
EXTENDS Integers, TLC

CONSTANTS N  \* Number of processes

VARIABLES pc,    \* Program counter for each process
         flag,   \* Flag array for each process
         turn    \* Whose turn it is

\* TypeOK ensures all variables have valid values and types
TypeOK == /\ pc \in [1..N -> {"non-critical", "trying", "critical"}]
          /\ flag \in [1..N -> {TRUE, FALSE}]
          /\ turn \in 1..N

\* Initial state: all processes start outside critical section
Init == /\ pc = [i \in 1..N |-> "non-critical"]
        /\ flag = [i \in 1..N |-> FALSE]
        /\ turn = 1

\* Process i enters critical section if:
\* 1. It's in "trying" state
\* 2. Its flag is set to TRUE
\* 3. Either it's its turn OR no other process has its flag set
Enter(i) == /\ pc[i] = "trying"
            /\ flag[i] = TRUE
            /\ \/ turn = i
               \/ \A j \in 1..N: ~flag[j]
            /\ pc' = [pc EXCEPT ![i] = "critical"]
            /\ UNCHANGED <<flag, turn>>

\* Process i exits critical section and:
\* 1. Returns to non-critical state
\* 2. Clears its flag
\* 3. Passes turn to next process (wraps around to 1 if at N)
Exit(i) == /\ pc[i] = "critical"
           /\ pc' = [pc EXCEPT ![i] = "non-critical"]
           /\ flag' = [flag EXCEPT ![i] = FALSE]
           /\ turn' = (turn % N) + 1
           /\ UNCHANGED <<>>

\* Process i indicates it wants to enter critical section
Try(i) == /\ pc[i] = "non-critical"
          /\ pc' = [pc EXCEPT ![i] = "trying"]
          /\ UNCHANGED <<flag, turn>>

\* Next state is any process performing any of its actions
Next == \E i \in 1..N: \/ Enter(i)
                            \/ Exit(i)
                            \/ Try(i)

\* Complete specification: initial state and all possible transitions
Spec == Init /\ [][Next]_<<pc, flag, turn>>

\* Safety property: no two processes can be in critical section at same time
MutualExclusion == \A i, j \in 1..N: 
                     (i # j) => ~(pc[i] = "critical" /\ pc[j] = "critical")

Liveness == <> MutualExclusion

\* Testing ligature: =~ =< |= !~ /\ \/ <>

