--------------------------- MODULE counter ---------------------------
(*
This spec specefies the logic that is used to implement atomix counter primitive
*)

EXTENDS Integers, TLC, Naturals

\* counter variable
VARIABLE counter

\* counter value before change
VARIABLE preValue

\* counter value after change
VARIABLE nextValue

\* counter change value
CONSTANT Delta

\* list of all possible values for a counter
CONSTANT Value

\* list of variables
vars == <<counter, preValue, nextValue>>


TypeInvariant == counter \in Int
               

\* initialize variables
Init ==
      /\ counter = 0
      /\ preValue = 0
      /\ nextValue = 0



\* set counter variable
Set(val) == 
         /\ counter' = val
         /\ UNCHANGED <<preValue, nextValue>>

\* increment counter variable
Increment(delta) ==
          /\ preValue' = counter
          /\ counter' = counter +  delta
          /\ nextValue' = counter'

\* decrement counter variable
Decrement(delta) ==
          /\ preValue' = counter
          /\ counter' = counter - delta
          /\ nextValue' = counter'


\* next state
Next ==
     \/ \E d \in Delta:
           Increment(d)
     \/ \E d \in Delta:
           Decrement(d)
     \/ \E v \in Value:
           Set(v)            

Spec == Init /\ [][Next]_<<vars>>
=============================================================================
\* Modification History
\* Last modified Thu Feb 13 19:17:59 PST 2020 by adibrastegarnia
\* Created Wed Feb 05 20:49:41 PST 2020 by adibrastegarnia
