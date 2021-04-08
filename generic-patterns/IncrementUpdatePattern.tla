----------------------- MODULE IncrementUpdatePattern -----------------------


EXTENDS Naturals, FiniteSets, FiniteSetTheorems, Sequences, SequenceOpTheorems,TLAPS

CONSTANTS MaxNum       \* Maximum number X can take
 
          
            
ASSUME SpecAssumption == 
         /\ MaxNum \in (Nat \ {0})
         
          
         
 
---------------------------------------------------------------------------------------          
          
VARIABLES valX, valY, clock, n
                   
 
 
 vars == <<valX, valY, clock, n>>  


(*
***********************************
Invariants and Temporal Properties
***********************************
*)

\* An invariant: ensures all the variables maintain the proper types.
TypeInvariant == 
   /\ valX \in [val:Nat, ts: Nat]
   /\ valY \in [val:Nat, ts: Nat]
   /\ clock \in Nat
   /\ n \in Nat
  
SafetyProperty == (valX.val > valY.val) => valX.ts >= valY.ts


Init == 
    /\  valX = [val|->1, ts|->0]
    /\  valY = [val|->0, ts|->0]
    /\  clock = 0
    /\  n = 0

Inc == 
       /\ n < MaxNum
       /\ valX.ts<=clock \*<-this is only for proof
       /\ valY.ts<=clock \*<-this is only for proof
       /\ n' = n+1
       /\ clock' = clock + 1
       
       /\ valX'=[val|->valX.val + 1, ts|->clock'] 
       \*/\ valX'.val = valX.val + 1 
       \*/\ valX'.ts= clock'
       /\ UNCHANGED<<valY>>

Update ==  
        /\ valY.val < valX.val
        /\ clock' = clock + 1
        /\ valY'=[val|->valX.val, ts|->clock'] 
        /\ UNCHANGED<<valX,n>>    

Next == Inc \/ Update

Spec == Init /\ [][Next]_vars  


------------------------------------------------------------------------------------------------------------
IInv == TypeInvariant 
THEOREM TypeCorrect == Spec => []IInv
<1>1. Init => IInv
  BY SpecAssumption DEF Init, IInv, TypeInvariant

<1>2. IInv /\ [Next]_vars => IInv'
  <2> SUFFICES ASSUME IInv,
                      [Next]_vars
               PROVE  IInv'
    OBVIOUS
  <2>. USE SpecAssumption DEF Init, IInv, TypeInvariant
  <2>1. CASE Inc
    BY <2>1 DEF Inc
  <2>2. CASE Update
    BY <2>2 DEF Update
  <2>3. CASE UNCHANGED vars
  BY SpecAssumption, <2>3 DEF vars
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next
   
    
    
<1>. QED  BY <1>1, <1>2, PTL DEF Spec
---------------------------------------------------------------------------------------------------------
  
THEOREM SafetyPropertyTheorem == Spec => []SafetyProperty
<1>1. Init => SafetyProperty

<2> SUFFICES ASSUME Init
                PROVE  SafetyProperty
     OBVIOUS
    <2>. USE SpecAssumption DEF Init, IInv, TypeInvariant, SafetyProperty
    <2>1. CASE Inc
        BY <2>1 DEF Inc
    <2>2. CASE Update
        BY <2>2 DEF Update
    <2>3. CASE UNCHANGED vars
        BY SpecAssumption, <2>3 DEF vars
    <2>4. QED
        BY <2>1, <2>2, <2>3 DEF SafetyProperty
   

  
<1>2. IInv /\ SafetyProperty /\ [Next]_vars => SafetyProperty'
  <2> SUFFICES ASSUME IInv,
                      SafetyProperty,
                      [Next]_vars
               PROVE  SafetyProperty'
    OBVIOUS
    <2>. USE SpecAssumption DEF Init, IInv, TypeInvariant, SafetyProperty
  <2>1. CASE Inc
  BY <2>1 DEF Inc
    (*<3>1. clock'>clock
        BY <2>1 DEF Inc
    <3>2. valX'.val>valX.val
         BY <2>1 DEF Inc
    <3>3. valX'.ts > valX.ts
         BY <2>1,<3>1 DEF Inc
    <3>4. valY'.ts < clock'  
         BY <2>1,<3>1 DEF Inc
    <3>5. QED
     BY <2>1,<3>1,<3>2,<3>3,<3>4 DEF Inc  *) 
  <2>2. CASE Update
   BY <2>2 DEF Update
  <2>3. CASE UNCHANGED vars
     BY <2>3 DEF vars
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next

 
<1>. QED  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec
  
  
  
     
=============================================================================
\* Modification History
\* Last modified Thu Apr 08 15:16:12 CDT 2021 by spadhy
\* Created Tue Mar 30 13:58:07 CDT 2021 by spadhy
