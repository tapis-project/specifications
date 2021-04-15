----------------------- MODULE inc_spec1 -----------------------
(* 
This spec demonstrate an example of Increment and update pattern of two variables - Increment the first variable at a time and then update the second variable with the incremented value  of the first variable.
This spec has two variables - valX and valY. valX and valY are represented as a record with two fields: val that can take Natural numbers and ts as time stamp associated with it.
valX is incremented by 1 and valY is updated with new value of valX. This increment and update pattern is an abstraction that can be used during server/worker zero-downtime updates.
We use TLAPS to prove the safety property of the spec.
*)

EXTENDS Naturals, TLAPS

CONSTANTS MaxNum       \* Maximum number X can take
 
          
            
(*ASSUME SpecAssumption == 
         /\ MaxNum \in (Nat \ {0}) \* MaxNum can not be zero
         
 *)         
         
 
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
   
(* If val of valX is greater than the val of valY, then the time of update of valX is greater than or equal to ValY *)   
  
SafetyProperty == (valX.val > valY.val) => valX.ts >= valY.ts

----------------------------------------------------------------------------------------

Init == 
    /\  valX = [val|->1, ts|->0]
    /\  valY = [val|->0, ts|->0]
    /\  clock = 0
    /\  n = 0

Inc == 
       /\ n < MaxNum
(*
       /\ valX.ts <= clock \*<-this is required only for proof
       /\ valY.ts <= clock \*<-this is required only for proof
*)
       /\ n' = n+1
       /\ clock' = clock + 1
       /\ valX'=[val|->valX.val + 1, ts|->clock'] 
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
  BY DEF Init, IInv, TypeInvariant

<1>2. IInv /\ [Next]_vars => IInv'
  <2> SUFFICES ASSUME IInv,
                      [Next]_vars
               PROVE  IInv'
    OBVIOUS
  <2>. USE  DEF Init, IInv, TypeInvariant
  <2>1. CASE Inc
    BY <2>1 DEF Inc
  <2>2. CASE Update
    BY <2>2 DEF Update
  <2>3. CASE UNCHANGED vars
  BY  <2>3 DEF vars
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next
<1>. QED  BY <1>1, <1>2, PTL DEF Spec
---------------------------------------------------------------------------------------------------------

(* sm: It is easy to see that the timestamps can never exceed the clock value.
       This property is needed in the proof of the safety property.
*)
ClockInv ==
  /\ valX.ts <= clock
  /\ valY.ts <= clock
  
THEOREM Spec => []ClockInv
  <1>1. Init => ClockInv
  BY  DEF Init, ClockInv
  <1>2. IInv /\ ClockInv /\ [Next]_vars => ClockInv'
    <2> SUFFICES ASSUME IInv,
                        ClockInv,
                        [Next]_vars
                 PROVE  ClockInv'
      OBVIOUS 
    <2>. USE DEF Init, IInv, TypeInvariant, ClockInv
      
    <2>1. CASE Inc
     BY <2>1 DEF Inc
    <2>2. CASE Update
        BY <2>2 DEF Update
    <2>3. CASE UNCHANGED vars
        BY <2>3 DEF vars
    <2>4. QED
      BY <2>1, <2>2, <2>3 DEF Next
  
  
  <1>. QED  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec
  
  

THEOREM Spec => []SafetyProperty
<1>1. Init => SafetyProperty /\ ClockInv
  BY  DEF Init, SafetyProperty, ClockInv
(* sm: It is obviously unnecessary to refer to the actions in this part of the proof
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
*)   

  
<1>2. IInv /\ SafetyProperty /\ ClockInv /\ [Next]_vars => SafetyProperty' /\ ClockInv'
  <2> SUFFICES ASSUME IInv,
                      SafetyProperty, ClockInv,
                      [Next]_vars
               PROVE  SafetyProperty' /\ ClockInv'
    OBVIOUS
    <2>. USE  DEF Init, IInv, TypeInvariant, SafetyProperty, ClockInv
  <2>1. CASE Inc
   BY <2>1 DEF Inc
 
  <2>2. CASE Update
   BY <2>2 DEF Update
  <2>3. CASE UNCHANGED vars
     BY <2>3 DEF vars
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next

 
<1>. QED  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec
  
  
  
     
=============================================================================
\* Modification History
\* Last modified Thu Apr 15 14:27:34 CDT 2021 by spadhy
\* Last modified Tue Apr 13 13:49:11 CDT 2021 by spadhy
\* Last modified Tue Apr 13 19:28:40 CEST 2021 by merz
\* Last modified Mon Apr 12 12:32:29 CDT 2021 by spadhy
\* Created Tue Mar 30 13:58:07 CDT 2021 by spadhy
