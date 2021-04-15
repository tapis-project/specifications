------------------------ MODULE IncUpdatePatternList ------------------------

EXTENDS Naturals, FiniteSets, FiniteSetTheorems, Sequences, SequenceOpTheorems,TLAPS

CONSTANTS MaxNum,       \* Maximum number X can take
          A,
          W
 
          
            
ASSUME SpecAssumption == 
         /\ MaxNum \in (Nat \ {0})
         /\ A # {}
         /\ W # {}
          
         
 
---------------------------------------------------------------------------------------          
          
VARIABLES valX, valY, clock, n, WtoA
                   
 
 
 vars == <<valX, valY, clock, n, WtoA>>  
 \*A == {"a1","a2"}
 \*W == {"w1","w2","w3"}

(*
***********************************
Invariants and Temporal Properties
***********************************
*)
AwithZero == A \cup {"-"}

\* An invariant: ensures all the variables maintain the proper types.
TypeInvariant == 
   /\ valX \in [A->[val:Nat, ts: Nat]]
   /\ valY \in [W->[val:Nat, ts: Nat]]
   /\ WtoA \in [W -> AwithZero] 
   /\ clock \in Nat
   /\ n \in Nat
  
SafetyProperty == \A w \in W: WtoA[w]# "-" =>((valX[WtoA[w]].val > valY[w].val) => valX[WtoA[w]].ts >= valY[w].ts)


Init == 
    /\  WtoA = [w \in W |-> "-"]
    /\  valX = [a \in A |->[val|->1, ts|->0]]
    /\  valY = [w \in W |->[val|->0, ts|->0]]
    /\  clock = 0
    /\  n = 0

(*AssignWtoA(w,a) == 
    /\ WtoA[w] = "-"
    /\ valY[w].val < valX[a].val \* This is for proof
    /\ valY[w].ts <= valX[a].ts   \* This is for proof
    /\ clock' = clock + 1
    /\ WtoA'= [WtoA EXCEPT ![w]=a]
    /\ UNCHANGED<<valX, valY, n>>
*)
Inc(a) == 
       /\ n < MaxNum
       \*/\ valX[a].ts<=clock
       \*/\ \A w \in W: valY[w].ts<=clock
       
       /\ n' = n+1
       /\ clock' = clock + 1
       /\ valX'=[valX EXCEPT ![a]=[val|->valX[a].val + 1, ts|->clock']] 
       /\ UNCHANGED<<valY, WtoA>>

(*Update(a,w) ==  
        /\ WtoA[w]=a
        /\ valY[w].val < valX[a].val
        /\ clock' = clock + 1
        /\ valY'=[valY EXCEPT ![w]=[val|->valX[a].val, ts|->clock']] 
        /\ UNCHANGED<<valX,WtoA, n>>  *) 

Update(a,w) ==  
        /\ WtoA[w]="-"
        /\ valY[w].val < valX[a].val
        \*/\ valY[w].ts <= valX[a].ts   \* This is for proof
        /\ clock' = clock + 1
        /\ WtoA'= [WtoA EXCEPT ![w]=a]
        /\ valY'=[valY EXCEPT ![w]=[val|->valX[a].val, ts|->clock']] 
        /\ UNCHANGED<<valX,WtoA, n>>    

Next == 
     \*\/ \E a \in A, w \in W: AssignWtoA(w,a)
     \/ \E a \in A: Inc(a)
     \/ \E a \in A, w \in W:Update(a,w)

Spec == Init /\ [][Next]_vars  
FairSpec == Spec 
            \*/\ WF_vars(\E w \in W, a \in A: AssignWtoA(w, a))
            /\ WF_vars(\E a \in A: Inc(a))
            /\ WF_vars(\E w \in W, a \in A: Update(w, a))


------------------------------------------------------------------------------------------------------------
IInv == TypeInvariant 
THEOREM TypeCorrect == Spec => []IInv

<1>1. Init => IInv
  BY SpecAssumption DEF Init, IInv, TypeInvariant, AwithZero

<1>2. IInv /\ [Next]_vars => IInv'
  <2> SUFFICES ASSUME IInv,
                      [Next]_vars
               PROVE  IInv'
    OBVIOUS
  <2>. USE SpecAssumption DEF Init, IInv, TypeInvariant, AwithZero
  (*<2>1. ASSUME NEW a \in A,
               NEW w \in W,
               AssignWtoA(w,a)
        PROVE  IInv'
        BY <2>1 DEF AssignWtoA*)
  <2>2. ASSUME NEW a \in A,
               Inc(a)
        PROVE  IInv'
        BY <2>2 DEF Inc
  <2>3. ASSUME NEW a \in A,
               NEW w \in W,
               Update(a,w)
        PROVE  IInv'
        BY <2>3 DEF Update
  <2>4. CASE UNCHANGED vars
        BY <2>4 DEF vars
  <2>5. QED
    BY  <2>2, <2>3, <2>4 DEF Next
 
<1>. QED  BY <1>1, <1>2, PTL DEF Spec
---------------------------------------------------------------------------------------------------------
ClockInv ==
  /\ \A a \in A: valX[a].ts <= clock
  /\ \A w \in W: valY[w].ts <= clock
  
THEOREM Spec => []ClockInv
  <1>1. Init => ClockInv
  BY  DEF Init, ClockInv
  <1>2. IInv /\ ClockInv /\ [Next]_vars => ClockInv'
    <2> SUFFICES ASSUME IInv,
                        ClockInv,
                        [Next]_vars
                 PROVE  ClockInv'
      OBVIOUS
    <2> USE DEF IInv, TypeInvariant, ClockInv 
    <2>1. ASSUME NEW a \in A,
                 Inc(a)
          PROVE  ClockInv'
          BY<2>1 DEF Inc
    <2>2. ASSUME NEW a \in A,
                 NEW w \in W,
                 Update(a,w)
          PROVE  ClockInv'
          BY <2>2 DEF Update
    <2>3. CASE UNCHANGED vars
        BY <2>3 DEF vars
    <2>4. QED
      BY <2>1, <2>2, <2>3 DEF Next
  
  
  <1>. QED  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec
  

  
THEOREM SafetyPropertyTheorem == Spec => []SafetyProperty
<1>1. Init => SafetyProperty /\ ClockInv
    BY SpecAssumption DEF Init, IInv, TypeInvariant, SafetyProperty, AwithZero, ClockInv
  
<1>2. IInv /\ SafetyProperty /\ ClockInv /\ [Next]_vars => SafetyProperty'/\ClockInv'
  <2> SUFFICES ASSUME IInv,
                      SafetyProperty,
                      [Next]_vars,
                      ClockInv
               PROVE  SafetyProperty'/\ClockInv'
    OBVIOUS
  <2>. USE SpecAssumption DEF Init, IInv, TypeInvariant, AwithZero,SafetyProperty, ClockInv
  (*<2>1. ASSUME NEW a \in A,
               NEW w \in W,
               AssignWtoA(w,a)
        PROVE  SafetyProperty'
        BY <2>1 DEF AssignWtoA*)
  <2>2. ASSUME NEW a \in A,
               Inc(a)
        PROVE  SafetyProperty'/\ ClockInv'
        BY <2>2 DEF Inc
  <2>3. ASSUME NEW a \in A,
               NEW w \in W,
               Update(a,w)
        PROVE  SafetyProperty'/\ ClockInv'
        BY <2>3 DEF Update
  <2>4. CASE UNCHANGED vars
        BY <2>4 DEF vars
  <2>5. QED
    BY  <2>2, <2>3, <2>4 DEF Next
 
 
<1>. QED  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec
  

=============================================================================
\* Modification History
\* Last modified Thu Apr 15 16:08:18 CDT 2021 by spadhy
\* Created Tue Apr 06 13:20:19 CDT 2021 by spadhy
