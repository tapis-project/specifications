------------------------- MODULE producer_consumer -------------------------

EXTENDS Naturals, Sequences, SequenceTheorems, TLAPS

CONSTANTS MaxTotalNumberOfItemsProduced, (* max number of items that can be produced by a producer *)
          MaxBufferLen                   (* max buffer capacity for produced items *)

ASSUME Assumption == 
         /\ MaxTotalNumberOfItemsProduced \in Nat
         /\ MaxBufferLen \in (Nat \ {0}) (* MaxbufferLen should be atleast 1 *)

-----------------------------------------------------------------------------

VARIABLES buffer, num_of_items_produced, num_of_items_consumed 
         
vars == <<buffer, num_of_items_produced, num_of_items_consumed>>  
 

Item == [type: {"item"}]
-----------------------------------------------------------------------------

(* Temporarl property: Any item that is produced gets eventually consumed *)
AllItemsConsumed == <>[](Len(buffer) = 0 /\ num_of_items_produced = num_of_items_consumed) 


(* Type Correctness *)
TypeInvariant == /\ buffer \in Seq(Item)
                 /\ Len(buffer) \in 0..MaxBufferLen 
                 /\ num_of_items_produced \in 0..MaxTotalNumberOfItemsProduced
                 /\ num_of_items_consumed \in 0..MaxTotalNumberOfItemsProduced
                
                 
                 

(* An Invariant: num of items consumed is always less than or equal to the total number of items produced *)
SafetyProperty == num_of_items_produced = num_of_items_consumed + Len(buffer)

------------------------------------------------------------------------------

(* Specification *)

Init == /\ buffer = <<>>
        /\ num_of_items_produced = 0 
        /\ num_of_items_consumed = 0              

Produce(item) == /\ Len(buffer) < MaxBufferLen
                 /\ num_of_items_produced < MaxTotalNumberOfItemsProduced
                 /\ buffer'= Append(buffer, item)
                 /\ num_of_items_produced' = num_of_items_produced + 1
                 /\ UNCHANGED<<num_of_items_consumed >>
           
Consume == /\ Len(buffer) > 0
           /\ buffer'= Tail(buffer)
           /\ num_of_items_consumed' = num_of_items_consumed + 1 
           /\ UNCHANGED<<num_of_items_produced>>          
           
Next == 
       \/ \E item \in Item: Produce(item)
       \/ Consume

Spec == Init /\ [][Next]_vars

FairSpec == Spec 
           /\ WF_vars(\E item \in Item: Produce(item))
           /\ WF_vars(Consume)
           
-------------------------------------------------------------------------------
 (* Proof *)
 
 
 
(* ---- Proof structure ---- *)
(* ----
   Correct = ...        \* The invariant you really want to prove
   IInv = ... /\ Correct    \* the inductive invariant

    THEOREM Spec=>[]Correct
    <1>1. Init => IInv
    <1>2. IInv /\ [Next]_vars => IInv'
    <1>3. IInv => Correct
    <1>4. QED
     BY <1>1, <1>2, <1>3 
  ------------------------ *)   
     
     
 
  (*---- Inductive Invariant -------*)
  
  IInv == /\ TypeInvariant
          /\ SafetyProperty  
 
(* While checking for the inductive invariant in TLC , Seq operator needs to be redefine as MySeq. *)

MySeq(P) == UNION {[1..n -> P] : n \in 0..MaxBufferLen}              

(* ---- Dr.Stephen's proof decomposition 1 ------- *)
THEOREM Spec => []IInv
<1>1. Init => IInv
  BY Assumption DEF Init, IInv, TypeInvariant, SafetyProperty
<1>2. IInv /\ [Next]_vars => IInv'
  <2> SUFFICES ASSUME IInv,
                      [Next]_vars
               PROVE  IInv'
    OBVIOUS
  <2>. USE Assumption DEF IInv, TypeInvariant, SafetyProperty
  <2>1. ASSUME NEW item \in Item,
               Produce(item)
        PROVE  IInv'
    BY <2>1, Assumption DEF Produce
  <2>2. CASE Consume
    <3>. Len(buffer') = Len(buffer)-1
      BY <2>2, HeadTailProperties DEF Consume
    <3>. QED  BY <2>2 DEF Consume
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF vars
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next
<1>. QED  BY <1>1, <1>2, PTL DEF Spec


(*------ Decomposition 1' ------ *)
THEOREM Spec => []IInv
<1>1. Init => IInv
  BY Assumption DEF Init, IInv, TypeInvariant, SafetyProperty
<1>2. IInv /\ [Next]_vars => IInv'
  <2> SUFFICES ASSUME IInv,
                      [Next]_vars
               PROVE  IInv'
    OBVIOUS
  <2>. USE Assumption DEF IInv, TypeInvariant, SafetyProperty
  <2>1. ASSUME NEW item \in Item,
               Produce(item)
        PROVE  IInv'
    BY <2>1, Assumption DEF Produce
  <2>2. CASE Consume
    <3>. Len(buffer') = Len(buffer)-1
      BY <2>2 DEF Consume
    <3>. QED BY <2>2 DEF Consume
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF vars
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next
<1>. QED  BY <1>1, <1>2, PTL DEF Spec


(* ----- Proof decomposition 2 ------- *)

THEOREM TypeCorrect == Init => IInv
  <1> SUFFICES ASSUME Init
               PROVE  IInv
    OBVIOUS
  <1>1. TypeInvariant
     BY Assumption DEF Init, IInv, TypeInvariant 
  <1>2. SafetyProperty
     BY DEF Init, IInv, SafetyProperty 
  <1>3. QED
    BY <1>1, <1>2 DEF IInv

THEOREM SecondStep== IInv /\[Next]_vars => IInv'
  <1> SUFFICES ASSUME IInv,
                      [Next]_vars
               PROVE  IInv'
    OBVIOUS
  <1>1. CASE Next 
    <2>. USE Assumption DEF IInv, TypeInvariant, SafetyProperty
    <2>1. ASSUME NEW item \in Item,
                 Produce(item)
          PROVE  IInv'
         BY <2>1, Assumption DEF Produce
          
    <2>2. CASE Consume
      <3>. Len(buffer') = Len(buffer)-1
      BY <2>2 DEF Consume
      <3>. QED  BY <2>2 DEF Consume
    <2>3. QED
      BY <1>1, <2>1, <2>2 DEF Next
  <1>2. CASE UNCHANGED vars 
   BY Assumption, <1>2 DEF vars, IInv, TypeInvariant, SafetyProperty
  <1>3. QED
    BY <1>1, <1>2
    
  THEOREM  Spec =>[]IInv
  BY TypeCorrect, SecondStep, PTL DEF Spec
  
  
(*USE Assumption DEF vars, Item,
                    Init, Next, Spec,
                    Produce, Consume,
                    TypeInvariant, SafetyProperty*)
  
(* ----- Proof decomposition 3 ------- *)
  THEOREM Spec => []IInv
    <1>1. Init => IInv
    BY Assumption DEF Init, IInv, TypeInvariant, SafetyProperty
    <1>2. IInv /\ [Next]_vars => IInv'
      <2> SUFFICES ASSUME IInv, [Next]_vars
                   PROVE  IInv'
        OBVIOUS
      <2>1. TypeInvariant'
        <3>1. ASSUME NEW item \in Item,
                     Produce(item)
              PROVE  TypeInvariant'
              BY <3>1, Assumption DEF Produce, IInv, TypeInvariant, SafetyProperty
       <3>2. CASE Consume
        BY <3>2, Assumption DEF Consume, IInv, TypeInvariant, SafetyProperty
       <3>3. CASE UNCHANGED vars
           BY Assumption, <3>3 DEF vars, IInv, TypeInvariant, SafetyProperty
        <3>4. QED
          BY <3>1, <3>2, <3>3 DEF Next
      <2>2. SafetyProperty'
        <3>1. ASSUME NEW item \in Item,
                     Produce(item)
              PROVE  SafetyProperty'
        BY <3>1, Assumption DEF Produce, IInv, TypeInvariant, SafetyProperty      
        <3>2. CASE Consume
         <4>. Len(buffer') = Len(buffer)-1
             BY <3>2 DEF Consume, IInv, TypeInvariant, SafetyProperty    
         <4>. QED  BY <3>2 DEF Consume, IInv, TypeInvariant, SafetyProperty       
        <3>3. CASE UNCHANGED vars
        BY Assumption, <3>3 DEF vars, IInv, TypeInvariant, SafetyProperty   
        <3>4. QED
          BY <3>1, <3>2, <3>3 DEF Next
      <2>3. QED
        BY <2>1, <2>2, PTL DEF IInv
  
   <1>. QED  BY <1>1, <1>2, PTL DEF Spec

(* Modification to the above decomposition 3 *)
 THEOREM Spec => []IInv
    <1>1. Init => IInv
    BY Assumption DEF Init, IInv, TypeInvariant, SafetyProperty
    <1>2. IInv /\ [Next]_vars => IInv'
      <2> SUFFICES ASSUME IInv, [Next]_vars
                   PROVE  IInv'
        OBVIOUS
      <2>1. TypeInvariant'
        <3>1. ASSUME NEW item \in Item,
                     Produce(item)
              PROVE  TypeInvariant'
              BY <3>1, Assumption DEF Produce, IInv, TypeInvariant, SafetyProperty   
       <3>2. CASE Consume
        BY <3>2, Assumption DEF Consume, IInv, TypeInvariant, SafetyProperty 
       <3>3. CASE UNCHANGED vars
           BY Assumption, <3>3 DEF vars, IInv, TypeInvariant, SafetyProperty 
        <3>4. QED
          BY <3>1, <3>2, <3>3 DEF Next
      <2>2. SafetyProperty'
        <3>1. ASSUME NEW item \in Item,
                     Produce(item)
              PROVE  SafetyProperty'
        BY <3>1, Assumption DEF Produce, IInv, TypeInvariant, SafetyProperty       
        <3>2. CASE Consume
          <4>1. ASSUME NEW item \in Item,
                       Produce(item)
                PROVE  SafetyProperty'
                BY <4>1, Assumption DEF Produce, IInv, TypeInvariant, SafetyProperty  
          <4>2. CASE Consume
          <5>. Len(buffer') = Len(buffer)-1
             BY <3>2, Assumption DEF Consume, IInv, TypeInvariant, SafetyProperty 
          <5>. QED  BY <4>2 DEF Consume, IInv, TypeInvariant, SafetyProperty    
          <4>3. CASE UNCHANGED vars
          BY <4>3 DEF vars, IInv, TypeInvariant, SafetyProperty 
          <4>4. QED
            BY <4>1, <4>2, <4>3 DEF Next
           
        <3>3. CASE UNCHANGED vars
        BY Assumption, <3>3 DEF vars, IInv, TypeInvariant, SafetyProperty 
        <3>4. QED
          BY <3>1, <3>2, <3>3 DEF Next
      <2>3. QED
        BY <2>1, <2>2, PTL DEF IInv
  
   <1>. QED  BY <1>1, <1>2, PTL DEF Spec

           
=============================================================================
\* Modification History
\* Last modified Mon Nov 16 11:58:54 CST 2020 by spadhy
\* Created Mon Oct 26 10:27:47 CDT 2020 by spadhy
