------------------------- MODULE producer_consumer -------------------------

EXTENDS Naturals, Sequences, TLAPS

CONSTANTS MaxTotalNumberOfItemsProduced, (* max number of items that can be produced by a producer *)
          MaxBufferLen                   (* max buffer capacity for produced items *)

ASSUME Assumption == 
         /\ MaxBufferLen \in (Nat \ {0}) (* MaxbufferLen should be atleast 1 *)

-----------------------------------------------------------------------------

VARIABLES buffer, num_of_items_produced, num_of_items_consumed 
         
vars == <<buffer, num_of_items_produced, num_of_items_consumed>>  
 

Item == [type: {"item"}]
-----------------------------------------------------------------------------

(* Temporarl property: Any item that is produced gets eventually consumed *)
AllItemsConsumed == <>[](Len(buffer) = 0 /\ num_of_items_produced = num_of_items_consumed) 


(* Type Correctness *)
TypeInvariant == /\ Len(buffer) \in 0..MaxBufferLen 
                 /\ buffer \in Seq(Item)
                 /\ num_of_items_produced \in 0..MaxTotalNumberOfItemsProduced
                 /\ num_of_items_consumed  \in 0..MaxTotalNumberOfItemsProduced

(* An Invariant: num of items consumed is always less than or equal to the total number of items produced *)
SafetyProperty == num_of_items_consumed <= num_of_items_produced    


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
 
 USE Assumption DEF vars, Item,
                    Init, Next, Spec,
                    Produce, Consume,
                    TypeInvariant, SafetyProperty
 
 
  (* Inductive Invariant *)
  IInv == /\ TypeInvariant
          /\ SafetyProperty
 
(* First to prove Inv *) 
THEOREM TypeCorrect == Init => IInv
  <1> SUFFICES ASSUME Init
               PROVE  IInv
    OBVIOUS
  <1>1. TypeInvariant
     BY DEF Init, IInv, TypeInvariant 
  <1>2. SafetyProperty
     BY DEF Init, IInv, SafetyProperty 
  <1>3. QED
    BY <1>1, <1>2 DEF IInv


(*THEOREM IInv /\ [Next]_vars => IInv'
  <1> SUFFICES ASSUME IInv,
                      [Next]_vars
               PROVE  IInv'
    OBVIOUS
  <1>1. ASSUME NEW item \in Item,
               Produce(item)
        PROVE  IInv'
         
  <1>2. CASE Consume
  <1>3. CASE UNCHANGED vars
  <1>4. QED
    BY <1>1, <1>2, <1>3 DEF Next*)
      
           
=============================================================================
\* Modification History
\* Last modified Thu Oct 29 17:21:28 CDT 2020 by spadhy
\* Created Mon Oct 26 10:27:47 CDT 2020 by spadhy
