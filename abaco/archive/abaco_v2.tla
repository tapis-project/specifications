------------------------------ MODULE abaco_v2 ------------------------------

\* The formal specification for Abaco's execution and autoscaler engine.


EXTENDS Integers, FiniteSets

CONSTANTS MaxActors,   \* Max number of Actors
          ActorIDs     \* Set of Actors Ids

VARIABLES actorIds,    \*  set of actor ids
          actorState  \*  each actor state
          \*actorsData   \* actor data store

\*execution_ids,next_execution_id, executions


\* Possible statuses for actors
actorStatus == { "SUBMITTED", "READY", "ERROR", "DELETED", "-" }
\* executionStatus == { "SUBMITTED", "RUNNING", "COMPLETE","-" }


\* Record types
\* ------------
\* An actor includes its id and its statuts
Actor == [ actorId: ActorIDs, status: actorStatus ]
noActor == [actorId |-> "a0", status|->"-"] \* initial actor state record

(*
  execution == [ execution_id: Nat, actor_id: Nat, status: executionStatus ] 
  noExecution == [ execution_id|->0, actor_id|->"", status|->"-" ]
  executions == [e \in execution_ids |-> execution]
  \* An execution includes its id, the id of the actor it is assigned to, and its status 
 *)


TypeInvariants ==  
/\ actorIds \subseteq ActorIDs
/\ actorState \in [ActorIDs -> Actor]

              

\* Init predicate
Init == /\ actorIds = {}
        /\ actorState = [a \in ActorIDs |-> noActor]  \* initialize the actorState
        \*/\ actorsData = {}
        
        (*/\ execution_ids = {}
        /\ next_execution_id = 0
        /\ executions = [e \in execution_ids |-> noExecution]*)
        




\*actorsData == [a \in actorIds |-> Actor]


\* actual stores variables (functions) map ids to records



\* Actions
\* -------
\* create a new actor with the next actor id.


vars == <<actorIds, actorState>>
\* execution_ids,next_execution_id, executions>>


createActor(a) ==  /\ Cardinality(actorIds) < MaxActors
                   /\ actorState[a].status="-" 
                   /\ actorState'= [ actorState EXCEPT ![a] = [actorId |-> a, status|->"SUBMITTED"]]
                   /\ actorIds' = actorIds \cup {a} 
                   \*/\ actorsData' = actorsData \cup {[a|->[actorId |-> a, status |-> "SUBMITTED"]]}                        
 
 (* Inc_Execution_Id == 
    next_execution_id' = next_execution_id + 1 *)
 
(* sendMessage(a) == 
 \* send a message to the nth actor; this is implemented as an execution in SUBMITTED status
    /\ next_execution_id <= Max_Executions
    /\ execution_ids' = execution_ids \cup {next_execution_id} \* add the next execution_id to the execution_ids set.
    /\ Inc_Execution_Id \* increment the next_execution_id var
    /\ executions' = [ executions EXCEPT ![next_execution_id] = [actor_id |-> a,
                                                 execution_id |-> next_execution_id,
                                                 status |-> "SUBMITTED" ] ]  *)               

Next == /\ \E a \in ActorIDs: createActor(a)
       (* /\ \E a \in Actors: sendMessage(a)*)
   

Spec == Init /\ [][Next]_vars      





=============================================================================
\* Modification History
\* Last modified Thu Jul 16 16:24:30 CDT 2020 by spadhy
\* Created Thu Jul 09 16:22:58 CDT 2020 by spadhy
