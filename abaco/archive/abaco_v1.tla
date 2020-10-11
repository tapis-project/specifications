------------------------------ MODULE abaco_v1 ------------------------------
\* The formal specification for Abaco's execution and autoscaler engine.


EXTENDS Integers

CONSTANTS Max_Actors,       \* max number of actors to support
          Max_Executions    \* max number of executions/messages the system will send
          
\* Possible statuses for actors, executions and workers
actor_statuses == { "SUBMITTED", "READY", "ERROR", "DELETED" }
worker_statuses == { "SUBMITTED", "READY", "ERROR" }
execution_statuses == { "SUBMITTED", "RUNNING", "COMPLETE" }

\* Record types
\* ------------
\* An actor includes its id and its statuts
actor == [ actor_id: Nat, status: actor_statuses ]

\* A worker includes its id, the id of the actor it is assigned to, and its status 
worker == [ worker_id: Nat, actor_id: Nat, status: worker_statuses ]

\* An execution includes its id, the id of the actor it is assigned to, and its status 
execution == [ execution_id: Nat, actor_id: Nat, status: execution_statuses ]


\* Stores
\* ------
\* all stores are initially enpty
actor_ids == {}
worker_ids == {}
execution_ids == {}

\* actual stores variables (functions) map ids to records
actors == [a \in actor_ids |-> actor]
workers == [w \in worker_ids |-> worker]
executions == [e \in execution_ids |-> execution]

VARIABLES next_actor_id,     \* global counter to track the next actor id. 
          next_worker_id,    \* global counter to track the next worker id.
          next_execution_id  \* global counter to track the next execution id.


vars == <<actors, workers, executions, next_actor_id, next_worker_id,next_execution_id>>




\* Initialize the variables to 0.
Store_Init ==
    /\ next_actor_id = 0
    /\ next_worker_id = 0
    /\ next_execution_id = 0
   \* /\ actors = {}


\* helpers

Inc_Actor_Id == 
    next_actor_id' = next_actor_id + 1

Inc_Worker_Id == 
    next_worker_id' = next_worker_id + 1

Inc_Execution_Id == 
    next_execution_id' = next_execution_id + 1


\* Actions
\* -------
\* create a new actor with the next actor id.
Create_Actor == 
    /\ next_actor_id <= Max_Actors
    /\ actor_ids' = actor_ids \cup {next_actor_id} \* add the next actor_id to the actor_ids set.
    /\ Inc_Actor_Id \* increment the next_actor_id var
    /\ actors' = [ actors EXCEPT ![next_actor_id] = [actor_id |-> next_actor_id,
                                                     status |-> "SUBMITTED" ] ]


Delete_Actor(n) ==
\* delete an actor from the registry
    /\ actors' = [ actors EXCEPT ![n] = [status |-> "DELETED" ] ]


Send_Message(n) ==
\* send a message to the nth actor; this is implemented as an execution in SUBMITTED status
    /\ next_execution_id <= Max_Executions
    /\ execution_ids' = execution_ids \cup {next_execution_id} \* add the next execution_id to the execution_ids set.
    /\ Inc_Execution_Id \* increment the next_execution_id var
    /\ executions' = [ executions EXCEPT ![n] = [actor_id |-> n,
                                                 execution_id |-> next_execution_id,
                                                 status |-> "SUBMITTED" ] ]


\* All initializations
Init == Store_Init

\* Defines what actions take place in the next phase
Next == /\ \/ Create_Actor
           \/ \E i \in {0..next_actor_id-1} : Send_Message(i)
           \/ \E i \in {0..next_actor_id-1} : Delete_Actor(i)
\*           \/ AS_Start_Worker()
\*           \/ AS_Stop_Worker()
\*           \/ Worker_Get_Command()
\*           \/ Worker_Get_Actor_Message()
\*           \/ Exectuion_Completes()


\* The Abaco spec --
Spec == Init /\ [][Next]_vars


=============================================================================
\* Modification History
\* Last modified Thu Jul 16 16:09:36 CDT 2020 by spadhy
\* Last modified Mon May 25 16:31:54 CDT 2020 by jstubbs
\* Created Mon May 18 16:59:16 CDT 2020 by jstubbs
