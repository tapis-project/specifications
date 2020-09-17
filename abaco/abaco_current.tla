---------------------------- MODULE abaco_current ----------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Actors,           \* Set of Actors
\*          Workers,          \* Set of Workers
          MaxQueueSize,     \* Maximum queue size of the message queue.
          MaxMessage,       \* Maximum number of HTTP requests that are sent
          MaxWorkers,       \* Maximum number of Workers that are allowed to be created 
          ScaleUpThreshold,  \* ScaleUpThreshold 
          MaxWorkersPerActor, \* Maximum number of Workers per Actors
          ImageVersion       \* list of image versions


VARIABLES actor_msg_queues,      \* message_queues. One queue corresponds to an actor
          command_queues,        \* queues holding messages for different commands, such as update actor, delete actor, ...
          Workers,               \* Set of all Workers, defined based on the MaxWorkers constant, below.
          worker_command_queues, \* queues holding messages for specific actors such as "shutdown"
          actorStatus,           \* set of actors
          workerStatus,          \* workers status 
          m,                     \* a counter to be increment to represent work 
          tmsg,                  \* a counter to keep track for total number of mesages sent
          totalNumWorkers,       \* a counter for total number of workers created so far
          currentTotActiveWorkers, \* a counter to represent the current total number of (non-deleted) workers.  
          workersCreated,        \* a set of workers created so far
                                 \* command queues for workers
          actorWorkers,          \* subset of workers for each actor
          
          currentImageVersion,   \* current image version for each actor
          currentImageVersionForWorkers 
         
          
vars == <<actor_msg_queues, command_queues,worker_command_queues,actorStatus,workerStatus,m, tmsg, totalNumWorkers, workersCreated, actorWorkers, currentImageVersion, currentImageVersionForWorkers, currentTotActiveWorkers,Workers >>        

WorkerState == {"-","IDLE", "BUSY","FINISHED","STOPPING", "SHUTDOWN_REQUESTED", "DELETED"} \* Worker state
AllActors == Actors \cup {"a0"}      \* actors in the Actors constant and a non-existent actor
AllImageVersions == ImageVersion \cup {"-"}


(**************************************************************************************
 ****** Set of all possible message types in the queue                             ****
 **************************************************************************************)
 
 \* These message types represent BOTH the HTTP request message (sent by the user) and the message queued in Abaco's queue.
 \* In the real implementation, the messages are not exactly the same, but we make this simplification for the spec:
ActorMessages == [type : {"EXECUTE"},  actor: Actors, image: ImageVersion]
CommandMessages == [type : {"DELETE", "UPDATE"},  actor: Actors, image: ImageVersion]

\* These are messages sent directly from internal Abaco processes (such as the autoscaler) to the worker.
WorkerMessages == [type: {"COMMAND", "HEALTH_CHECK"}, message: {"SHUTDOWN", "HEALTH_CHECK"}]


(*
***********************************
Invariants and Temporal Properties
***********************************
*)

\* An invariant: ensures all the variables maintain the proper types.
TypeInvariant == 
  /\ actorStatus \in [Actors -> { "SUBMITTED", "READY", "ERROR", "SHUTTING_DOWN","UPDATING_IMAGE","DELETED"}] 
  /\ actor_msg_queues \in [Actors -> Seq(ActorMessages)] \* multiple queues
  /\ command_queues \in [Actors -> Seq(CommandMessages)] \* multiple queues
  /\ worker_command_queues \in [Workers -> Seq(WorkerMessages)] \* multiple queues
  /\ workerStatus \in [Workers -> [actor:AllActors, status:WorkerState]] \* Note actor belongs to AllActors which incudes the non-existent actor
  /\ workersCreated \subseteq Workers
  /\ actorWorkers \in [Actors -> SUBSET Workers] \*  each actor mapped to subset of workers
  /\ currentImageVersion \in [Actors -> AllImageVersions]
  /\ currentImageVersionForWorkers  \in [Workers -> AllImageVersions]
 
\* An invariant: ensures all the workers of an actor will eventually use the same Image version. 
AllWorkersOfActorUseSameImageVersion == \A a \in Actors: \A x, y \in actorWorkers[a]:
    currentImageVersionForWorkers[x] = currentImageVersionForWorkers[y]  
  
\* A temporal property: ensures all actor messages are eventually processed 
\* (i.e., that the actors_msq_queue is eventually 0 from some point until the end of the run.)
AllActorMessagesProcessed == <>[](\A a \in Actors: Len(actor_msg_queues[a]) = 0)    

\* A temporal property: ensures all command messages are eventually processed 
\* (i.e., that the command_queues is eventually 0 from some point until the end of the run.)
AllCommandMessagesProcessed == <>[](\A a \in Actors: Len(command_queues[a]) = 0)    
  
\* A temporal property: ensures all workers are deleted after all executions have been processed.
AllWorkersDeleted == <>[](currentTotActiveWorkers = 0)    

(*
*****************
Helper Operators
*****************
*)

Range(F) == { F[x] : x \in DOMAIN F }

Str(i) == CASE i = 1 -> "1" 
            [] i = 2 -> "2" 
            [] i = 3 -> "3"
            [] i = 4 -> "4"
            [] i = 5 -> "5"
 
(*
****************************
Initialization of Variables
****************************
*)

Init == 
    /\ actorStatus = [a \in Actors |-> "READY"] 
    /\ Workers = {"w"\o Str(i) : i \in 1..MaxWorkers+1}
    /\ workerStatus = [w \in Workers|-> [actor|->"a0",status|->"-"]] \* a0 is in AllActors but not in Actors
    /\ actor_msg_queues = [a \in Actors |-> <<>>]
    /\ command_queues = [a \in Actors |-> <<>>]
    /\ worker_command_queues = [w \in Workers|-> <<>>]
    /\ m = 0
    /\ tmsg = 0
    /\ totalNumWorkers = 0
    /\ currentTotActiveWorkers = 0
    /\ workersCreated = {}
    /\ actorWorkers = [a \in Actors |-> {}]   \* actorWorkers are also empty
    /\ currentImageVersion = [a \in Actors |-> "-"] \* Initially no images
    /\ currentImageVersionForWorkers  = [w \in Workers |-> "-"]
    
    
(*    
*************************************
HTTP Requests/Synchronous Processing
*************************************
*)

ActorExecuteRecv(msg, a) ==    
(*
Represents the Abaco platform receiving an HTTP request to the POST /actors/{id}/messages endpoint (i.e., to execute an actor)
*)
    /\  actorStatus[a]= "READY" \/ actorStatus[a]= "UPDATING_IMAGE"
    /\  msg.type = "EXECUTE"
    /\  msg.actor = a
    /\  tmsg < MaxMessage
    /\  Len(actor_msg_queues[a]) <  MaxQueueSize
    /\  actor_msg_queues'= [actor_msg_queues EXCEPT ![a] = Append(actor_msg_queues[a],msg)] \* QUESTION: do we want to queue this message? 
    /\  tmsg' = tmsg + 1
    /\  currentImageVersion'=[currentImageVersion EXCEPT ![a]= IF currentImageVersion[a]="-" THEN msg.image
                                                                                          ELSE currentImageVersion[a]] 
    /\  UNCHANGED<<worker_command_queues,actorStatus,workerStatus,m,totalNumWorkers, workersCreated, actorWorkers,currentImageVersionForWorkers,command_queues,currentTotActiveWorkers,Workers>>   

 
ActorDeleteRecv(msg,a) ==
(*
Represents the Abaco platform receiving an HTTP request to the DELETE /actors/{id} endpoint (i.e., to delete an actor)
*)

    /\ actorStatus[a] = "READY"
    /\ msg.type = "DELETE"
    /\ msg.actor = a
    /\ tmsg < MaxMessage
\*    /\ Len(command_queues[a]) <  MaxQueueSize   --- TODO: what criteria to put here?
                                                      \* perhaps queue must be empty? 
    /\ command_queues'= [command_queues EXCEPT ![a] = Append(command_queues[a],msg)]
    /\ actorStatus' = [actorStatus EXCEPT ![a] = "SHUTTING_DOWN"]
    /\ tmsg' = tmsg + 1
    /\ UNCHANGED<<worker_command_queues,m, workerStatus,totalNumWorkers, workersCreated, actorWorkers, currentImageVersion,currentImageVersionForWorkers,actor_msg_queues,currentTotActiveWorkers,Workers>>                                                                        
 
 
ActorUpdateRecv(msg, a) ==    
(*
Represents the Abaco platform receiving an HTTP request to the PUT /actors/{id} endpoint (i.e., to update an actor definition)
*)

    /\  actorStatus[a] = "READY"
    /\  msg.type = "UPDATE"
    /\  msg.actor = a
    /\  tmsg < MaxMessage
\*    /\  Len(command_queues[a]) <  MaxQueueSize  --- TODO: same as for DeleteRecv...
    /\  actorStatus' = [actorStatus EXCEPT ![a] = "UPDATING_IMAGE"]
    /\ command_queues'= [command_queues EXCEPT ![a] = Append(command_queues[a],msg)]
    /\  currentImageVersion' = [currentImageVersion EXCEPT ![a] = msg.image]
    /\  tmsg' = tmsg + 1
    /\  UNCHANGED<<worker_command_queues,workerStatus,m,totalNumWorkers, workersCreated,actorWorkers,currentImageVersionForWorkers,actor_msg_queues,currentTotActiveWorkers,Workers>>  


(*    
*****************************
Asynchronous Task Processing
*****************************
*)
 
UpdateActor(a) == 
(*
Represents internal processing of an actor update request. We represent this as an independent action because the processing happens 
asynchronously to the original HTTP request.
The enabling condition is the actorStatus value (UPDATING_IMAGE) which is set when receiving the HTTP request.
*)
    /\ Len(command_queues[a]) > 0
    /\ Head(command_queues[a]).type = "UPDATE"
    /\ actorStatus[a] = "UPDATING_IMAGE"
    /\ actorWorkers[a] = {} \* TODO --- what about workerStatus function? workers still active and assigned to actors there.
    /\ actorStatus' = [actorStatus EXCEPT ![a] = "READY"]
    /\ command_queues' = [command_queues EXCEPT ![a] = Tail(command_queues[a])]
    /\ UNCHANGED<<actor_msg_queues,worker_command_queues,tmsg,workerStatus,m,totalNumWorkers, workersCreated,actorWorkers,currentImageVersion,currentImageVersionForWorkers,currentTotActiveWorkers,Workers>>
         
           
StartDeleteWorker(w,a) ==
(*
Represents internal processing that occurrs when the autoscaler determines that a worker should be deleted.
*)
    /\ actorStatus[a] = "SHUTTING_DOWN" \/ (actorStatus[a] = "UPDATING_IMAGE" /\ workerStatus[w].status = "IDLE") \/ (workerStatus[w].status = "IDLE" /\ Len(actor_msg_queues[a]) = 0)
    /\ workerStatus[w].status # "-"
    /\ workerStatus[w].status # "SHUTDOWN_REQUESTED"
    /\ w \in actorWorkers[a]
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"SHUTDOWN_REQUESTED"]]
    /\ worker_command_queues' = [worker_command_queues EXCEPT ![w] = Append(worker_command_queues[w], [type |->"COMMAND", message |->"SHUTDOWN"])]
    /\ actorWorkers'=  [actorWorkers EXCEPT ![a] = actorWorkers[a] \ {w}]
    /\ UNCHANGED<<actor_msg_queues,command_queues,actorStatus,m, tmsg, totalNumWorkers,workersCreated, currentImageVersion,currentImageVersionForWorkers,currentTotActiveWorkers,Workers>>                                                  
 

DropWorkerCommandMessage(w,a) ==
(*
Represents the network (or any other event really) dropping a worker command queue message. 
*)
    /\ Len(worker_command_queues[w]) > 0
    /\ worker_command_queues' = [worker_command_queues EXCEPT ![w] = Tail(worker_command_queues[w])]
    /\ UNCHANGED<<actor_msg_queues,actorWorkers,workerStatus,command_queues,actorStatus,m, tmsg, totalNumWorkers, workersCreated, currentImageVersion,currentImageVersionForWorkers,currentTotActiveWorkers,Workers>>


CompleteDeleteWorker(w,a) ==
(*
Represents a worker receiving a message to shutdown and completing the shutdown process.
*)
    /\ Len(worker_command_queues[w]) > 0
    /\ Head(worker_command_queues[w]).type = "COMMAND"
    /\ Head(worker_command_queues[w]).message = "SHUTDOWN"
    /\ workerStatus[w].status = "SHUTDOWN_REQUESTED"
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"DELETED"]]
    /\ worker_command_queues' = [worker_command_queues EXCEPT ![w] = Tail(worker_command_queues[w])]
    /\ currentTotActiveWorkers'=currentTotActiveWorkers - 1
    /\ UNCHANGED<<actor_msg_queues,command_queues,actorStatus,m, tmsg, totalNumWorkers, workersCreated, currentImageVersion,currentImageVersionForWorkers,actorWorkers,Workers>>


\* DEPRECATED -----
DeleteWorker(w,a) ==
(*
Represents internal processing to delete a worker.
*)
    /\ actorStatus[a] = "SHUTTING_DOWN" \/ (actorStatus[a] = "UPDATING_IMAGE" /\ workerStatus[w].status = "IDLE") \* \/ (workerStatus[w].status = "IDLE" /\ Len(actor_msg_queues[a]) = 0)
    /\ workerStatus[w].status # "-"
    /\ w \in actorWorkers[a]
    /\ actorWorkers'=  [actorWorkers EXCEPT ![a] = actorWorkers[a] \ {w}]
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"DELETED"]]
    /\ currentTotActiveWorkers' = currentTotActiveWorkers - 1
    /\ UNCHANGED<<actor_msg_queues,command_queues,worker_command_queues,actorStatus,m, tmsg, totalNumWorkers, workersCreated, currentImageVersion,currentImageVersionForWorkers,Workers>>                                                  
\* ------ 
 
 
DeleteActor(a) ==
(*
Represents internal processing to delete an actor. Similar to UpdateActor, we represent this as an indpendent action because the processing
happens asynchronously to the original HTTP request.
*)
    /\ Len(command_queues[a]) > 0
    /\ Head(command_queues[a]).type = "DELETE"
    /\ actorStatus[a] = "SHUTTING_DOWN"
    /\ actorWorkers[a] = {}
    /\ actorStatus' = [actorStatus EXCEPT ![a]="DELETED"] 
    /\ command_queues' = [command_queues EXCEPT ![a] = Tail(command_queues[a])]
    /\ actor_msg_queues'= [actor_msg_queues EXCEPT ![a] = <<>>]
    /\ UNCHANGED<<worker_command_queues,workerStatus,m, tmsg, totalNumWorkers, workersCreated,actorWorkers, currentImageVersion,currentImageVersionForWorkers,currentTotActiveWorkers,Workers>> 
 
 
CreateWorker(w,a) ==
(*
Represents internal processing to create a worker.
*)

    /\ Len(actor_msg_queues[a]) >= ScaleUpThreshold
    /\ Cardinality({x \in Range(workerStatus): x.status # "SHUTDOWN_REQUESTED" /\ x.status # "-" /\ x.status # "DELETED"}) < MaxWorkers
\*    /\ currentTotActiveWorkers < MaxWorkers
\*    /\ totalNumWorkers < MaxWorkers
    /\ Cardinality(actorWorkers[a]) < MaxWorkersPerActor 
    /\ actorStatus[a]="READY"
    /\ workerStatus[w]=[actor|->"a0", status|->"-"]
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"IDLE"]] 
    /\ workersCreated' = workersCreated \cup {w}
    /\ actorWorkers' = [actorWorkers EXCEPT ![a]= actorWorkers[a] \cup {w}]  
    /\ currentImageVersionForWorkers' = [currentImageVersionForWorkers EXCEPT ![w] = currentImageVersion[a]]                                            
    /\ totalNumWorkers' = totalNumWorkers + 1
    /\ currentTotActiveWorkers' = currentTotActiveWorkers + 1
    /\ UNCHANGED<<actor_msg_queues,command_queues,worker_command_queues,actorStatus,m,tmsg, currentImageVersion,Workers>>
   

WorkerRecv(w,a) ==
(*
Represents internal processing that occurs when a worker receives an actor message (i.e., a message sent to an actor by a user.
This action dequeues the message an represents starting the execution. 
*)

    /\ Len(actor_msg_queues[a]) > 0  
    /\ actorStatus[a] # "SHUTTING_DOWN" 
    /\ actorStatus[a] # "UPDATING_IMAGE"
    /\ workerStatus[w] = [actor|->a, status|->"IDLE"]
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"BUSY"]]  
    /\ actor_msg_queues'= [actor_msg_queues EXCEPT ![a] = Tail(actor_msg_queues[a])]
    /\ UNCHANGED<<command_queues,worker_command_queues,actorStatus,m, tmsg, totalNumWorkers, workersCreated,actorWorkers, currentImageVersion,currentImageVersionForWorkers,currentTotActiveWorkers,Workers>>    

WorkerBusy(w,a) == 
(*
Represents internal processing that occurs when an actor execution initially completes.
This action changes the worker's status to FINISHED, which represents a state between BUSY and IDLE. The worker still needs to 
finalize the execution before being returned to the pool;
*)

    /\ actorStatus[a] # "SHUTTING_DOWN"
    /\ workerStatus[w] = [actor|->a, status|->"BUSY"]  
    /\ m' = m + 1  
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"FINISHED"]]    
    /\ UNCHANGED<<actor_msg_queues,command_queues,worker_command_queues,actorStatus,tmsg, totalNumWorkers, workersCreated,actorWorkers, currentImageVersion,currentImageVersionForWorkers,currentTotActiveWorkers,Workers>>   

FreeWorker(w,a) ==
(*
Represents internal processing that occurs when an actor execution has been finalized.
This action changes the worker's status to IDLE, which returns it to the pool;
*)

    /\ actorStatus[a] # "SHUTTING_DOWN"
    /\ workerStatus[w] = [actor|->a, status|->"FINISHED"]
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"IDLE"]] \*<-- This is not ensuring worker returns to the common pool
    /\ UNCHANGED<<actor_msg_queues,command_queues,worker_command_queues,actorStatus,m, tmsg, totalNumWorkers, workersCreated,actorWorkers, currentImageVersion,currentImageVersionForWorkers,currentTotActiveWorkers,Workers>>         


Next == 
    \/ \E msg \in ActorMessages, a \in Actors: ActorExecuteRecv(msg,a)
    \/ \E msg \in CommandMessages, a \in Actors: ActorUpdateRecv(msg, a) 
    \/ \E msg \in CommandMessages, a \in Actors:  ActorDeleteRecv(msg,a)
    \/ \E a \in Actors: UpdateActor(a)
    \/ \E w \in Workers,  a \in Actors: CreateWorker(w,a)
    \/ \E w \in Workers,  a \in Actors: DropWorkerCommandMessage(w,a)  
    \/ \E w \in Workers, a \in Actors: WorkerRecv(w, a)
    \/ \E w \in Workers, a\in Actors: WorkerBusy(w,a)
    \/ \E w \in Workers, a\in Actors: FreeWorker(w,a)
\*    \/ \E w \in Workers, a \in Actors: DeleteWorker(w,a)
    \/ \E w \in Workers, a\in Actors: StartDeleteWorker(w,a)
    \/ \E w \in Workers, a\in Actors: CompleteDeleteWorker(w,a)
    \/ \E a \in Actors: DeleteActor(a)

Spec == Init /\ [][Next]_vars  


FairSpec == Spec
        /\ WF_vars(\E w \in Workers, a \in Actors: CreateWorker(w,a))
        /\ WF_vars(\E w \in Workers, a \in Actors: WorkerRecv(w,a))
        /\ WF_vars(\E w \in Workers, a \in Actors: WorkerBusy(w,a))
        /\ WF_vars(\E w \in Workers,a \in Actors: FreeWorker(w,a))
        /\ WF_vars(\E a \in Actors: UpdateActor(a))
        /\ WF_vars(\E a \in Actors: DeleteActor(a))
        /\ WF_vars(\E w \in Workers, a \in Actors: DeleteWorker(w,a))
        /\ WF_vars(\E w \in Workers, a \in Actors: StartDeleteWorker(w,a))
        /\ WF_vars(\E w \in Workers, a \in Actors: CompleteDeleteWorker(w,a))


\* Inductive Invariant
InductiveInvariant == /\ TypeInvariant
                      /\ AllWorkersOfActorUseSameImageVersion

THEOREM Init => InductiveInvariant
<1> SUFFICES ASSUME Init
    PROVE InductiveInvariant
    OBVIOUS
<1>1. TypeInvariant
   <2>1. actorStatus \in [Actors -> { "SUBMITTED", "READY", "ERROR", "SHUTTING_DOWN","UPDATING_IMAGE","DELETED"}]
    BY DEF Init,InductiveInvariant
  <2>2. actor_msg_queues \in [Actors -> Seq(ActorMessages)]
    BY DEF Init,InductiveInvariant
  <2>3. command_queues \in [Actors -> Seq(CommandMessages)]
    BY DEF Init,InductiveInvariant
  <2>4. worker_command_queues \in [Workers -> Seq(WorkerMessages)]
    BY DEF Init,InductiveInvariant
  <2>5. workerStatus \in [Workers -> [actor:AllActors, status:WorkerState]]
    BY DEF AllActors,WorkerState,Init,InductiveInvariant
  <2>6. workersCreated \subseteq Workers
    BY DEF Init,InductiveInvariant
  <2>7. actorWorkers \in [Actors -> SUBSET Workers]
    BY DEF Init,InductiveInvariant
  <2>8. currentImageVersion \in [Actors -> AllImageVersions]
    BY DEF AllImageVersions,Init,InductiveInvariant
  <2>9. currentImageVersionForWorkers  \in [Workers -> AllImageVersions]
    BY DEF AllImageVersions,Init,InductiveInvariant
  <2>10. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeInvariant
   
<1>2. AllWorkersOfActorUseSameImageVersion
  <2>1. SUFFICES ASSUME NEW a \in Actors,
                      NEW x \in actorWorkers[a], NEW y \in actorWorkers[a]
               PROVE  currentImageVersionForWorkers[x] = currentImageVersionForWorkers[y]
    BY DEF AllWorkersOfActorUseSameImageVersion
  <2>2. QED
    BY DEF Init, InductiveInvariant, TypeInvariant
<1>3. QED
  BY <1>1, <1>2 DEF InductiveInvariant

             



=============================================================================
\* Modification History
\* Last modified Thu Sep 17 15:59:57 CDT 2020 by spadhy
\* Last modified Sun Sep 13 11:00:41 CDT 2020 by jstubbs
\* Created Wed Aug 19 11:19:50 CDT 2020 by spadhy
