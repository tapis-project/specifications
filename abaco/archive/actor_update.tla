---------------------------- MODULE actor_update ----------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Actors,           \* Set of Actors
          Workers,          \* Set of Workers
          MaxQueueSize,     \* Maximum queue size of the message queue.
          MaxMessage,       \* Maximum number of message that are sent
          MaxWorkers,       \* Maximum number of Workers that are allowed to be created 
          ScaleUpThreshold,  \* ScaleUpThreshold 
          MaxWorkersPerActor, \* Maximum number of Workers per Actors
          ImageVersion       \* list of image versions

VARIABLES msg_queues,         \* message_queues. One queue corresponds to an actor
          actorStatus,        \* set of actors
          workerStatus,       \* workers status 
          m,                  \* a counter to be increment to represent work 
          tmsg,               \* a counter to keep track for total number of mesages sent
          totalNumWorkers,    \* a counter for total number of workers created so far
          workersCreated,     \* a set of workers created so far
                              \* command queues for workers
          actorWorkers,       \* subset of workers for each actor
          
          currentImageVersion,  \* current image version for each actor
          currentImageVersionForWorkers,
          currentTotActiveWorkers 
         
          
vars == <<msg_queues,actorStatus,workerStatus,m, tmsg, totalNumWorkers, workersCreated, actorWorkers,
          currentImageVersion, currentImageVersionForWorkers,currentTotActiveWorkers >>        

WorkerState == {"-","IDLE", "BUSY","FINISHED","STOPPING","DELETED"} \* Worker state
AllActors == Actors \cup {"a0"}      \* actors in the Actors constant and a non-existent actor
AllImageVersions == ImageVersion \cup {"-"}

(**************************************************************************************
 ****** Set of all possible message types in the queue                             ****
 **************************************************************************************)
 Messages == [type : {"DELETE","EXECUTE", "UPDATE"},  actor: Actors, image: ImageVersion]
 

(*
***********************************
Invariants and Temporal Properties
***********************************
*)

TypeInvariant == 
  /\ actorStatus \in [Actors -> { "SUBMITTED", "READY", "ERROR", "SHUTTING_DOWN","UPDATING_IMAGE","DELETED"}] 
  /\ msg_queues \in [Actors -> Seq(Messages)] \* multiple queues
  /\ workerStatus \in [Workers -> [actor:AllActors, status:WorkerState]] \* Note actor belongs to AllActors which incudes the non-existent actor
  /\ workersCreated \subseteq Workers
  /\ actorWorkers \in [Actors -> SUBSET Workers] \*  each actor mapped to subset of workers
  /\ currentImageVersion \in [Actors -> AllImageVersions]
  /\ currentImageVersionForWorkers  \in [Workers -> AllImageVersions]
 
  \* An invariant: ensures all the workers of an actor will eventually use the same Image version. 
  AllWorkersOfActorUseSameImageVersion == \A a \in Actors: \A x, y \in actorWorkers[a]:
    currentImageVersionForWorkers[x] = currentImageVersionForWorkers[y]  
  
  \* A temporal property: ensures the msq_queue is eventually 0 from now on.
  AllMessagesProcessed == <>[](\A a \in Actors: Len(msg_queues[a]) = 0)    
  
  \* A temporal property: ensures all workers are deleted after all executions have been processed.
  AllWorkersDeleted == <>[](currentTotActiveWorkers = 0) 

Init == 
    /\ actorStatus = [a \in Actors |-> "READY"] 
    /\ workerStatus = [w \in Workers|-> [actor|->"a0",status|->"-"]] \* a0 is in AllActors but not in Actors
    /\ msg_queues = [a \in Actors |-> <<>>]
    /\ m = 0
    /\ tmsg = 0
    /\ totalNumWorkers = 0
    /\ workersCreated = {}
    /\ actorWorkers = [a \in Actors |-> {}]   \* actorWorkers are also empty
    /\ currentImageVersion = [a \in Actors |-> "-"] \* Initially no images
    /\ currentImageVersionForWorkers  = [w \in Workers |-> "-"]
    /\ currentTotActiveWorkers = 0
    
    
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
    /\  Len(msg_queues[a]) <  MaxQueueSize
    /\  msg_queues'= [msg_queues EXCEPT ![a] = Append(msg_queues[a],msg)] \* QUESTION: do we want to queue this message? 
    /\  tmsg' = tmsg + 1
    /\  currentImageVersion'=[currentImageVersion EXCEPT ![a]= IF currentImageVersion[a]="-" THEN msg.image
                                                                                          ELSE currentImageVersion[a]] 
    /\  UNCHANGED<<actorStatus,workerStatus,m,totalNumWorkers, workersCreated, actorWorkers,currentImageVersionForWorkers,currentTotActiveWorkers>>   

 
ActorDeleteRecv(msg,a) ==
(*
Represents the Abaco platform receiving an HTTP request to the DELETE /actors/{id} endpoint (i.e., to delete an actor)
*)

    /\ actorStatus[a] = "READY"
    /\ msg.type = "DELETE"
    /\ msg.actor = a
    /\ tmsg < MaxMessage
    /\ Len(msg_queues[a]) <  MaxQueueSize
    /\ msg_queues'= [msg_queues EXCEPT ![a] = Append(msg_queues[a],msg)]
    /\ actorStatus' = [actorStatus EXCEPT ![a] = "SHUTTING_DOWN"]
    /\ tmsg' = tmsg + 1
    /\ UNCHANGED<<m, workerStatus,totalNumWorkers, workersCreated, actorWorkers, currentImageVersion,currentImageVersionForWorkers,currentTotActiveWorkers>>                                                                        
 
ActorUpdateRecv(msg, a) ==    
(*
Represents the Abaco platform receiving an HTTP request to the PUT /actors/{id} endpoint (i.e., to update an actor definition)
*)

    /\  actorStatus[a] = "READY"
    /\  msg.type = "UPDATE"
    /\  msg.actor = a
    /\  tmsg < MaxMessage
    /\  Len(msg_queues[a]) <  MaxQueueSize
    /\  actorStatus' = [actorStatus EXCEPT ![a] = "UPDATING_IMAGE"]
    /\  currentImageVersion' = [currentImageVersion EXCEPT ![a] = msg.image]
    /\  tmsg' = tmsg + 1
    /\  UNCHANGED<<msg_queues,workerStatus,m,totalNumWorkers, workersCreated,actorWorkers,currentImageVersionForWorkers,currentTotActiveWorkers>>  



(*    
*****************************
Asynchronous Task Processing
*****************************
*)

 
UpdateActor(a) == 
(*
Represents internal processing of an actor update request. We represent this as an independent __ because the processing happens 
asynchronously to the original HTTP request.
The enabling condition is the actorStatus value (UPDATING_IMAGE) which is set when receiving the HTTP request.
*)

         /\ actorStatus[a] = "UPDATING_IMAGE"
         /\ actorWorkers[a] = {}
         /\ actorStatus' = [actorStatus EXCEPT ![a] = "READY"]
         \* QUESTION: this process does not change the msg_queues[a] variable, which means the UPDATE message is not consumed here.
         /\ UNCHANGED<<msg_queues,tmsg,workerStatus,m,totalNumWorkers, workersCreated,actorWorkers,currentImageVersion,currentImageVersionForWorkers,currentTotActiveWorkers>>
         
           
DeleteWorker(w,a) ==
(*
Represents internal processing to delete a worker.
*)
    /\ actorStatus[a] = "SHUTTING_DOWN" \/ (actorStatus[a] = "UPDATING_IMAGE" /\ workerStatus[w].status = "IDLE")\/ (workerStatus[w].status = "IDLE" /\ Len(msg_queues[a]) = 0)
    /\ workerStatus[w].status # "-"
    /\ w \in actorWorkers[a]
    /\ actorWorkers'=  [actorWorkers EXCEPT ![a] = actorWorkers[a] \ {w}]
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"DELETED"]]  
    /\ currentTotActiveWorkers'=currentTotActiveWorkers - 1
    /\ UNCHANGED<<msg_queues,actorStatus,m, tmsg, totalNumWorkers, workersCreated, currentImageVersion,currentImageVersionForWorkers>>                                                  
 
 
DeleteActor(a) ==
(*
Represents internal processing to delete an actor. Similar to UpdateActor, we represent this as an indpendent __ because the processing
happens asynchronously to the original HTTP request.
*)
     /\ actorStatus[a] = "SHUTTING_DOWN"
     /\ actorWorkers[a] = {}
     /\ Len(msg_queues[a]) > 0
     /\ actorStatus' = [actorStatus EXCEPT ![a]="DELETED"] 
     /\ msg_queues'= [msg_queues EXCEPT ![a] = <<>>]
     
     /\ UNCHANGED<<workerStatus,m, tmsg, totalNumWorkers, workersCreated,actorWorkers, currentImageVersion,currentImageVersionForWorkers,currentTotActiveWorkers>> 
 

 
CreateWorker(w,a) ==
(*
Represents internal processing to create a worker.
*)

    /\ Len(msg_queues[a]) >= ScaleUpThreshold
    /\ totalNumWorkers < MaxWorkers
    /\ Cardinality(actorWorkers[a]) < MaxWorkersPerActor 
    /\ actorStatus[a]="READY"
    /\ workerStatus[w]=[actor|->"a0", status|->"-"]
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"IDLE"]] 
    /\ workersCreated' = workersCreated \cup {w}
    /\ actorWorkers' = [actorWorkers EXCEPT ![a]= actorWorkers[a] \cup {w}]  
    /\ currentImageVersionForWorkers' = [currentImageVersionForWorkers EXCEPT ![w] = currentImageVersion[a]]                                            
    /\ totalNumWorkers' = totalNumWorkers + 1   
    /\ currentTotActiveWorkers'=currentTotActiveWorkers + 1   
    /\ UNCHANGED<<msg_queues,actorStatus,m,tmsg, currentImageVersion>>
     

WorkerRecv(w,a) ==
(*
Represents internal processing that occurs when a worker receives an actor message (i.e., a message sent to an actor by a user.
This __ dequeues the message an represents starting the execution. 
*)

    /\ Len(msg_queues[a]) > 0  
    /\ actorStatus[a] # "SHUTTING_DOWN" 
    /\ actorStatus[a] # "UPDATING_IMAGE"
    /\ workerStatus[w] = [actor|->a, status|->"IDLE"]
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"BUSY"]]  
    /\ msg_queues'= [msg_queues EXCEPT ![a] = Tail(msg_queues[a])]
    /\ UNCHANGED<<actorStatus,m, tmsg, totalNumWorkers, workersCreated,actorWorkers, currentImageVersion,currentImageVersionForWorkers,currentTotActiveWorkers>>    

WorkerBusy(w,a) == 
(*
Represents internal processing that occurs when an actor execution initially completes.
This __ changes the worker's status to FINISHED, which represents a state between BUSY and IDLE. The worker still needs to 
finalize the execution before being returned to the pool;
*)

    /\ actorStatus[a] # "SHUTTING_DOWN"
    /\ workerStatus[w] = [actor|->a, status|->"BUSY"]  
    /\ m' = m + 1  
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"FINISHED"]]    
    /\ UNCHANGED<<msg_queues,actorStatus,tmsg, totalNumWorkers, workersCreated,actorWorkers, currentImageVersion,currentImageVersionForWorkers,currentTotActiveWorkers>>   

FreeWorker(w,a) ==
(*
Represents internal processing that occurs when an actor execution has been finalized.
This __ changes the worker's status to IDLE, which returns it to the pool;
*)

    /\ actorStatus[a] # "SHUTTING_DOWN"
    /\ workerStatus[w] = [actor|->a, status|->"FINISHED"]
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"IDLE"]] \*<-- This is not ensuring worker returns to the common pool
    /\ UNCHANGED<<msg_queues,actorStatus,m, tmsg, totalNumWorkers, workersCreated,actorWorkers, currentImageVersion,currentImageVersionForWorkers,currentTotActiveWorkers>>         


Next == 
    \/ \E msg \in Messages, a \in Actors: ActorExecuteRecv(msg,a)
    \/ \E msg \in Messages, a \in Actors: ActorUpdateRecv(msg, a) 
    \/ \E a \in Actors: UpdateActor(a)
    \/ \E msg \in Messages, a \in Actors:  ActorDeleteRecv(msg,a)
    \/ \E w \in Workers,  a \in Actors: CreateWorker(w,a)  
    \/ \E w \in Workers, a \in Actors: WorkerRecv(w, a)
    \/ \E w \in Workers, a\in Actors: WorkerBusy(w,a)
    \/ \E w \in Workers, a\in Actors: FreeWorker(w,a)
    \/ \E w \in Workers, a \in Actors: DeleteWorker(w,a)
    \/ \E a \in Actors: DeleteActor(a)
 


Spec == Init /\ [][Next]_vars  
        /\ WF_vars(\E w \in Workers, a \in Actors: CreateWorker(w,a))
        /\ WF_vars(\E w \in Workers, a \in Actors: WorkerRecv(w,a))
        /\ WF_vars(\E w \in Workers, a \in Actors: WorkerBusy(w,a))
        /\ WF_vars(\E w \in Workers,a \in Actors: FreeWorker(w,a))
        /\ WF_vars(\E a \in Actors: UpdateActor(a))
        /\ WF_vars(\E a \in Actors: DeleteActor(a))
        /\ WF_vars(\E w \in Workers, a \in Actors: DeleteWorker(w,a))


=============================================================================
\* Modification History
\* Last modified Sun Sep 20 13:14:10 CDT 2020 by spadhy
\* Last modified Thu Sep 10 15:36:10 CDT 2020 by jstubbs
\* Created Wed Aug 19 11:19:50 CDT 2020 by spadhy
