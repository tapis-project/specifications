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
          currentImageVersionForWorkers 
         
          
vars == <<msg_queues,actorStatus,workerStatus,m, tmsg, totalNumWorkers, workersCreated, actorWorkers, currentImageVersion, currentImageVersionForWorkers >>        

WorkerState == {"-","IDLE", "BUSY","FINISHED","STOPPING","DELETED"} \* Worker state
AllActors == Actors \cup {"a0"}      \* actors in the Actors constant and a non-existent actor
AllImageVersions == ImageVersion \cup {"-"}

(**************************************************************************************
 ****** Set of all possible message types in the queue                             ****
 **************************************************************************************)
 Messages == [type : {"DELETE","EXECUTE", "UPDATE"},  actor: Actors, image: ImageVersion]
 

TypeInvariant == 
  /\ actorStatus \in [Actors -> { "SUBMITTED", "READY", "ERROR", "SHUTTING_DOWN","UPDATING_IMAGE","DELETED"}] 
  /\ msg_queues \in [Actors -> Seq(Messages)] \* multiple queues
  /\ workerStatus \in [Workers -> [actor:AllActors, status:WorkerState]] \* Note actor belongs to AllActors which incudes the non-existent actor
  /\ workersCreated \subseteq Workers
  /\ actorWorkers \in [Actors -> SUBSET Workers] \*  each actor mapped to subset of workers
  /\ currentImageVersion \in [Actors -> AllImageVersions]
  /\ currentImageVersionForWorkers  \in [Workers -> AllImageVersions]
 
  
  \* A temporal property: ensures the msq_queue is eventually 0 from now on.
  AllMessagesProcessed == <>[](\A a \in Actors: Len(msg_queues[a]) = 0)    
    

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
    
    
    
ActorExecuteRecv(msg, a) ==    
    /\  actorStatus[a]= "READY" \/ actorStatus[a]= "UPDATING_IMAGE"
    /\  msg.type = "EXECUTE"
    /\  msg.actor = a
    /\  tmsg < MaxMessage
    /\  Len(msg_queues[a]) <  MaxQueueSize
    /\  msg_queues'= [msg_queues EXCEPT ![a] = Append(msg_queues[a],msg)]
    /\  tmsg' = tmsg + 1
    /\  currentImageVersion'=[currentImageVersion EXCEPT ![a]= IF currentImageVersion[a]="-" THEN msg.image
                                                                                          ELSE currentImageVersion[a]] 
    /\  UNCHANGED<<actorStatus,workerStatus,m,totalNumWorkers, workersCreated, actorWorkers,currentImageVersionForWorkers>>   

 
 ActorDeleteRecv(msg,a) ==
    /\ actorStatus[a] = "READY"
    /\ msg.type = "DELETE"
    /\ msg.actor = a
    /\ tmsg < MaxMessage
    /\ Len(msg_queues[a]) <  MaxQueueSize
    /\ msg_queues'= [msg_queues EXCEPT ![a] = Append(msg_queues[a],msg)]
    /\ actorStatus' = [actorStatus EXCEPT ![a] = "SHUTTING_DOWN"]
    /\ tmsg' = tmsg + 1
    /\ UNCHANGED<<m, workerStatus,totalNumWorkers, workersCreated, actorWorkers, currentImageVersion,currentImageVersionForWorkers>>                                                                        
 
 ActorUpdateRecv(msg, a) ==    
    /\  actorStatus[a] = "READY"
    /\  msg.type = "UPDATE"
    /\  msg.actor = a
    /\  tmsg < MaxMessage
    /\  Len(msg_queues[a]) <  MaxQueueSize
    /\  actorStatus' = [actorStatus EXCEPT ![a] = "UPDATING_IMAGE"]
    /\  currentImageVersion' = [currentImageVersion EXCEPT ![a] = msg.image]
    /\  tmsg' = tmsg + 1
    /\  UNCHANGED<<msg_queues,workerStatus,m,totalNumWorkers, workersCreated,actorWorkers,currentImageVersionForWorkers>>  
 
 UpdateActor(a) == 
         /\ actorStatus[a] = "UPDATING_IMAGE"
         /\ actorWorkers[a] = {}
         /\ actorStatus' = [actorStatus EXCEPT ![a] = "READY"]
         
         /\ UNCHANGED<<msg_queues,tmsg,workerStatus,m,totalNumWorkers, workersCreated,actorWorkers,currentImageVersion,currentImageVersionForWorkers>>
         
         
  
 DeleteWorker(w,a) ==
    /\ actorStatus[a] = "SHUTTING_DOWN" \/ (actorStatus[a] = "UPDATING_IMAGE" /\ workerStatus[w].status = "IDLE")
    /\ workerStatus[w].status # "-"
    /\ w \in actorWorkers[a]
    /\ actorWorkers'=  [actorWorkers EXCEPT ![a] = actorWorkers[a] \ {w}]
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"DELETED"]]  
    /\ UNCHANGED<<msg_queues,actorStatus,m, tmsg, totalNumWorkers, workersCreated, currentImageVersion,currentImageVersionForWorkers>>                                                  
 
 
 DeleteActor(a) ==
     /\ actorStatus[a] = "SHUTTING_DOWN"
     /\ actorWorkers[a] = {}
     /\ Len(msg_queues[a]) > 0
     /\ actorStatus' = [actorStatus EXCEPT ![a]="DELETED"] 
     /\ msg_queues'= [msg_queues EXCEPT ![a] = <<>>]
     
     /\ UNCHANGED<<workerStatus,m, tmsg, totalNumWorkers, workersCreated,actorWorkers, currentImageVersion,currentImageVersionForWorkers>> 
 
 


CreateWorker(w,a) ==
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
    /\ UNCHANGED<<msg_queues,actorStatus,m,tmsg, currentImageVersion>>
   

WorkerRecv(w,a) ==
    /\ Len(msg_queues[a]) > 0  
    /\ actorStatus[a] # "SHUTTING_DOWN" 
    /\ actorStatus[a] # "UPDATING_IMAGE"
    /\ workerStatus[w] = [actor|->a, status|->"IDLE"]
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"BUSY"]]  
    /\ msg_queues'= [msg_queues EXCEPT ![a] = Tail(msg_queues[a])]
    /\ UNCHANGED<<actorStatus,m, tmsg, totalNumWorkers, workersCreated,actorWorkers, currentImageVersion,currentImageVersionForWorkers>>    

WorkerBusy(w,a) == 
    /\ actorStatus[a] # "SHUTTING_DOWN"
    /\ workerStatus[w] = [actor|->a, status|->"BUSY"]  
    /\ m' = m + 1  
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"FINISHED"]]    
    /\ UNCHANGED<<msg_queues,actorStatus,tmsg, totalNumWorkers, workersCreated,actorWorkers, currentImageVersion,currentImageVersionForWorkers>>   

FreeWorker(w,a) ==
    /\ actorStatus[a] # "SHUTTING_DOWN"
    /\ workerStatus[w] = [actor|->a, status|->"FINISHED"]
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"IDLE"]] \*<-- This is not ensuring worker returns to the common pool
    /\ UNCHANGED<<msg_queues,actorStatus,m, tmsg, totalNumWorkers, workersCreated,actorWorkers, currentImageVersion,currentImageVersionForWorkers>>         


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
\* Last modified Fri Aug 21 10:58:45 CDT 2020 by spadhy
\* Created Wed Aug 19 11:19:50 CDT 2020 by spadhy
