------------------------------ MODULE pub_sub ------------------------------
(********************************************************************

This is is the specification for a messaging queue model in Abaco.
Each actor in the actor set is associated with a message queue. 
A message for the actor for execution is appended to the queue.
A worker from the set of workers working for the actor picks the message
is its status is IDLE. If number of messages in the queue exceeds the
 ScaleUpThreshold, a new worker is created.

*******************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Actors,           \* Set of Actors
          Workers,          \* Set of Workers
          Message,          \* Set of messages that can be sent
          
          \*Data,
          MaxQueueSize,     \* Maximum queue size of the message queue.
          MaxMessage,       \* Maximum number of message that are sent
          MaxWorkers,       \* Maximum number of Workers that are allowed to be created 
          ScaleUpThreshold,  \* ScaleUpThreshold 
          MaxWorkersPerActor 
VARIABLES msg_queues,         \* message_queues. One queue corresponds to an actor
          actorStatus,        \* set of actors
          workerStatus,       \* workers status 
          m,                  \* a counter to be increment to represent work 
          tmsg,               \* a counter to keep track for total number of mesages sent
          totalNumWorkers,    \* a counter for total number of workers created so far
          workersCreated,      \* a set of workers created so far
          actorWorkers        \* subset of workers for each actor
          
          
vars == <<msg_queues,actorStatus,workerStatus,m, tmsg, totalNumWorkers, workersCreated,actorWorkers>>        

WorkerState == {"-","IDLE", "BUSY","FINISHED"} \* Worker state
AllActors == Actors \cup {"a0"}  \* actors in the Actors constant and a non-existent actor

(**************************************************************************************
 ****** Set of all possible message types in the queue with the Actor that sent it ****
 ************************************************************************************** *)
\* Messages == [type : {"UPDATE","DELETE","STOP","EXECUTE"}, actor : Actors, value:Data]


TypeInvariant == 
  /\ actorStatus \in [Actors -> { "SUBMITTED", "READY", "ERROR", "DELETED"}] 
  /\ msg_queues \in [Actors -> Seq(Message)] \* multiple queues
  /\ workerStatus \in [Workers -> [actor:AllActors, status:WorkerState]] \* Note actor belongs to AllActors which incudes the non-existent actor
  /\ workersCreated \subseteq Workers
  /\ actorWorkers \in [Actors -> SUBSET Workers] \*  each actor mapped to subset of workers
 
 
  
  

Init == 
    /\ actorStatus = [a \in Actors |-> "READY"] 
    /\ workerStatus = [w \in Workers|-> [actor|->"a0",status|->"-"]] \* a0 is in AllActors but not in Actors
    /\ msg_queues = [a \in Actors |-> <<>>]
    /\ m = 0
    /\ tmsg = 0
    /\ totalNumWorkers = 0
    /\ workersCreated = {}
    /\ actorWorkers = [a \in Actors |-> {}]   \* actorWorkers are also empty
  

\* A temporal property: ensures the msq_queue is eventually 0 from now on.
AllMessagesProcessed == <>[](\A a \in Actors: Len(msg_queues[a]) = 0)    
    
ActorRecv(msg, a) ==    
    /\  actorStatus[a] = "READY"
    /\  tmsg < MaxMessage
    /\  Len(msg_queues[a]) <  MaxQueueSize
   \* /\  msg_queues' = [ a1 \in Actors |-> IF a=a1 THEN Append(msg_queues[a],msg)  \* Note the way an element of sequence is updated
    \*                                             ELSE msg_queues[a]]
    /\  msg_queues'= [msg_queues EXCEPT ![a] = Append(msg_queues[a],msg)] 
    /\  tmsg' = tmsg + 1
    /\  UNCHANGED<<actorStatus,workerStatus,m,totalNumWorkers, workersCreated,actorWorkers>>   

 
      
CreateWorker(w,a) ==
    /\ Len(msg_queues[a]) >=ScaleUpThreshold
    /\ totalNumWorkers < MaxWorkers
    /\ Cardinality(actorWorkers[a]) < MaxWorkersPerActor 
    /\ workerStatus[w]=[actor|->"a0", status|->"-"]
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"IDLE"]] 
    /\ workersCreated' = workersCreated \cup {w}
    /\ actorWorkers' = [actorWorkers EXCEPT ![a]= actorWorkers[a] \cup {w}]
    /\ totalNumWorkers' = totalNumWorkers + 1
    /\ UNCHANGED<<msg_queues,actorStatus,m,tmsg>>
   

WorkerRecv(w,a) ==
    /\ Len(msg_queues[a]) > 0  
    /\ workerStatus[w] = [actor|->a, status|->"IDLE"]
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"BUSY"]]  
    \*/\ msg_queues' = [ a1 \in Actors |-> IF a=a1 THEN Tail(msg_queues[a])
    \*                                             ELSE msg_queues[a]]
    /\ msg_queues' = [msg_queues EXCEPT ![a] = Tail(msg_queues[a])]                                           
    /\ UNCHANGED<<actorStatus,m, tmsg, totalNumWorkers, workersCreated,actorWorkers>>    

WorkerBusy(w,a) == 
    /\ workerStatus[w] = [actor|->a, status|->"BUSY"]  
    /\ m' = m + 1  
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"FINISHED"]]    
    /\ UNCHANGED<<msg_queues,actorStatus,tmsg, totalNumWorkers, workersCreated,actorWorkers>>   

FreeWorker(w,a) ==
 /\ workerStatus[w] = [actor|->a, status|->"FINISHED"]
 /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"IDLE"]] 
 /\ UNCHANGED<<msg_queues,actorStatus,m, tmsg, totalNumWorkers, workersCreated,actorWorkers>>         

Next ==     \/ \E msg \in Message, a \in Actors: ActorRecv(msg,a)  
            \/ \E w \in Workers,  a \in Actors: CreateWorker(w,a)
            \/ \E w \in Workers, a \in Actors: WorkerRecv(w, a)
            \/ \E w \in Workers, a\in Actors: WorkerBusy(w,a)
            \/ \E w \in Workers, a\in Actors: FreeWorker(w,a)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E w \in Workers, a \in Actors: CreateWorker(w,a))
        /\ WF_vars(\E w \in Workers, a \in Actors: WorkerRecv(w,a))
        /\ WF_vars(\E w \in Workers, a \in Actors: WorkerBusy(w,a))
        /\ WF_vars(\E w \in Workers,a \in Actors: FreeWorker(w,a))  
        

=============================================================================
\* Modification History
\* Last modified Sun Aug 16 16:07:33 CDT 2020 by spadhy
\* Created Mon Aug 10 10:23:50 CDT 2020 by spadhy
