---------------------------- MODULE async_queue ----------------------------
(*
Algorithm Steps:
1. Send message to an Actor : Send(msg, a)
    a) Actor's status is ready
    b) stateful is false
2. The Actor recieves the message: ActorRecv(msg)
    a) creates an execution
    b) queues the execution, that is append the message into the queue tail
           
3. Worker recieves the message: WorkerRecv(msg)
    If queue length > 1 and a worker's state is idle (and no other workers picks that up)

    a) dequeue the execution message from thw head of queue
    b) Does the execution
    
4. Worker does the execution Do(W):
   a) status of worker changes from Busy to Finished
   b) perform the task

*)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Actors,           \* Set of Actors
          Message,          \* Set of all messages that can be sent
          MaxWorkers,       \* Maximum number of Workers started by the system,
          Workers,
          QueueLengthLimit, \* The limit after which autoscaler spawn a new worker
          MaxQueueSize,      \* Maximum queue size.  This we can make in unbounded as well 
          MaxMessage

VARIABLES msg_queue,    \* message_queue for messages
          actorStatus,          \* set of actors
          workerStatus,
          m,
          tmsg 
          
  vars == <<msg_queue,actorStatus,workerStatus,m, tmsg>>        


TypeInvariant == 
  /\ actorStatus \in [Actors -> { "SUBMITTED", "READY", "ERROR", "DELETED"}]
  /\ workerStatus \in [Workers -> {"IDLE", "BUSY","FINISHED"}] 
  \*/\ chan \in [val: Message, rdy:{0,1}]
  /\ msg_queue \in Seq(Message)
  
  

Init == 
    /\ actorStatus = [a \in Actors |-> "READY"] 
    /\ workerStatus = [w \in Workers|-> "IDLE"]
    /\ msg_queue = <<>>
    /\ m=0
    /\ tmsg = 0
    
    
(*Send(msg,a) == 
    /\ actorStatus[a]="READY"
    /\ chan' = [chan EXCEPT !.val = msg, !.rdy = 1 - @]
    *)

\*CreateExec(e) == 

ActorRecv(msg, a) ==    \* enabling condition ??
    \*/\ Create_Exec(e)
    /\  actorStatus[a]="READY"
    /\  tmsg < MaxMessage
    /\  Len(msg_queue) <  MaxQueueSize
    /\ msg_queue'= Append(msg_queue,msg)
    /\ tmsg' = tmsg + 1
    /\ UNCHANGED<<actorStatus,workerStatus,m>>   

DoWork(msg, w) == 
\*    /\ workerStatus[w] = "BUSY"
    /\ m' = m + 1
    /\ workerStatus' = [workerStatus EXCEPT ![w] = "FINISHED"]  
    /\ UNCHANGED<<msg_queue,actorStatus, tmsg>>     

WorkerRecv(w) ==
    /\ Len(msg_queue) > 0  
    /\ workerStatus[w] = "IDLE"
    /\ m' = m + 1
    /\ workerStatus' = [workerStatus EXCEPT ![w] = "FINISHED"]       
    /\ msg_queue'=Tail(msg_queue)
    /\ UNCHANGED<<actorStatus, tmsg>>   

FreeWorker(w) ==
 /\ workerStatus[w] = "FINISHED"
 /\ workerStatus' = [workerStatus EXCEPT ![w] = "IDLE"]
 /\ UNCHANGED<<msg_queue,actorStatus,m,tmsg>>   

 Next == /\ \/ \E msg \in Message, a \in Actors: ActorRecv(msg,a)
    \/ \E w \in Workers: WorkerRecv(w)
    \/ \E w2 \in Workers: FreeWorker(w2)
       
   

Spec == Init /\ [][Next]_vars  

=============================================================================
\* Modification History
\* Last modified Wed Jul 22 22:58:15 CDT 2020 by jstubbs
\* Last modified Wed Jul 22 17:53:11 CDT 2020 by spadhy
\* Created Tue Jul 21 23:41:57 CDT 2020 by spadhy
