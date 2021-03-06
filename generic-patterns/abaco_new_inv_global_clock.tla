--------------------- MODULE abaco_new_inv_global_clock ---------------------

EXTENDS Naturals, FiniteSets, FiniteSetTheorems, Sequences, SequenceOpTheorems,TLAPS

CONSTANTS MaxMessage,        \* Maximum number of HTTP requests that are sent
          ScaleUpThreshold,  \* ScaleUpThreshold 
          MinimumWorkersAlwaysUpPerActor,  \* Minimum number of workers should always be running per actor
          MaxWorkers,        \* Maximum Number of workers that can be created
          Actors             \* Actor list
                
          
            
ASSUME SpecAssumption == 
         /\ MaxMessage \in (Nat \ {0})
         /\ ScaleUpThreshold \in (Nat \ {0}) (* ScaleUpThreshold should be atleast 1 *)   
         /\ MinimumWorkersAlwaysUpPerActor \in (Nat \ {0})  (* Atleast one worker should always be running *) 
         /\ MaxWorkers \in (Nat \ {0})
         /\ MinimumWorkersAlwaysUpPerActor <= MaxWorkers 
         /\ Actors # {}
         /\ MinimumWorkersAlwaysUpPerActor * Cardinality(Actors) <= MaxWorkers
         
          
         
 
---------------------------------------------------------------------------------------          
          
VARIABLES Workers,              \* Total number of workers being created
          actor_msg_queues,     \* Message queue per actor
          command_queues,
          worker_command_queues,
          actorStatus,          \* actor's status
          workerStatus,         \* worker status
          
          tmsg,                 \* total number of messages sent
          work,                 \* representation of work
          actorWorkers,         \*
          idleworkers,          \* Set of Idle workers
          busyworkers,          \* Set of Busy workers
         
          revision_number,      \* current actor revision number
          revision_number_for_workers, \* revision number of workers using which a worker is started
          hist_actor_rev_number,  \* history of actor's image revision number,
          hist_worker_rev_number, \* history of actor image used by the worker at the time of worker's creation
          clock
                   
 
 
 vars == <<Workers, actor_msg_queues, command_queues, worker_command_queues, actorStatus, workerStatus, 
 tmsg, work, actorWorkers, idleworkers, busyworkers,revision_number, revision_number_for_workers, 
 hist_actor_rev_number,  hist_worker_rev_number, clock>>  
 
\* workerState
workerState == {"-","IDLE","BUSY", "SHUTDOWN_REQUESTED"}

\* Actor State
ActorState == {"STARTING_UP","READY","UPDATING_IMAGE"}

\* All Actors Set
AllActors == Actors \cup {"-"}

(*
************************************************************************************
Set of all possible message types in the queue             
************************************************************************************
*)
 
 \* These message types represent BOTH the HTTP request message (sent by the user)
 \* and the message queued in a message queue
 \* In the real implementation, the messages are not exactly the same,
 \* but we make this simplification for the spec:

ActorMessage == [type : {"EXECUTE"}, actor:Actors]

CommandMessage == [type : {"UPDATE"},  actor: Actors]


\* These are messages sent directly from internal Abaco processes (such as the autoscaler) to the worker.
WorkerMessage == [type: {"COMMAND"}, message: {"SHUTDOWN"}]


HistoryRecord == [rnum: Nat, ts:Nat]
----------------------------------------------------------------------------------------


(*
***********************************
Invariants and Temporal Properties
***********************************
*)

\* An invariant: ensures all the variables maintain the proper types.
TypeInvariant == 
  /\ actorStatus \in [Actors -> ActorState ] 
  /\ Workers \in {1..MaxWorkers}
  /\ workerStatus \in [Workers -> [status:workerState,actor:AllActors]] 
  /\ actor_msg_queues \in [Actors->Seq(ActorMessage)]
  /\ command_queues \in [Actors -> Seq(CommandMessage)] \* multiple queues
  /\ worker_command_queues \in [Workers -> Seq(WorkerMessage)] \* multiple queues
  /\ tmsg \in 0..MaxMessage
  /\ \A a \in Actors: tmsg >= Len(actor_msg_queues[a])
  /\ work \in 1..MaxMessage
  /\ actorWorkers \in [Actors -> SUBSET Workers]
  /\ idleworkers \in SUBSET Workers
  /\ \A s1 \in idleworkers:workerStatus[s1].status = "IDLE"
  /\ busyworkers \in SUBSET Workers
  /\ \A s2 \in busyworkers:workerStatus[s2].status = "BUSY"
  /\ idleworkers \intersect busyworkers = {} 
  /\ revision_number \in [Actors -> Nat]
  /\ revision_number_for_workers \in [Workers -> Nat]
  /\ hist_actor_rev_number \in [Actors -> [rnum:Nat, ts: Nat]]
  /\ hist_worker_rev_number \in [Workers ->[rnum:Nat, ts: Nat]]
  /\ clock \in Nat
  
  

TotalworkersRunning == idleworkers \cup busyworkers
  

ClockInv ==  /\ \A a \in Actors: hist_actor_rev_number[a].ts<= clock 
             /\ \A w \in Workers: hist_worker_rev_number[w].ts<=clock    


SafetyProperty ==  /\ Cardinality(idleworkers) \in 0..MaxWorkers
                   /\ Cardinality(busyworkers) \in 0..MaxWorkers
                   /\ IsFiniteSet(idleworkers)
                   /\ IsFiniteSet(busyworkers)
                   /\ Cardinality(idleworkers) + Cardinality(busyworkers) <= MaxWorkers
                   /\ \A s \in Workers:workerStatus[s].status = "IDLE" => s \in idleworkers
                   /\ \A s \in Workers:workerStatus[s].status = "BUSY" => s \in busyworkers
                   /\ \A a\in Actors: IsFiniteSet(actorWorkers[a])
                   /\ \A a \in Actors: actorStatus[a]="READY"=>(Cardinality(actorWorkers[a]) >= MinimumWorkersAlwaysUpPerActor)
                   
                   

                   



\* what we want to prove SafetyProperty1 ==  \A w \in Workers:  workerStatus[w].actor # "-" => (\A x \in hist_actor_rev_number[workerStatus[w].actor]: x.ts < hist_worker_rev_number[w].ts => x.rnum <= hist_worker_rev_number[w].rnum)

 SafetyProperty1 ==  \A w \in Workers:  workerStatus[w].actor # "-" =>  (hist_worker_rev_number[w].rnum < hist_actor_rev_number[workerStatus[w].actor].rnum => hist_actor_rev_number[workerStatus[w].actor].ts >= hist_worker_rev_number[w].ts)


\* (i.e., that the length of msq_queue is eventually 0  
\* from some point until the end of the run.)
AllMessagesProcessed == <>[](\A a \in Actors: Len(actor_msg_queues[a]) = 0)   

      
 
(*
****************************
Initialization of Variables
****************************
*)

Init == 
    /\ actorStatus = [a \in Actors |-> "STARTING_UP" ] \* Each Actor is starting up 
    /\ Workers = 1..MaxWorkers
    /\ workerStatus = [s \in Workers |-> [status|->"-", actor|->"-"]] \* worker has not yet started/created
    /\ actor_msg_queues = [a \in Actors |-> <<>>]
    /\ command_queues = [a \in Actors |-> <<>>]
    /\ worker_command_queues = [w \in Workers|-> <<>>]
    /\ tmsg  = 0
    /\ work = 1
    /\ actorWorkers = [a \in Actors |-> {}]
    /\ idleworkers = {}
    /\ busyworkers = {}
    /\ revision_number = [a \in Actors |-> 1] \* changed from 0 to 1 for proof 
    /\ revision_number_for_workers = [w \in Workers |-> 0]
    /\ hist_actor_rev_number = [a \in Actors|-> [rnum|->1, ts|->0]]
    /\ hist_worker_rev_number = [w \in Workers|-> [rnum|->0, ts|->0]]
    /\ clock = 0
  
 
----------------------------------------------------------------------------------    
(*    
*************************************
HTTP Requests/Synchronous Processing
*************************************
*)

(*
 
Creates Minimum number of workers for each actor when the system bootstraps

*)
(*/\ WtoA[w]="-"
        /\ valY[w].val < valX[a].val
        /\ valY[w].ts <= valX[a].ts   \* This is for proof
        /\ clock' = clock + 1
        /\ WtoA'= [WtoA EXCEPT ![w]=a]
        /\ valY'=[valY EXCEPT ![w]=[val|->valX[a].val, ts|->clock']] 
        /\ UNCHANGED<<valX,WtoA, n>>  
        *)  
Startworker(w,a) ==
    /\ Cardinality(actorWorkers[a]) < MinimumWorkersAlwaysUpPerActor     \* Actor does not have minimum number of workers up
    /\ Cardinality(idleworkers) + Cardinality(busyworkers) < MaxWorkers \* Total number of workers created should not exceed Maxworkers
    /\ workerStatus[w].actor = "-"        \* For proof, represent each element of the record instead of record notation workerStatus[w]=[actor|-> "-",status|->"-" ]
    /\ workerStatus[w].status = "-"
    /\ actorStatus[a] = "STARTING_UP"
    /\ hist_worker_rev_number[w].rnum < hist_actor_rev_number[a].rnum \* Adding for proof
    /\ hist_worker_rev_number[w].ts <= hist_actor_rev_number[a].ts
    /\ clock' = clock + 1
    /\ workerStatus'= [workerStatus EXCEPT ![w] = [actor|->a, status|->"IDLE"]]     
    /\ idleworkers' = idleworkers \cup {w}
    /\ actorWorkers'= [actorWorkers EXCEPT ![a] =  actorWorkers[a] \cup {w}]
    /\ revision_number_for_workers' = [revision_number_for_workers EXCEPT ![w] = revision_number[a]] \* This could have been revision_number_for_workers[w]+1] as it is part of the bootstrap but for consistency and safety property proof, we made it equal to revision_number[a]
    /\ hist_worker_rev_number' = [hist_worker_rev_number EXCEPT![w] = [rnum|->hist_actor_rev_number[a].rnum, ts|->clock']] \* checking for proof
    /\ UNCHANGED<<Workers,actorStatus, tmsg, actor_msg_queues, work, busyworkers, command_queues, worker_command_queues ,revision_number, hist_actor_rev_number>>

(*
Update Actor status from STARTING_UP to READY when minimum number of actors have been created for the actor
*)
UpdateActorStatus(a) ==
    /\ actorStatus[a] = "STARTING_UP"
    /\ Cardinality(actorWorkers[a])= MinimumWorkersAlwaysUpPerActor
    /\ clock'=clock+1
    /\ actorStatus'= [actorStatus EXCEPT ![a] = "READY"]  \* This could have been merged with previous step. We divided it into two steps for ease of proof
    /\ UNCHANGED<<Workers,tmsg, actor_msg_queues, work, busyworkers, command_queues, worker_command_queues ,revision_number, revision_number_for_workers, actorWorkers, idleworkers, workerStatus, hist_actor_rev_number,hist_worker_rev_number>>


APIExecuteRecv(msg, a) ==    
(*
Represents the API platform receiving an HTTP request to the POST /resource/{id} endpoint 
*)
    /\  actorStatus[a]= "READY" \/ actorStatus[a]= "UPDATING_IMAGE"
    /\  msg.type = "EXECUTE"
    /\  msg.actor = a
    /\  tmsg < MaxMessage
    /\  clock' = clock + 1
    /\  actor_msg_queues'= [actor_msg_queues EXCEPT ![a] = Append(actor_msg_queues[a],msg)]
    /\  tmsg' = tmsg + 1
    /\  UNCHANGED<<Workers, actorStatus, actorWorkers, work, workerStatus, busyworkers, idleworkers, command_queues, revision_number, revision_number_for_workers, worker_command_queues, hist_actor_rev_number,hist_worker_rev_number>>   



ActorUpdateRecv(msg, a) ==    
(*
Represents the Abaco platform receiving an HTTP request to the PUT /actors/{id} endpoint (i.e., to update an actor definition)
*)

    /\  actorStatus[a] = "READY"
    /\  msg.type = "UPDATE"
    /\  msg.actor = a
    /\  tmsg < MaxMessage
    /\  clock' = clock + 1
    /\  actorStatus' = [actorStatus EXCEPT ![a] = "UPDATING_IMAGE"]
    /\  command_queues'= [command_queues EXCEPT ![a] = Append(command_queues[a],msg)]
    /\  tmsg' = tmsg + 1
    /\  revision_number' = [revision_number EXCEPT ![a] =  revision_number[a]+ 1]
    /\  hist_actor_rev_number' = [hist_actor_rev_number EXCEPT ![a] =[rnum|->hist_actor_rev_number[a].rnum + 1,ts|->clock']]
    /\  UNCHANGED<<Workers, worker_command_queues, actorWorkers,
       actor_msg_queues, work, idleworkers, revision_number_for_workers, hist_worker_rev_number,busyworkers, workerStatus>> 
 
(*    
*****************************
Asynchronous Task Processing
*****************************
*)

UpdateActor(a, w) == 
(*
Represents internal processing of an actor update request. We represent this as an independent action because the processing happens 
asynchronously to the original HTTP request.
The enabling condition is the actorStatus value (UPDATING_IMAGE) which is set when receiving the HTTP request.
*)
    /\ Len(command_queues[a]) > 0
    /\ Head(command_queues[a]).type = "UPDATE"
    /\ actorStatus[a] = "UPDATING_IMAGE"
    \*/\ \A w \in actorWorkers[a]: revision_number_for_workers[w] = revision_number[a] <- TLAPS cannot able to proof, mostly because actorWorkers contains Workers with status IDLE, BUSY, SHUTDOWN_REQUESTED. 
    \* In that case, revision_number_for_workers[w] = revision_number[a] may not be true for SHUTDOWN_REQUESTED status. However, this step is enabled when all workers in actorWorkers with SHUTDOWN_REQUESTED
    \* status are stopped and released to the pool of workers.
    \* The following condition allows Actor status going from UPDATING_IMAGE to READY if for workers of the actor status's are not "-" or "SHUTDOWN_REQUESTED" that is the status is IDLE or BUSY,
    \* revision number used by worker should be equal to revision number of the actor
    
   \* /\ \A w \in Workers: (workerStatus[w].actor = a /\ workerStatus[w].status \notin {"-","SHUTDOWN_REQUESTED"})=> (revision_number_for_workers[w] = revision_number[workerStatus[w].actor])   \* an alternative to previous step      
    /\ workerStatus[w].actor = a 
    /\ workerStatus[w].status \notin {"-","SHUTDOWN_REQUESTED"}
    /\ revision_number_for_workers[w] = revision_number[workerStatus[w].actor]
    /\ Cardinality(actorWorkers[a]) >= MinimumWorkersAlwaysUpPerActor \* This condition is required so when number of workers always up falls below the threshold MinimumWorkersAlwaysUpPerActor,
    \* createworkers is called before updating the actor's status from UPDATING_IMAGE to READY
    /\  clock' = clock + 1
    /\ actorStatus' = [actorStatus EXCEPT ![a] = "READY"]
    /\ command_queues' = [command_queues EXCEPT ![a] = Tail(command_queues[a])]
    /\ UNCHANGED<<actor_msg_queues,worker_command_queues,tmsg,
       actorWorkers, Workers, revision_number, revision_number_for_workers, workerStatus, busyworkers,idleworkers, work,hist_actor_rev_number,hist_worker_rev_number>>


StartDeleteWorker(w,a) ==
(*
Represents internal processing that occurrs when the autoscaler determines that a worker should be deleted.
*)
\* change #2 - we enable a worker to be deleted if it is IDLE and does not have the most recent image revision number:
    /\ actorStatus[a] = "UPDATING_IMAGE" 
    /\ workerStatus[w].status = "IDLE"
    /\ workerStatus[w].actor = a \* for proof
    /\ revision_number_for_workers[w] # revision_number[a]
    /\ w \in actorWorkers[a]
    /\ clock' = clock + 1
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"SHUTDOWN_REQUESTED"]]
    /\ worker_command_queues' = [worker_command_queues EXCEPT ![w] = Append(worker_command_queues[w], [type |->"COMMAND", message |->"SHUTDOWN"])]
    /\ idleworkers' = idleworkers \ {w}
    /\ UNCHANGED<<actor_msg_queues,command_queues,actorStatus,tmsg,  
       actorWorkers, Workers, revision_number, revision_number_for_workers,busyworkers,work, hist_actor_rev_number,hist_worker_rev_number>>                                                  


CompleteDeleteWorker(w,a) ==
(*
Represents a worker receiving a message to shutdown and completing the shutdown process.
*)
    /\ Len(worker_command_queues[w]) > 0
    /\ Head(worker_command_queues[w]).type = "COMMAND"
    /\ Head(worker_command_queues[w]).message = "SHUTDOWN"
    /\ workerStatus[w].status = "SHUTDOWN_REQUESTED"
    /\ w \in actorWorkers[a]
    /\ (actorStatus[a]="READY"/\ Cardinality(actorWorkers[a]) > MinimumWorkersAlwaysUpPerActor) \/ actorStatus[a]="UPDATING_IMAGE" \* note the change in condition for the proof
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->"-", status|->"-"]]
    /\ clock' = clock + 1
    /\ revision_number_for_workers' = [revision_number_for_workers EXCEPT ![w] = 0]  \* as we are releasing workers
    /\ worker_command_queues' = [worker_command_queues EXCEPT ![w] = Tail(worker_command_queues[w])]
    /\ actorWorkers'=  [actorWorkers EXCEPT ![a] = actorWorkers[a] \ {w}]
    /\ hist_worker_rev_number' = [hist_worker_rev_number EXCEPT ![w]= [rnum|->0,ts|->0]]
    /\ UNCHANGED<<actor_msg_queues,command_queues,actorStatus, tmsg, busyworkers,
     Workers, revision_number, idleworkers, work, hist_actor_rev_number>>

 
 Createworker(w, a) ==
    /\ actorStatus[a]= "READY" \/ actorStatus[a]="UPDATING_IMAGE"
    /\ (Len(actor_msg_queues[a]) >= ScaleUpThreshold) \/ (actorStatus[a]="UPDATING_IMAGE"/\ Cardinality(actorWorkers[a]) < MinimumWorkersAlwaysUpPerActor) \* Condition modified for proof
    /\ ~(\E s1 \in actorWorkers[a]: workerStatus[s1].status = "IDLE")
    /\ workerStatus[w].status = "-"
    /\ w \notin actorWorkers[a] \* required for the proof 
    /\ Cardinality(idleworkers) + Cardinality(busyworkers) < MaxWorkers \* This condition is required for the proof of Safety property
    /\ hist_actor_rev_number[a].ts > hist_worker_rev_number[w].ts \* adding for proof
    /\ hist_actor_rev_number[a].rnum > hist_worker_rev_number[w].rnum \* adding for proof
    /\  clock' = clock + 1
    /\ workerStatus'= [workerStatus EXCEPT ![w] = [actor|->a,status|->"IDLE"]]     
    /\ idleworkers' = idleworkers \cup {w}
    /\ actorWorkers'= [actorWorkers EXCEPT ![a] =  actorWorkers[a] \cup {w}]
    /\ revision_number_for_workers' = [revision_number_for_workers EXCEPT ![w] = revision_number[a]]  
    /\ hist_worker_rev_number' = [hist_worker_rev_number EXCEPT![w] = [rnum|->hist_actor_rev_number[a].rnum, ts|->clock']]
    /\ UNCHANGED<<Workers,actorStatus,tmsg,actor_msg_queues, work, busyworkers, command_queues, revision_number, worker_command_queues, hist_actor_rev_number>>
        

 WorkerRecv(s,a) == 
    /\  Len(actor_msg_queues[a]) > 0 
    /\  actorStatus[a]= "READY" \/ actorStatus[a]="UPDATING_IMAGE" 
    /\  revision_number_for_workers[s] = revision_number[a]
    /\  workerStatus[s].actor = a
    /\  workerStatus[s].status = "IDLE"
    /\  clock' = clock + 1
    /\  actor_msg_queues'= [actor_msg_queues EXCEPT ![a] = Tail(actor_msg_queues[a])]
    /\  workerStatus'= [workerStatus EXCEPT ![s] = [actor|->a,status|->"BUSY"]]
    \*/\  workerStatus'= [workerStatus EXCEPT ![s] = [actor|->a,status|->"STARTING_EXECUTION"]]
    /\  busyworkers' = busyworkers \cup {s}
    /\  idleworkers' = idleworkers \ {s}
    /\  UNCHANGED<<Workers, actorStatus, actorWorkers, tmsg, work, command_queues, revision_number, revision_number_for_workers, worker_command_queues, hist_actor_rev_number, hist_worker_rev_number>>
   
   
 workerBusy(w, a) ==
    /\  actorStatus[a]= "READY" \/ actorStatus[a]= "UPDATING_IMAGE"
    /\  workerStatus[w].actor = a
    /\  workerStatus[w].status = "BUSY"
    /\  clock' = clock + 1
    /\  work' = (work % MaxMessage) + 1
    /\  workerStatus'= [workerStatus EXCEPT ![w] = [actor|->a, status|->"IDLE"]]
    /\  idleworkers' = idleworkers \cup {w}  
    /\  busyworkers' = busyworkers \ {w}
    /\  UNCHANGED<<Workers, actorStatus, actorWorkers, tmsg, actor_msg_queues, command_queues, revision_number, revision_number_for_workers, worker_command_queues,hist_actor_rev_number,hist_worker_rev_number>>


 Stopworker(w,a) == 
    /\  Len(actor_msg_queues[a]) = 0
    /\  revision_number_for_workers[w] = revision_number[a]
    /\  workerStatus[w].actor = a
    /\  workerStatus[w].status = "IDLE"
    /\  Cardinality({w1 \in actorWorkers[a]:workerStatus[w1].status="IDLE" }) > MinimumWorkersAlwaysUpPerActor \* note the change in the condition. a worker can be in actorWorkers set but in SHUTDOWN_REQUESTED Status
    /\  actorStatus[a]="READY"
    /\  w \in actorWorkers[a] \* required for proof and also a required condition
    /\  clock' = clock + 1
    /\  workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"SHUTDOWN_REQUESTED"]]
    /\  worker_command_queues' = [worker_command_queues EXCEPT ![w] = Append(worker_command_queues[w], [type |->"COMMAND", message |->"SHUTDOWN"])]
    /\  idleworkers' = idleworkers \ {w}
    /\  UNCHANGED<<Workers,actorStatus, tmsg,actor_msg_queues, work,actorWorkers, busyworkers,command_queues, revision_number, revision_number_for_workers,hist_actor_rev_number,hist_worker_rev_number>>
    
 Next == 
       \/ \E w \in Workers, a \in Actors: Startworker(w, a)
       \/ \E a \in Actors: UpdateActorStatus(a)
       \/ \E msg \in ActorMessage, a \in Actors: APIExecuteRecv(msg, a)
       \/ \E msg \in CommandMessage, a \in Actors: ActorUpdateRecv(msg, a)
       \/ \E a \in Actors, w \in Workers: UpdateActor(a,w)
       \/ \E w \in Workers, a \in Actors: Createworker(w, a)
       \/ \E w \in Workers, a \in Actors: WorkerRecv(w, a)
       \/ \E w \in Workers, a \in Actors: workerBusy(w, a)
       \/ \E w \in Workers, a \in Actors: Stopworker(w, a)
       \/ \E w \in Workers, a \in Actors: StartDeleteWorker(w,a)
       \/ \E w \in Workers, a \in Actors: CompleteDeleteWorker(w,a)
       

Spec == Init /\ [][Next]_vars  

FairSpec == Spec
        /\ WF_vars(\E w \in Workers, a \in Actors: Startworker(w, a))
        /\ WF_vars(\E a \in Actors: UpdateActorStatus(a))
        /\ WF_vars(\E a \in Actors, w \in Workers: UpdateActor(a, w))
        /\ WF_vars(\E w \in Workers, a \in Actors: Createworker(w, a))
        /\ WF_vars(\E w \in Workers, a \in Actors: WorkerRecv(w, a)) 
        /\ WF_vars(\E w \in Workers, a \in Actors: workerBusy(w, a)) 
        /\ WF_vars(\E w \in Workers, a \in Actors: Stopworker(w, a)) 
        /\ WF_vars(\E w \in Workers, a \in Actors: StartDeleteWorker(w,a))
        /\ WF_vars(\E w \in Workers, a \in Actors: CompleteDeleteWorker(w,a))



(*------------------------------------------------ Proof -------------------------------------*)


IInv == TypeInvariant


 
THEOREM TypeCorrect == Spec => []IInv
<1>1. Init => IInv
  BY SpecAssumption DEF Init, IInv, TypeInvariant, workerState, ActorState, AllActors, ActorMessage

<1>2. IInv /\ [Next]_vars => IInv'

<2> SUFFICES ASSUME IInv,
                      [Next]_vars
               PROVE  IInv'
    OBVIOUS
  <2>. USE SpecAssumption DEF Init, IInv, TypeInvariant, workerState, ActorState, AllActors, ActorMessage, CommandMessage,WorkerMessage
  <2>1. ASSUME NEW msg \in ActorMessage,
        NEW a \in Actors,
               APIExecuteRecv(msg,a)
        PROVE  IInv'
     BY <2>1 DEF APIExecuteRecv 
  <2>2. ASSUME NEW s \in Workers,
               NEW a \in Actors,   
               Startworker(s,a)  
        PROVE IInv'   
        <3>1. workerStatus' \in [Workers -> [status:workerState,actor:AllActors]] 
             BY <2>2 DEF Startworker
        <3>2. worker_command_queues' \in [Workers -> Seq(WorkerMessage)] \* multiple queues
             BY <2>2  DEF Startworker
        <3>3. idleworkers' \intersect busyworkers' = {} 
             BY <2>2  DEF Startworker
        <3>4. QED  
            BY <2>2 , <3>1,<3>2,<3>3 DEF Startworker
   <2>3. ASSUME NEW s \in Workers,
               NEW a \in Actors,
               Createworker(s, a)
        PROVE IInv'
        
        <3>1. clock' \in Nat
         BY <2>3 DEF Createworker
        <3>8. QED
     BY <2>3, <3>1 DEF Createworker
  <2>4. ASSUME NEW s \in Workers,
               NEW a \in Actors,  
                 WorkerRecv(s, a)
        PROVE IInv'
     BY <2>4 DEF WorkerRecv
  <2>5. ASSUME NEW s \in Workers,
               NEW a \in Actors, 
               workerBusy(s,a)
        PROVE IInv'
        
        <3>1. work' \in 1..MaxMessage
            BY <2>5 DEF workerBusy
        <3>2. clock' \in Nat
         BY <2>5 DEF workerBusy    
        <3>2a. actorStatus' \in [Actors -> ActorState ] 
          BY <2>5 DEF workerBusy
        <3>3. Workers' \in {1..MaxWorkers}
          BY <2>5 DEF workerBusy
      
        <3>20.QED
            BY <2>5,<3>1,<3>2,<3>3 DEF workerBusy                          
  <2>6. ASSUME NEW s \in Workers,
               NEW a \in Actors,
               Stopworker(s, a)
        PROVE IInv'
        <3>1. worker_command_queues' \in [Workers -> Seq(WorkerMessage)] \* multiple queues
             BY <2>6 DEF Stopworker
        <3>2. clock' \in Nat
         BY <2>6 DEF Stopworker
      
        <3>4. workerStatus' \in [Workers' -> [status:workerState,actor:AllActors]] 
         BY <2>6 DEF Stopworker
        
        <3>20. QED  
     BY <2>6, <3>1,<3>2, <3>4  DEF Stopworker         
  <2>7. ASSUME NEW msg \in CommandMessage,
        NEW a \in Actors,
        ActorUpdateRecv(msg, a) 
        PROVE IInv'
        BY <2>7 DEF ActorUpdateRecv
  <2>8.  ASSUME NEW  a\in Actors, NEW w\in Workers,
         UpdateActor(a,w)
         PROVE IInv'
     BY <2>8 DEF UpdateActor    
  <2>9.   ASSUME NEW  a \in Actors,
          NEW w \in Workers,
            StartDeleteWorker(w,a)  
            PROVE IInv'
     
        <3>1. worker_command_queues' \in [Workers -> Seq(WorkerMessage)] \* multiple queues
              BY <2>9 DEF StartDeleteWorker 
        <3>2. clock' \in Nat     
             BY <2>9 DEF StartDeleteWorker  
        <3>3 QED  
        BY <2>9, <3>1,<3>2 DEF StartDeleteWorker    
           
   <2>10. ASSUME NEW  a \in Actors,
          NEW w \in Workers,
            CompleteDeleteWorker(w,a)  
            PROVE IInv'
         BY <2>10 DEF CompleteDeleteWorker                 
  <2>12. CASE UNCHANGED vars
    BY <2>12 DEF vars
  <2>13. ASSUME NEW a \in Actors, UpdateActorStatus(a)
          PROVE IInv'
          BY <2>13 DEF  UpdateActorStatus
  <2>14. QED
    BY <2>1,<2>2,<2>3,<2>4,<2>5,<2>6,<2>7, <2>8,<2>9,<2>10,<2>12, <2>13 DEF Next
    
<1>. QED  BY <1>1, <1>2, PTL DEF Spec
---------------------------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------------------------
(******************************* inductive Invariant - Safety Property proof ******************************************)
THEOREM SafetyPropertyTheorem == Spec => []SafetyProperty
<1>1. Init => SafetyProperty
   <2> SUFFICES ASSUME Init
                PROVE  SafetyProperty
     OBVIOUS
   
   <2>1. IsFiniteSet(idleworkers)
        <3>1.IsFiniteSet(Workers)
        BY  SpecAssumption, FS_Interval DEF Init
        <3>2. QED  BY <3>1, SpecAssumption, FS_EmptySet, FS_Subset DEF Init
   <2>2. IsFiniteSet(busyworkers)
        BY  SpecAssumption, FS_EmptySet, FS_Subset DEF Init
     
   <2>4. Cardinality(idleworkers)+ Cardinality(busyworkers) <= MaxWorkers
      BY  <2>1,<2>2,SpecAssumption, FS_EmptySet, FS_Subset DEF Init
   <2>5. Cardinality(idleworkers) \in 0..MaxWorkers
         BY SpecAssumption, <2>1, FS_Interval DEF Init
   <2>6. Cardinality(busyworkers) \in 0..MaxWorkers
        BY SpecAssumption, <2>2, FS_EmptySet DEF Init
   <2>7. \A s \in Workers:workerStatus[s].status = "IDLE" => s \in idleworkers
        BY DEF Init
   <2>8. \A s \in Workers:workerStatus[s].status = "BUSY" => s \in busyworkers
        BY DEF Init
   <2>9. \A a\in Actors: IsFiniteSet(actorWorkers[a]) 
        BY FS_EmptySet, FS_Subset DEF Init
   <2>10. \A a \in Actors: actorStatus[a]="READY"=>(Cardinality(actorWorkers[a]) >= MinimumWorkersAlwaysUpPerActor)
        BY  <2>1,<2>2, SpecAssumption, FS_EmptySet, FS_Subset DEF Init
    
   <2>11. QED
       BY <2>1, <2>2, <2>4,<2>5,<2>6,<2>7,<2>8,<2>9,<2>10 DEF SafetyProperty
 
<1>2. IInv /\ SafetyProperty /\ [Next]_vars => SafetyProperty'
  <2> SUFFICES ASSUME IInv,
                      SafetyProperty,
                      [Next]_vars
               PROVE  SafetyProperty'
    BY DEF SafetyProperty
  <2>.USE SpecAssumption DEF IInv, TypeInvariant, Init, workerState, ActorMessage, ActorState, SafetyProperty,TotalworkersRunning, AllActors, CommandMessage, WorkerMessage
  <2>1. ASSUME NEW s \in Workers,
            NEW a \in Actors,
               Startworker(s,a)
        PROVE  SafetyProperty'
        <3>1. IsFiniteSet(Workers')
            BY <2>1, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF Startworker 
        <3>2. IsFiniteSet(idleworkers')
            BY <2>1, <3>1,FS_EmptySet, FS_AddElement, FS_Subset DEF Startworker
        <3>3. IsFiniteSet(busyworkers')
            BY <2>1, FS_EmptySet, FS_Subset DEF Startworker
        <3>4. Cardinality(idleworkers') = Cardinality(idleworkers) + 1
            BY <2>1,<3>1,<3>2, FS_EmptySet, FS_Subset, FS_AddElement DEF Startworker        
        <3>5. Cardinality(idleworkers') \in 0..MaxWorkers
             BY  <2>1,<3>1,<3>2,<3>4, FS_EmptySet, FS_Interval,FS_AddElement, FS_Subset DEF Startworker
        <3>6. Cardinality(busyworkers') \in 0..MaxWorkers
            BY  <2>1,<3>2,FS_EmptySet,FS_AddElement, FS_Subset DEF Startworker
        <3>7. Cardinality(idleworkers') + Cardinality(busyworkers') <= MaxWorkers
            BY <2>1, <3>1, <3>2,<3>3,<3>4,<3>5, FS_EmptySet, FS_Subset DEF Startworker
        <3>10. \A a1 \in Actors: IsFiniteSet(actorWorkers'[a1]) 
            BY <2>1, FS_EmptySet, FS_Interval,FS_AddElement, FS_Subset DEF Startworker     
        <3>11.\A a1 \in Actors: actorStatus'[a1]="READY"=>(Cardinality(actorWorkers'[a1]) >= MinimumWorkersAlwaysUpPerActor)
             BY <2>1 DEF Startworker   
        <3>13. QED BY <2>1, <3>1, <3>2,<3>3,<3>4,<3>5, <3>6, <3>7,<3>10,<3>11, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF Startworker   
  <2>2. ASSUME NEW msg \in ActorMessage,
               NEW a \in Actors,
               APIExecuteRecv(msg, a)
        PROVE  SafetyProperty'
        BY <2>2 DEF APIExecuteRecv  
  
  <2>3. ASSUME NEW s \in Workers,
            NEW a \in Actors,
               Createworker(s,a)
        PROVE  SafetyProperty'
         
       <3>1. IsFiniteSet(Workers')
            BY <2>3, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF Createworker 
        <3>2. IsFiniteSet(idleworkers')
            BY <2>3, <3>1, FS_EmptySet, FS_AddElement, FS_Subset DEF Createworker
        <3>3. IsFiniteSet(busyworkers')
            BY <2>3, FS_EmptySet, FS_Subset DEF Createworker
        <3>4. Cardinality(idleworkers') = Cardinality(idleworkers) + 1
           
            <4>2. idleworkers' = idleworkers \cup {s}
             BY <2>3,<3>1,<3>2, FS_EmptySet, FS_Subset, FS_AddElement DEF Createworker
            <4>3. s \notin idleworkers
            BY <2>3, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF Createworker
            <4>4. QED 
                 BY <2>1,<3>1,<3>2,<4>2,<4>3, FS_EmptySet, FS_Subset, FS_AddElement DEF Createworker        
        <3>5. Cardinality(idleworkers') \in 0..MaxWorkers
           <4>1. idleworkers' \in SUBSET Workers'
           BY <2>3 DEF Createworker
           <4>2. Cardinality(Workers') = MaxWorkers
           BY <2>3, FS_Interval DEF Createworker
           <4>3. Cardinality(idleworkers') <= MaxWorkers \*Cardinality(workers')
                BY <2>3,<3>1,<3>2,<4>1,<4>2, FS_EmptySet, FS_Subset DEF Createworker
           <4>4. QED 
                BY  <2>3,<3>1,<3>2,<3>4,<4>1,<4>2,<4>3,FS_EmptySet, FS_Interval,FS_AddElement, FS_Subset DEF Createworker
        
        <3>6. Cardinality(busyworkers') \in 0..MaxWorkers
            BY  <2>3,<3>2,FS_EmptySet,FS_AddElement, FS_Subset DEF Createworker
        <3>7. Cardinality(idleworkers') + Cardinality(busyworkers') <= MaxWorkers
            BY <2>3, <3>1, <3>2,<3>3,<3>4,<3>5, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF Createworker
        <3>8.  \A s1 \in Workers': workerStatus'[s1].status = "IDLE" => s1 \in idleworkers'
            BY <2>3 DEF Createworker
        <3>9. \A s2 \in Workers':workerStatus'[s2].status = "BUSY" => s2 \in busyworkers'
                   BY <2>3, <3>1, <3>2,<3>3,<3>4,<3>5, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF Createworker
        <3>10. \A a1 \in Actors: IsFiniteSet(actorWorkers'[a1]) 
            BY <2>3, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF Createworker    
        <3>11.Cardinality(actorWorkers'[a]) =  Cardinality(actorWorkers[a]) + 1
            <4>1. IsFiniteSet(actorWorkers[a]) 
            BY <2>3, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF Createworker 
            <4>2. s \notin actorWorkers[a]
            BY <2>3 DEF Createworker 
            <4>3. actorWorkers'[a] = actorWorkers[a] \cup {s}
            BY <2>3 DEF Createworker 
            <4>4. IsFiniteSet(actorWorkers'[a])
            BY <2>3,FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF Createworker 
            <4>5. QED 
            BY <2>3,<3>10,<4>1,<4>2,<4>3,<4>4,FS_EmptySet, FS_Interval,FS_AddElement, FS_CardinalityType, FS_Subset DEF Createworker
            
        <3>12. \A a1 \in Actors: actorStatus'[a1]="READY"=>(Cardinality(actorWorkers'[a1]) >= MinimumWorkersAlwaysUpPerActor)
             BY <2>3, <3>1, <3>11,FS_EmptySet,FS_AddElement, FS_CardinalityType, FS_Subset DEF Createworker 
            
        <3>20. QED BY <2>3, <3>1, <3>2,<3>3,<3>4,<3>5, <3>6,<3>7,<3>8,<3>9,<3>10,<3>12, FS_EmptySet, FS_Interval, FS_CardinalityType, FS_AddElement, FS_Subset DEF Createworker   
  
  
  <2>4. ASSUME NEW s \in Workers,
                 NEW a \in Actors,
               WorkerRecv(s,a)
              
        PROVE  SafetyProperty'
            
        <3>1. IsFiniteSet(idleworkers')
            BY <2>4, FS_EmptySet, FS_Subset DEF WorkerRecv
        <3>2. IsFiniteSet(busyworkers')
            BY <2>4, FS_EmptySet, FS_AddElement, FS_Subset DEF WorkerRecv
            
        <3>3. Cardinality(busyworkers') = Cardinality(busyworkers) + 1
            BY <2>4, FS_EmptySet, FS_AddElement, FS_Subset DEF WorkerRecv    
        <3>4. Cardinality(idleworkers') =  Cardinality(idleworkers) - 1
            BY <2>4, FS_EmptySet, FS_RemoveElement, FS_Subset DEF WorkerRecv
            
        <3>20. QED BY <2>4, <3>1,<3>2,<3>3,<3>4, FS_EmptySet,FS_AddElement, FS_RemoveElement, FS_Subset DEF WorkerRecv
       
  <2>5. ASSUME NEW s \in Workers,
                 NEW a \in Actors,
               workerBusy(s,a)
        PROVE  SafetyProperty'
        <3>1. IsFiniteSet(idleworkers')
            BY <2>5, FS_EmptySet, FS_AddElement, FS_Subset DEF workerBusy
        <3>2. IsFiniteSet(busyworkers')
            BY <2>5, FS_EmptySet, FS_Subset DEF workerBusy
        <3>3. Cardinality(busyworkers') = Cardinality(busyworkers) - 1
            BY <2>5,FS_EmptySet, FS_RemoveElement, FS_Subset DEF workerBusy 
        <3>4. Cardinality(idleworkers') =  Cardinality(idleworkers) + 1
            BY <2>5, FS_EmptySet, FS_AddElement, FS_Subset DEF workerBusy
        <3>5. Cardinality(idleworkers')+ Cardinality(busyworkers') <= MaxWorkers
            BY <2>5, <3>1, <3>2,<3>3, <3>4 
        <3>6. Cardinality(busyworkers') \in 0..MaxWorkers
         BY  <2>5, <3>2,<3>3, <3>5,FS_EmptySet,FS_RemoveElement, FS_Interval,FS_Subset DEF workerBusy    
        <3>7. Cardinality(idleworkers') \in 0..MaxWorkers 
               BY  <2>5,<3>1, <3>4, <3>5,FS_EmptySet,FS_AddElement, FS_Interval,FS_Subset DEF workerBusy  
        <3>8. \A s1 \in Workers': workerStatus'[s1].status = "IDLE" => s1 \in idleworkers'
            BY <2>5 DEF workerBusy  
        <3>9. \A s2 \in Workers':workerStatus'[s2].status = "BUSY" => s2 \in busyworkers'
             BY <2>5 DEF workerBusy
        <3>14. QED BY <2>5, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, FS_EmptySet, FS_AddElement, FS_RemoveElement, FS_Subset DEF workerBusy
  
  <2>6. ASSUME NEW s \in Workers,
                 NEW a \in Actors,
               Stopworker(s,a)
        PROVE  SafetyProperty'
         <3>1. IsFiniteSet(idleworkers')
            BY <2>6,FS_EmptySet, FS_Subset DEF Stopworker
        <3>2. IsFiniteSet(busyworkers')
            BY <2>6 DEF Stopworker
        <3>3. Cardinality(busyworkers') = Cardinality(busyworkers)
            BY <2>6 DEF Stopworker 
        <3>4. Cardinality(idleworkers') =  Cardinality(idleworkers) - 1
            BY <2>6,<3>1, FS_EmptySet, FS_RemoveElement, FS_Subset DEF Stopworker
        <3>5. Cardinality(idleworkers')+ Cardinality(busyworkers') <= MaxWorkers
            BY <2>6, <3>1, <3>2, <3>3, <3>4     
        <3>6. Cardinality(busyworkers') \in 0..MaxWorkers
         BY  <2>6, <3>2,<3>3, <3>5,FS_EmptySet, FS_Interval,FS_Subset   
        <3>7. Cardinality(idleworkers') \in 0..MaxWorkers 
               BY  <2>6,<3>1, <3>4, <3>5, FS_EmptySet, FS_Subset, FS_Interval 
        <3>8. \A s1 \in Workers': workerStatus'[s1].status = "IDLE" => s1 \in idleworkers'
           BY <2>6 DEF Stopworker
        <3>9. \A s2 \in Workers':workerStatus'[s2].status = "BUSY" => s2 \in busyworkers'
           BY <2>6 DEF Stopworker
        <3>10. \A a1 \in Actors: IsFiniteSet(actorWorkers'[a1]) 
            BY <2>6, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF Stopworker     
        <3>12. \A a1 \in Actors: actorStatus'[a1]="READY"=>(Cardinality(actorWorkers'[a1]) >= MinimumWorkersAlwaysUpPerActor)
             BY <2>6, <3>10, <3>1,FS_EmptySet,FS_RemoveElement, FS_Subset, FS_CardinalityType DEF Stopworker      \* CardinalityType is Required     
        <3>20. QED BY <2>6, <3>1, <3>2,<3>4,<3>5,<3>6,<3>7,<3>8,<3>9,<3>10,<3>12, FS_EmptySet,FS_Interval,FS_AddElement, FS_RemoveElement, FS_CardinalityType, FS_Subset DEF Stopworker
  <2>7. ASSUME NEW msg \in CommandMessage,
        NEW a \in Actors,
        ActorUpdateRecv(msg, a) 
        PROVE SafetyProperty'
        BY <2>7 DEF ActorUpdateRecv
  <2>8. ASSUME NEW a \in Actors,
  NEW w \in Workers,
       UpdateActor(a,w)
       PROVE SafetyProperty'
        <3>1. TypeInvariant'
        BY <2>8 DEF UpdateActor
        <3>2. SafetyProperty'
         BY <2>8 DEF UpdateActor
        <3>10. QED
      BY <2>8, <3>1,<3>2 DEF UpdateActor 
  <2>9.  ASSUME NEW w \in Workers, 
        NEW a \in Actors,
         StartDeleteWorker(w,a) 
         PROVE SafetyProperty'
        <3>1. IsFiniteSet(idleworkers')
            BY <2>9,FS_EmptySet, FS_Subset DEF StartDeleteWorker
        <3>2. IsFiniteSet(busyworkers')
            BY <2>9 DEF StartDeleteWorker
        <3>3. Cardinality(busyworkers') = Cardinality(busyworkers)
            BY <2>9 DEF StartDeleteWorker 
        <3>4. Cardinality(idleworkers') =  Cardinality(idleworkers) - 1
            BY <2>9,<3>1, FS_EmptySet, FS_RemoveElement, FS_Subset DEF StartDeleteWorker
        <3>5. Cardinality(idleworkers')+ Cardinality(busyworkers') <= MaxWorkers
            BY <2>9, <3>1, <3>2, <3>3, <3>4     
        <3>6. Cardinality(busyworkers') \in 0..MaxWorkers
         BY  <2>9, <3>2,<3>3, <3>5,FS_EmptySet, FS_Interval,FS_Subset   
        <3>7. Cardinality(idleworkers') \in 0..MaxWorkers 
               BY  <2>9,<3>1, <3>4, <3>5, FS_EmptySet, FS_Subset, FS_Interval 
        <3>10. \A a1 \in Actors: IsFiniteSet(actorWorkers'[a1]) 
            BY <2>9, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF StartDeleteWorker  
        
        <3>12. \A a1 \in Actors: actorStatus'[a1]="READY"=>(Cardinality(actorWorkers'[a1]) >= MinimumWorkersAlwaysUpPerActor)
             BY <2>9, <3>10, <3>1,FS_EmptySet,FS_RemoveElement, FS_Subset, FS_CardinalityType DEF StartDeleteWorker     \* CardinalityType is Required     
      
       <3>17. QED
            BY <2>9, <3>1,<3>2, <3>3,<3>4,<3>5,<3>6,<3>7,<3>10,<3>12, FS_EmptySet,FS_Interval,FS_AddElement, FS_RemoveElement, FS_CardinalityType, FS_Subset DEF StartDeleteWorker   
  <2>10. ASSUME NEW  a \in Actors,
          NEW w \in Workers,
            CompleteDeleteWorker(w,a)  
            PROVE SafetyProperty'
        
    
     <3>1. IsFiniteSet(idleworkers')
            BY <2>10,FS_EmptySet, FS_Subset DEF CompleteDeleteWorker
        <3>2. IsFiniteSet(busyworkers')
            BY <2>10 DEF CompleteDeleteWorker
        <3>3. Cardinality(busyworkers') = Cardinality(busyworkers)
            BY <2>10 DEF CompleteDeleteWorker
        <3>4. Cardinality(idleworkers') =  Cardinality(idleworkers)
            BY <2>10,<3>1, FS_EmptySet, FS_RemoveElement, FS_Subset DEF CompleteDeleteWorker
        <3>5. Cardinality(idleworkers')+ Cardinality(busyworkers') <= MaxWorkers
            BY <2>10, <3>1, <3>2, <3>3, <3>4     
        <3>6. Cardinality(busyworkers') \in 0..MaxWorkers
         BY  <2>10, <3>2,<3>3, <3>5,FS_EmptySet, FS_Interval,FS_Subset   
        <3>7. Cardinality(idleworkers') \in 0..MaxWorkers 
               BY  <2>10,<3>1, <3>4, <3>5, FS_EmptySet, FS_Subset, FS_Interval 
        <3>8. \A s1 \in Workers': workerStatus'[s1].status = "IDLE" => s1 \in idleworkers'
            BY <2>10 DEF CompleteDeleteWorker
        <3>9. \A s2 \in Workers':workerStatus'[s2].status = "BUSY" => s2 \in busyworkers'
             BY <2>10 DEF CompleteDeleteWorker 
             
        <3>10. \A a1 \in Actors: IsFiniteSet(actorWorkers'[a1]) 
            BY <2>10, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF CompleteDeleteWorker
        <3>11.Cardinality(actorWorkers'[a]) =  Cardinality(actorWorkers[a]) - 1
            <4>1. IsFiniteSet(actorWorkers[a]) 
            BY <2>10, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF CompleteDeleteWorker  
            <4>2. w \in actorWorkers[a]
            BY <2>10 DEF CompleteDeleteWorker  
            <4>3. actorWorkers'[a] = actorWorkers[a] \ {w}
            BY <2>10 DEF CompleteDeleteWorker  
            <4>4. IsFiniteSet(actorWorkers'[a])
            BY <2>10,FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF CompleteDeleteWorker  
            <4>5. QED 
            BY <2>10,<3>10,<4>1,<4>2,<4>3,<4>4,FS_EmptySet, FS_Interval,FS_RemoveElement, FS_CardinalityType, FS_Subset DEF CompleteDeleteWorker 
        <3>12. \A a1 \in Actors: actorStatus'[a1]="READY"=>(Cardinality(actorWorkers'[a1]) >= MinimumWorkersAlwaysUpPerActor)
             BY <2>10, <3>10, <3>1,<3>11,FS_EmptySet,FS_RemoveElement, FS_Subset, FS_CardinalityType DEF CompleteDeleteWorker
      
     <3>16. QED
       BY <2>10, <3>1,<3>2, <3>3,<3>5,<3>4, <3>6,<3>7,<3>8,<3>9,<3>10,<3>12,FS_EmptySet,FS_Interval,FS_AddElement, FS_RemoveElement, FS_CardinalityType, FS_Subset DEF CompleteDeleteWorker    
        
  <2>15. CASE UNCHANGED vars
        BY <2>15 DEF vars
   <2>16. ASSUME NEW a \in Actors, UpdateActorStatus(a)
          PROVE SafetyProperty'
          BY <2>16 DEF  UpdateActorStatus     
  <2>17. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6,<2>7,<2>8,<2>9,<2>10,<2>15, <2>16 DEF Next
 
<1>. QED  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec




(*
   ClockInv ==  /\ \A a \in Actors: hist_actor_rev_number[a].ts<= clock 
             /\ \A w \in Workers: hist_worker_rev_number[w].ts<=clock    
   
*)

THEOREM Spec=>[]ClockInv
  <1>1. Init => ClockInv
  BY  DEF Init, ClockInv
  <1>2. IInv /\ ClockInv /\ [Next]_vars => ClockInv'
    <2> SUFFICES ASSUME IInv,
                        ClockInv,
                        [Next]_vars
                 PROVE  ClockInv'
      OBVIOUS
    <2>. USE SpecAssumption DEF IInv, TypeInvariant, Init, workerState, ActorMessage, ActorState, SafetyProperty,TotalworkersRunning, AllActors, CommandMessage, WorkerMessage, ClockInv
    <2>1. ASSUME NEW w \in Workers,
                 NEW a \in Actors,
                 Startworker(w, a)
          PROVE  ClockInv'
          BY <2>1 DEF Startworker
    <2>2. ASSUME NEW a \in Actors,
                 UpdateActorStatus(a)
          PROVE  ClockInv'
          BY <2>2 DEF UpdateActorStatus
    <2>3. ASSUME NEW msg \in ActorMessage,
                 NEW a \in Actors,
                 APIExecuteRecv(msg, a)
          PROVE  ClockInv'
          BY <2>3 DEF APIExecuteRecv
    <2>4. ASSUME NEW msg \in CommandMessage,
                 NEW a \in Actors,
                 ActorUpdateRecv(msg, a)
          PROVE  ClockInv'
          BY <2>4 DEF ActorUpdateRecv
    <2>5. ASSUME NEW a \in Actors,
                 NEW w \in Workers,
                 UpdateActor(a,w)
          PROVE  ClockInv'
          BY <2>5 DEF UpdateActor
    <2>6. ASSUME NEW w \in Workers,
                 NEW a \in Actors,
                 Createworker(w, a)
          PROVE  ClockInv'
          BY <2>6 DEF Createworker
    <2>7. ASSUME NEW w \in Workers,
                 NEW a \in Actors,
                 WorkerRecv(w, a)
          PROVE  ClockInv'
          BY <2>7 DEF WorkerRecv
    <2>8. ASSUME NEW w \in Workers,
                 NEW a \in Actors,
                 workerBusy(w, a)
          PROVE  ClockInv'
          BY <2>8 DEF  workerBusy 
    <2>9. ASSUME NEW w \in Workers,
                 NEW a \in Actors,
                 Stopworker(w, a)
          PROVE  ClockInv'
          BY <2>9 DEF Stopworker     
    <2>10. ASSUME NEW w \in Workers,
                  NEW a \in Actors,
                  StartDeleteWorker(w,a)
           PROVE  ClockInv'
           BY <2>10 DEF StartDeleteWorker
    <2>11. ASSUME NEW w \in Workers,
                  NEW a \in Actors,
                  CompleteDeleteWorker(w,a)
           PROVE  ClockInv'
           BY <2>11 DEF CompleteDeleteWorker
    <2>12. CASE UNCHANGED vars
            BY <2>12 DEF vars
    <2>13. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Next
 
  
  <1>. QED  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

(*
--------------------------------------------------------------------------------------------------
--------------------------------------------- Inductive Invariant 2 Proof ------------------------
--------------------------------------------------------------------------------------------------
*)

\*SafetyProperty1 ==  \A w \in Workers:  workerStatus[w].actor # "-" =>  (hist_worker_rev_number[w].rnum = hist_actor_rev_number[workerStatus[w].actor].rnum => hist_actor_rev_number[workerStatus[w].actor].ts < hist_worker_rev_number[w].ts)

IInv2 == TypeInvariant /\ SafetyProperty /\ SafetyProperty1/\ClockInv   


THEOREM Spec => []SafetyProperty1   
<1>1. Init => SafetyProperty1 /\ ClockInv   
     BY  SpecAssumption DEF IInv, TypeInvariant, Init,workerState, ActorState, AllActors, ActorMessage, SafetyProperty,SafetyProperty1,ClockInv   
   

<1>2. IInv /\ SafetyProperty/\ ClockInv /\ SafetyProperty1 /\ ClockInv/\ [Next]_vars => SafetyProperty1'/\ ClockInv' 
  <2> SUFFICES ASSUME IInv,
                      SafetyProperty,
                      SafetyProperty1,
                      [Next]_vars, ClockInv
               PROVE  SafetyProperty1'/\ ClockInv'
    BY DEF IInv, SafetyProperty, SafetyProperty1
  <2>.USE SpecAssumption DEF IInv, TypeInvariant, Init, workerState, ActorMessage, ActorState, SafetyProperty,TotalworkersRunning, AllActors, CommandMessage, WorkerMessage,SafetyProperty1,ClockInv       
  <2>1. ASSUME NEW w \in Workers,
            NEW a \in Actors,
               Startworker(w,a)
        PROVE  SafetyProperty1'/\ ClockInv' 
    <3>1. SafetyProperty1'
        <4>1. workerStatus'[w].actor # "-" =>((hist_worker_rev_number'[w].rnum <  hist_actor_rev_number'[a].rnum) =>(hist_actor_rev_number'[a].ts >= hist_worker_rev_number'[w].ts))
            BY <2>1 DEF Startworker
      
       <4>2. QED BY <2>1, <4>1 DEF Startworker
      \*BY <2>1 DEF Startworker
    <3>2. ClockInv'
      BY <2>1 DEF Startworker
    <3>3. QED
      BY <3>1, <3>2
    
  
  <2>2. ASSUME NEW msg \in ActorMessage,
               NEW a \in Actors,
               APIExecuteRecv(msg, a)
        PROVE  SafetyProperty1' /\ ClockInv'
        BY <2>2 DEF APIExecuteRecv  
  
  <2>3. ASSUME NEW w \in Workers,
            NEW a \in Actors,
               Createworker(w,a)
        PROVE  SafetyProperty1'/\ ClockInv' 
       <3>1. SafetyProperty1'
        <4>1. workerStatus'[w].actor # "-" =>((hist_worker_rev_number'[w].rnum <  hist_actor_rev_number'[a].rnum) =>(hist_actor_rev_number'[a].ts >= hist_worker_rev_number'[w].ts))
            BY <2>3 DEF Createworker 
      
        <4>2. QED 
       BY <2>3,<4>1 DEF Createworker 
      <3>2. ClockInv'
      BY <2>3 DEF Createworker 
      <3>3. QED BY <3>1,<3>2
      \*BY <2>3,<>1 DEF Createworker
  
  
  <2>4. ASSUME NEW w \in Workers,
                 NEW a \in Actors,
               WorkerRecv(w,a)
              
        PROVE  SafetyProperty1'/\ ClockInv' 
      <3>1. SafetyProperty1'
       BY <2>4 DEF WorkerRecv 
      <3>2. ClockInv'
      BY <2>4 DEF WorkerRecv 
      <3>3. QED BY <3>1,<3>2
         
       
  <2>5. ASSUME NEW s \in Workers,
                 NEW a \in Actors,
               workerBusy(s,a)
        PROVE  SafetyProperty1'/\ ClockInv' 
       <3>1. SafetyProperty1'
       BY <2>5 DEF workerBusy 
      <3>2. ClockInv'
      BY <2>5 DEF workerBusy 
      <3>3. QED BY <3>1,<3>2
         
  
  <2>6. ASSUME NEW s \in Workers,
                 NEW a \in Actors,
               Stopworker(s,a)
        PROVE  SafetyProperty1'/\ ClockInv' 
       <3>1. SafetyProperty1'
      BY <2>6 DEF Stopworker
      <3>2. ClockInv'
      BY <2>6 DEF Stopworker
      <3>3. QED BY <3>1,<3>2
       
  
  <2>7. ASSUME NEW msg \in CommandMessage,
        NEW a \in Actors,
        ActorUpdateRecv(msg, a) 
        PROVE SafetyProperty1'/\ ClockInv' 
       <3>1. SafetyProperty1'
        <4>1. \A w \in Workers: workerStatus'[w].actor = a =>((hist_worker_rev_number'[w].rnum <  hist_actor_rev_number'[workerStatus'[w].actor].rnum) =>(hist_actor_rev_number'[workerStatus'[w].actor].ts >= hist_worker_rev_number'[w].ts))
           BY <2>7 DEF ActorUpdateRecv
      
       <4>2. QED 
       BY <2>7, <4>1 DEF ActorUpdateRecv
       <3>2. ClockInv'
       BY <2>7 DEF ActorUpdateRecv
      <3>3. QED BY <3>1,<3>2
  <2>8. ASSUME NEW a \in Actors, 
        NEW w \in Workers, 
       UpdateActor(a, w)
       PROVE SafetyProperty1'/\ ClockInv' 
      <3>1. SafetyProperty1'
      BY <2>8 DEF UpdateActor
      <3>2. ClockInv'
      BY <2>8 DEF UpdateActor
      <3>3. QED BY <3>1,<3>2
     
     
  <2>9.  ASSUME NEW w \in Workers, 
        NEW a \in Actors,
         StartDeleteWorker(w,a) 
         PROVE SafetyProperty1'/\ ClockInv' 
      <3>1. SafetyProperty1'
      BY <2>9 DEF StartDeleteWorker
      <3>2. ClockInv'
      BY <2>9 DEF StartDeleteWorker
      <3>3. QED BY <3>1,<3>2    
     
     
  <2>10. ASSUME NEW  a \in Actors,
          NEW w \in Workers,
            CompleteDeleteWorker(w,a)  
            PROVE SafetyProperty1'/\ ClockInv' 
      <3>1. SafetyProperty1'
      BY <2>10 DEF CompleteDeleteWorker
      <3>2. ClockInv'
      BY <2>10 DEF CompleteDeleteWorker
      <3>3. QED BY <3>1,<3>2         
     
      
  <2>14. ASSUME NEW a \in Actors, UpdateActorStatus(a)
          PROVE SafetyProperty1'/\ ClockInv' 
          BY <2>14 DEF  UpdateActorStatus      
  <2>15. CASE UNCHANGED vars
        BY <2>15 DEF vars
  <2>16. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6,<2>7,<2>8,<2>9,<2>10,<2>14,<2>15,ClockInv,FS_EmptySet,FS_Interval,FS_AddElement, FS_RemoveElement, FS_CardinalityType, FS_Subset DEF Next
 
<1>. QED  BY <1>1, <1>2, TypeCorrect, SafetyPropertyTheorem, PTL DEF Spec

=============================================================================
\* Modification History
\* Last modified Thu Apr 15 16:00:06 CDT 2021 by spadhy
\* Created Mon Mar 29 11:27:54 CDT 2021 by spadhy
