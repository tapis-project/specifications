------------------------- MODULE fmcad_abaco_proof -------------------------
EXTENDS Naturals, FiniteSets, FiniteSetTheorems, Sequences, SequenceOpTheorems,TLAPS, TLC 

CONSTANTS MaxHTTPRequests,   \* Maximum number of HTTP requests that are sent
          ScaleUpThreshold,  \* ScaleUpThreshold 
          MinimumWorkersAlwaysUpPerActor,  \* Minimum number of workers should always be running per actor
          MaxWorkers,        \* Maximum Number of workers that can be created
          Actors             \* Actor list
                
          
            
ASSUME SpecAssumption == 
         /\ MaxHTTPRequests \in (Nat \ {0})
         /\ ScaleUpThreshold \in (Nat \ {0}) (* ScaleUpThreshold should be atleast 1 *)   
         /\ MinimumWorkersAlwaysUpPerActor \in (Nat \ {0})  (* Atleast one worker should always be running *) 
         /\ MaxWorkers \in (Nat \ {0})
         /\ MinimumWorkersAlwaysUpPerActor <= MaxWorkers 
         /\ Actors # {}
         /\ MinimumWorkersAlwaysUpPerActor * Cardinality(Actors) <= MaxWorkers
         
          
         
 
---------------------------------------------------------------------------------------          
          
VARIABLES Workers,              \* Total number of workers being created
          actorMsgQueues,     \* Message queue per actor
          commandQueues,
          workerCommandQueues,
          actorStatus,          \* actor's status
          workerStatus,         \* worker status
          
          totalHTTPSRequests,   \* total number of HTTP requests sent
          work,                 \* representation of work
          actorWorkers,         \*
          idleWorkers,          \* Set of Idle workers
          busyWorkers,          \* Set of Busy workers
         
          \*revisionNumber,      \* current actor revision number
          \*revisionNumberForWorkers, \* revision number of workers using which a worker is started
         actorRev,  \* history of actor's image revision number,
          workerRev, \* history of actor image used by the worker at the time of worker's creation
          clock
                   
 
 
 vars == <<Workers, actorMsgQueues, commandQueues, workerCommandQueues, actorStatus, workerStatus, 
 totalHTTPSRequests, work, actorWorkers, idleWorkers, busyWorkers,(*revisionNumber, revisionNumberForWorkers,*) 
actorRev,  workerRev, clock>>  
 
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
  /\ actorMsgQueues \in [Actors->Seq(ActorMessage)]
  /\ commandQueues \in [Actors -> Seq(CommandMessage)] \* multiple queues
  /\ workerCommandQueues \in [Workers -> Seq(WorkerMessage)] \* multiple queues
  /\ totalHTTPSRequests \in 0..MaxHTTPRequests
  /\ \A a \in Actors: totalHTTPSRequests >= Len(actorMsgQueues[a])
  /\ work \in 1..MaxHTTPRequests
  /\ actorWorkers \in [Actors -> SUBSET Workers]
  /\ idleWorkers \in SUBSET Workers
  /\ \A s1 \in idleWorkers:workerStatus[s1].status = "IDLE"
  /\ busyWorkers \in SUBSET Workers
  /\ \A s2 \in busyWorkers:workerStatus[s2].status = "BUSY"
  /\ idleWorkers \intersect busyWorkers = {} 
  (*/\ revisionNumber \in [Actors -> Nat]
  /\ revisionNumberForWorkers \in [Workers -> Nat]*)
  /\actorRev \in [Actors -> [rnum:Nat, ts: Nat]]
  /\ workerRev \in [Workers ->[rnum:Nat, ts: Nat]]
  /\ clock \in Nat
  
  

TotalWorkersRunning == idleWorkers \cup busyWorkers
  

ClockInv ==  /\ \A a \in Actors:actorRev[a].ts<= clock 
             /\ \A w \in Workers: workerRev[w].ts<=clock    


MinimalWorkerProperty ==  
                   /\ Cardinality(idleWorkers) \in 0..MaxWorkers
                   /\ Cardinality(busyWorkers) \in 0..MaxWorkers
                   /\ IsFiniteSet(idleWorkers)
                   /\ IsFiniteSet(busyWorkers)
                   /\ Cardinality(idleWorkers) + Cardinality(busyWorkers) <= MaxWorkers
                   /\ \A s \in Workers:workerStatus[s].status = "IDLE" => s \in idleWorkers
                   /\ \A s \in Workers:workerStatus[s].status = "BUSY" => s \in busyWorkers
                   /\ \A a\in Actors: IsFiniteSet(actorWorkers[a])
                   /\ \A a \in Actors: actorStatus[a]="READY"
                            =>(Cardinality(actorWorkers[a]) >= MinimumWorkersAlwaysUpPerActor)
                   

                   



\* what we want to prove RevisionNumberInv ==  \A w \in Workers:  workerStatus[w].actor # "-" => (\A x \inactorRev[workerStatus[w].actor]: x.ts < workerRev[w].ts => x.rnum <= workerRev[w].rnum)

RevisionNumberInv ==  \A w \in Workers:  workerStatus[w].actor # "-" =>  (workerRev[w].rnum <actorRev[workerStatus[w].actor].rnum =>actorRev[workerStatus[w].actor].ts >= workerRev[w].ts)


\* (i.e., that the length of msq_queue is eventually 0  
\* from some point until the end of the run.)
AllMessagesProcessed == <>[](\A a \in Actors: Len(actorMsgQueues[a]) = 0)   

      
 
(*
****************************
Initialization of Variables
****************************
*)

Init == 
    /\ actorStatus = [a \in Actors |-> "STARTING_UP" ] \* Each Actor is starting up 
    /\ Workers = 1..MaxWorkers
    /\ workerStatus = [s \in Workers |-> [status|->"-", actor|->"-"]] \* worker has not yet started/created
    /\ actorMsgQueues = [a \in Actors |-> <<>>]
    /\ commandQueues = [a \in Actors |-> <<>>]
    /\ workerCommandQueues = [w \in Workers|-> <<>>]
    /\ totalHTTPSRequests  = 0
    /\ work = 1
    /\ actorWorkers = [a \in Actors |-> {}]
    /\ idleWorkers = {}
    /\ busyWorkers = {}
    (*/\ revisionNumber = [a \in Actors |-> 1] \* changed from 0 to 1 for proof 
    /\ revisionNumberForWorkers = [w \in Workers |-> 0]
    *)
    /\actorRev = [a \in Actors|-> [rnum|->1, ts|->0]]
    /\ workerRev = [w \in Workers|-> [rnum|->0, ts|->0]]
    /\ clock = 0
  
 
----------------------------------------------------------------------------------    
(*    
**********************
Initialization Actions
**********************
*)

InitializeMinimalWorkers(w,a) ==
(*
Creates Minimum number of workers for each actor when the system bootstraps
*)
    /\ Cardinality(actorWorkers[a]) < MinimumWorkersAlwaysUpPerActor     \* Actor does not have minimum number of workers up
    /\ Cardinality(idleWorkers) + Cardinality(busyWorkers) < MaxWorkers \* Total number of workers created should not exceed Maxworkers
    /\ workerStatus[w].actor = "-"        \* For proof, represent each element of the record instead of record notation workerStatus[w]=[actor|-> "-",status|->"-" ]
    /\ workerStatus[w].status = "-"
    /\ actorStatus[a] = "STARTING_UP"
    /\ workerRev[w].rnum <actorRev[a].rnum \* Adding for proof
    /\ workerRev[w].ts <=actorRev[a].ts
    /\ clock' = clock + 1
    /\ workerStatus'= [workerStatus EXCEPT ![w] = [actor|->a, status|->"IDLE"]]    
    \*/\ PrintT(<<"InitializeMinimalWorkers:", clock', a, actorStatus[a], w, workerStatus'[w].status>>) 
    /\ idleWorkers' = idleWorkers \cup {w}
    /\ actorWorkers'= [actorWorkers EXCEPT ![a] =  actorWorkers[a] \cup {w}]
    \*/\ revisionNumberForWorkers' = [revisionNumberForWorkers EXCEPT ![w] = revisionNumber[a]] \* This could have been revisionNumberForWorkers[w]+1] as it is part of the bootstrap but for consistency and safety property proof, we made it equal to revisionNumber[a]
    /\ workerRev' = [workerRev EXCEPT![w] = [rnum|->actorRev[a].rnum, ts|->clock']] \* checking for proof
    /\ UNCHANGED<<Workers,actorStatus, totalHTTPSRequests, actorMsgQueues, work, busyWorkers, commandQueues, workerCommandQueues ,(*revisionNumber,*)actorRev>>

InitializeActorStatusReady(a) ==
(*
Update Actor status from STARTING_UP to READY when minimum number of actors have been created for the actor
*)
    /\ actorStatus[a] = "STARTING_UP"
    /\ Cardinality(actorWorkers[a])= MinimumWorkersAlwaysUpPerActor
    /\ clock'=clock+1
    /\ actorStatus'= [actorStatus EXCEPT ![a] = "READY"]  \* This could have been merged with previous step. We divided it into two steps for ease of proof
    \*/\ PrintT(<<"InitializeActorStatusReady:", clock', a, actorStatus'[a]>>)
    /\ UNCHANGED<<Workers,totalHTTPSRequests, actorMsgQueues, work, busyWorkers, commandQueues, workerCommandQueues ,(*revisionNumber, revisionNumberForWorkers,*) actorWorkers, idleWorkers, workerStatus,actorRev,workerRev>>



(*
*************************************
HTTP Requests/Synchronous Processing
*************************************
*)

HTTPActorMessageRecv(msg, a) ==    
(*
Represents the API platform receiving an HTTP request to the POST /actors/{id}/messages endpoint;
This endpoint is used to send the actor with id {id} a message. 
*)
    /\  actorStatus[a]= "READY" \/ actorStatus[a]= "UPDATING_IMAGE"
    /\  msg.type = "EXECUTE"
    /\  msg.actor = a
    /\  totalHTTPSRequests < MaxHTTPRequests
    /\  clock' = clock + 1
    \*/\  PrintT(<<"HTTPActorMessageRecv:", clock'>>)
    /\  actorMsgQueues'= [actorMsgQueues EXCEPT ![a] = Append(actorMsgQueues[a],msg)]
    /\  totalHTTPSRequests' = totalHTTPSRequests + 1
    /\  UNCHANGED<<Workers, actorStatus, actorWorkers, work, workerStatus, busyWorkers, idleWorkers, commandQueues, (*revisionNumber, revisionNumberForWorkers,*) workerCommandQueues,actorRev,workerRev>>   



HTTPActorUpdateRecv(msg, a) ==    
(*
Represents the Abaco platform receiving an HTTP request to the PUT /actors/{id} endpoint.
This endpoint is used to update an actor definition.
*)

    /\  actorStatus[a] = "READY"
    /\  msg.type = "UPDATE"
    /\  msg.actor = a
    /\  totalHTTPSRequests < MaxHTTPRequests
    /\  clock' = clock + 1
    \*/\  PrintT(<<"HTTPActorUpdateRecv:", clock'>>)
    /\  actorStatus' = [actorStatus EXCEPT ![a] = "UPDATING_IMAGE"]
    /\  commandQueues'= [commandQueues EXCEPT ![a] = Append(commandQueues[a],msg)]
    /\  totalHTTPSRequests' = totalHTTPSRequests + 1
    \*/\  revisionNumber' = [revisionNumber EXCEPT ![a] =  revisionNumber[a]+ 1]
    /\ actorRev' = [actorRev EXCEPT ![a] =[rnum|->actorRev[a].rnum + 1,ts|->clock']]
    /\  UNCHANGED<<Workers, workerCommandQueues, actorWorkers,
       actorMsgQueues, work, idleWorkers, (*revisionNumberForWorkers,*) workerRev,busyWorkers, workerStatus>> 


CreateWorker(w, a) ==
 (*
 Represents the autoscaler creating a new worker; worker is put into IDLE status.
 *)
    /\ actorStatus[a]= "READY" \/ actorStatus[a]="UPDATING_IMAGE"
    /\ (Len(actorMsgQueues[a]) >= ScaleUpThreshold) \/ (actorStatus[a]="UPDATING_IMAGE"/\ Cardinality(actorWorkers[a]) < MinimumWorkersAlwaysUpPerActor) \* Condition modified for proof
    /\ ~(\E s1 \in actorWorkers[a]: workerStatus[s1].status = "IDLE")
    /\ workerStatus[w].status = "-"
    /\ w \notin actorWorkers[a] \* required for the proof 
    /\ Cardinality(idleWorkers) + Cardinality(busyWorkers) < MaxWorkers \* This condition is required for the proof of Safety property
    /\actorRev[a].ts > workerRev[w].ts \* adding for proof
    /\actorRev[a].rnum > workerRev[w].rnum \* adding for proof
    /\  clock' = clock + 1
    /\ workerStatus'= [workerStatus EXCEPT ![w] = [actor|->a,status|->"IDLE"]]     
    /\ idleWorkers' = idleWorkers \cup {w}
    /\ actorWorkers'= [actorWorkers EXCEPT ![a] =  actorWorkers[a] \cup {w}]
    \*/\ revisionNumberForWorkers' = [revisionNumberForWorkers EXCEPT ![w] = revisionNumber[a]]  
    /\ workerRev' = [workerRev EXCEPT![w] = [rnum|->actorRev[a].rnum, ts|->clock']]
    /\ UNCHANGED<<Workers,actorStatus,totalHTTPSRequests,actorMsgQueues, work, busyWorkers, commandQueues, (*revisionNumber,*) workerCommandQueues,actorRev>>
        

StartDeleteWorker(w,a) ==
(*
Represents internal processing that occurs when the autoscaler determines that a worker should be deleted.
*)
\* change #2 - we enable a worker to be deleted if it is IDLE and does not have the most recent image revision number:
    /\ actorStatus[a] = "UPDATING_IMAGE"
    /\ workerStatus[w].status = "IDLE"
    /\ workerStatus[w].actor = a \* for proof
    \*/\ revisionNumberForWorkers[w] # revisionNumber[a]
    /\ workerRev[w].rnum #actorRev[a].rnum
    /\ w \in actorWorkers[a]
    /\ clock' = clock + 1
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"SHUTDOWN_REQUESTED"]]
    /\ workerCommandQueues' = [workerCommandQueues EXCEPT ![w] = Append(workerCommandQueues[w], [type |->"COMMAND", message |->"SHUTDOWN"])]
    /\ idleWorkers' = idleWorkers \ {w}
    /\ UNCHANGED<<actorMsgQueues,commandQueues,actorStatus,totalHTTPSRequests,
       actorWorkers, Workers, (*revisionNumber, revisionNumberForWorkers,*) busyWorkers,work,actorRev,workerRev>>




(*    
*****************************
Asynchronous Task Processing
*****************************
*)

ProcessUpdateActor(a, w) == 
(*
Represents internal processing of an actor update request. We represent this as an independent action because the processing happens 
asynchronously to the original HTTP request.
The enabling condition is the actorStatus value (UPDATING_IMAGE) which is set when receiving the HTTP request.
*)
    /\ Len(commandQueues[a]) > 0
    /\ Head(commandQueues[a]).type = "UPDATE"
    /\ actorStatus[a] = "UPDATING_IMAGE"
    \*/\ \A w \in actorWorkers[a]: revisionNumberForWorkers[w] = revisionNumber[a] <- TLAPS cannot able to proof, mostly because actorWorkers contains Workers with status IDLE, BUSY, SHUTDOWN_REQUESTED. 
    \* In that case, revisionNumberForWorkers[w] = revisionNumber[a] may not be true for SHUTDOWN_REQUESTED status. However, this step is enabled when all workers in actorWorkers with SHUTDOWN_REQUESTED
    \* status are stopped and released to the pool of workers.
    \* The following condition allows Actor status going from UPDATING_IMAGE to READY if for workers of the actor status's are not "-" or "SHUTDOWN_REQUESTED" that is the status is IDLE or BUSY,
    \* revision number used by worker should be equal to revision number of the actor
    
   \* /\ \A w \in Workers: (workerStatus[w].actor = a /\ workerStatus[w].status \notin {"-","SHUTDOWN_REQUESTED"})=> (revisionNumberForWorkers[w] = revisionNumber[workerStatus[w].actor])   \* an alternative to previous step      
    /\ workerStatus[w].actor = a 
    /\ workerStatus[w].status \notin {"-","SHUTDOWN_REQUESTED"}
    \*/\ revisionNumberForWorkers[w] = revisionNumber[workerStatus[w].actor]
    /\ workerRev[w].rnum =actorRev[workerStatus[w].actor].rnum
    /\ Cardinality(actorWorkers[a]) >= MinimumWorkersAlwaysUpPerActor \* This condition is required so when number of workers always up falls below the threshold MinimumWorkersAlwaysUpPerActor,
    \* CreateWorkers is called before updating the actor's status from UPDATING_IMAGE to READY
    /\  clock' = clock + 1
    /\ actorStatus' = [actorStatus EXCEPT ![a] = "READY"]
    /\ commandQueues' = [commandQueues EXCEPT ![a] = Tail(commandQueues[a])]
    /\ UNCHANGED<<actorMsgQueues,workerCommandQueues,totalHTTPSRequests,
       actorWorkers, Workers, (*revisionNumber, revisionNumberForWorkers,*) workerStatus, busyWorkers,idleWorkers, work,actorRev,workerRev>>


CompleteDeleteWorker(w,a) ==
(*
Represents a worker receiving a message to shutdown and completing the shutdown process.
*)
    /\ Len(workerCommandQueues[w]) > 0
    /\ Head(workerCommandQueues[w]).type = "COMMAND"
    /\ Head(workerCommandQueues[w]).message = "SHUTDOWN"
    /\ workerStatus[w].status = "SHUTDOWN_REQUESTED"
    /\ w \in actorWorkers[a]
    /\ (actorStatus[a]="READY"/\ Cardinality(actorWorkers[a]) > MinimumWorkersAlwaysUpPerActor) \/ actorStatus[a]="UPDATING_IMAGE" \* note the change in condition for the proof
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->"-", status|->"-"]]
    /\ clock' = clock + 1
    \*/\ revisionNumberForWorkers' = [revisionNumberForWorkers EXCEPT ![w] = 0]  \* as we are releasing workers
    /\ workerCommandQueues' = [workerCommandQueues EXCEPT ![w] = Tail(workerCommandQueues[w])]
    /\ actorWorkers'=  [actorWorkers EXCEPT ![a] = actorWorkers[a] \ {w}]
    /\ workerRev' = [workerRev EXCEPT ![w]= [rnum|->0,ts|->0]]
    /\ UNCHANGED<<actorMsgQueues,commandQueues,actorStatus, totalHTTPSRequests, busyWorkers,
     Workers, (*revisionNumber,*) idleWorkers, work,actorRev>>

 
 
 WorkerIdleToBusy(s,a) ==
 (*
 Represents a worker pulling a new message off the actor message queue and moving from IDLE to BUSY.
 *)
    /\  Len(actorMsgQueues[a]) > 0 
    /\  actorStatus[a]= "READY" \/ actorStatus[a]="UPDATING_IMAGE" 
    \*/\  revisionNumberForWorkers[s] = revisionNumber[a]
    /\ workerRev[s].rnum =actorRev[a].rnum
    /\  workerStatus[s].actor = a
    /\  workerStatus[s].status = "IDLE"
    /\  clock' = clock + 1
    /\  actorMsgQueues'= [actorMsgQueues EXCEPT ![a] = Tail(actorMsgQueues[a])]
    /\  workerStatus'= [workerStatus EXCEPT ![s] = [actor|->a,status|->"BUSY"]]
    \*/\  workerStatus'= [workerStatus EXCEPT ![s] = [actor|->a,status|->"STARTING_EXECUTION"]]
    /\  busyWorkers' = busyWorkers \cup {s}
    /\  idleWorkers' = idleWorkers \ {s}
    /\  UNCHANGED<<Workers, actorStatus, actorWorkers, totalHTTPSRequests, work, commandQueues, (*revisionNumber, revisionNumberForWorkers,*) workerCommandQueues,actorRev, workerRev>>
   
   
 WorkerIBusyToIdle(w, a) ==
 (*
 Represents an actor execution completing and he supervising worker moving from BUSY to IDLE.
 *)
    /\  actorStatus[a]= "READY" \/ actorStatus[a]= "UPDATING_IMAGE"
    /\  workerStatus[w].actor = a
    /\  workerStatus[w].status = "BUSY"
    /\  clock' = clock + 1
    /\  work' = (work % MaxHTTPRequests) + 1
    /\  workerStatus'= [workerStatus EXCEPT ![w] = [actor|->a, status|->"IDLE"]]
    /\  idleWorkers' = idleWorkers \cup {w}  
    /\  busyWorkers' = busyWorkers \ {w}
    /\  UNCHANGED<<Workers, actorStatus, actorWorkers, totalHTTPSRequests, actorMsgQueues, commandQueues, (*revisionNumber, revisionNumberForWorkers,*) workerCommandQueues,actorRev,workerRev>>


 WorkerIdleToShutdownReqd(w,a) ==
 (*
 Represents an IDLE worker receiving a message to shutdown and moving from IDLE to SHUTDOWN_REQUESTED.
 *)
    /\  Len(actorMsgQueues[a]) = 0
   \* /\  revisionNumberForWorkers[w] = revisionNumber[a]
    /\  workerRev[w].rnum =actorRev[a].rnum
    /\  workerStatus[w].actor = a
    /\  workerStatus[w].status = "IDLE"
    /\  Cardinality({w1 \in actorWorkers[a]:workerStatus[w1].status="IDLE" }) > MinimumWorkersAlwaysUpPerActor \* note the change in the condition. a worker can be in actorWorkers set but in SHUTDOWN_REQUESTED Status
    /\  actorStatus[a]="READY"
    /\  w \in actorWorkers[a] \* required for proof and also a required condition
    /\  clock' = clock + 1
    /\  workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"SHUTDOWN_REQUESTED"]]
    /\  workerCommandQueues' = [workerCommandQueues EXCEPT ![w] = Append(workerCommandQueues[w], [type |->"COMMAND", message |->"SHUTDOWN"])]
    /\  idleWorkers' = idleWorkers \ {w}
    /\  UNCHANGED<<Workers,actorStatus, totalHTTPSRequests,actorMsgQueues, work,actorWorkers, busyWorkers,commandQueues, (*revisionNumber, revisionNumberForWorkers,*)actorRev,workerRev>>
    
 Next == 
       \/ \E w \in Workers, a \in Actors: InitializeMinimalWorkers(w, a)
       \/ \E a \in Actors: InitializeActorStatusReady(a)
       \/ \E msg \in ActorMessage, a \in Actors: HTTPActorMessageRecv(msg, a)
       \/ \E msg \in CommandMessage, a \in Actors: HTTPActorUpdateRecv(msg, a)
       \/ \E a \in Actors, w \in Workers: ProcessUpdateActor(a,w)
       \/ \E w \in Workers, a \in Actors: CreateWorker(w, a)
       \/ \E w \in Workers, a \in Actors: WorkerIdleToBusy(w, a)
       \/ \E w \in Workers, a \in Actors: WorkerIBusyToIdle(w, a)
       \/ \E w \in Workers, a \in Actors: WorkerIdleToShutdownReqd(w, a)
       \/ \E w \in Workers, a \in Actors: StartDeleteWorker(w,a)
       \/ \E w \in Workers, a \in Actors: CompleteDeleteWorker(w,a)
       

Spec == Init /\ [][Next]_vars  

FairSpec == Spec
        /\ WF_vars(\E w \in Workers, a \in Actors: InitializeMinimalWorkers(w, a))
        /\ WF_vars(\E a \in Actors: InitializeActorStatusReady(a))
        /\ WF_vars(\E a \in Actors, w \in Workers: ProcessUpdateActor(a, w))
        /\ WF_vars(\E w \in Workers, a \in Actors: CreateWorker(w, a))
        /\ WF_vars(\E w \in Workers, a \in Actors: WorkerIdleToBusy(w, a)) 
        /\ WF_vars(\E w \in Workers, a \in Actors: WorkerIBusyToIdle(w, a)) 
        /\ WF_vars(\E w \in Workers, a \in Actors: WorkerIdleToShutdownReqd(w, a)) 
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
               HTTPActorMessageRecv(msg,a)
        PROVE  IInv'
     BY <2>1 DEF HTTPActorMessageRecv 
  <2>2. ASSUME NEW s \in Workers,
               NEW a \in Actors,   
               InitializeMinimalWorkers(s,a)  
        PROVE IInv'   
        <3>1. workerStatus' \in [Workers -> [status:workerState,actor:AllActors]] 
             BY <2>2 DEF InitializeMinimalWorkers
        <3>2. workerCommandQueues' \in [Workers -> Seq(WorkerMessage)] \* multiple queues
             BY <2>2  DEF InitializeMinimalWorkers
        <3>3. idleWorkers' \intersect busyWorkers' = {} 
             BY <2>2  DEF InitializeMinimalWorkers
        <3>4. QED  
            BY <2>2 , <3>1,<3>2,<3>3 DEF InitializeMinimalWorkers
   <2>3. ASSUME NEW s \in Workers,
               NEW a \in Actors,
               CreateWorker(s, a)
        PROVE IInv'
        
        <3>1. clock' \in Nat
         BY <2>3 DEF CreateWorker
        <3>8. QED
     BY <2>3, <3>1 DEF CreateWorker
  <2>4. ASSUME NEW s \in Workers,
               NEW a \in Actors,  
                 WorkerIdleToBusy(s, a)
        PROVE IInv'
     BY <2>4 DEF WorkerIdleToBusy
  <2>5. ASSUME NEW s \in Workers,
               NEW a \in Actors, 
               WorkerIBusyToIdle(s,a)
        PROVE IInv'
        
        <3>1. work' \in 1..MaxHTTPRequests
            BY <2>5 DEF WorkerIBusyToIdle
        <3>2. clock' \in Nat
         BY <2>5 DEF WorkerIBusyToIdle    
        <3>2a. actorStatus' \in [Actors -> ActorState ] 
          BY <2>5 DEF WorkerIBusyToIdle
        <3>3. Workers' \in {1..MaxWorkers}
          BY <2>5 DEF WorkerIBusyToIdle
        <3>20.QED
            BY <2>5,<3>1,<3>2,<3>2a,<3>3 DEF WorkerIBusyToIdle                          

  <2>6. ASSUME NEW s \in Workers,
               NEW a \in Actors,
               WorkerIdleToShutdownReqd(s, a)
        PROVE IInv'
        <3>1. workerCommandQueues' \in [Workers -> Seq(WorkerMessage)] \* multiple queues
             BY <2>6 DEF WorkerIdleToShutdownReqd
        <3>2. clock' \in Nat
         BY <2>6 DEF WorkerIdleToShutdownReqd
      
        <3>4. workerStatus' \in [Workers' -> [status:workerState,actor:AllActors]] 
         BY <2>6 DEF WorkerIdleToShutdownReqd
        
        <3>20. QED  
     BY <2>6, <3>1,<3>2, <3>4  DEF WorkerIdleToShutdownReqd         
  <2>7. ASSUME NEW msg \in CommandMessage,
        NEW a \in Actors,
        HTTPActorUpdateRecv(msg, a) 
        PROVE IInv'
        BY <2>7 DEF HTTPActorUpdateRecv
  <2>8.  ASSUME NEW  a\in Actors, NEW w\in Workers,
         ProcessUpdateActor(a,w)
         PROVE IInv'
     BY <2>8 DEF ProcessUpdateActor    
  <2>9.   ASSUME NEW  a \in Actors,
          NEW w \in Workers,
            StartDeleteWorker(w,a)  
            PROVE IInv'
     
        <3>1. workerCommandQueues' \in [Workers -> Seq(WorkerMessage)] \* multiple queues
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
  <2>13. ASSUME NEW a \in Actors, InitializeActorStatusReady(a)
          PROVE IInv'
          BY <2>13 DEF  InitializeActorStatusReady
  <2>14. QED
    BY <2>1,<2>2,<2>3,<2>4,<2>5,<2>6,<2>7, <2>8,<2>9,<2>10,<2>12, <2>13 DEF Next
    
<1>. QED  BY <1>1, <1>2, PTL DEF Spec
---------------------------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------------------------
(******************************* inductive Invariant - Safety Property proof ******************************************)
THEOREM SafetyPropertyTheorem == Spec => []MinimalWorkerProperty
<1>1. Init => MinimalWorkerProperty
   <2> SUFFICES ASSUME Init
                PROVE  MinimalWorkerProperty
     OBVIOUS
   
   <2>1. IsFiniteSet(idleWorkers)
        <3>1.IsFiniteSet(Workers)
        BY  SpecAssumption, FS_Interval DEF Init
        <3>2. QED  BY <3>1, SpecAssumption, FS_EmptySet, FS_Subset DEF Init
   <2>2. IsFiniteSet(busyWorkers)
        BY  SpecAssumption, FS_EmptySet, FS_Subset DEF Init
     
   <2>4. Cardinality(idleWorkers)+ Cardinality(busyWorkers) <= MaxWorkers
      BY  <2>1,<2>2,SpecAssumption, FS_EmptySet, FS_Subset DEF Init
   <2>5. Cardinality(idleWorkers) \in 0..MaxWorkers
         BY SpecAssumption, <2>1, FS_Interval DEF Init
   <2>6. Cardinality(busyWorkers) \in 0..MaxWorkers
        BY SpecAssumption, <2>2, FS_EmptySet DEF Init
   <2>7. \A s \in Workers:workerStatus[s].status = "IDLE" => s \in idleWorkers
        BY DEF Init
   <2>8. \A s \in Workers:workerStatus[s].status = "BUSY" => s \in busyWorkers
        BY DEF Init
   <2>9. \A a\in Actors: IsFiniteSet(actorWorkers[a]) 
        BY FS_EmptySet, FS_Subset DEF Init
   <2>10. \A a \in Actors: actorStatus[a]="READY"=>(Cardinality(actorWorkers[a]) >= MinimumWorkersAlwaysUpPerActor)
        BY  <2>1,<2>2, SpecAssumption, FS_EmptySet, FS_Subset DEF Init
    
   <2>11. QED
       BY <2>1, <2>2, <2>4,<2>5,<2>6,<2>7,<2>8,<2>9,<2>10 DEF MinimalWorkerProperty
 
<1>2. IInv /\ MinimalWorkerProperty /\ [Next]_vars => MinimalWorkerProperty'
  <2> SUFFICES ASSUME IInv,
                      MinimalWorkerProperty,
                      [Next]_vars
               PROVE  MinimalWorkerProperty'
    BY DEF MinimalWorkerProperty
  <2>.USE SpecAssumption DEF IInv, TypeInvariant, Init, workerState, ActorMessage, ActorState, MinimalWorkerProperty,TotalWorkersRunning, AllActors, CommandMessage, WorkerMessage
  <2>1. ASSUME NEW s \in Workers,
            NEW a \in Actors,
               InitializeMinimalWorkers(s,a)
        PROVE  MinimalWorkerProperty'
        <3>1. IsFiniteSet(Workers')
            BY <2>1, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF InitializeMinimalWorkers 
        <3>2. IsFiniteSet(idleWorkers')
            BY <2>1, <3>1,FS_EmptySet, FS_AddElement, FS_Subset DEF InitializeMinimalWorkers
        <3>3. IsFiniteSet(busyWorkers')
            BY <2>1, FS_EmptySet, FS_Subset DEF InitializeMinimalWorkers
        <3>4. Cardinality(idleWorkers') = Cardinality(idleWorkers) + 1
            BY <2>1,<3>1,<3>2, FS_EmptySet, FS_Subset, FS_AddElement DEF InitializeMinimalWorkers        
        <3>5. Cardinality(idleWorkers') \in 0..MaxWorkers
             BY  <2>1,<3>1,<3>2,<3>4, FS_EmptySet, FS_Interval,FS_AddElement, FS_Subset DEF InitializeMinimalWorkers
        <3>6. Cardinality(busyWorkers') \in 0..MaxWorkers
            BY  <2>1,<3>2,FS_EmptySet,FS_AddElement, FS_Subset DEF InitializeMinimalWorkers
        <3>7. Cardinality(idleWorkers') + Cardinality(busyWorkers') <= MaxWorkers
            BY <2>1, <3>1, <3>2,<3>3,<3>4,<3>5, FS_EmptySet, FS_Subset DEF InitializeMinimalWorkers
        <3>10. \A a1 \in Actors: IsFiniteSet(actorWorkers'[a1]) 
            BY <2>1, FS_EmptySet, FS_Interval,FS_AddElement, FS_Subset DEF InitializeMinimalWorkers     
        <3>11.\A a1 \in Actors: actorStatus'[a1]="READY"=>(Cardinality(actorWorkers'[a1]) >= MinimumWorkersAlwaysUpPerActor)
             BY <2>1 DEF InitializeMinimalWorkers   
        <3>13. QED BY <2>1, <3>1, <3>2,<3>3,<3>4,<3>5, <3>6, <3>7,<3>10,<3>11, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF InitializeMinimalWorkers   
  <2>2. ASSUME NEW msg \in ActorMessage,
               NEW a \in Actors,
               HTTPActorMessageRecv(msg, a)
        PROVE  MinimalWorkerProperty'
        BY <2>2 DEF HTTPActorMessageRecv  
  
  <2>3. ASSUME NEW s \in Workers,
            NEW a \in Actors,
               CreateWorker(s,a)
        PROVE  MinimalWorkerProperty'
         
       <3>1. IsFiniteSet(Workers')
            BY <2>3, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF CreateWorker 
        <3>2. IsFiniteSet(idleWorkers')
            BY <2>3, <3>1, FS_EmptySet, FS_AddElement, FS_Subset DEF CreateWorker
        <3>3. IsFiniteSet(busyWorkers')
            BY <2>3, FS_EmptySet, FS_Subset DEF CreateWorker
        <3>4. Cardinality(idleWorkers') = Cardinality(idleWorkers) + 1
           
            <4>2. idleWorkers' = idleWorkers \cup {s}
             BY <2>3,<3>1,<3>2, FS_EmptySet, FS_Subset, FS_AddElement DEF CreateWorker
            <4>3. s \notin idleWorkers
            BY <2>3, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF CreateWorker
            <4>4. QED 
                 BY <2>1,<3>1,<3>2,<4>2,<4>3, FS_EmptySet, FS_Subset, FS_AddElement DEF CreateWorker        
        <3>5. Cardinality(idleWorkers') \in 0..MaxWorkers
           <4>1. idleWorkers' \in SUBSET Workers'
           BY <2>3 DEF CreateWorker
           <4>2. Cardinality(Workers') = MaxWorkers
           BY <2>3, FS_Interval DEF CreateWorker
           <4>3. Cardinality(idleWorkers') <= MaxWorkers \*Cardinality(workers')
                BY <2>3,<3>1,<3>2,<4>1,<4>2, FS_EmptySet, FS_Subset DEF CreateWorker
           <4>4. QED 
                BY  <2>3,<3>1,<3>2,<3>4,<4>1,<4>2,<4>3,FS_EmptySet, FS_Interval,FS_AddElement, FS_Subset DEF CreateWorker
        
        <3>6. Cardinality(busyWorkers') \in 0..MaxWorkers
            BY  <2>3,<3>2,FS_EmptySet,FS_AddElement, FS_Subset DEF CreateWorker
        <3>7. Cardinality(idleWorkers') + Cardinality(busyWorkers') <= MaxWorkers
            BY <2>3, <3>1, <3>2,<3>3,<3>4,<3>5, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF CreateWorker
        <3>8.  \A s1 \in Workers': workerStatus'[s1].status = "IDLE" => s1 \in idleWorkers'
            BY <2>3 DEF CreateWorker
        <3>9. \A s2 \in Workers':workerStatus'[s2].status = "BUSY" => s2 \in busyWorkers'
                   BY <2>3, <3>1, <3>2,<3>3,<3>4,<3>5, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF CreateWorker
        <3>10. \A a1 \in Actors: IsFiniteSet(actorWorkers'[a1]) 
            BY <2>3, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF CreateWorker    
        <3>11.Cardinality(actorWorkers'[a]) =  Cardinality(actorWorkers[a]) + 1
            <4>1. IsFiniteSet(actorWorkers[a]) 
            BY <2>3, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF CreateWorker 
            <4>2. s \notin actorWorkers[a]
            BY <2>3 DEF CreateWorker 
            <4>3. actorWorkers'[a] = actorWorkers[a] \cup {s}
            BY <2>3 DEF CreateWorker 
            <4>4. IsFiniteSet(actorWorkers'[a])
            BY <2>3,FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF CreateWorker 
            <4>5. QED 
            BY <2>3,<3>10,<4>1,<4>2,<4>3,<4>4,FS_EmptySet, FS_Interval,FS_AddElement, FS_CardinalityType, FS_Subset DEF CreateWorker
            
        <3>12. \A a1 \in Actors: actorStatus'[a1]="READY"=>(Cardinality(actorWorkers'[a1]) >= MinimumWorkersAlwaysUpPerActor)
             BY <2>3, <3>1, <3>11,FS_EmptySet,FS_AddElement, FS_CardinalityType, FS_Subset DEF CreateWorker 
            
        <3>20. QED BY <2>3, <3>1, <3>2,<3>3,<3>4,<3>5, <3>6,<3>7,<3>8,<3>9,<3>10,<3>12, FS_EmptySet, FS_Interval, FS_CardinalityType, FS_AddElement, FS_Subset DEF CreateWorker   
  
  
  <2>4. ASSUME NEW s \in Workers,
                 NEW a \in Actors,
               WorkerIdleToBusy(s,a)
              
        PROVE  MinimalWorkerProperty'
            
        <3>1. IsFiniteSet(idleWorkers')
            BY <2>4, FS_EmptySet, FS_Subset DEF WorkerIdleToBusy
        <3>2. IsFiniteSet(busyWorkers')
            BY <2>4, FS_EmptySet, FS_AddElement, FS_Subset DEF WorkerIdleToBusy
            
        <3>3. Cardinality(busyWorkers') = Cardinality(busyWorkers) + 1
            BY <2>4, FS_EmptySet, FS_AddElement, FS_Subset DEF WorkerIdleToBusy    
        <3>4. Cardinality(idleWorkers') =  Cardinality(idleWorkers) - 1
            BY <2>4, FS_EmptySet, FS_RemoveElement, FS_Subset DEF WorkerIdleToBusy
            
        <3>20. QED BY <2>4, <3>1,<3>2,<3>3,<3>4, FS_EmptySet,FS_AddElement, FS_RemoveElement, FS_Subset DEF WorkerIdleToBusy
       
  <2>5. ASSUME NEW s \in Workers,
                 NEW a \in Actors,
               WorkerIBusyToIdle(s,a)
        PROVE  MinimalWorkerProperty'
        <3>1. IsFiniteSet(idleWorkers')
            BY <2>5, FS_EmptySet, FS_AddElement, FS_Subset DEF WorkerIBusyToIdle
        <3>2. IsFiniteSet(busyWorkers')
            BY <2>5, FS_EmptySet, FS_Subset DEF WorkerIBusyToIdle
        <3>3. Cardinality(busyWorkers') = Cardinality(busyWorkers) - 1
            BY <2>5,FS_EmptySet, FS_RemoveElement, FS_Subset DEF WorkerIBusyToIdle 
        <3>4. Cardinality(idleWorkers') =  Cardinality(idleWorkers) + 1
            BY <2>5, FS_EmptySet, FS_AddElement, FS_Subset DEF WorkerIBusyToIdle
        <3>5. Cardinality(idleWorkers')+ Cardinality(busyWorkers') <= MaxWorkers
            BY <2>5, <3>1, <3>2,<3>3, <3>4 
        <3>6. Cardinality(busyWorkers') \in 0..MaxWorkers
         BY  <2>5, <3>2,<3>3, <3>5,FS_EmptySet,FS_RemoveElement, FS_Interval,FS_Subset DEF WorkerIBusyToIdle    
        <3>7. Cardinality(idleWorkers') \in 0..MaxWorkers 
               BY  <2>5,<3>1, <3>4, <3>5,FS_EmptySet,FS_AddElement, FS_Interval,FS_Subset DEF WorkerIBusyToIdle  
        <3>8. \A s1 \in Workers': workerStatus'[s1].status = "IDLE" => s1 \in idleWorkers'
            BY <2>5 DEF WorkerIBusyToIdle  
        <3>9. \A s2 \in Workers':workerStatus'[s2].status = "BUSY" => s2 \in busyWorkers'
             BY <2>5 DEF WorkerIBusyToIdle
        <3>14. QED BY <2>5, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, FS_EmptySet, FS_AddElement, FS_RemoveElement, FS_Subset DEF WorkerIBusyToIdle
  
  <2>6. ASSUME NEW s \in Workers,
                 NEW a \in Actors,
               WorkerIdleToShutdownReqd(s,a)
        PROVE  MinimalWorkerProperty'
         <3>1. IsFiniteSet(idleWorkers')
            BY <2>6,FS_EmptySet, FS_Subset DEF WorkerIdleToShutdownReqd
        <3>2. IsFiniteSet(busyWorkers')
            BY <2>6 DEF WorkerIdleToShutdownReqd
        <3>3. Cardinality(busyWorkers') = Cardinality(busyWorkers)
            BY <2>6 DEF WorkerIdleToShutdownReqd 
        <3>4. Cardinality(idleWorkers') =  Cardinality(idleWorkers) - 1
            BY <2>6,<3>1, FS_EmptySet, FS_RemoveElement, FS_Subset DEF WorkerIdleToShutdownReqd
        <3>5. Cardinality(idleWorkers')+ Cardinality(busyWorkers') <= MaxWorkers
            BY <2>6, <3>1, <3>2, <3>3, <3>4     
        <3>6. Cardinality(busyWorkers') \in 0..MaxWorkers
         BY  <2>6, <3>2,<3>3, <3>5,FS_EmptySet, FS_Interval,FS_Subset   
        <3>7. Cardinality(idleWorkers') \in 0..MaxWorkers 
               BY  <2>6,<3>1, <3>4, <3>5, FS_EmptySet, FS_Subset, FS_Interval 
        <3>8. \A s1 \in Workers': workerStatus'[s1].status = "IDLE" => s1 \in idleWorkers'
           BY <2>6 DEF WorkerIdleToShutdownReqd
        <3>9. \A s2 \in Workers':workerStatus'[s2].status = "BUSY" => s2 \in busyWorkers'
           BY <2>6 DEF WorkerIdleToShutdownReqd
        <3>10. \A a1 \in Actors: IsFiniteSet(actorWorkers'[a1]) 
            BY <2>6, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF WorkerIdleToShutdownReqd     
        <3>12. \A a1 \in Actors: actorStatus'[a1]="READY"=>(Cardinality(actorWorkers'[a1]) >= MinimumWorkersAlwaysUpPerActor)
             BY <2>6, <3>10, <3>1,FS_EmptySet,FS_RemoveElement, FS_Subset, FS_CardinalityType DEF WorkerIdleToShutdownReqd      \* CardinalityType is Required     
        <3>20. QED BY <2>6, <3>1, <3>2,<3>4,<3>5,<3>6,<3>7,<3>8,<3>9,<3>10,<3>12, FS_EmptySet,FS_Interval,FS_AddElement, FS_RemoveElement, FS_CardinalityType, FS_Subset DEF WorkerIdleToShutdownReqd
  <2>7. ASSUME NEW msg \in CommandMessage,
        NEW a \in Actors,
        HTTPActorUpdateRecv(msg, a) 
        PROVE MinimalWorkerProperty'
        BY <2>7 DEF HTTPActorUpdateRecv
  <2>8. ASSUME NEW a \in Actors,
  NEW w \in Workers,
       ProcessUpdateActor(a,w)
       PROVE MinimalWorkerProperty'
        <3>1. TypeInvariant'
        BY <2>8 DEF ProcessUpdateActor
        <3>2. MinimalWorkerProperty'
         BY <2>8 DEF ProcessUpdateActor
        <3>10. QED
      BY <2>8, <3>1,<3>2 DEF ProcessUpdateActor 
  <2>9.  ASSUME NEW w \in Workers, 
        NEW a \in Actors,
         StartDeleteWorker(w,a) 
         PROVE MinimalWorkerProperty'
        <3>1. IsFiniteSet(idleWorkers')
            BY <2>9,FS_EmptySet, FS_Subset DEF StartDeleteWorker
        <3>2. IsFiniteSet(busyWorkers')
            BY <2>9 DEF StartDeleteWorker
        <3>3. Cardinality(busyWorkers') = Cardinality(busyWorkers)
            BY <2>9 DEF StartDeleteWorker 
        <3>4. Cardinality(idleWorkers') =  Cardinality(idleWorkers) - 1
            BY <2>9,<3>1, FS_EmptySet, FS_RemoveElement, FS_Subset DEF StartDeleteWorker
        <3>5. Cardinality(idleWorkers')+ Cardinality(busyWorkers') <= MaxWorkers
            BY <2>9, <3>1, <3>2, <3>3, <3>4     
        <3>6. Cardinality(busyWorkers') \in 0..MaxWorkers
         BY  <2>9, <3>2,<3>3, <3>5,FS_EmptySet, FS_Interval,FS_Subset   
        <3>7. Cardinality(idleWorkers') \in 0..MaxWorkers 
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
            PROVE MinimalWorkerProperty'
        
    
     <3>1. IsFiniteSet(idleWorkers')
            BY <2>10,FS_EmptySet, FS_Subset DEF CompleteDeleteWorker
        <3>2. IsFiniteSet(busyWorkers')
            BY <2>10 DEF CompleteDeleteWorker
        <3>3. Cardinality(busyWorkers') = Cardinality(busyWorkers)
            BY <2>10 DEF CompleteDeleteWorker
        <3>4. Cardinality(idleWorkers') =  Cardinality(idleWorkers)
            BY <2>10,<3>1, FS_EmptySet, FS_RemoveElement, FS_Subset DEF CompleteDeleteWorker
        <3>5. Cardinality(idleWorkers')+ Cardinality(busyWorkers') <= MaxWorkers
            BY <2>10, <3>1, <3>2, <3>3, <3>4     
        <3>6. Cardinality(busyWorkers') \in 0..MaxWorkers
         BY  <2>10, <3>2,<3>3, <3>5,FS_EmptySet, FS_Interval,FS_Subset   
        <3>7. Cardinality(idleWorkers') \in 0..MaxWorkers 
               BY  <2>10,<3>1, <3>4, <3>5, FS_EmptySet, FS_Subset, FS_Interval 
        <3>8. \A s1 \in Workers': workerStatus'[s1].status = "IDLE" => s1 \in idleWorkers'
            BY <2>10 DEF CompleteDeleteWorker
        <3>9. \A s2 \in Workers':workerStatus'[s2].status = "BUSY" => s2 \in busyWorkers'
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
   <2>16. ASSUME NEW a \in Actors, InitializeActorStatusReady(a)
          PROVE MinimalWorkerProperty'
          BY <2>16 DEF  InitializeActorStatusReady     
  <2>17. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6,<2>7,<2>8,<2>9,<2>10,<2>15, <2>16 DEF Next
 
<1>. QED  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec




(*
   ClockInv ==  /\ \A a \in Actors:actorRev[a].ts<= clock 
             /\ \A w \in Workers: workerRev[w].ts<=clock    
   
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
    <2>. USE SpecAssumption DEF IInv, TypeInvariant, Init, workerState, ActorMessage, ActorState, MinimalWorkerProperty,TotalWorkersRunning, AllActors, CommandMessage, WorkerMessage, ClockInv
    <2>1. ASSUME NEW w \in Workers,
                 NEW a \in Actors,
                 InitializeMinimalWorkers(w, a)
          PROVE  ClockInv'
          BY <2>1 DEF InitializeMinimalWorkers
    <2>2. ASSUME NEW a \in Actors,
                 InitializeActorStatusReady(a)
          PROVE  ClockInv'
          BY <2>2 DEF InitializeActorStatusReady
    <2>3. ASSUME NEW msg \in ActorMessage,
                 NEW a \in Actors,
                 HTTPActorMessageRecv(msg, a)
          PROVE  ClockInv'
          BY <2>3 DEF HTTPActorMessageRecv
    <2>4. ASSUME NEW msg \in CommandMessage,
                 NEW a \in Actors,
                 HTTPActorUpdateRecv(msg, a)
          PROVE  ClockInv'
          BY <2>4 DEF HTTPActorUpdateRecv
    <2>5. ASSUME NEW a \in Actors,
                 NEW w \in Workers,
                 ProcessUpdateActor(a,w)
          PROVE  ClockInv'
          BY <2>5 DEF ProcessUpdateActor
    <2>6. ASSUME NEW w \in Workers,
                 NEW a \in Actors,
                 CreateWorker(w, a)
          PROVE  ClockInv'
          BY <2>6 DEF CreateWorker
    <2>7. ASSUME NEW w \in Workers,
                 NEW a \in Actors,
                 WorkerIdleToBusy(w, a)
          PROVE  ClockInv'
          BY <2>7 DEF WorkerIdleToBusy
    <2>8. ASSUME NEW w \in Workers,
                 NEW a \in Actors,
                 WorkerIBusyToIdle(w, a)
          PROVE  ClockInv'
          BY <2>8 DEF  WorkerIBusyToIdle 
    <2>9. ASSUME NEW w \in Workers,
                 NEW a \in Actors,
                 WorkerIdleToShutdownReqd(w, a)
          PROVE  ClockInv'
          BY <2>9 DEF WorkerIdleToShutdownReqd     
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

\*RevisionNumberInv ==  \A w \in Workers:  workerStatus[w].actor # "-" =>  (workerRev[w].rnum =actorRev[workerStatus[w].actor].rnum =>actorRev[workerStatus[w].actor].ts < workerRev[w].ts)

IInv2 == 
    /\ TypeInvariant 
    /\ MinimalWorkerProperty 
    /\ RevisionNumberInv 
    /\ ClockInv   


THEOREM Spec => []RevisionNumberInv   
<1>1. Init => RevisionNumberInv /\ ClockInv   
     BY  SpecAssumption DEF IInv, TypeInvariant, Init,workerState, ActorState, AllActors, ActorMessage, MinimalWorkerProperty,RevisionNumberInv,ClockInv   
   

<1>2. IInv /\ MinimalWorkerProperty /\ ClockInv
      /\ RevisionNumberInv /\ [Next]_vars 
      => RevisionNumberInv'/\ ClockInv' 
  <2> SUFFICES ASSUME IInv,
                      MinimalWorkerProperty,
                      RevisionNumberInv,
                      [Next]_vars, ClockInv
               PROVE  RevisionNumberInv'/\ ClockInv'
    BY DEF IInv, MinimalWorkerProperty, RevisionNumberInv
  <2>.USE SpecAssumption DEF IInv, TypeInvariant, Init, workerState, ActorMessage, ActorState, MinimalWorkerProperty,TotalWorkersRunning, AllActors, CommandMessage, WorkerMessage,RevisionNumberInv,ClockInv       
  <2>1. ASSUME NEW w \in Workers,
            NEW a \in Actors,
               InitializeMinimalWorkers(w,a)
        PROVE  RevisionNumberInv'/\ ClockInv' 
    <3>1. RevisionNumberInv'
        <4>1. workerStatus'[w].actor # "-" =>((workerRev'[w].rnum < actorRev'[a].rnum) =>(actorRev'[a].ts >= workerRev'[w].ts))
            BY <2>1 DEF InitializeMinimalWorkers
      
       <4>2. QED BY <2>1, <4>1 DEF InitializeMinimalWorkers
      \*BY <2>1 DEF InitializeMinimalWorkers
    <3>2. ClockInv'
      BY <2>1 DEF InitializeMinimalWorkers
    <3>3. QED
      BY <3>1, <3>2
    
  
  <2>2. ASSUME NEW msg \in ActorMessage,
               NEW a \in Actors,
               HTTPActorMessageRecv(msg, a)
        PROVE  RevisionNumberInv' /\ ClockInv'
        BY <2>2 DEF HTTPActorMessageRecv  
  
  <2>3. ASSUME NEW w \in Workers,
            NEW a \in Actors,
               CreateWorker(w,a)
        PROVE  RevisionNumberInv'/\ ClockInv' 
       <3>1. RevisionNumberInv'
        <4>1. workerStatus'[w].actor # "-" =>((workerRev'[w].rnum < actorRev'[a].rnum) =>(actorRev'[a].ts >= workerRev'[w].ts))
            BY <2>3 DEF CreateWorker 
      
        <4>2. QED 
       BY <2>3,<4>1 DEF CreateWorker 
      <3>2. ClockInv'
      BY <2>3 DEF CreateWorker 
      <3>3. QED BY <3>1,<3>2
      \*BY <2>3,<>1 DEF CreateWorker
  
  
  <2>4. ASSUME NEW w \in Workers,
                 NEW a \in Actors,
               WorkerIdleToBusy(w,a)
              
        PROVE  RevisionNumberInv'/\ ClockInv' 
      <3>1. RevisionNumberInv'
       BY <2>4 DEF WorkerIdleToBusy 
      <3>2. ClockInv'
      BY <2>4 DEF WorkerIdleToBusy 
      <3>3. QED BY <3>1,<3>2
         
       
  <2>5. ASSUME NEW s \in Workers,
                 NEW a \in Actors,
               WorkerIBusyToIdle(s,a)
        PROVE  RevisionNumberInv'/\ ClockInv' 
       <3>1. RevisionNumberInv'
       BY <2>5 DEF WorkerIBusyToIdle 
      <3>2. ClockInv'
      BY <2>5 DEF WorkerIBusyToIdle 
      <3>3. QED BY <3>1,<3>2
         
  
  <2>6. ASSUME NEW s \in Workers,
                 NEW a \in Actors,
               WorkerIdleToShutdownReqd(s,a)
        PROVE  RevisionNumberInv'/\ ClockInv' 
       <3>1. RevisionNumberInv'
      BY <2>6 DEF WorkerIdleToShutdownReqd
      <3>2. ClockInv'
      BY <2>6 DEF WorkerIdleToShutdownReqd
      <3>3. QED BY <3>1,<3>2
       
  
  <2>7. ASSUME NEW msg \in CommandMessage,
        NEW a \in Actors,
        HTTPActorUpdateRecv(msg, a) 
        PROVE RevisionNumberInv'/\ ClockInv' 
       <3>1. RevisionNumberInv'
        <4>1. \A w \in Workers: workerStatus'[w].actor = a =>((workerRev'[w].rnum < actorRev'[workerStatus'[w].actor].rnum) =>(actorRev'[workerStatus'[w].actor].ts >= workerRev'[w].ts))
           BY <2>7 DEF HTTPActorUpdateRecv
      
       <4>2. QED 
       BY <2>7, <4>1 DEF HTTPActorUpdateRecv
       <3>2. ClockInv'
       BY <2>7 DEF HTTPActorUpdateRecv
      <3>3. QED BY <3>1,<3>2
  <2>8. ASSUME NEW a \in Actors, 
        NEW w \in Workers, 
       ProcessUpdateActor(a, w)
       PROVE RevisionNumberInv'/\ ClockInv' 
      <3>1. RevisionNumberInv'
      BY <2>8 DEF ProcessUpdateActor
      <3>2. ClockInv'
      BY <2>8 DEF ProcessUpdateActor
      <3>3. QED BY <3>1,<3>2
     
     
  <2>9.  ASSUME NEW w \in Workers, 
        NEW a \in Actors,
         StartDeleteWorker(w,a) 
         PROVE RevisionNumberInv'/\ ClockInv' 
      <3>1. RevisionNumberInv'
      BY <2>9 DEF StartDeleteWorker
      <3>2. ClockInv'
      BY <2>9 DEF StartDeleteWorker
      <3>3. QED BY <3>1,<3>2    
     
     
  <2>10. ASSUME NEW  a \in Actors,
          NEW w \in Workers,
            CompleteDeleteWorker(w,a)  
            PROVE RevisionNumberInv'/\ ClockInv' 
      <3>1. RevisionNumberInv'
      BY <2>10 DEF CompleteDeleteWorker
      <3>2. ClockInv'
      BY <2>10 DEF CompleteDeleteWorker
      <3>3. QED BY <3>1,<3>2         
     
      
  <2>14. ASSUME NEW a \in Actors, InitializeActorStatusReady(a)
          PROVE RevisionNumberInv'/\ ClockInv' 
          BY <2>14 DEF  InitializeActorStatusReady      
  <2>15. CASE UNCHANGED vars
        BY <2>15 DEF vars
  <2>16. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6,<2>7,<2>8,<2>9,<2>10,<2>14,<2>15,ClockInv,FS_EmptySet,FS_Interval,FS_AddElement, FS_RemoveElement, FS_CardinalityType, FS_Subset DEF Next

<1>. QED  BY <1>1, <1>2, TypeCorrect, SafetyPropertyTheorem, PTL DEF Spec


   
          

     
  


=============================================================================
\* Modification History
\* Last modified Sun May 16 14:57:55 CDT 2021 by spadhy
\* Created Tue Apr 27 09:38:58 CDT 2021 by spadhy
