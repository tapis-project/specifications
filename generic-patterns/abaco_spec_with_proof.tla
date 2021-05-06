----------------------- MODULE abaco_spec_with_proof -----------------------

EXTENDS Naturals, FiniteSets, FiniteSetTheorems, Sequences, TLAPS

CONSTANTS \*MaxMessage,        \* Maximum number of HTTP requests that are sent
          ScaleUpThreshold,  \* ScaleUpThreshold 
          MinimumWorkersAlwaysUpPerActor,  \* Minimum number of workers should 
                                           \* always be running per actor
          MaxWorkers,        \* Maximum Number of workers that can be created
          Actors,             \* Actor list
          largestNat
                
          
            
ASSUME SpecAssumption == 
         \*/\ MaxMessage \in (Nat \ {0})
         (* ScaleUpThreshold should be atleast 1 *)
         /\ ScaleUpThreshold \in (Nat \ {0})    
         (* Atleast one worker should always be running *) 
         /\ MinimumWorkersAlwaysUpPerActor \in (Nat \ {0})  
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
          \*tmsg,                 \* total number of messages sent
          \*work,                 \* representation of work
          actorWorkers,         \*
          idleworkers,          \* Set of Idle workers
          busyworkers,          \* Set of Busy workers
          actor_rev,            \* Actor's image revision number and the time of last update
          worker_rev, \* Actor's image revision number used by the worker at the time
                                  \* of worker's creation
          clock
                   
 
 
 vars == <<Workers, actor_msg_queues, command_queues, worker_command_queues, actorStatus,
            workerStatus, (*tmsg, work,*) actorWorkers, idleworkers, busyworkers,
            actor_rev,  worker_rev, clock>>  
 
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
 \* and the message queued in a message queue. In the real implementation,
 \* the messages are not exactly the same, but we make this simplification for the spec.

ActorMessage == [type : {"EXECUTE"}, actor:Actors]

CommandMessage == [type : {"UPDATE"},  actor: Actors]


\* These are messages sent directly from internal Abaco processes 
\* (such as the autoscaler) to the worker.
WorkerMessage == [type: {"COMMAND"}, message: {"SHUTDOWN"}]


------------------------------------------------------------------------------------------------


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
  /\ command_queues \in [Actors -> Seq(CommandMessage)] 
  /\ worker_command_queues \in [Workers -> Seq(WorkerMessage)]
  (*/\ tmsg \in 0..MaxMessage
  /\ \A a \in Actors: tmsg >= Len(actor_msg_queues[a])
  /\ work \in 1..MaxMessage*)
  /\ actorWorkers \in [Actors -> SUBSET Workers]
  /\ idleworkers \in SUBSET Workers
  /\ \A s1 \in idleworkers:workerStatus[s1].status = "IDLE"
  /\ busyworkers \in SUBSET Workers
  /\ \A s2 \in busyworkers:workerStatus[s2].status = "BUSY"
  /\ idleworkers \intersect busyworkers = {} 
  /\ actor_rev \in [Actors -> [rnum:Nat, ts: Nat]]
  /\ worker_rev \in [Workers ->[rnum:Nat, ts: Nat]]
  /\ clock \in Nat
  
  

TotalworkersRunning == idleworkers \cup busyworkers
  



SafetyProperty ==  /\ Cardinality(idleworkers) \in 0..MaxWorkers
                   /\ Cardinality(busyworkers) \in 0..MaxWorkers
                   /\ IsFiniteSet(idleworkers)
                   /\ IsFiniteSet(busyworkers)
                   /\ Cardinality(idleworkers) + Cardinality(busyworkers) <= MaxWorkers
                   /\ \A s \in Workers:workerStatus[s].status = "IDLE" => s \in idleworkers
                   /\ \A s \in Workers:workerStatus[s].status = "BUSY" => s \in busyworkers
                   /\ \A a\in Actors: IsFiniteSet(actorWorkers[a])
                   /\ \A a \in Actors: actorStatus[a]="READY"
                            =>(Cardinality(actorWorkers[a]) >= MinimumWorkersAlwaysUpPerActor)
                   
                   

                   
ClockInv ==  /\ \A a \in Actors: actor_rev[a].ts<= clock 
             /\ \A w \in Workers: worker_rev[w].ts<=clock    

RevisionNumberInv == 
              \A w \in Workers:  workerStatus[w].actor # "-" =>  
              (worker_rev[w].rnum < actor_rev[workerStatus[w].actor].rnum
              => actor_rev[workerStatus[w].actor].ts >= worker_rev[w].ts)


AllMessagesProcessed == <>[](\A a \in Actors: Len(actor_msg_queues[a]) = 0)   

StateConstraint ==
  /\ clock < largestNat
  /\ \A a \in Actors: actor_rev[a].rnum < largestNat
  /\ \A a \in Actors: actor_rev[a].ts <largestNat
  /\ \A w \in Workers: worker_rev[w].rnum < largestNat    
  /\ \A w \in Workers: worker_rev[w].ts < largestNat   
 
(*
****************************
Initialization of Variables
****************************
*)

Init == 
    /\ actorStatus = [a \in Actors |-> "STARTING_UP" ] 
    /\ Workers = 1..MaxWorkers
    /\ workerStatus = [s \in Workers |-> [status|->"-", actor|->"-"]] 
    /\ actor_msg_queues = [a \in Actors |-> <<>>]
    /\ command_queues = [a \in Actors |-> <<>>]
    /\ worker_command_queues = [w \in Workers|-> <<>>]
    \*/\ tmsg  = 0
    \*/\ work = 1
    /\ actorWorkers = [a \in Actors |-> {}]
    /\ idleworkers = {}
    /\ busyworkers = {}
    /\ actor_rev = [a \in Actors|-> [rnum|->1, ts|->0]]
    /\ worker_rev = [w \in Workers|-> [rnum|->0, ts|->0]]
    /\ clock = 0
  
 
-------------------------------------------------------------------------------------------    
(*    
*************************************
HTTP Requests/Synchronous Processing
*************************************
*)

(*  
   Creates Minimum number of workers for each actor when the system bootstraps
*)
  
Startworker(w,a) ==
    /\ Cardinality(actorWorkers[a]) < MinimumWorkersAlwaysUpPerActor     
    /\ Cardinality(idleworkers) + Cardinality(busyworkers) < MaxWorkers 
    /\ workerStatus[w].actor = "-"        
    /\ workerStatus[w].status = "-"
    /\ actorStatus[a] = "STARTING_UP"
    /\ worker_rev[w].rnum < actor_rev[a].rnum 
    /\ worker_rev[w].ts <= actor_rev[a].ts
    /\ clock' = clock + 1
    /\ workerStatus'= [workerStatus EXCEPT ![w] = [actor|->a, status|->"IDLE"]]     
    /\ idleworkers' = idleworkers \cup {w}
    /\ actorWorkers'= [actorWorkers EXCEPT ![a] =  actorWorkers[a] \cup {w}]
    /\ worker_rev' = [worker_rev 
                EXCEPT![w] = [rnum|->actor_rev[a].rnum, ts|->clock']] 
    /\ UNCHANGED<<Workers,actorStatus, (*tmsg,*) actor_msg_queues, (*work,*) busyworkers, 
                command_queues, worker_command_queues, actor_rev>>

(*
    Update Actor status from STARTING_UP to READY when minimum number of actors have been created for the actor
*)

UpdateActorStatus(a) ==
    /\ actorStatus[a] = "STARTING_UP"
    /\ Cardinality(actorWorkers[a])= MinimumWorkersAlwaysUpPerActor
    /\ clock'=clock+1
    /\ actorStatus'= [actorStatus EXCEPT ![a] = "READY"]
    /\ UNCHANGED<<Workers,(*tmsg,*) actor_msg_queues, (*work,*) busyworkers, command_queues,
                 worker_command_queues , actorWorkers, idleworkers, workerStatus,
                 actor_rev,worker_rev>>


APIExecuteRecv(msg, a) ==    
(*
Represents the API platform receiving an HTTP request to the POST /resource/{id} endpoint 
*)
    /\  actorStatus[a]= "READY" \/ actorStatus[a]= "UPDATING_IMAGE"
    /\  msg.type = "EXECUTE"
    /\  msg.actor = a
    \*/\  tmsg < MaxMessage
    /\  clock' = clock + 1
    /\  actor_msg_queues'= [actor_msg_queues EXCEPT ![a]=Append(actor_msg_queues[a],msg)]
    \*/\  tmsg' = tmsg + 1
    /\  UNCHANGED<<Workers, actorStatus, actorWorkers, (*work,*) workerStatus, busyworkers,
         idleworkers, command_queues, worker_command_queues, actor_rev,
         worker_rev>>   



ActorUpdateRecv(msg, a) ==    
(*
Represents the Abaco platform receiving an HTTP request to the PUT /actors/{id} endpoint (i.e., to update an actor definition)
*)

    /\  actorStatus[a] = "READY"
    /\  msg.type = "UPDATE"
    /\  msg.actor = a
    \*/\  tmsg < MaxMessage
    /\  clock' = clock + 1
    /\  actorStatus' = [actorStatus EXCEPT ![a] = "UPDATING_IMAGE"]
    /\  command_queues'= [command_queues EXCEPT ![a] = Append(command_queues[a],msg)]
    \*/\  tmsg' = tmsg + 1
    /\  actor_rev' = [actor_rev 
                EXCEPT ![a] =[rnum|->actor_rev[a].rnum + 1,ts|->clock']]
    /\  UNCHANGED<<Workers, worker_command_queues, actorWorkers,
       actor_msg_queues, (*work,*) idleworkers, worker_rev,busyworkers, workerStatus>> 
 
(*    
*****************************
Asynchronous Task Processing
*****************************
*)

(*
Represents internal processing of an actor update request. We represent this as an independent action 
because the processing happens asynchronously to the original HTTP request.
The enabling condition is the actorStatus value (UPDATING_IMAGE) which is set when receiving the HTTP request.
*)

UpdateActor(a, w) == 
    /\ Len(command_queues[a]) > 0
    /\ Head(command_queues[a]).type = "UPDATE"
    /\ actorStatus[a] = "UPDATING_IMAGE"
    /\ workerStatus[w].actor = a 
    /\ workerStatus[w].status \notin {"-","SHUTDOWN_REQUESTED"}
    /\ worker_rev[w].rnum = actor_rev[workerStatus[w].actor].rnum
    /\ Cardinality(actorWorkers[a]) >= MinimumWorkersAlwaysUpPerActor 
    /\ clock' = clock + 1
    /\ actorStatus' = [actorStatus EXCEPT ![a] = "READY"]
    /\ command_queues' = [command_queues EXCEPT ![a] = Tail(command_queues[a])]
    /\ UNCHANGED<<actor_msg_queues,worker_command_queues,(*tmsg,*)
       actorWorkers, Workers, workerStatus, busyworkers, idleworkers, (*work,*)
       actor_rev, worker_rev>>


(*
Represents internal processing that occurrs when the autoscaler determines that a worker should be deleted.
*)

StartDeleteWorker(w,a) ==
    /\ actorStatus[a] = "UPDATING_IMAGE" 
    /\ workerStatus[w].status = "IDLE"
    /\ workerStatus[w].actor = a 
    /\ w \in actorWorkers[a]
    /\ worker_rev[w].rnum # actor_rev[a].rnum
    /\ clock' = clock + 1
    /\ workerStatus' = [workerStatus EXCEPT ![w]=
        [actor|->a, status|->"SHUTDOWN_REQUESTED"]]
    /\ worker_command_queues' = [worker_command_queues EXCEPT ![w]=
       Append(worker_command_queues[w],[type|->"COMMAND", message|->"SHUTDOWN"])]
    /\ idleworkers' = idleworkers \ {w}
    /\ UNCHANGED<<actor_msg_queues,command_queues,actorStatus,(*tmsg,*) actorWorkers, 
        Workers, busyworkers,(*work,*) actor_rev,worker_rev>>                                                  

(*
Represents a worker receiving a message to shutdown and completing the shutdown process.
*)
CompleteDeleteWorker(w,a) ==
    /\ Len(worker_command_queues[w]) > 0
    /\ Head(worker_command_queues[w]).type = "COMMAND"
    /\ Head(worker_command_queues[w]).message = "SHUTDOWN"
    /\ workerStatus[w].status = "SHUTDOWN_REQUESTED"
    /\ w \in actorWorkers[a]
    /\ \/ (actorStatus[a]="READY"
            /\ Cardinality(actorWorkers[a]) > MinimumWorkersAlwaysUpPerActor) 
       \/ actorStatus[a]="UPDATING_IMAGE" 
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->"-", status|->"-"]]
    /\ clock' = clock + 1
    /\ worker_command_queues' = [worker_command_queues 
                                EXCEPT ![w] = Tail(worker_command_queues[w])]
    /\ actorWorkers'=  [actorWorkers EXCEPT ![a] = actorWorkers[a] \ {w}]
    /\ worker_rev' = [worker_rev EXCEPT ![w]= [rnum|->0,ts|->0]]
    /\ UNCHANGED<<actor_msg_queues,command_queues,actorStatus, (*tmsg,*) busyworkers,
     Workers, idleworkers, (*work,*) actor_rev>>

 
 Createworker(w, a) ==
    /\ actorStatus[a]= "READY" \/ actorStatus[a]="UPDATING_IMAGE"
    /\ \/ (Len(actor_msg_queues[a]) >= ScaleUpThreshold) 
       \/ (actorStatus[a]="UPDATING_IMAGE"
            /\ Cardinality(actorWorkers[a])<MinimumWorkersAlwaysUpPerActor) 
    /\ ~(\E s1 \in actorWorkers[a]: workerStatus[s1].status = "IDLE")
    /\ workerStatus[w].status = "-"
    /\ w \notin actorWorkers[a] \* required for the proof 
    /\ Cardinality(idleworkers) + Cardinality(busyworkers) < MaxWorkers 
    /\ actor_rev[a].rnum > worker_rev[w].rnum 
    /\ clock' = clock + 1
    /\ workerStatus'= [workerStatus EXCEPT ![w] = [actor|->a,status|->"IDLE"]]     
    /\ idleworkers' = idleworkers \cup {w}
    /\ actorWorkers'= [actorWorkers EXCEPT ![a] =  actorWorkers[a] \cup {w}]
    /\ worker_rev' = [worker_rev 
            EXCEPT![w] = [rnum|->actor_rev[a].rnum, ts|->clock']]
    /\ UNCHANGED<<Workers,actorStatus,(*tmsg,*) actor_msg_queues, (*work,*) busyworkers, 
            command_queues,  worker_command_queues, actor_rev>>
        

 WorkerRecv(w,a) == 
    /\  Len(actor_msg_queues[a]) > 0 
    /\  actorStatus[a]= "READY" \/ actorStatus[a]="UPDATING_IMAGE" 
    /\  worker_rev[w].rnum  = actor_rev[a].rnum
    /\  workerStatus[w].actor = a
    /\  workerStatus[w].status = "IDLE"
    /\  clock' = clock + 1
    /\  actor_msg_queues'= [actor_msg_queues EXCEPT ![a] = Tail(actor_msg_queues[a])]
    /\  workerStatus'= [workerStatus EXCEPT ![w] = [actor|->a,status|->"BUSY"]]
    /\  busyworkers' = busyworkers \cup {w}
    /\  idleworkers' = idleworkers \ {w}
    /\  UNCHANGED<<Workers, actorStatus, actorWorkers, (*tmsg, work,*) command_queues, 
            worker_command_queues, actor_rev, worker_rev>>
   
   
 workerBusy(w, a) ==
    /\  actorStatus[a]= "READY" \/ actorStatus[a]= "UPDATING_IMAGE"
    /\  workerStatus[w].actor = a
    /\  workerStatus[w].status = "BUSY"
    /\  clock' = clock + 1
    \*/\  work' = (work % MaxMessage) + 1
    /\  workerStatus'= [workerStatus EXCEPT ![w] = [actor|->a, status|->"IDLE"]]
    /\  idleworkers' = idleworkers \cup {w}  
    /\  busyworkers' = busyworkers \ {w}
    /\  UNCHANGED<<Workers, actorStatus, actorWorkers, (*tmsg,*) actor_msg_queues, command_queues,
         worker_command_queues, actor_rev, worker_rev>>


 Stopworker(w,a) == 
    /\  Len(actor_msg_queues[a]) = 0
    /\  worker_rev[w].rnum  = actor_rev[a].rnum
    /\  workerStatus[w].actor = a
    /\  workerStatus[w].status = "IDLE"
    /\  Cardinality({w1 \in actorWorkers[a]:workerStatus[w1].status="IDLE" }) 
        > MinimumWorkersAlwaysUpPerActor 
    /\  actorStatus[a]="READY"
    /\  w \in actorWorkers[a] 
    /\  clock' = clock + 1
    /\  workerStatus' = [workerStatus EXCEPT ![w] =
        [actor|->a, status|->"SHUTDOWN_REQUESTED"]]
    /\  worker_command_queues' = [worker_command_queues EXCEPT ![w] = 
        Append(worker_command_queues[w], [type |->"COMMAND", message |->"SHUTDOWN"])]
    /\  idleworkers' = idleworkers \ {w}
    /\  UNCHANGED<<Workers,actorStatus, (*tmsg,*) actor_msg_queues, (*work,*) actorWorkers, busyworkers,
        command_queues, actor_rev,worker_rev>>
    
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
        
        (*<3>1. work' \in 1..MaxMessage
            BY <2>5 DEF workerBusy*)
        <3>2. clock' \in Nat
         BY <2>5 DEF workerBusy    
        <3>2a. actorStatus' \in [Actors -> ActorState ] 
          BY <2>5 DEF workerBusy
        <3>3. Workers' \in {1..MaxWorkers}
          BY <2>5 DEF workerBusy
      
        <3>20.QED
            BY <2>5,(*<3>1,*)<3>2,<3>2a,<3>3 DEF workerBusy                          
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
   ClockInv ==  /\ \A a \in Actors: actor_rev[a].ts<= clock 
             /\ \A w \in Workers: worker_rev[w].ts<=clock    
   
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

\*RevisionNumberInv ==  \A w \in Workers:  workerStatus[w].actor # "-" =>  (worker_rev[w].rnum = actor_rev[workerStatus[w].actor].rnum => actor_rev[workerStatus[w].actor].ts < worker_rev[w].ts)

IInv2 == TypeInvariant /\ SafetyProperty /\ RevisionNumberInv/\ClockInv   


THEOREM Spec => []RevisionNumberInv   
<1>1. Init => RevisionNumberInv /\ ClockInv   
     BY  SpecAssumption DEF IInv, TypeInvariant, Init,workerState, ActorState, AllActors, ActorMessage, SafetyProperty,RevisionNumberInv,ClockInv   
   

<1>2. IInv /\ SafetyProperty/\ ClockInv /\ RevisionNumberInv /\ ClockInv/\ [Next]_vars => RevisionNumberInv'/\ ClockInv' 
  <2> SUFFICES ASSUME IInv,
                      SafetyProperty,
                      RevisionNumberInv,
                      [Next]_vars, ClockInv
               PROVE  RevisionNumberInv'/\ ClockInv'
    BY DEF IInv, SafetyProperty, RevisionNumberInv
  <2>.USE SpecAssumption DEF IInv, TypeInvariant, Init, workerState, ActorMessage, ActorState, SafetyProperty,TotalworkersRunning, AllActors, CommandMessage, WorkerMessage,RevisionNumberInv,ClockInv       
  <2>1. ASSUME NEW w \in Workers,
            NEW a \in Actors,
               Startworker(w,a)
        PROVE  RevisionNumberInv'/\ ClockInv' 
    <3>1. RevisionNumberInv'
        <4>1. workerStatus'[w].actor # "-" =>((worker_rev'[w].rnum <  actor_rev'[a].rnum) =>(actor_rev'[a].ts >= worker_rev'[w].ts))
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
        PROVE  RevisionNumberInv' /\ ClockInv'
        BY <2>2 DEF APIExecuteRecv  
  
  <2>3. ASSUME NEW w \in Workers,
            NEW a \in Actors,
               Createworker(w,a)
        PROVE  RevisionNumberInv'/\ ClockInv' 
       <3>1. RevisionNumberInv'
        <4>1. workerStatus'[w].actor # "-" =>((worker_rev'[w].rnum <  actor_rev'[a].rnum) =>(actor_rev'[a].ts >= worker_rev'[w].ts))
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
              
        PROVE  RevisionNumberInv'/\ ClockInv' 
      <3>1. RevisionNumberInv'
       BY <2>4 DEF WorkerRecv 
      <3>2. ClockInv'
      BY <2>4 DEF WorkerRecv 
      <3>3. QED BY <3>1,<3>2
         
       
  <2>5. ASSUME NEW s \in Workers,
                 NEW a \in Actors,
               workerBusy(s,a)
        PROVE  RevisionNumberInv'/\ ClockInv' 
       <3>1. RevisionNumberInv'
       BY <2>5 DEF workerBusy 
      <3>2. ClockInv'
      BY <2>5 DEF workerBusy 
      <3>3. QED BY <3>1,<3>2
         
  
  <2>6. ASSUME NEW s \in Workers,
                 NEW a \in Actors,
               Stopworker(s,a)
        PROVE  RevisionNumberInv'/\ ClockInv' 
       <3>1. RevisionNumberInv'
      BY <2>6 DEF Stopworker
      <3>2. ClockInv'
      BY <2>6 DEF Stopworker
      <3>3. QED BY <3>1,<3>2
       
  
  <2>7. ASSUME NEW msg \in CommandMessage,
        NEW a \in Actors,
        ActorUpdateRecv(msg, a) 
        PROVE RevisionNumberInv'/\ ClockInv' 
       <3>1. RevisionNumberInv'
        <4>1. \A w \in Workers: workerStatus'[w].actor = a =>((worker_rev'[w].rnum <  actor_rev'[workerStatus'[w].actor].rnum) =>(actor_rev'[workerStatus'[w].actor].ts >= worker_rev'[w].ts))
           BY <2>7 DEF ActorUpdateRecv
      
       <4>2. QED 
       BY <2>7, <4>1 DEF ActorUpdateRecv
       <3>2. ClockInv'
       BY <2>7 DEF ActorUpdateRecv
      <3>3. QED BY <3>1,<3>2
  <2>8. ASSUME NEW a \in Actors, 
        NEW w \in Workers, 
       UpdateActor(a, w)
       PROVE RevisionNumberInv'/\ ClockInv' 
      <3>1. RevisionNumberInv'
      BY <2>8 DEF UpdateActor
      <3>2. ClockInv'
      BY <2>8 DEF UpdateActor
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
     
      
  <2>14. ASSUME NEW a \in Actors, UpdateActorStatus(a)
          PROVE RevisionNumberInv'/\ ClockInv' 
          BY <2>14 DEF  UpdateActorStatus      
  <2>15. CASE UNCHANGED vars
        BY <2>15 DEF vars
  <2>16. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6,<2>7,<2>8,<2>9,<2>10,<2>14,<2>15,ClockInv,FS_EmptySet,FS_Interval,FS_AddElement, FS_RemoveElement, FS_CardinalityType, FS_Subset DEF Next
 
<1>. QED  BY <1>1, <1>2, TypeCorrect, SafetyPropertyTheorem, PTL DEF Spec
=============================================================================
\* Modification History
\* Last modified Mon May 03 14:13:24 CDT 2021 by spadhy
\* Created Sat May 01 09:34:58 CDT 2021 by spadhy
