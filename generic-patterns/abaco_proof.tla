---------------------------- MODULE abaco_proof ----------------------------

EXTENDS Naturals, FiniteSets, FiniteSetTheorems, Sequences, TLAPS

CONSTANTS MaxMessage,       \* Maximum number of HTTP requests that are sent
          ScaleUpThreshold,  \* ScaleUpThreshold 
          MinimumWorkersAlwaysUpPerActor,  \* Minimum number of workers should always be running per actor
          MaxWorkers,           \* Maximum Number of workers that can be created
          Actors
         \* ImageVersion        
          
            
ASSUME SpecAssumption == 
         /\ MaxMessage \in (Nat \ {0})
         /\ ScaleUpThreshold \in (Nat \ {0}) (* ScaleUpThreshold should be atleast 1 *)   
         /\ MinimumWorkersAlwaysUpPerActor \in (Nat \ {0})  (* Atleast one worker should always be running *) 
         /\ MaxWorkers \in (Nat \ {0})
         /\ MinimumWorkersAlwaysUpPerActor <= MaxWorkers 
         /\ Actors # {}
         /\ MinimumWorkersAlwaysUpPerActor * Cardinality(Actors) <= MaxWorkers
         \*/\ ImageVersion \in Nat
          
         
 
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
          busyworkers,           \* Set of Busy workers
          \*currentImageVersion,   \* current image version for each actor
          \*currentImageVersionForWorkers, \* Imahe version used by each worker
          revision_number,
          revision_number_for_workers 
                   
 vars == <<Workers, actor_msg_queues, command_queues, worker_command_queues, actorStatus, workerStatus, 
 tmsg, work, actorWorkers, idleworkers, busyworkers,revision_number,
          revision_number_for_workers>>  
 
\* workerState
workerState == {"-","IDLE", "BUSY", "SHUTDOWN_REQUESTED", "FINISHED"}
ActorState == {"STARTING_UP","READY","UPDATING_IMAGE"}

AllActors == Actors \cup {"-"}
\*AllImageVersion == ImageVersion \cup {"-"}

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
\*CommandMessage == [type : {"UPDATE"},  actor: Actors, image: ImageVersion]
CommandMessage == [type : {"UPDATE"},  actor: Actors]
\* These are messages sent directly from internal Abaco processes (such as the autoscaler) to the worker.
WorkerMessage == [type: {"COMMAND"}, message: {"SHUTDOWN"}]

----------------------------------------------------------------------------------------
\*TotalMsg(X) == IF X=0 THEN 0 ELSE  
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
  
  

TotalworkersRunning == idleworkers \cup busyworkers
  

SafetyProperty ==  /\ Cardinality(idleworkers) \in 0..MaxWorkers
                   /\ Cardinality(busyworkers) \in 0..MaxWorkers
                   /\ IsFiniteSet(idleworkers)
                   /\ IsFiniteSet(busyworkers)
                   /\ Cardinality(idleworkers)+ Cardinality(busyworkers) <= MaxWorkers
                   /\ \A s \in Workers:workerStatus[s].status = "IDLE" => s \in idleworkers
                   /\ \A s \in Workers:workerStatus[s].status = "BUSY" => s \in busyworkers
                   /\ \A a\in Actors: IsFiniteSet(actorWorkers[a])
                   /\ \A a \in Actors: actorStatus[a]="READY"=>(Cardinality(actorWorkers[a]) >= MinimumWorkersAlwaysUpPerActor)
                   
                   
                  

 
\* A temporal property: ensures all messages are eventually processed 
\* (i.e., that the length of msq_queue is eventually 0 
\* from some point until the end of the run.)
AllMessagesProcessed == <>[](\A a \in Actors: Len(actor_msg_queues[a]) = 0)   

      
 
(*
****************************
Initialization of Variables
****************************
*)

Init == 
    \*/\ actorStatus = [a \in Actors |-> "READY" ]
    /\ actorStatus = [a \in Actors |-> "STARTING_UP" ] \* Each Actor is starting up 
    /\ Workers = 1..MaxWorkers
    /\ workerStatus = [s \in Workers |-> [status|->"-", actor|->"-"]] \* worker has not yet started
    /\ actor_msg_queues = [a \in Actors |-> <<>>]
    /\ command_queues = [a \in Actors |-> <<>>]
    /\ worker_command_queues = [w \in Workers|-> <<>>]
    /\ tmsg  = 0
    /\ work = 1
    /\ actorWorkers = [a \in Actors |-> {}]
    /\ idleworkers = {}
    /\ busyworkers = {}
    /\ revision_number = [a \in Actors |-> 0]
    /\ revision_number_for_workers = [w \in Workers |-> 0]
 
----------------------------------------------------------------------------------    
(*    
*************************************
HTTP Requests/Synchronous Processing
*************************************
*)
Startworker(w,a) ==
    /\ Cardinality(actorWorkers[a]) < MinimumWorkersAlwaysUpPerActor \* Actor does not have minimum number of workers up
    /\ Cardinality(idleworkers) + Cardinality(busyworkers) < MaxWorkers \* Total number of workers created should not exceed Maxworkers
    \*/\ workerStatus[s] = [actor|-> "-", status|->"-"]
    /\ workerStatus[w].actor = "-"
    /\ workerStatus[w].status = "-"
    /\ actorStatus[a] = "STARTING_UP"
    /\ workerStatus'= [workerStatus EXCEPT ![w] = [actor|->a, status|->"IDLE"]]     
    /\ idleworkers' = idleworkers \cup {w}
    /\ actorWorkers'= [actorWorkers EXCEPT ![a] =  actorWorkers[a] \cup {w}]
    \*/\ revision_number = [revision_number EXCEPT ![a] = 1]
    \*/\ revision_number_for_workers = [revision_number_for_workers EXCEPT ![w] = 1]
    /\ actorStatus'= [actorStatus EXCEPT ![a] = IF Cardinality(actorWorkers'[a])= MinimumWorkersAlwaysUpPerActor THEN "READY" ELSE actorStatus[a]]
    /\ UNCHANGED<<Workers,tmsg, actor_msg_queues, work, busyworkers, command_queues, worker_command_queues, revision_number,revision_number_for_workers>>


APIExecuteRecv(msg, a) ==    
(*
Represents the API platform receiving an HTTP request to the POST /resource/{id} endpoint 
*)
    /\  actorStatus[a]= "READY" \/ actorStatus[a]= "UPDATING_IMAGE"
    /\  msg.type = "EXECUTE"
    /\  msg.actor = a
    /\  tmsg < MaxMessage
    /\  actor_msg_queues'= [actor_msg_queues EXCEPT ![a] = Append(actor_msg_queues[a],msg)]
    /\  tmsg' = tmsg + 1
    /\  UNCHANGED<<Workers, actorStatus, actorWorkers, workerStatus, work, idleworkers, busyworkers,command_queues, revision_number, revision_number_for_workers, worker_command_queues>>   



ActorUpdateRecv(msg, a) ==    
(*
Represents the Abaco platform receiving an HTTP request to the PUT /actors/{id} endpoint (i.e., to update an actor definition)
*)

    /\  actorStatus[a] = "READY"
    /\  msg.type = "UPDATE"
    /\  msg.actor = a
    /\  tmsg < MaxMessage
    /\  actorStatus' = [actorStatus EXCEPT ![a] = "UPDATING_IMAGE"]
    /\  command_queues'= [command_queues EXCEPT ![a] = Append(command_queues[a],msg)]
   \* /\  currentImageVersion' = [currentImageVersion EXCEPT ![a] = msg.image]
   
    /\  tmsg' = tmsg + 1
    /\  revision_number' = [revision_number EXCEPT ![a] =  revision_number[a]+ 1]
    /\  UNCHANGED<<Workers, worker_command_queues, workerStatus, actorWorkers,
       actor_msg_queues, work, idleworkers, busyworkers, revision_number_for_workers>> 
 
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
   \* change #1 -- we no longer require the actor's workers to be empty...
   \*    /\ actorWorkers[a] = {} \* TODO --- what about workerStatus function? workers still active and assigned to actors there.
   \*  /\ \A w \in actorWorkers[a]: currentImageVersionForWorkers[w]=currentImageVersion[a]
    /\ \A w \in actorWorkers[a]: revision_number_for_workers[w] = revision_number[a]
    /\ Cardinality(actorWorkers[a]) >= MinimumWorkersAlwaysUpPerActor
    /\ actorStatus' = [actorStatus EXCEPT ![a] = "READY"]
    /\ command_queues' = [command_queues EXCEPT ![a] = Tail(command_queues[a])]
    /\ UNCHANGED<<actor_msg_queues,worker_command_queues,tmsg,workerStatus,
       actorWorkers, Workers, revision_number, revision_number_for_workers,busyworkers, idleworkers, work>>

StartDeleteWorker(w,a) ==
(*
Represents internal processing that occurrs when the autoscaler determines that a worker should be deleted.
*)
\*    /\ actorStatus[a] = "SHUTTING_DOWN" \/ (actorStatus[a] = "UPDATING_IMAGE" /\ workerStatus[w].status = "IDLE") \*\/ (workerStatus[w].status = "IDLE" /\ Len(actor_msg_queues[a]) = 0)
\* change #2 - we enable a worker to be deleted if it is IDLE and does not have the most recent image:
    \*/\ actorStatus[a] = "SHUTTING_DOWN" \/ ( (workerStatus[w].status = "IDLE" \/ workerStatus[w].status = "FINISHED") /\ currentImageVersionForWorkers[w] # currentImageVersion[a] )
    /\ actorStatus[a] ="UPDATING_IMAGE" 
    /\ workerStatus[w].status = "IDLE"/\ (revision_number_for_workers[w] # revision_number[a]) 
    \*/\ workerStatus[w].status # "-"
   \* /\ workerStatus[w].status # "SHUTDOWN_REQUESTED"
    /\ w \in actorWorkers[a]
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"SHUTDOWN_REQUESTED"]]
    /\ worker_command_queues' = [worker_command_queues EXCEPT ![w] = Append(worker_command_queues[w], [type |->"COMMAND", message |->"SHUTDOWN"])]
    \*/\ actorWorkers'=  [actorWorkers EXCEPT ![a] = actorWorkers[a] \ {w}
    /\ idleworkers'=idleworkers \ {w}
    /\ UNCHANGED<<actor_msg_queues,command_queues,actorStatus,tmsg,  
       actorWorkers, Workers, revision_number, revision_number_for_workers,busyworkers, work>>                                                  
 
 



CompleteDeleteWorker(w,a) ==
(*
Represents a worker receiving a message to shutdown and completing the shutdown process.
*)
    /\ Len(worker_command_queues[w]) > 0
    /\ Head(worker_command_queues[w]).type = "COMMAND"
    /\ Head(worker_command_queues[w]).message = "SHUTDOWN"
    /\ workerStatus[w].status = "SHUTDOWN_REQUESTED"
    /\ w \in actorWorkers[a]
    /\ workerStatus' = [workerStatus EXCEPT ![w]=[actor|->"-", status|->"-"]]
    /\ worker_command_queues' = [worker_command_queues EXCEPT ![w] = Tail(worker_command_queues[w])]
    /\ actorWorkers'=  [actorWorkers EXCEPT ![a] = actorWorkers[a] \ {w}]
    \*/\ actorStatus' = [actorStatus EXCEPT ![a] = IF Cardinality(actorWorkers'[a])>= MinimumWorkersAlwaysUpPerActor THEN actorStatus[a] ELSE "STARTING_UP"]
    /\ UNCHANGED<<actor_msg_queues,command_queues,actorStatus, tmsg, 
     Workers, revision_number, revision_number_for_workers,busyworkers, idleworkers, work>>

 
 Createworker(s, a) ==
    /\ actorStatus[a]= "READY" \/ actorStatus[a]="UPDATING_IMAGE"
    /\ (Len(actor_msg_queues[a]) >= ScaleUpThreshold) \/ (Cardinality(actorWorkers[a]) < MinimumWorkersAlwaysUpPerActor)
    /\ ~(\E s1 \in actorWorkers[a]: workerStatus[s1].status = "IDLE")
    /\ workerStatus[s].status = "-"
    /\ s \notin actorWorkers[a] \* required for the proof 
    /\ Cardinality(idleworkers) + Cardinality(busyworkers) < MaxWorkers \* This condition is required for the proof of Safety property
    /\ workerStatus'= [workerStatus EXCEPT ![s] = [actor|->a,status|->"IDLE"]]     
    /\ idleworkers' = idleworkers \cup {s}
    /\ actorWorkers'= [actorWorkers EXCEPT ![a] =  actorWorkers[a] \cup {s}]
    /\ revision_number_for_workers' = [revision_number_for_workers EXCEPT ![s] = revision_number[a]]  
    /\ UNCHANGED<<Workers,actorStatus,tmsg,actor_msg_queues, work, busyworkers, command_queues, revision_number, worker_command_queues>>
        
 WorkerRecv(s,a) == 
    /\  Len(actor_msg_queues[a]) > 0 
    /\  actorStatus[a]= "READY" \/ actorStatus[a]="UPDATING_IMAGE" 
    /\  revision_number_for_workers[s] = revision_number[a]
   \* /\  workerStatus[s] = [actor|-> a, status|->"IDLE"] \* This format Prover cannot able to prove the theorem
    /\  workerStatus[s].actor = a
    /\  workerStatus[s].status = "IDLE"
    /\  actor_msg_queues'= [actor_msg_queues EXCEPT ![a] = Tail(actor_msg_queues[a])]
    /\  workerStatus'= [workerStatus EXCEPT ![s] = [actor|->a,status|->"BUSY"]]
    /\  busyworkers' = busyworkers \cup {s}
    /\  idleworkers' = idleworkers \ {s}
    /\  UNCHANGED<<Workers, actorStatus, actorWorkers, tmsg, work, command_queues, revision_number, revision_number_for_workers, worker_command_queues>>
    
 
 workerBusy(s, a) ==
    /\  actorStatus[a]= "READY" \/ actorStatus[a]= "UPDATING_IMAGE"
    /\  workerStatus[s].actor = a
    /\  workerStatus[s].status = "BUSY"
    /\  work' = (work % MaxMessage) + 1
    /\  workerStatus'= [workerStatus EXCEPT ![s] = [actor|->a, status|->"IDLE"]]
    /\  idleworkers' = idleworkers \cup {s}  
    /\  busyworkers' = busyworkers \ {s}
    /\  UNCHANGED<<Workers, actorStatus, actorWorkers, tmsg, actor_msg_queues, command_queues, revision_number, revision_number_for_workers, worker_command_queues>>




 Stopworker(w,a) == 
    /\  Len(actor_msg_queues[a]) = 0
    /\  revision_number_for_workers[w] = revision_number[a]
    \*/\  workerStatus[s] = [actor|-> a, status|->"IDLE"]
    /\  workerStatus[w].actor = a
    /\  workerStatus[w].status = "IDLE"
    /\  Cardinality({w1 \in actorWorkers[a]:workerStatus[w1].status="IDLE" }) > MinimumWorkersAlwaysUpPerActor \* note the change in the condition. a worker can be in actorWorkers set but in SHUTDOWN_REQUESTED Status
    /\  actorStatus[a]="READY"
    /\  w \in actorWorkers[a] \* required for proof and also a required condition
    /\  workerStatus' = [workerStatus EXCEPT ![w]=[actor|->a, status|->"SHUTDOWN_REQUESTED"]]
    /\  worker_command_queues' = [worker_command_queues EXCEPT ![w] = Append(worker_command_queues[w], [type |->"COMMAND", message |->"SHUTDOWN"])]
    /\  idleworkers' = idleworkers \ {w}
   \* /\  workerStatus'= [workerStatus EXCEPT ![w] = [actor|-> "-", status|->"-"]]
   \* /\  actorWorkers'= [actorWorkers EXCEPT ![a] =  actorWorkers[a] \ {w}]
    /\  UNCHANGED<<Workers,actorStatus, tmsg,actor_msg_queues, work, busyworkers,actorWorkers, command_queues, revision_number, revision_number_for_workers>>
    
 Next == 
       \/ \E s \in Workers, a \in Actors: Startworker(s, a)
       \/ \E msg \in ActorMessage, a \in Actors: APIExecuteRecv(msg, a)
       \/ \E msg \in CommandMessage, a \in Actors: ActorUpdateRecv(msg, a)
       \/ \E a \in Actors: UpdateActor(a)
       \/ \E w \in Workers, a \in Actors: Createworker(w, a)
       \/ \E w \in Workers, a \in Actors: WorkerRecv(w, a)
       \/ \E w \in Workers, a \in Actors: workerBusy(w, a)
       \/ \E w \in Workers, a \in Actors: Stopworker(w, a)
       \/ \E w \in Workers, a \in Actors: StartDeleteWorker(w,a)
       \/ \E w \in Workers, a \in Actors: CompleteDeleteWorker(w,a)
       

Spec == Init /\ [][Next]_vars  

FairSpec == Spec
        /\ WF_vars(\E w \in Workers, a \in Actors: Startworker(w, a))
        /\ WF_vars(\E w \in Workers, a \in Actors: Createworker(w, a))
        /\ WF_vars(\E w \in Workers, a \in Actors: WorkerRecv(w, a)) 
        /\ WF_vars(\E w \in Workers, a \in Actors: workerBusy(w, a)) 
        /\ WF_vars(\E w \in Workers, a \in Actors: Stopworker(w, a)) 
        /\ WF_vars(\E w \in Workers, a \in Actors: StartDeleteWorker(w,a))
        /\ WF_vars(\E w \in Workers, a \in Actors: CompleteDeleteWorker(w,a))


(* ~~~~~~ For TLC Proof ~~~~~~~ *)
 
MySeq(P) == UNION {[1..n -> P] : n \in 0..MaxMessage}   

(*** Proof ******)
IInv == TypeInvariant
IInv1 == TypeInvariant /\ SafetyProperty


 
THEOREM Spec => []IInv
<1>1. Init => IInv
  BY SpecAssumption DEF Init, IInv, TypeInvariant, workerState, ActorState, AllActors, ActorMessage

<1>2. IInv /\ [Next]_vars => IInv'

<2> SUFFICES ASSUME IInv,
                      [Next]_vars
               PROVE  IInv'
    OBVIOUS
  <2>. USE SpecAssumption DEF Init, IInv, TypeInvariant, workerState, ActorState, AllActors, ActorMessage
  <2>1. ASSUME NEW msg \in ActorMessage,
        NEW a \in Actors,
               APIExecuteRecv(msg,a)
        PROVE  IInv'
     BY <2>1 DEF APIExecuteRecv 
  <2>2. ASSUME NEW s \in Workers,
               NEW a \in Actors,   
               Startworker(s,a)  
        PROVE IInv'       
     BY <2>2 DEF Startworker            
  <2>3. ASSUME NEW s \in Workers,
               NEW a \in Actors,
               Createworker(s, a)
        PROVE IInv'
     BY <2>3 DEF Createworker
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
        <3>2.QED
            BY <2>5,<3>1 DEF workerBusy                          
  <2>6. ASSUME NEW s \in Workers,
               NEW a \in Actors,
               Stopworker(s, a)
        PROVE IInv'
     BY <2>6 DEF Stopworker         
  <2>7. CASE UNCHANGED vars
    BY <2>7 DEF vars
  <2>8. QED
    BY <2>1,<2>2,<2>3,<2>4,<2>5,<2>6,<2>7 DEF Next
    
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

(*THEOREM FS_MutualExclusiveUnion ==
  ASSUME 
  NEW S, IsFiniteSet(S),
  NEW T, IsFiniteSet(T),
  S \intersect T = {}
         
  PROVE  /\ IsFiniteSet(S \cup T)
         /\ Cardinality(S \cup T) =
               Cardinality(S) + Cardinality(T) 
    *)     

THEOREM Inc== 
ASSUME NEW a \in Nat, 
NEW b \in Nat\{0},  a >= b
PROVE /\ (a + 1) \in Nat
      /\ (a + 1) >= b
OBVIOUS

  

THEOREM Spec => []IInv1
<1>1. Init => IInv1
   <2> SUFFICES ASSUME Init
                PROVE  IInv1
     OBVIOUS
   <2>1. TypeInvariant
    BY SpecAssumption DEF IInv1, TypeInvariant, Init,workerState, ActorState, AllActors, ActorMessage
   <2>2. SafetyProperty
     <3>1. IsFiniteSet(idleworkers)
        <4>1.IsFiniteSet(Workers)
        BY  SpecAssumption, FS_Interval DEF Init
        <4>2. QED  BY <4>1, SpecAssumption, FS_EmptySet, FS_Subset DEF Init
     <3>2. IsFiniteSet(busyworkers)
        BY  SpecAssumption, FS_EmptySet, FS_Subset DEF Init
     
     <3>4. Cardinality(idleworkers)+ Cardinality(busyworkers) <= MaxWorkers
      BY  <3>1,<3>2,SpecAssumption, FS_EmptySet, FS_Subset DEF Init
     <3>5. Cardinality(idleworkers) \in 0..MaxWorkers
         BY SpecAssumption, <3>1, FS_Interval DEF Init
     <3>6. Cardinality(busyworkers) \in 0..MaxWorkers
        BY SpecAssumption, <3>2, FS_EmptySet DEF Init
     <3>7. \A s \in Workers:workerStatus[s].status = "IDLE" => s \in idleworkers
        BY DEF Init
     <3>8. \A s \in Workers:workerStatus[s].status = "BUSY" => s \in busyworkers
        BY DEF Init
     <3>9. \A a\in Actors: IsFiniteSet(actorWorkers[a]) 
        BY FS_EmptySet, FS_Subset DEF Init
     <3>10. \A a \in Actors: actorStatus[a]="READY"=>(Cardinality(actorWorkers[a]) >= MinimumWorkersAlwaysUpPerActor)
        BY  <3>1,<3>2, SpecAssumption, FS_EmptySet, FS_Subset DEF Init
    
     <3>11. QED
       BY <3>1, <3>2, <3>4,<3>5,<3>6,<3>7,<3>8,<3>9,<3>10 DEF SafetyProperty
    <2>3. QED
     BY <2>1, <2>2 DEF IInv1
  

<1>2. IInv1 /\ [Next]_vars => IInv1'
  <2> SUFFICES ASSUME TypeInvariant,
                      SafetyProperty,
                      [Next]_vars
               PROVE  IInv1'
    BY DEF IInv1, SafetyProperty
  <2>.USE SpecAssumption DEF IInv1, TypeInvariant, Init, workerState, ActorMessage, ActorState, SafetyProperty,TotalworkersRunning, AllActors  
  <2>1. ASSUME NEW s \in Workers,
            NEW a \in Actors,
               Startworker(s,a)
        PROVE  IInv1'
        <3>1. IsFiniteSet(Workers')
            BY <2>1, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF Startworker 
        <3>2. IsFiniteSet(idleworkers')
            BY <2>1, <3>1,FS_EmptySet, FS_AddElement, FS_Subset DEF Startworker
        <3>3. IsFiniteSet(busyworkers')
            BY <2>1, FS_EmptySet, FS_Subset DEF Startworker
        <3>4. Cardinality(idleworkers') = Cardinality(idleworkers) + 1
            (*<4>1. IsFiniteSet(idleworkers)
                 BY <2>1, FS_EmptySet, FS_AddElement, FS_Subset DEF Startworker*)
            (*<4>2. idleworkers' = idleworkers \cup {s}
             BY <2>1,<3>1,<3>2 DEF Startworker 
            <4>3. s \notin idleworkers
            BY <2>1 DEF Startworker*)
           \* <4>4. QED 
                 BY <2>1,<3>1,<3>2, FS_EmptySet, FS_Subset, FS_AddElement DEF Startworker        
        <3>5. Cardinality(idleworkers') \in 0..MaxWorkers
             BY  <2>1,<3>1,<3>2,<3>4, FS_EmptySet, FS_Interval,FS_AddElement, FS_Subset DEF Startworker
        <3>6. Cardinality(busyworkers') \in 0..MaxWorkers
            BY  <2>1,<3>2,FS_EmptySet,FS_AddElement, FS_Subset DEF Startworker
        <3>7. Cardinality(idleworkers') + Cardinality(busyworkers') <= MaxWorkers
            BY <2>1, <3>1, <3>2,<3>3,<3>4,<3>5, FS_EmptySet, FS_Subset DEF Startworker
        (*<3>8.  \A s1 \in workers': workerStatus'[s1].status = "IDLE" => s1 \in idleworkers'
            BY <2>1 DEF Startworker
        <3>9. \A s2 \in workers':workerStatus'[s2].status = "BUSY" => s2 \in busyworkers'
                   BY <2>1 DEF Startworker
                   *)
        <3>10. \A a1 \in Actors: IsFiniteSet(actorWorkers'[a1]) 
            BY <2>1, FS_EmptySet, FS_Interval,FS_AddElement, FS_Subset DEF Startworker     
        <3>11.\A a1 \in Actors: actorStatus'[a1]="READY"=>(Cardinality(actorWorkers'[a1]) >= MinimumWorkersAlwaysUpPerActor)
             BY <2>1 DEF Startworker     
        <3>12. QED BY <2>1, <3>1, <3>2,<3>3,<3>4,<3>5, <3>6, <3>7,<3>10,<3>11, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF Startworker   
  <2>2. ASSUME NEW msg \in ActorMessage,
               NEW a \in Actors,
               APIExecuteRecv(msg, a)
        PROVE  IInv1'
        BY <2>2 DEF APIExecuteRecv  
  
  <2>3. ASSUME NEW s \in Workers,
            NEW a \in Actors,
               Createworker(s,a)
        PROVE  IInv1'
         
       <3>1. IsFiniteSet(Workers')
            BY <2>3, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF Createworker 
        <3>2. IsFiniteSet(idleworkers')
            BY <2>3, <3>1, FS_EmptySet, FS_AddElement, FS_Subset DEF Createworker
        <3>3. IsFiniteSet(busyworkers')
            BY <2>3, FS_EmptySet, FS_Subset DEF Createworker
        <3>4. Cardinality(idleworkers') = Cardinality(idleworkers) + 1
            (*<4>1. IsFiniteSet(idleworkers)
                 BY <2>3, FS_EmptySet, FS_AddElement, FS_Subset DEF Createworker*)
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
        (*<3>8.  \A s1 \in workers': workerStatus'[s1].status = "IDLE" => s1 \in idleworkers'
            BY <2>3 DEF Createworker*)
        (*<3>9. \A s2 \in workers':workerStatus'[s2].status = "BUSY" => s2 \in busyworkers'
                   BY <2>3, <3>1, <3>2,<3>3,<3>4,<3>5, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF Createworker*)
        (*<3>10. \A a1 \in Actors: IsFiniteSet(actorWorkers'[a1]) 
            BY <2>3, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF Createworker *)   
        <3>11.Cardinality(actorWorkers'[a]) =  Cardinality(actorWorkers[a]) + 1
            <4>1. \A a1 \in Actors: IsFiniteSet(actorWorkers[a1]) 
            BY <2>3, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF Createworker 
            <4>2. QED 
            BY <2>3,<4>1,FS_EmptySet, FS_AddElement, FS_Subset DEF Createworker 
            
        <3>12. \A a1 \in Actors: actorStatus'[a1]="READY"=>(Cardinality(actorWorkers'[a1]) >= MinimumWorkersAlwaysUpPerActor)
             BY <2>3, <3>1, <3>11, FS_EmptySet,FS_AddElement, FS_CardinalityType, FS_Subset DEF Createworker 
            
        <3>13. TypeInvariant' 
             BY <2>3 DEF Createworker       
        <3>20. QED BY <2>3, <3>1, <3>2,<3>3,<3>4,<3>5, <3>6,<3>7,<3>11,<3>12, <3>13,FS_EmptySet, FS_Interval, FS_CardinalityType, FS_AddElement, FS_Subset DEF Createworker   
  
  
  <2>4. ASSUME NEW s \in Workers,
                 NEW a \in Actors,
               WorkerRecv(s,a)
              
        PROVE  IInv1'
            
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
        PROVE  IInv1'
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
        <3>10. workerStatus'
           \in [Workers' ->
                  [status : {"-", "IDLE", "BUSY"}, actor : Actors \cup {"-"}]]
           BY <2>5 DEF workerBusy         
        <3>11. work' \in 1..MaxMessage
            BY <2>5 DEF workerBusy
        <3>12. idleworkers' \in SUBSET Workers'
             BY <2>5 DEF workerBusy  
        <3>13. idleworkers' \cap busyworkers' = {}
            BY <2>5 DEF workerBusy   
        <3>14. QED BY <2>5, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11, <3>12, <3>13, FS_EmptySet, FS_AddElement, FS_RemoveElement, FS_Subset DEF workerBusy
  
  <2>6. ASSUME NEW s \in Workers,
                 NEW a \in Actors,
               Stopworker(s,a)
        PROVE  IInv1'
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
        (*<3>8. \A s1 \in workers': workerStatus'[s1].status = "IDLE" => s1 \in idleworkers'
            BY <2>6 DEF Stopworker  
        <3>9. \A s2 \in workers':workerStatus'[s2].status = "BUSY" => s2 \in busyworkers'
             BY <2>6 DEF Stopworker 
             *)
        <3>10. \A a1 \in Actors: IsFiniteSet(actorWorkers'[a1]) 
            BY <2>6, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF Stopworker    
        <3>11.Cardinality(actorWorkers'[a]) =  Cardinality(actorWorkers[a]) - 1
            <4>1. \A a1 \in Actors: IsFiniteSet(actorWorkers[a1]) 
            BY <2>6, FS_EmptySet, FS_Subset DEF Stopworker 
            <4>2. s \in actorWorkers[a]
            BY <2>6  DEF Stopworker
            <4>3. QED 
            BY <2>6,<4>1,<4>2,FS_EmptySet, FS_RemoveElement, FS_Subset DEF Stopworker 
        <3>12. \A a1 \in Actors: actorStatus'[a1]="READY"=>(Cardinality(actorWorkers'[a1]) >= MinimumWorkersAlwaysUpPerActor)
             BY <2>6, <3>10, <3>1,<3>11,  FS_EmptySet,FS_RemoveElement, FS_Subset, FS_CardinalityType DEF Stopworker      \* CardinalityType is Required     
        <3>13. TypeInvariant' 
             BY <2>6 DEF Stopworker 
        <3>20. QED BY <2>6, <3>1, <3>2,<3>4,<3>5,<3>6,<3>7,<3>10,<3>11,<3>12,<3>13, FS_EmptySet,FS_Interval,FS_AddElement, FS_RemoveElement, FS_CardinalityType, FS_Subset DEF Stopworker
  <2>7. CASE UNCHANGED vars
        BY <2>7 DEF vars
  <2>8. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6,<2>7 DEF Next
 
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

=============================================================================
\* Modification History
\* Last modified Mon Jan 04 17:33:15 CST 2021 by spadhy
\* Created Mon Dec 07 11:36:52 CST 2020 by spadhy

