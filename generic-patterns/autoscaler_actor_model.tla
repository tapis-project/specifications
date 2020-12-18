----------------------- MODULE autoscaler_actor_model -----------------------


EXTENDS Naturals, FiniteSets, FiniteSetTheorems, Sequences, TLAPS

CONSTANTS MaxMessage,       \* Maximum number of HTTP requests that are sent
          ScaleUpThreshold,  \* ScaleUpThreshold 
          MinimumServersAlwaysUpPerActor,  \* Minimum number of servers should always be running per actor
          MaxServers,           \* Maximum Number of Servers that can be created
          Actors
          
            
ASSUME SpecAssumption == 
         /\ MaxMessage \in (Nat \ {0})
         /\ ScaleUpThreshold \in (Nat \ {0}) (* ScaleUpThreshold should be atleast 1 *)   
         /\ MinimumServersAlwaysUpPerActor \in (Nat \ {0})  (* Atleast one server should always be running *) 
         /\ MaxServers \in (Nat \ {0})
         /\ MinimumServersAlwaysUpPerActor <= MaxServers 
         /\ Actors # {}
         /\ MinimumServersAlwaysUpPerActor * Cardinality(Actors) <= MaxServers
          
         
 
---------------------------------------------------------------------------------------          
          
VARIABLES Servers,              \* Total number of servers being created
          actor_msg_queues,     \* Message queue per actor
          actorStatus,          \* actor's status
          serverStatus,         \* server status
          tmsg,                 \* total number of message sent
          work,                 \* representation of work
          actorServers,         \*
          idleServers,          \* Set of Idle servers
          busyServers           \* Set of Busy servers
                   
 vars == <<Servers, actor_msg_queues, actorStatus, serverStatus, tmsg, work, actorServers, idleServers, busyServers>>  
 
\* serverState
ServerState == {"-","IDLE", "BUSY"}
ActorState == {"STARTING_UP","READY"}

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
  /\ Servers \in {1..MaxServers}
  /\ serverStatus \in [Servers -> [status:ServerState,actor:AllActors]] 
  /\ actor_msg_queues \in [Actors->Seq(ActorMessage)]
  /\ tmsg \in 0..MaxMessage
  /\ \A a \in Actors: tmsg >= Len(actor_msg_queues[a])
  /\ work \in 1..MaxMessage
  /\ actorServers \in [Actors -> SUBSET Servers]
  /\ idleServers \in SUBSET Servers
  /\ \A s1 \in idleServers:serverStatus[s1].status = "IDLE"
  /\ busyServers \in SUBSET Servers
  /\ \A s2 \in busyServers:serverStatus[s2].status = "BUSY"
  /\ idleServers \intersect busyServers = {} 
  

TotalServersRunning == idleServers \cup busyServers
  

SafetyProperty ==  /\ Cardinality(idleServers) \in 0..MaxServers
                   /\ Cardinality(busyServers) \in 0..MaxServers
                   /\ IsFiniteSet(idleServers)
                   /\ IsFiniteSet(busyServers)
                   /\ Cardinality(idleServers)+ Cardinality(busyServers) <= MaxServers
                   /\ \A s \in Servers:serverStatus[s].status = "IDLE" => s \in idleServers
                   /\ \A s \in Servers:serverStatus[s].status = "BUSY" => s \in busyServers
                   /\ \A a\in Actors: IsFiniteSet(actorServers[a])
                   /\ \A a \in Actors: actorStatus[a]="READY"=>(Cardinality(actorServers[a]) >= MinimumServersAlwaysUpPerActor)
                   
                   
                  

 
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
    /\ Servers = 1..MaxServers
    /\ serverStatus = [s \in Servers |-> [status|->"-", actor|->"-"]] \* Server has not yet started
    /\ actor_msg_queues = [a \in Actors |-> <<>>]
    /\ tmsg  = 0
    /\ work = 1
    /\ actorServers = [a \in Actors |-> {}]
    /\ idleServers = {}
    /\ busyServers = {}
 
----------------------------------------------------------------------------------    
(*    
*************************************
HTTP Requests/Synchronous Processing
*************************************
*)
StartServer(s,a) ==
    /\ Cardinality(actorServers[a]) < MinimumServersAlwaysUpPerActor \* Actor does not have minimum number of servers up
    /\ Cardinality(idleServers) + Cardinality(busyServers) < MaxServers \* Total number of servers created should not exceed MaxServers
    \*/\ serverStatus[s] = [actor|-> "-", status|->"-"]
    /\ serverStatus[s].actor = "-"
    /\ serverStatus[s].status = "-"
    /\ actorStatus[a] = "STARTING_UP"
    /\ serverStatus'= [serverStatus EXCEPT ![s] = [actor|->a, status|->"IDLE"]]     
    /\ idleServers' = idleServers \cup {s}
    /\ actorServers'= [actorServers EXCEPT ![a] =  actorServers[a] \cup {s}]
    /\ actorStatus'= [actorStatus EXCEPT ![a] = IF Cardinality(actorServers'[a])= MinimumServersAlwaysUpPerActor THEN "READY" ELSE actorStatus[a]]
    /\ UNCHANGED<<Servers,tmsg,actor_msg_queues, work, busyServers>>


APIExecuteRecv(msg, a) ==    
(*
Represents the API platform receiving an HTTP request to the POST /resource/{id} endpoint 
*)
    /\  actorStatus[a]= "READY"
    /\  msg.type = "EXECUTE"
    /\  msg.actor = a
    /\  tmsg < MaxMessage
    /\  actor_msg_queues'= [actor_msg_queues EXCEPT ![a] = Append(actor_msg_queues[a],msg)]
    /\  tmsg' = tmsg + 1
    /\  UNCHANGED<<Servers, actorStatus, actorServers, serverStatus, work, idleServers, busyServers>>   

 
(*    
*****************************
Asynchronous Task Processing
*****************************
*)
 
 CreateServer(s, a) ==
    /\ actorStatus[a]= "READY"
    /\ Len(actor_msg_queues[a]) >= ScaleUpThreshold
    /\ ~(\E s1 \in actorServers[a]: serverStatus[s1].status = "IDLE")
    /\ serverStatus[s].status = "-"
    /\ s \notin actorServers[a] \* required for the proof 
    /\ Cardinality(idleServers) + Cardinality(busyServers) < MaxServers \* This condition is required for the proof of Safety property
    /\ serverStatus'= [serverStatus EXCEPT ![s] = [actor|->a,status|->"IDLE"]]     
    /\ idleServers' = idleServers \cup {s}
    /\ actorServers'= [actorServers EXCEPT ![a] =  actorServers[a] \cup {s}]
    /\ UNCHANGED<<Servers,actorStatus,tmsg,actor_msg_queues, work, busyServers>>
        
 ServerRecv(s,a) == 
    /\  Len(actor_msg_queues[a]) > 0 
    /\  actorStatus[a]= "READY" 
   \* /\  serverStatus[s] = [actor|-> a, status|->"IDLE"] \* This format Prover cannot able to prove the theorem
    /\  serverStatus[s].actor = a
    /\  serverStatus[s].status = "IDLE"
    /\  actor_msg_queues'= [actor_msg_queues EXCEPT ![a] = Tail(actor_msg_queues[a])]
    /\  serverStatus'= [serverStatus EXCEPT ![s] = [actor|->a,status|->"BUSY"]]
    /\  busyServers' = busyServers \cup {s}
    /\  idleServers' = idleServers \ {s}
    /\  UNCHANGED<<Servers, actorStatus, actorServers, tmsg, work>>
    
 
 ServerBusy(s, a) ==
    /\  actorStatus[a] = "READY"
    /\  serverStatus[s].actor = a
    /\  serverStatus[s].status = "BUSY"
    /\  work' = (work % MaxMessage) + 1
    /\  serverStatus'= [serverStatus EXCEPT ![s] = [actor|->a, status|->"IDLE"]]
    /\  idleServers' = idleServers \cup {s}  
    /\  busyServers' = busyServers \ {s}
    /\  UNCHANGED<<Servers, actorStatus, actorServers, tmsg, actor_msg_queues>>




 StopServer(s,a) == 
    /\  Len(actor_msg_queues[a]) = 0
    \*/\  serverStatus[s] = [actor|-> a, status|->"IDLE"]
    /\  serverStatus[s].actor = a
    /\  serverStatus[s].status = "IDLE"
    /\  Cardinality(actorServers[a]) > MinimumServersAlwaysUpPerActor
    /\  actorStatus[a]="READY"
    /\  s \in actorServers[a] \* required for proof and also a required condition
    /\  idleServers' = idleServers \ {s}
    /\  serverStatus'= [serverStatus EXCEPT ![s] = [actor|-> "-", status|->"-"]]
    /\  actorServers'= [actorServers EXCEPT ![a] =  actorServers[a] \ {s}]
    /\  UNCHANGED<<Servers,actorStatus, tmsg,actor_msg_queues, work, busyServers>>
    
 Next == 
       \/ \E s \in Servers, a \in Actors: StartServer(s, a)
       \/ \E msg \in ActorMessage, a \in Actors: APIExecuteRecv(msg, a)
       \/ \E s \in Servers, a \in Actors: CreateServer(s, a)
       \/ \E s \in Servers, a \in Actors: ServerRecv(s, a)
       \/ \E s \in Servers, a \in Actors: ServerBusy(s, a)
       \/ \E s \in Servers, a \in Actors: StopServer(s, a)

Spec == Init /\ [][Next]_vars  

FairSpec == Spec
        /\ WF_vars(\E s \in Servers, a \in Actors: StartServer(s, a))
        /\ WF_vars(\E s \in Servers, a \in Actors: CreateServer(s, a))
        /\ WF_vars(\E s \in Servers, a \in Actors: ServerRecv(s, a)) 
        /\ WF_vars(\E s \in Servers, a \in Actors: ServerBusy(s, a)) 
        /\ WF_vars(\E s \in Servers, a \in Actors: StopServer(s, a)) 


(* ~~~~~~ For TLC Proof ~~~~~~~ *)
 
 MySeq(P) == UNION {[1..n -> P] : n \in 0..MaxMessage}   

(*** Proof ******)
IInv == TypeInvariant
IInv1 == TypeInvariant /\ SafetyProperty


 
THEOREM Spec => []IInv
<1>1. Init => IInv
  BY SpecAssumption DEF Init, IInv, TypeInvariant, ServerState, ActorState, AllActors, ActorMessage

<1>2. IInv /\ [Next]_vars => IInv'

<2> SUFFICES ASSUME IInv,
                      [Next]_vars
               PROVE  IInv'
    OBVIOUS
  <2>. USE SpecAssumption DEF Init, IInv, TypeInvariant, ServerState, ActorState, AllActors, ActorMessage
  <2>1. ASSUME NEW msg \in ActorMessage,
        NEW a \in Actors,
               APIExecuteRecv(msg,a)
        PROVE  IInv'
     BY <2>1 DEF APIExecuteRecv 
  <2>2. ASSUME NEW s \in Servers,
               NEW a \in Actors,   
               StartServer(s,a)  
        PROVE IInv'       
     BY <2>2 DEF StartServer            
  <2>3. ASSUME NEW s \in Servers,
               NEW a \in Actors,
               CreateServer(s, a)
        PROVE IInv'
     BY <2>3 DEF CreateServer
  <2>4. ASSUME NEW s \in Servers,
               NEW a \in Actors,  
                 ServerRecv(s, a)
        PROVE IInv'
     BY <2>4 DEF ServerRecv
  <2>5. ASSUME NEW s \in Servers,
               NEW a \in Actors, 
               ServerBusy(s,a)
        PROVE IInv'
        
        <3>1. work' \in 1..MaxMessage
            BY <2>5 DEF ServerBusy
        <3>2.QED
            BY <2>5,<3>1 DEF ServerBusy                          
  <2>6. ASSUME NEW s \in Servers,
               NEW a \in Actors,
               StopServer(s, a)
        PROVE IInv'
     BY <2>6 DEF StopServer         
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
    BY SpecAssumption DEF IInv1, TypeInvariant, Init,ServerState, ActorState, AllActors, ActorMessage
   <2>2. SafetyProperty
     <3>1. IsFiniteSet(idleServers)
        <4>1.IsFiniteSet(Servers)
        BY  SpecAssumption, FS_Interval DEF Init
        <4>2. QED  BY <4>1, SpecAssumption, FS_EmptySet, FS_Subset DEF Init
     <3>2. IsFiniteSet(busyServers)
        BY  SpecAssumption, FS_EmptySet, FS_Subset DEF Init
     
     <3>4. Cardinality(idleServers)+ Cardinality(busyServers) <= MaxServers
      BY  <3>1,<3>2,SpecAssumption, FS_EmptySet, FS_Subset DEF Init
     <3>5. Cardinality(idleServers) \in 0..MaxServers
         BY SpecAssumption, <3>1, FS_Interval DEF Init
     <3>6. Cardinality(busyServers) \in 0..MaxServers
        BY SpecAssumption, <3>2, FS_EmptySet DEF Init
     <3>7. \A s \in Servers:serverStatus[s].status = "IDLE" => s \in idleServers
        BY DEF Init
     <3>8. \A s \in Servers:serverStatus[s].status = "BUSY" => s \in busyServers
        BY DEF Init
     <3>9. \A a\in Actors: IsFiniteSet(actorServers[a]) 
        BY FS_EmptySet, FS_Subset DEF Init
     <3>10. \A a \in Actors: actorStatus[a]="READY"=>(Cardinality(actorServers[a]) >= MinimumServersAlwaysUpPerActor)
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
  <2>.USE SpecAssumption DEF IInv1, TypeInvariant, Init, ServerState, ActorMessage, ActorState, SafetyProperty,TotalServersRunning, AllActors  
  <2>1. ASSUME NEW s \in Servers,
            NEW a \in Actors,
               StartServer(s,a)
        PROVE  IInv1'
        <3>1. IsFiniteSet(Servers')
            BY <2>1, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF StartServer 
        <3>2. IsFiniteSet(idleServers')
            BY <2>1, <3>1,FS_EmptySet, FS_AddElement, FS_Subset DEF StartServer
        <3>3. IsFiniteSet(busyServers')
            BY <2>1, FS_EmptySet, FS_Subset DEF StartServer
        <3>4. Cardinality(idleServers') = Cardinality(idleServers) + 1
            (*<4>1. IsFiniteSet(idleServers)
                 BY <2>1, FS_EmptySet, FS_AddElement, FS_Subset DEF StartServer*)
            (*<4>2. idleServers' = idleServers \cup {s}
             BY <2>1,<3>1,<3>2 DEF StartServer 
            <4>3. s \notin idleServers
            BY <2>1 DEF StartServer*)
           \* <4>4. QED 
                 BY <2>1,<3>1,<3>2, FS_EmptySet, FS_Subset, FS_AddElement DEF StartServer        
        <3>5. Cardinality(idleServers') \in 0..MaxServers
             BY  <2>1,<3>1,<3>2,<3>4, FS_EmptySet, FS_Interval,FS_AddElement, FS_Subset DEF StartServer
        <3>6. Cardinality(busyServers') \in 0..MaxServers
            BY  <2>1,<3>2,FS_EmptySet,FS_AddElement, FS_Subset DEF StartServer
        <3>7. Cardinality(idleServers') + Cardinality(busyServers') <= MaxServers
            BY <2>1, <3>1, <3>2,<3>3,<3>4,<3>5, FS_EmptySet, FS_Subset DEF StartServer
        (*<3>8.  \A s1 \in Servers': serverStatus'[s1].status = "IDLE" => s1 \in idleServers'
            BY <2>1 DEF StartServer
        <3>9. \A s2 \in Servers':serverStatus'[s2].status = "BUSY" => s2 \in busyServers'
                   BY <2>1 DEF StartServer
                   *)
        <3>10. \A a1 \in Actors: IsFiniteSet(actorServers'[a1]) 
            BY <2>1, FS_EmptySet, FS_Interval,FS_AddElement, FS_Subset DEF StartServer     
        <3>11.\A a1 \in Actors: actorStatus'[a1]="READY"=>(Cardinality(actorServers'[a1]) >= MinimumServersAlwaysUpPerActor)
             BY <2>1 DEF StartServer     
        <3>12. QED BY <2>1, <3>1, <3>2,<3>3,<3>4,<3>5, <3>6, <3>7,<3>10,<3>11, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF StartServer   
  <2>2. ASSUME NEW msg \in ActorMessage,
               NEW a \in Actors,
               APIExecuteRecv(msg, a)
        PROVE  IInv1'
        BY <2>2 DEF APIExecuteRecv  
  
  <2>3. ASSUME NEW s \in Servers,
            NEW a \in Actors,
               CreateServer(s,a)
        PROVE  IInv1'
         
       <3>1. IsFiniteSet(Servers')
            BY <2>3, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF CreateServer 
        <3>2. IsFiniteSet(idleServers')
            BY <2>3, <3>1, FS_EmptySet, FS_AddElement, FS_Subset DEF CreateServer
        <3>3. IsFiniteSet(busyServers')
            BY <2>3, FS_EmptySet, FS_Subset DEF CreateServer
        <3>4. Cardinality(idleServers') = Cardinality(idleServers) + 1
            (*<4>1. IsFiniteSet(idleServers)
                 BY <2>3, FS_EmptySet, FS_AddElement, FS_Subset DEF CreateServer*)
            <4>2. idleServers' = idleServers \cup {s}
             BY <2>3,<3>1,<3>2, FS_EmptySet, FS_Subset, FS_AddElement DEF CreateServer
            <4>3. s \notin idleServers
            BY <2>3, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF CreateServer
            <4>4. QED 
                 BY <2>1,<3>1,<3>2,<4>2,<4>3, FS_EmptySet, FS_Subset, FS_AddElement DEF CreateServer        
        <3>5. Cardinality(idleServers') \in 0..MaxServers
           <4>1. idleServers' \in SUBSET Servers'
           BY <2>3 DEF CreateServer
           <4>2. Cardinality(Servers') = MaxServers
           BY <2>3, FS_Interval DEF CreateServer
           <4>3. Cardinality(idleServers') <= MaxServers \*Cardinality(Servers')
                BY <2>3,<3>1,<3>2,<4>1,<4>2, FS_EmptySet, FS_Subset DEF CreateServer
           <4>4. QED 
                BY  <2>3,<3>1,<3>2,<3>4,<4>1,<4>2,<4>3,FS_EmptySet, FS_Interval,FS_AddElement, FS_Subset DEF CreateServer
        
        <3>6. Cardinality(busyServers') \in 0..MaxServers
            BY  <2>3,<3>2,FS_EmptySet,FS_AddElement, FS_Subset DEF CreateServer
        <3>7. Cardinality(idleServers') + Cardinality(busyServers') <= MaxServers
            BY <2>3, <3>1, <3>2,<3>3,<3>4,<3>5, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF CreateServer
        (*<3>8.  \A s1 \in Servers': serverStatus'[s1].status = "IDLE" => s1 \in idleServers'
            BY <2>3 DEF CreateServer*)
        (*<3>9. \A s2 \in Servers':serverStatus'[s2].status = "BUSY" => s2 \in busyServers'
                   BY <2>3, <3>1, <3>2,<3>3,<3>4,<3>5, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF CreateServer*)
        (*<3>10. \A a1 \in Actors: IsFiniteSet(actorServers'[a1]) 
            BY <2>3, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF CreateServer *)   
        <3>11.Cardinality(actorServers'[a]) =  Cardinality(actorServers[a]) + 1
            <4>1. \A a1 \in Actors: IsFiniteSet(actorServers[a1]) 
            BY <2>3, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF CreateServer 
            <4>2. QED 
            BY <2>3,<4>1,FS_EmptySet, FS_AddElement, FS_Subset DEF CreateServer 
            
        <3>12. \A a1 \in Actors: actorStatus'[a1]="READY"=>(Cardinality(actorServers'[a1]) >= MinimumServersAlwaysUpPerActor)
             BY <2>3, <3>1, <3>11, FS_EmptySet,FS_AddElement, FS_CardinalityType, FS_Subset DEF CreateServer 
            
        <3>13. TypeInvariant' 
             BY <2>3 DEF CreateServer       
        <3>20. QED BY <2>3, <3>1, <3>2,<3>3,<3>4,<3>5, <3>6,<3>7,<3>11,<3>12, <3>13,FS_EmptySet, FS_Interval, FS_CardinalityType, FS_AddElement, FS_Subset DEF CreateServer   
  
  
  <2>4. ASSUME NEW s \in Servers,
                 NEW a \in Actors,
               ServerRecv(s,a)
              
        PROVE  IInv1'
            
        <3>1. IsFiniteSet(idleServers')
            BY <2>4, FS_EmptySet, FS_Subset DEF ServerRecv
        <3>2. IsFiniteSet(busyServers')
            BY <2>4, FS_EmptySet, FS_AddElement, FS_Subset DEF ServerRecv
            
        <3>3. Cardinality(busyServers') = Cardinality(busyServers) + 1
            BY <2>4, FS_EmptySet, FS_AddElement, FS_Subset DEF ServerRecv    
        <3>4. Cardinality(idleServers') =  Cardinality(idleServers) - 1
            BY <2>4, FS_EmptySet, FS_RemoveElement, FS_Subset DEF ServerRecv
            
        <3>20. QED BY <2>4, <3>1,<3>2,<3>3,<3>4, FS_EmptySet,FS_AddElement, FS_RemoveElement, FS_Subset DEF ServerRecv
       
  <2>5. ASSUME NEW s \in Servers,
                 NEW a \in Actors,
               ServerBusy(s,a)
        PROVE  IInv1'
        <3>1. IsFiniteSet(idleServers')
            BY <2>5, FS_EmptySet, FS_AddElement, FS_Subset DEF ServerBusy
        <3>2. IsFiniteSet(busyServers')
            BY <2>5, FS_EmptySet, FS_Subset DEF ServerBusy
        <3>3. Cardinality(busyServers') = Cardinality(busyServers) - 1
            BY <2>5,FS_EmptySet, FS_RemoveElement, FS_Subset DEF ServerBusy 
        <3>4. Cardinality(idleServers') =  Cardinality(idleServers) + 1
            BY <2>5, FS_EmptySet, FS_AddElement, FS_Subset DEF ServerBusy
        <3>5. Cardinality(idleServers')+ Cardinality(busyServers') <= MaxServers
            BY <2>5, <3>1, <3>2,<3>3, <3>4 
        <3>6. Cardinality(busyServers') \in 0..MaxServers
         BY  <2>5, <3>2,<3>3, <3>5,FS_EmptySet,FS_RemoveElement, FS_Interval,FS_Subset DEF ServerBusy    
        <3>7. Cardinality(idleServers') \in 0..MaxServers 
               BY  <2>5,<3>1, <3>4, <3>5,FS_EmptySet,FS_AddElement, FS_Interval,FS_Subset DEF ServerBusy  
        <3>8. \A s1 \in Servers': serverStatus'[s1].status = "IDLE" => s1 \in idleServers'
            BY <2>5 DEF ServerBusy  
        <3>9. \A s2 \in Servers':serverStatus'[s2].status = "BUSY" => s2 \in busyServers'
             BY <2>5 DEF ServerBusy
        <3>10. serverStatus'
           \in [Servers' ->
                  [status : {"-", "IDLE", "BUSY"}, actor : Actors \cup {"-"}]]
           BY <2>5 DEF ServerBusy         
        <3>11. work' \in 1..MaxMessage
            BY <2>5 DEF ServerBusy
        <3>12. idleServers' \in SUBSET Servers'
             BY <2>5 DEF ServerBusy  
        <3>13. idleServers' \cap busyServers' = {}
            BY <2>5 DEF ServerBusy   
        <3>14. QED BY <2>5, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11, <3>12, <3>13, FS_EmptySet, FS_AddElement, FS_RemoveElement, FS_Subset DEF ServerBusy
  
  <2>6. ASSUME NEW s \in Servers,
                 NEW a \in Actors,
               StopServer(s,a)
        PROVE  IInv1'
         <3>1. IsFiniteSet(idleServers')
            BY <2>6,FS_EmptySet, FS_Subset DEF StopServer
        <3>2. IsFiniteSet(busyServers')
            BY <2>6 DEF StopServer
        <3>3. Cardinality(busyServers') = Cardinality(busyServers)
            BY <2>6 DEF StopServer 
        <3>4. Cardinality(idleServers') =  Cardinality(idleServers) - 1
            BY <2>6,<3>1, FS_EmptySet, FS_RemoveElement, FS_Subset DEF StopServer
        <3>5. Cardinality(idleServers')+ Cardinality(busyServers') <= MaxServers
            BY <2>6, <3>1, <3>2, <3>3, <3>4     
        <3>6. Cardinality(busyServers') \in 0..MaxServers
         BY  <2>6, <3>2,<3>3, <3>5,FS_EmptySet, FS_Interval,FS_Subset   
        <3>7. Cardinality(idleServers') \in 0..MaxServers 
               BY  <2>6,<3>1, <3>4, <3>5, FS_EmptySet, FS_Subset, FS_Interval 
        (*<3>8. \A s1 \in Servers': serverStatus'[s1].status = "IDLE" => s1 \in idleServers'
            BY <2>6 DEF StopServer  
        <3>9. \A s2 \in Servers':serverStatus'[s2].status = "BUSY" => s2 \in busyServers'
             BY <2>6 DEF StopServer 
             *)
        <3>10. \A a1 \in Actors: IsFiniteSet(actorServers'[a1]) 
            BY <2>6, FS_EmptySet, FS_Interval, FS_AddElement, FS_Subset DEF StopServer    
        <3>11.Cardinality(actorServers'[a]) =  Cardinality(actorServers[a]) - 1
            <4>1. \A a1 \in Actors: IsFiniteSet(actorServers[a1]) 
            BY <2>6, FS_EmptySet, FS_Subset DEF StopServer 
            <4>2. s \in actorServers[a]
            BY <2>6  DEF StopServer
            <4>3. QED 
            BY <2>6,<4>1,<4>2,FS_EmptySet, FS_RemoveElement, FS_Subset DEF StopServer 
        <3>12. \A a1 \in Actors: actorStatus'[a1]="READY"=>(Cardinality(actorServers'[a1]) >= MinimumServersAlwaysUpPerActor)
             BY <2>6, <3>10, <3>1,<3>11,  FS_EmptySet,FS_RemoveElement, FS_Subset, FS_CardinalityType DEF StopServer      \* CardinalityType is Required     
        <3>13. TypeInvariant' 
             BY <2>6 DEF StopServer 
        <3>20. QED BY <2>6, <3>1, <3>2,<3>4,<3>5,<3>6,<3>7,<3>10,<3>11,<3>12,<3>13, FS_EmptySet,FS_Interval,FS_AddElement, FS_RemoveElement, FS_CardinalityType, FS_Subset DEF StopServer
  <2>7. CASE UNCHANGED vars
        BY <2>7 DEF vars
  <2>8. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6,<2>7 DEF Next
 
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

=============================================================================
\* Modification History
\* Last modified Fri Dec 18 15:36:22 CST 2020 by spadhy
\* Created Mon Dec 07 11:36:52 CST 2020 by spadhy
