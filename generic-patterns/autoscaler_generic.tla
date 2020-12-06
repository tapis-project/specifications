------------------------- MODULE autoscaler_generic -------------------------
EXTENDS Naturals, FiniteSets, FiniteSetTheorems, Functions, WellFoundedInduction, NaturalsInduction, Sequences, TLAPS

CONSTANTS MaxMessage,       \* Maximum number of HTTP requests that are sent
          ScaleUpThreshold,  \* ScaleUpThreshold 
          MinimumServersAlwaysUp,  \* Minimum number of servers should always be running
          MaxServers           \* Maximum Number of Servers that can be created

ASSUME SpecAssumption == 
         /\ MaxMessage \in (Nat \ {0})
         /\ ScaleUpThreshold \in (Nat \ {0}) (* ScaleUpThreshold should be atleast 1 *)   
         /\ MinimumServersAlwaysUp \in (Nat \ {0})  (* Atleast one server should always be running *) 
         /\ MaxServers \in (Nat \ {0})
         /\ MinimumServersAlwaysUp <= MaxServers 
 
---------------------------------------------------------------------------------------          
          
VARIABLES Servers,          \* Servers being created
          msg_queue,        \* Message queue
          serverStatus,     \* server status
          tmsg,             \* total number of message sent
          work,             \* representation of work
          idleServers,      \* Set of Idle servers
          busyServers       \* Set of Busy servers
                   
 vars == <<Servers, msg_queue, serverStatus, tmsg, work, idleServers, busyServers>>  
 
\* serverState
ServerState == {"-","IDLE", "BUSY"}

(*
************************************************************************************
Set of all possible message types in the queue             
************************************************************************************
*)
 
 \* These message types represent BOTH the HTTP request message (sent by the user)
 \* and the message queued in a message queue
 \* In the real implementation, the messages are not exactly the same,
 \* but we make this simplification for the spec:

Messages == [type : {"EXECUTE"}]

----------------------------------------------------------------------------------------



(*
***********************************
Invariants and Temporal Properties
***********************************
*)

\*MaxServers == MaxMessage + 1

\* An invariant: ensures all the variables maintain the proper types.
TypeInvariant == 
  /\ Servers \in {1..MaxServers}
  /\ serverStatus \in [Servers -> ServerState] 
  /\ msg_queue \in Seq(Messages)
  /\ Len(msg_queue) \in 0..MaxMessage
  /\ tmsg \in 0..MaxMessage
  \*/\ tmsg + Len(msg_queue)<= 2*MaxMessage
  /\ tmsg >= Len(msg_queue)
  /\ work \in 1..MaxMessage
  /\ idleServers \in SUBSET Servers
  /\ \A s1 \in idleServers:serverStatus[s1] = "IDLE"
  /\ busyServers \in SUBSET Servers
  /\ \A s2 \in busyServers:serverStatus[s2] = "BUSY"
  /\ idleServers \intersect busyServers = {} 
 
  

 TotalServersRunning == idleServers \cup busyServers
  

SafetyProperty ==  /\ Cardinality(idleServers) \in 0..MaxServers
                   /\ Cardinality(busyServers) \in 0..MaxServers
                   /\ IsFiniteSet(idleServers)
                   /\ IsFiniteSet(busyServers)
                   /\ Cardinality(idleServers)+ Cardinality(busyServers) <= MaxServers
                   /\ \A s \in Servers:serverStatus[s] = "IDLE" => s \in idleServers
                   /\ \A s \in Servers:serverStatus[s] = "BUSY" => s \in busyServers
                   /\ Cardinality(idleServers)+ Cardinality(busyServers) >= MinimumServersAlwaysUp
                  

 
\* A temporal property: ensures all messages are eventually processed 
\* (i.e., that the length of msq_queue is eventually 0 
\* from some point until the end of the run.)
AllMessagesProcessed == <>[](\A a \in Servers: Len(msg_queue) = 0)    

      
 
(*
****************************
Initialization of Variables
****************************
*)

Init == 
    \*/\ Servers = {1..MaxServers}
    /\ Servers = 1..MaxServers
    /\ serverStatus = [s \in Servers |-> IF s<=MinimumServersAlwaysUp THEN "IDLE"
                                                                      ELSE "-"] \* Server has not yet started
    /\ msg_queue = <<>>
    /\ tmsg  = 0
    /\ work = 1
    \*/\ idleServers={s \in Servers:serverStatus[s]="IDLE"}
   \* /\ idleServers={s \in Servers: s<=MinimumServersAlwaysUp}
    /\ idleServers=1..MinimumServersAlwaysUp
    /\ busyServers = {}
 
----------------------------------------------------------------------------------    
(*    
*************************************
HTTP Requests/Synchronous Processing
*************************************
*)
StartServer(s) ==
    /\ Cardinality(TotalServersRunning) < MinimumServersAlwaysUp
    /\ Cardinality(idleServers) + Cardinality(busyServers) < MaxServers
    /\ serverStatus[s] = "-"
    /\ serverStatus'= [serverStatus EXCEPT ![s] = "IDLE"]     
    /\ idleServers' = idleServers \cup {s}
    /\ UNCHANGED<<Servers,tmsg,msg_queue, work, busyServers>>


APIExecuteRecv(msg, s) ==    
(*
Represents the API platform receiving an HTTP request to the POST /resource/{id} endpoint 
*)
    /\  msg.type = "EXECUTE"
    /\  tmsg < MaxMessage
    /\  msg_queue'= Append(msg_queue,msg)
    /\  tmsg' = tmsg + 1
    /\  UNCHANGED<<Servers, serverStatus, work, idleServers, busyServers>>   
 
(*    
*****************************
Asynchronous Task Processing
*****************************
*)
 
 CreateServer(s) ==
    /\ Len(msg_queue) >= ScaleUpThreshold
    /\ ~(\E s1 \in Servers: serverStatus[s1] = "IDLE")
    /\ serverStatus[s] = "-"
    /\ Cardinality(busyServers) < MaxServers \* This condition is required for the proof of Safety property
    /\ serverStatus'= [serverStatus EXCEPT ![s] = "IDLE"]     
    /\ idleServers' = idleServers \cup {s}
    /\ UNCHANGED<<Servers,tmsg,msg_queue, work, busyServers>>
    
 ServerRecv(s) == 
    /\  serverStatus[s] = "IDLE"
    /\  Len(msg_queue) >= 1
    /\  msg_queue'= Tail(msg_queue)
    /\  serverStatus'= [serverStatus EXCEPT ![s] = "BUSY"]  
    /\  busyServers' = busyServers \cup {s}
    /\  idleServers' = idleServers \ {s}
    /\  UNCHANGED<<Servers,tmsg, work>>
 
 ServerBusy(s) ==
    /\  serverStatus[s] = "BUSY"
    /\  work' = (work % MaxMessage) + 1
    /\  serverStatus'= [serverStatus EXCEPT ![s] = "IDLE"]
    /\  idleServers' = idleServers \cup {s}  
    /\  busyServers' = busyServers \ {s}
    /\  UNCHANGED<<Servers,tmsg, msg_queue>>
 
 StopServer(s) == 
    /\  Len(msg_queue) = 0
    /\  serverStatus[s] = "IDLE"
    /\  Cardinality(idleServers) + Cardinality(busyServers) > MinimumServersAlwaysUp
    /\  idleServers' = idleServers \ {s}
    /\  serverStatus'= [serverStatus EXCEPT ![s] = "-"]
    /\  UNCHANGED<<Servers,tmsg,msg_queue, work, busyServers>>
    
 Next == 
   
   \/ \E msg \in Messages, s \in Servers: APIExecuteRecv(msg, s)
   \/ \E s \in Servers: CreateServer(s)
   \/ \E s \in Servers: ServerRecv(s)
   \/ \E s \in Servers: ServerBusy(s)
   \/ \E s \in Servers: StopServer(s)

Spec == Init /\ [][Next]_vars  


FairSpec == Spec
        \*/\ WF_vars(\E s \in Servers: StartServer(s))
        /\ WF_vars(\E s \in Servers: CreateServer(s))
        /\ WF_vars(\E s \in Servers: ServerRecv(s)) 
        /\ WF_vars(\E s \in Servers: ServerBusy(s)) 
        
 (* --------------------------- Spec Proof ------------------------------------------ *) 
 
 -------------------------------------------------------------------------------------      
 (* ~~~~~~ For TLC Proof ~~~~~~~ *)
 
 MySeq(P) == UNION {[1..n -> P] : n \in 0..MaxMessage}   
 
 
  ------------------------------------------------------------------------------------
  ------------------------------------------------------------------------------------
 
 IInv == TypeInvariant
 
 THEOREM Spec => []IInv
<1>1. Init => IInv
  BY SpecAssumption DEF Init, IInv, TypeInvariant, ServerState

<1>2. IInv /\ [Next]_vars => IInv'
  <2> SUFFICES ASSUME IInv,
                      [Next]_vars
               PROVE  IInv'
    OBVIOUS
  <2>. USE SpecAssumption DEF IInv, TypeInvariant, Init, ServerState, Messages
  <2>1. ASSUME NEW msg \in Messages,
        NEW s \in Servers,
               APIExecuteRecv(msg, s)
        PROVE  IInv'
     BY <2>1 DEF APIExecuteRecv  
  <2>2. ASSUME NEW s \in Servers,
               CreateServer(s)
        PROVE IInv'
     BY <2>2 DEF CreateServer
  <2>3. ASSUME NEW s \in Servers,
                 ServerRecv(s)
        PROVE IInv'
     BY <2>3 DEF ServerRecv
  <2>4. ASSUME NEW s \in Servers,
                 ServerBusy(s)
        PROVE IInv'
     BY <2>4 DEF ServerBusy                              
  (*<2>5. ASSUME NEW s \in Servers,
               StartServer(s)
        PROVE IInv'
     BY <2>5 DEF StartServer  *)       
  <2>6. CASE UNCHANGED vars
    BY <2>6 DEF vars
  <2>7. QED
    BY <2>1, <2>2, <2>3, <2>4,<2>6 DEF Next
<1>. QED  BY <1>1, <1>2, PTL DEF Spec
          
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
(* --------------------- Proof of the Inductive Invariant --------------------*)

IInv1 == TypeInvariant /\ SafetyProperty

(*THEOREM FS_MutualExclusiveUnion ==
  ASSUME 
  NEW S, IsFiniteSet(S),
  NEW T, IsFiniteSet(T),
  S \intersect T = {}
         
  PROVE  /\ IsFiniteSet(S \cup T)
         /\ Cardinality(S \cup T) =
               Cardinality(S) + Cardinality(T) 
    *)     

THEOREM Spec => []IInv1
 
 <1>1. Init => IInv1
   <2> SUFFICES ASSUME Init
                PROVE  IInv1
     OBVIOUS
   <2>1. TypeInvariant
    BY SpecAssumption DEF IInv1, TypeInvariant, Init,ServerState, Messages
   <2>2. SafetyProperty
     <3>1. IsFiniteSet(idleServers)
        <4>1.IsFiniteSet(Servers)
        BY  SpecAssumption, FS_Interval DEF Init
        <4>2. QED  BY <4>1, SpecAssumption, FS_EmptySet, FS_Subset DEF Init
     <3>2. IsFiniteSet(busyServers)
        BY  SpecAssumption, FS_EmptySet, FS_Subset DEF Init
     <3>3. Cardinality(idleServers) = MinimumServersAlwaysUp
        BY  SpecAssumption, FS_Interval DEF Init
     <3>4. Cardinality(idleServers)+ Cardinality(busyServers) <= MaxServers
      BY  <3>1,<3>2,<3>3,SpecAssumption, FS_EmptySet, FS_Subset DEF Init
     <3>5. Cardinality(idleServers) \in 0..MaxServers
         BY SpecAssumption, <3>1, FS_Interval DEF Init
     <3>6. Cardinality(busyServers) \in 0..MaxServers
        BY SpecAssumption, <3>2, FS_EmptySet DEF Init
     <3>7. \A s \in Servers:serverStatus[s] = "IDLE" => s \in idleServers
        BY DEF Init
     <3>8. \A s \in Servers:serverStatus[s] = "BUSY" => s \in busyServers
        BY DEF Init
     <3>9. Cardinality(idleServers)+ Cardinality(busyServers) >= MinimumServersAlwaysUp
        (*<4>1. Cardinality(busyServers) = 0
         BY  SpecAssumption, FS_EmptySet, FS_Subset DEF IInv1,Init, TypeInvariant
         <4>2. Cardinality(idleServers) = MinimumServersAlwaysUp
         BY SpecAssumption, FS_EmptySet, FS_Subset,FS_AddElement,FS_Interval DEF IInv1,Init, TypeInvariant
        <4>3. QED *)BY  <3>1,<3>2,<3>3, SpecAssumption, FS_EmptySet, FS_Subset DEF Init
     
     <3>10. QED
       BY <3>1, <3>2, <3>3, <3>4,<3>5,<3>6,<3>7,<3>8,<3>9 DEF SafetyProperty
    <2>3. QED
     BY <2>1, <2>2 DEF IInv1
  

<1>2. IInv1 /\ [Next]_vars => IInv1'
  <2> SUFFICES ASSUME TypeInvariant,
                      SafetyProperty,
                      [Next]_vars
               PROVE  IInv1'
    BY DEF IInv1, SafetyProperty
  <2>.USE SpecAssumption DEF IInv1, TypeInvariant, Init, ServerState, Messages, SafetyProperty,TotalServersRunning  
  <2>1. ASSUME NEW msg \in Messages,
               NEW s \in Servers,
               APIExecuteRecv(msg, s)
        PROVE  IInv1'
        BY <2>1 DEF APIExecuteRecv  
  <2>2. ASSUME NEW s \in Servers,
               CreateServer(s)
        PROVE  IInv1'
        <3>1. IsFiniteSet(idleServers')
            BY <2>2, FS_EmptySet, FS_AddElement, FS_Subset DEF CreateServer
        <3>2. IsFiniteSet(busyServers')
            BY <2>2, FS_EmptySet, FS_Subset DEF CreateServer
        <3>3. idleServers={}
            BY <2>2, FS_EmptySet, FS_Subset DEF CreateServer
        <3>4. Cardinality(idleServers') = Cardinality(idleServers) + 1
            BY <2>2,<3>1, FS_EmptySet, FS_AddElement, FS_Subset DEF CreateServer
        <3>5. Cardinality(idleServers') + Cardinality(busyServers') <= MaxServers
            BY <2>2, <3>1,<3>2, <3>3,<3>4,  FS_EmptySet, FS_AddElement, FS_Subset DEF CreateServer           
        <3>6. QED BY <2>2, <3>1, <3>2,<3>3,<3>4, FS_EmptySet, FS_AddElement, FS_Subset DEF CreateServer
  <2>3. ASSUME NEW s \in Servers,
               ServerRecv(s)
        PROVE  IInv1'
         <3>1. IsFiniteSet(idleServers')
            BY <2>3, FS_EmptySet, FS_Subset DEF ServerRecv
        <3>2. IsFiniteSet(busyServers')
            BY <2>3, FS_EmptySet, FS_AddElement, FS_Subset DEF ServerRecv
        <3>3. Cardinality(busyServers') = Cardinality(busyServers) + 1
            BY <2>3, <3>2,FS_EmptySet, FS_AddElement, FS_Subset DEF ServerRecv    
        <3>4. Cardinality(idleServers') =  Cardinality(idleServers) - 1
            BY <2>3,<3>1, FS_EmptySet, FS_RemoveElement, FS_Subset DEF ServerRecv
        <3>5. Cardinality(idleServers')+ Cardinality(busyServers') <= MaxServers
          BY <2>3, <3>1, <3>2,<3>3,<3>4        
        <3>6. QED BY <2>3, <3>1, <3>2,<3>3,<3>4,<3>5,FS_EmptySet,FS_AddElement, FS_RemoveElement, FS_Subset DEF ServerRecv
       
  <2>4. ASSUME NEW s \in Servers,
               ServerBusy(s)
        PROVE  IInv1'
        <3>1. IsFiniteSet(idleServers')
            BY <2>4, FS_EmptySet, FS_AddElement, FS_Subset DEF ServerBusy
        <3>2. IsFiniteSet(busyServers')
            BY <2>4, FS_EmptySet, FS_Subset DEF ServerBusy
        <3>3. Cardinality(busyServers') = Cardinality(busyServers) - 1
            BY <2>4,FS_EmptySet, FS_RemoveElement, FS_Subset DEF ServerBusy 
        <3>4. Cardinality(idleServers') =  Cardinality(idleServers) + 1
            BY <2>4, FS_EmptySet, FS_AddElement, FS_Subset DEF ServerBusy
        <3>5. Cardinality(idleServers')+ Cardinality(busyServers') <= MaxServers
            BY <2>4, <3>1, <3>2,<3>3, <3>4       
        <3>6. QED BY <2>4, <3>1, <3>2,<3>3, <3>4,<3>5, FS_EmptySet, FS_AddElement, FS_RemoveElement, FS_Subset DEF ServerBusy
  
  <2>5. ASSUME NEW s \in Servers,
               StopServer(s)
        PROVE  IInv1'
         <3>1. IsFiniteSet(idleServers')
            BY <2>5, FS_EmptySet, FS_Subset DEF StopServer
        <3>2. IsFiniteSet(busyServers')
            BY <2>5, FS_EmptySet, FS_AddElement, FS_Subset DEF StopServer
        <3>3. Cardinality(busyServers') = Cardinality(busyServers)
            BY <2>5, <3>2,FS_EmptySet, FS_AddElement, FS_Subset DEF StopServer 
        <3>4. Cardinality(idleServers') =  Cardinality(idleServers) - 1
            BY <2>5,<3>1, FS_EmptySet, FS_RemoveElement, FS_Subset DEF StopServer
        <3>5. Cardinality(idleServers')+ Cardinality(busyServers') <= MaxServers
            BY <2>5, <3>1, <3>2,<3>3,<3>4     
        <3>6. Cardinality(idleServers')+ Cardinality(busyServers') >= MinimumServersAlwaysUp
            BY <2>5, <3>1, <3>2,<3>3,<3>4 ,<3>5 DEF StopServer       
        <3>7. QED BY <2>5, <3>1, <3>2,<3>3,<3>4,<3>5,<3>6,FS_EmptySet,FS_AddElement, FS_RemoveElement, FS_Subset DEF StopServer
  <2>6. CASE UNCHANGED vars
        BY <2>6 DEF vars
  <2>7. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next
 
<1>. QED  BY <1>1, <1>2, PTL DEF Spec


=============================================================================
\* Modification History
\* Last modified Sun Dec 06 17:56:08 CST 2020 by spadhy
\* Created Sun Dec 06 17:11:35 CST 2020 by spadhy
