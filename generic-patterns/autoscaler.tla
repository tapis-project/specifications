----------------------------- MODULE autoscaler --------------------------------------

EXTENDS Naturals, FiniteSets, Sequences,SequenceTheorems, TLAPS

CONSTANTS MaxMessage,       \* Maximum number of HTTP requests that are sent
          ScaleUpThreshold  \* ScaleUpThreshold 
          
ASSUME SpecAssumption == 
         /\ MaxMessage \in (Nat \ {0})
         /\ ScaleUpThreshold \in (Nat \ {0}) (* ScaleUpThreshold should be atleast 1 *)        
 
---------------------------------------------------------------------------------------          
          
VARIABLES Servers,          \* servers being created
          msg_queue,        \* Message queue
          serverStatus,     \* server status
          tmsg,              \* total number of message sent
          work              \* representation of work
          
 vars == <<Servers, msg_queue, serverStatus, tmsg, work>>  
 
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
Messages == [type : {"EXECUTE"},  server: Servers]

----------------------------------------------------------------------------------------
(*
***********************************
Invariants and Temporal Properties
***********************************
*)

MaxServers == MaxMessage + 1

\* An invariant: ensures all the variables maintain the proper types.
TypeInvariant == 
  /\ Servers \in {1..MaxServers}
  /\ serverStatus \in [Servers -> ServerState] 
  /\ msg_queue \in Seq(Messages)
  /\ Len(msg_queue) \in 0..MaxMessage
  /\ tmsg \in 0..MaxMessage
  /\ tmsg + Len(msg_queue)<= 2*MaxMessage
  /\ tmsg >= Len(msg_queue)
  /\ work \in 1..MaxMessage
  
 
 
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
    /\ Servers \in {1..MaxServers}
    /\ serverStatus = [s \in Servers |-> "-"] \* Server has not yet started
    /\ msg_queue = <<>>
    /\ tmsg  = 0
    /\ work = 1
   
 
----------------------------------------------------------------------------------    
(*    
*************************************
HTTP Requests/Synchronous Processing
*************************************
*)

APIExecuteRecv(msg, s) ==    
(*
Represents the API platform receiving an HTTP request to the POST /resource/{id} endpoint 
*)
    /\  msg.type = "EXECUTE"
    /\  tmsg < MaxMessage
    /\  msg_queue'= Append(msg_queue,msg)
    /\  tmsg' = tmsg + 1
    /\  UNCHANGED<<Servers, serverStatus, work>>   
 
(*    
*****************************
Asynchronous Task Processing
*****************************
*)
 
 CreateServer(s) ==
    /\ Len(msg_queue) >= ScaleUpThreshold
    /\ ~(\E s1 \in Servers: serverStatus[s1] = "IDLE")
    /\ serverStatus[s] = "-"
    /\ serverStatus'= [serverStatus EXCEPT ![s] = "IDLE"]        
    /\ UNCHANGED<<Servers,tmsg,msg_queue, work>>
    
 ServerRecv(s) == 
    /\  serverStatus[s] = "IDLE"
    /\  Len(msg_queue) >= 1
    /\  msg_queue'= Tail(msg_queue)
    /\  serverStatus'= [serverStatus EXCEPT ![s] = "BUSY"]   
    /\  UNCHANGED<<Servers,tmsg, work>>
 
 ServerBusy(s) ==
    /\  serverStatus[s] = "BUSY"
    /\  work' = (work % MaxMessage) + 1
    /\  serverStatus'= [serverStatus EXCEPT ![s] = "IDLE"]   
    /\  UNCHANGED<<Servers,tmsg, msg_queue>>
    
 Next == 
   \/ \E msg \in Messages, s \in Servers: APIExecuteRecv(msg, s)
   \/ \E s \in Servers: CreateServer(s)
   \/ \E s \in Servers: ServerRecv(s)
   \/ \E s \in Servers: ServerBusy(s)

Spec == Init /\ [][Next]_vars  


FairSpec == Spec
        /\ WF_vars(\E s \in Servers: CreateServer(s))
        /\ WF_vars(\E s \in Servers: ServerRecv(s)) 
        /\ WF_vars(\E s \in Servers: ServerBusy(s)) 
        
 (* ~~~~~ Proof ~~~~~~~~~~~~~~~~ *)       
 (* ~~~~~~ For TLC Proof ~~~~~~~ *)
 MySeq(P) == UNION {[1..n -> P] : n \in 0..MaxMessage}   
 
 
 
 IInv == TypeInvariant
 
 THEOREM Spec => []IInv
<1>1. Init => IInv
  BY SpecAssumption DEF Init, IInv, TypeInvariant, MaxServers, ServerState

<1>2. IInv /\ [Next]_vars => IInv'
  <2> SUFFICES ASSUME IInv,
                      [Next]_vars
               PROVE  IInv'
    OBVIOUS
  <2>. USE SpecAssumption DEF IInv, TypeInvariant, Init, MaxServers, ServerState, Messages
  <2>1. ASSUME NEW msg \in Messages,
        NEW s \in Servers,
               APIExecuteRecv(msg, s)
        PROVE  IInv'
     BY <2>1, SpecAssumption DEF APIExecuteRecv  
  <2>2. ASSUME NEW s \in Servers,
               CreateServer(s)
        PROVE IInv'
     BY <2>2, SpecAssumption DEF CreateServer
  <2>3. ASSUME NEW s \in Servers,
                 ServerRecv(s)
        PROVE IInv'
     BY <2>3, SpecAssumption DEF ServerRecv
  <2>4. ASSUME NEW s \in Servers,
                 ServerBusy(s)
        PROVE IInv'
     BY <2>4, SpecAssumption DEF ServerBusy                              
  <2>5. CASE UNCHANGED vars
    BY <2>5, SpecAssumption DEF vars
  <2>6. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>. QED  BY <1>1, <1>2, PTL DEF Spec
          

          
=============================================================================
\* Modification History
\* Last modified Tue Nov 24 12:32:15 CST 2020 by spadhy
\* Created Tue Oct 20 14:31:41 CDT 2020 by spadhy
