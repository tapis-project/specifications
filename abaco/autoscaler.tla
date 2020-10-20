----------------------------- MODULE autoscaler -----------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS MaxMessage,       \* Maximum number of HTTP requests that are sent
          ScaleUpThreshold  \* ScaleUpThreshold 
          
VARIABLES Servers,          \* servers being created
          msg_queue,        \* Message queue
          serverStatus,     \* server status
          tmsg,              \* total number of message sent
          work              \* representation of work
          
 vars == <<Servers, msg_queue,serverStatus, tmsg>>  
 
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

(*
***********************************
Invariants and Temporal Properties
***********************************
*)

MaxServers == MaxMessage + 1

\* An invariant: ensures all the variables maintain the proper types.
TypeInvariant == 
  /\ serverStatus \in [Servers -> ServerState] 
  /\ msg_queue \in Seq(Messages) 
  /\ Servers \in SUBSET Nat
  
  
\* A temporal property: ensures all messages are eventually processed 
\* (i.e., that the length of msq_queue is eventually 0 
\* from some point until the end of the run.)
AllMessagesProcessed == <>[](\A a \in Servers: Len(msg_queue) = 0)    

(*
*****************
Helper Operators
*****************
*)

Range(F) == { F[x] : x \in DOMAIN F }

 
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
    /\ work = 0
   
 
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
    /\  UNCHANGED<<Servers,tmsg>>
 
 ServerBusy(s) ==
    /\  serverStatus[s] = "BUSY"
    /\  work' = work + 1
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
=============================================================================
\* Modification History
\* Last modified Tue Oct 20 14:43:50 CDT 2020 by spadhy
\* Created Tue Oct 20 14:31:41 CDT 2020 by spadhy
