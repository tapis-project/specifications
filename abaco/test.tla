---- MODULE test ----
EXTENDS TLC, Integers

(* --algorithm counter
variable x = 0;

process counter = "counter"
begin Count:
  while x < 10 do
    x := x + 1;
  end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-0fabd8827d3cfedd75d70b145da631c5
VARIABLES x, pc

vars == << x, pc >>

ProcSet == {"counter"}

Init == (* Global variables *)
        /\ x = 0
        /\ pc = [self \in ProcSet |-> "Count"]

Count == /\ pc["counter"] = "Count"
         /\ IF x < 10
               THEN /\ x' = x + 1
                    /\ pc' = [pc EXCEPT !["counter"] = "Count"]
               ELSE /\ pc' = [pc EXCEPT !["counter"] = "Done"]
                    /\ x' = x

counter == Count

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == counter
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-844bbddc34c6281dc768e8f069f4d284

====
