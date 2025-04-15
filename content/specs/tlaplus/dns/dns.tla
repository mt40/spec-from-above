---- MODULE dns ----
EXTENDS TLC, Integers
VARIABLES state, resolverIP, cache, resultIP

\* All variables. Used for fairness definition
vars == <<state, resolverIP, cache, resultIP>>

\* TODO: support diff domain name levels

RootServers == /\ state = "query_root_servers"
               /\ resolverIP' \in 1..10
               /\ state' = "query_tld"
               /\ UNCHANGED <<resultIP, cache>>

TLDResolver == /\ state = "query_tld"
               /\ resolverIP' \in 101..110
               /\ state' = "resolve_to_ip"
               /\ UNCHANGED <<resultIP, cache>>

FirstLevelResolver == /\ state = "resolve_to_ip"
               /\ resultIP' = cache
               /\ state' = "done"
               /\ UNCHANGED <<resolverIP, cache>>

\* Update DNS cache to a new random value
DNSUpdate == /\ cache' \in 1..10
             /\ UNCHANGED <<state, resolverIP, resultIP>>

Init == /\ state = "query_root_servers"
        /\ cache \in 1..10
        /\ resolverIP = 0
        /\ resultIP = 0

Resolution == \/ RootServers
              \/ TLDResolver
              \/ FirstLevelResolver

\* DNS cache can be updated at any time
Next == \/ Resolution
        \/ DNSUpdate

NoStuttering == /\ WF_vars(Next)
                /\ WF_vars(Resolution)

Spec == Init /\ [][Next]_vars /\ NoStuttering

(* Properties *)

\* Eventually, we can get the latest IP
EventualConsistency == <>(resultIP = cache)

====