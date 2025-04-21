---- MODULE dns ----
EXTENDS TLC, Integers

(******************************************************************************)
(* States                                                                     *)
(******************************************************************************)

VARIABLES state, resolverIP, resultIP

\* All variables. Used for fairness definition
vars == <<state, resolverIP, resultIP>>

(******************************************************************************)
(* Constants                                                                  *)
(******************************************************************************)

\* Aka number of Resolvers
resolverIPSet == 100..103

\* A set of Resolvers (DNS servers)
\* Each contains a cached IP that is the address of the domain we want
\* to resolve.
\* The initial value is 1 but can be increased at any time until it reaches max value
maxResultIP == 10
initialResolverData == [cache |-> 1]
resolvers == [ip \in resolverIPSet |-> initialResolverData]


(******************************************************************************)
(* DNS query steps                                                            *)
(* We will use www.example.com as an example                                  *)
(******************************************************************************)

\* Let say we need to resolve IP of www.example.com.
\* Query Root Servers, managed by ICANN, to get resolver IPs for
\* Top Level Domain
RootServers == /\ state = "query_root_servers"
               /\ resolverIP' \in resolverIPSet
               /\ state' = "query_tld"
               /\ UNCHANGED <<resultIP>>

\* Query resolvers of Top Level Domain ".com" for resolver IPs of 
\* 1st Level Domain, managed by Registries
TLDResolver == /\ state = "query_tld"
               /\ resolverIP' \in resolverIPSet
               /\ state' = "resolve_to_ip"
               /\ UNCHANGED <<resultIP>>

\* Query resolvers of 1st Level Domain ".example" for IPs of the website,
\* usually managed by Registrants (developers) themselves
\* Sub-domain "www" resolution is skipped for simplicity.
FirstLevelResolver == /\ state = "resolve_to_ip"
                      /\ resultIP' = resolvers[resolverIP].cache
                      /\ state' = "done"
                      /\ UNCHANGED <<resolverIP>>

Reset == /\ state = "done"
         /\ state' = "query_root_servers"
         /\ resolverIP' = 0
         /\ resultIP' = 0

(******************************************************************************)
(* Complications                                                              *)
(* e.g. data changes, faults, etc.                                            *)
(******************************************************************************)

\* Update DNS cache to a new random value.
\* To do this, we pick any resolver_ip and any value in the result domain
\* then update the cache of the resolver with resolver_ip.
newResolverData(r) == IF 
                        r.cache = maxResultIP 
                      THEN
                        r
                      ELSE 
                        [cache |-> r.cache + 1]
updateResolver(ip) == resolvers' = [
                        resolvers EXCEPT ![ip] = newResolverData(@)
                    ]                 
DNSUpdate == /\ \E ip \in resolverIPSet: updateResolver(ip)
             /\ UNCHANGED <<state, resolverIP, resultIP>>

(******************************************************************************)
(* Specification metadata                                                     *)
(******************************************************************************)

Init == /\ state = "query_root_servers"
        /\ resolverIP = 0
        /\ resultIP = 0

Resolution == \/ RootServers
              \/ TLDResolver
              \/ FirstLevelResolver
              \/ Reset

\* DNS cache can be updated at any time
Next == \/ Resolution
        \/ DNSUpdate

\* Ensure resolution can make progress if any step is valid
NoStuttering == /\ WF_vars(Next)
                /\ WF_vars(Resolution)

Spec == Init /\ [][Next]_vars /\ NoStuttering

(******************************************************************************)
(* Correctness properties                                                     *)
(******************************************************************************)

\* If there is no change to the cache, the resultIP will eventually 
\* be the same as the cache
EventualConsistency == <>(\A ip \in resolverIPSet: resolvers[ip].cache = resultIP)

====