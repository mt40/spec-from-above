---- MODULE dns ----
EXTENDS TLC, Integers, FiniteSets

(******************************************************************************)
(* States                                                                     *)
(******************************************************************************)

VARIABLES 
    state, \* current state of the query process
    resolverIP, \* current IP of the resolver that we will query next
    resolvers, \* a set of available resolvers
    resultIP \* current result IP

\* All variables. Used for fairness definition
vars == <<state, resolverIP, resolvers, resultIP>>

(******************************************************************************)
(* Constants                                                                  *)
(******************************************************************************)

\* A set of IPs of resolver servers
resolverIPSet == 100..105

\* A set of Resolvers (DNS servers)
\* Each contains a cached IP that is the address of 
\* the domain we want to resolve.
\* The initial value is 1 but can be increased at 
\* any time until it reaches maxResultIP.
maxResultIP == 10
initialResolverData == [cache |-> 1, crashed |-> FALSE]

\* Max number of resolvers that can crash. If this number is 
\* equal to or more than resolverIPSet, the system will 
\* not be able to recover.
maxCrashes == 1

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
               /\ UNCHANGED <<resultIP, resolvers>>

\* Query resolvers of Top Level Domain ".com" for resolver IPs of 
\* 1st Level Domain, managed by Registries.
TLDResolver == /\ state = "query_tld"
               /\ resolverIP \in resolverIPSet
               /\ resolvers[resolverIP].crashed = FALSE
               /\ resolverIP' \in resolverIPSet
               /\ state' = "resolve_to_ip"
               /\ UNCHANGED <<resultIP, resolvers>>

\* Following resolverIP again, we reach resolvers of
\* 1st Level Domain ".example" for IPs of the website,
\* usually managed by Registrants (developers) themselves.
\*
\* Sub-domain "www" resolution will be skipped for
\* simplicity so here, we get our final IP address of
\* www.example.com as resultIP.
\*
\* If the resolver we try to query crashed, we will
\* try another resolver. It is guaranteed that we can find
\* one that did not crashed if maxCrashes is less than
\* or equal to resolverIPSet.
FirstLevelResolver == 
    LET
        readCache ==
            /\ resolvers[resolverIP].crashed = FALSE
            /\ resultIP' = resolvers[resolverIP].cache
            /\ UNCHANGED <<resolverIP, resolvers>>
        failover ==
            /\ resolvers[resolverIP].crashed = TRUE
            /\ \E ip \in resolverIPSet: 
                /\ resolvers[ip].crashed = FALSE
                /\ resultIP' = resolvers[ip].cache
                /\ resolverIP' = ip
            /\ UNCHANGED <<resolvers>>
    IN
        /\ state = "resolve_to_ip"
        /\ (readCache \/ failover)
        /\ state' = "done"

Reset == /\ state = "done"
         /\ state' = "query_root_servers"
         /\ resolverIP' = 0
         /\ resultIP' = 0
         /\ resolvers' = [ip \in resolverIPSet |-> initialResolverData]

(******************************************************************************)
(* Complications                                                              *)
(* e.g. data changes, faults, etc.                                            *)
(******************************************************************************)

\* Update DNS cache to a new value, up to maxResultIP.
\* To do this, we pick any value in the result domain
\* then update the cache of all resolver with that value.
\* We ignore crashed resolvers.
\* Very interstingly, if we don't ignore crashed resolvers,
\* we can't guarantee consistency as describe further down below.
newResolverData(r) ==
    IF
        r.cache = maxResultIP \/ r.crashed = TRUE
    THEN
        r
    ELSE
        [cache |-> r.cache + 1, crashed |-> FALSE]

DNSUpdate ==
    /\ resolvers' = [ip \in resolverIPSet |-> newResolverData(resolvers[ip])]
    /\ UNCHANGED <<state, resolverIP, resultIP>>

\* Simulate a simple crash fault.
\* At any time, a resolver can crash and stop responding. It is expected
\* that the system can recover by querying another resolver.
FirstLevelResolverCrash == 
    LET 
        crashedResolverIPs == {ip \in resolverIPSet: resolvers[ip].crashed}
        getCrashedResolverData == [
            cache |-> 0,
            crashed |-> TRUE
        ]
    IN 
        /\ state = "resolve_to_ip"
        /\ Cardinality(crashedResolverIPs) < maxCrashes
        /\ resolvers' = [
                resolvers 
                EXCEPT ![resolverIP] = getCrashedResolverData
            ]
        /\ resolverIP' \in resolverIPSet \ crashedResolverIPs
        /\ UNCHANGED <<state, resultIP>>

Complications == \/ FirstLevelResolverCrash
                 \/ DNSUpdate

(******************************************************************************)
(* Specification metadata                                                     *)
(******************************************************************************)

Init == /\ state = "query_root_servers"
        /\ resolverIP = 0
        /\ resolvers = [ip \in resolverIPSet |-> initialResolverData]
        /\ resultIP = 0
        

Resolution == \/ RootServers
              \/ TLDResolver
              \/ FirstLevelResolver
              \/ Reset

Next == \/ Resolution
        \/ Complications

\* Ensure resolution can make progress if the operator is often TRUE
Fairness == /\ SF_vars(Resolution)
            /\ SF_vars(FirstLevelResolverCrash)
            /\ SF_vars(DNSUpdate)

Spec == Init /\ [][Next]_vars /\ Fairness

(******************************************************************************)
(* Correctness properties                                                     *)
(******************************************************************************)

\* If there is no change to the cache, modeled by maxResultIP, resultIP 
\* will eventually “catch up” to the latest value. This means resultIP 
\* will eventually get the highest value stored in all resolvers.
EventualConsistency == 
    LET 
        gotHighestIP == 
            \E a \in resolverIPSet: 
                \A b \in resolverIPSet: 
                    /\ resolvers[a].cache >= resolvers[b].cache
                    /\ resultIP = resolvers[a].cache
    IN
        <>gotHighestIP

====