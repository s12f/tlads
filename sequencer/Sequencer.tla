-------------------------------- MODULE Sequencer -------------------------------

EXTENDS Integers, Sequences

CONSTANTS Servers, BatchSize, None

\* Server States
VARIABLES states
\* history: Seq({Begin, End})
VARIABLES history
\* storage: Nat
VARIABLES storage
\* next request id
VARIABLES nextRid

Leader ≜ "Leader"
Backup ≜ "Backup"

Begin ≜ "Begin"
LP ≜ "LP"
End ≜ "End"

\* ServerState ≜ [ role, in, seq ]
\*             ∪ [ role ]

\* TypeOK ≜
\*     ∧ epoch ∈ Nat
\*     ∧ states ∈ [ Servers → ServerState ]
\*     ∧ output ∈ Seq(1 ‥ MaxSeq)
\*     ∧ diskSeq ∈ Nat

\* Constraint ≜
\*     ∧ output ∈ Seq(1 ‥ MaxSeq)
\*     ∧ diskSeq ∈ 0‥MaxSeq
\*     ∧ ¬ ∃s ∈ Servers: states[s].role = Leader ∧ states[s].seq > MaxSeq

Init ≜ 
    ∧ states = [ s ∈ Servers ↦ [ role ↦ Backup ] ]
    ∧ history = ⟨⟩
    ∧ storage = 0
    ∧ nextRid = 1

HandleRequest(s) ≜
    ∧ states[s].role = Leader
    ∧ states[s].in = None
    ∧ States' = [ states EXCEPT ![s].in = nextRid ]
    ∧ nextRid' = nextRid + 1
    ∧ history = Append(history, [ rid ↦ nextRid, typ ↦ Begin])
    ∧ UNCHANGED ⟨storage⟩

(* 
 This is the most important point of the algorithm,
 the Server will always put request into inbox first(Request Action),
 then check whether itself is still a Leader(The Linearizable Point),
 If it is, the sequence in the inbox can send to client safely.
 *)
CheckRole(s) ≜
    ∧ states[s].in ≠ None
    ∧ IF states[s].role = Leader
      THEN ∧ states' = [ states EXCEPT
                        ![s].out = [ rid ↦ ![s].in, seq ↦ ![s].nextSeq ],
                        ![s].in = None,
                        ![s].nextSeq = @ + 1
                       ]
           ∧ history' = Append(history, [ typ ↦ LP, rid ↦ ![s].in, seq ↦ ![s].nextSeq])
      \* Drop all states
      ELSE ∧ states' =[ states EXCEPT ![s] = [ role ↦ Backup ] ]
           ∧ UNCHANGED ⟨history⟩
    ∧ UNCHANGED ⟨storage, nextRid⟩

RenewLease(s) ≜
    ∧ states[s].role = Leader
    ∧ states[s].nextSeq = storage
    ∧ states' = [ states EXCEPT ![s].nextSeq = storage + BatchSize ]
    ∧ storage' = storage + BatchSize
    ∧ UNCHANGED ⟨history, nextRid⟩

Response(s) ≜
    ∧ states[s].out ≠ None
    ∧ states' = [ states EXCEPT ![s].out = None ]
    ∧ history' = Append(history, [ rid ↦ out.rid, typ ↦ End, seq ↦ out.seq ])
    ∧ UNCHANGED ⟨storage, nextRid⟩

\* Loss all states
RestartLeader(s) ≜
    ∧ states[s].role = Leader
    ∧ states' = [states EXCEPT ![s] = [ role ↦ Backup ]]
    ∧ UNCHANGED ⟨history, storage, nextRid⟩

\* All states of the leader still in memory except
\* the role have be change to Backup asynchronously.
LeaseTimeout(s) ≜
    ∧ states[s].role = Leader
    ∧ states' = [ states EXCEPT ![s].role = Backup ]
    ∧ UNCHANGED ⟨history, storage, nextRid⟩

\* compete on storage, winner become the leader
NewLeader(s) ≜
    ∧ ∀a ∈ Servers: states[a].role = Backup
    ∧ storage' = storage + BatchSize
    ∧ states' = [ states EXCEPT ![s] = [ role ↦ Leader, seq ↦  storage, in ↦ None, out ↦ None] ]
    ∧ UNCHANGED ⟨history, nextRid⟩

Next ≜ ∃s ∈ Servers:
    ∨ HandleRequest(s)
    ∨ CheckRole(s)
    ∨ RenewLease(s)
    ∨ Response(s)
    ∨ RestartLeader(s)
    ∨ LeaseTimeout(s)
    ∨ NewLeader(s)

Spec ≜ Init ∧ □[Next]_⟨states, history, storage, nextRid⟩

----------------------------------------------------------------------------

SafeLeader ≜
    ∀x, y ∈ Servers:
        states[x].role = Leader ∧ states[y].role = Leader
            ⇒ x = y

\* Verify Linearizability by Linearizable points.
LinearizableHistory(s) ≜
    ∀e1, e2 ∈ DOMAIN history:
        history[e1].typ = LP ∧ history[e2].typ = LP ∧ e2 > e1
            ⇒ history[e2].seq > history[e1].seq

Inv ≜
    ∧ TypeOK
    ∧ SafeLeader
    ∧ LinearizableHistory(output)

============================================================================

