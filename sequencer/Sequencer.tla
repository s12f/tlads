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

BackupServer ≜
    [ role ↦ Backup
    , validLease ↦ FALSE
    , nextSeq ↦ 0
    , maxSeq ↦ 0
    , in ↦ None
    , out ↦ None
    ]

Init ≜ 
    ∧ states = [ s ∈ Servers ↦ BackupServer ]
    ∧ history = ⟨⟩
    ∧ storage = 0
    ∧ nextRid = 1

HandleRequest(s) ≜
    ∧ states[s].role = Leader
    ∧ states[s].in = None
    ∧ states[s].nextSeq < states[s].maxSeq
    ∧ states' = [ states EXCEPT ![s].in = nextRid ]
    ∧ nextRid' = nextRid + 1
    ∧ history' = Append(history, [ rid ↦ nextRid, typ ↦ Begin])
    ∧ UNCHANGED ⟨storage⟩

(* 
 This is the most important point of the algorithm,
 the Server will always put request into inbox first(HandleRequest Action),
 then check whether itself still has a valid lease(The Linearizable Point),
 If it is, the sequence in the inbox can send to client safely.
 *)
CheckRole(s) ≜
    ∧ states[s].role = Leader
    ∧ states[s].in ≠ None
    ∧ IF states[s].validLease
      THEN ∧ states' = [ states EXCEPT
                        ![s].out = [ rid ↦ states[s].in, seq ↦ states[s].nextSeq ],
                        ![s].in = None,
                        ![s].nextSeq = @ + 1
                       ]
           ∧ history' = Append(history, [ typ ↦ LP, rid ↦ states[s].in, seq ↦ states[s].nextSeq])
      \* Drop all states
      ELSE ∧ states' =[ states EXCEPT ![s] = BackupServer ]
           ∧ UNCHANGED ⟨history⟩
    ∧ UNCHANGED ⟨storage, nextRid⟩

RenewLease(s) ≜
    ∧ states[s].role = Leader
    ∧ states[s].nextSeq = states[s].maxSeq
    ∧ storage' = storage + BatchSize
    ∧ states' = [ states EXCEPT ![s].maxSeq = storage + BatchSize ]
    ∧ UNCHANGED ⟨history, nextRid⟩

Response(s) ≜
    ∧ states[s].out ≠ None
    ∧ states' = [ states EXCEPT ![s].out = None ]
    ∧ history' = Append(history, [ rid ↦ states[s].out.rid, typ ↦ End, seq ↦ states[s].out.seq ])
    ∧ UNCHANGED ⟨storage, nextRid⟩

\* Loss all states
RestartLeader(s) ≜
    ∧ states[s].role = Leader
    ∧ states' = [states EXCEPT ![s] = BackupServer ]
    ∧ UNCHANGED ⟨history, storage, nextRid⟩

\* All states of the leader are still in memory,
\* but the lease is invalid asynchronously(on clock).
LeaseTimeout(s) ≜
    ∧ states[s].validLease
    ∧ states' = [ states EXCEPT ![s].validLease = FALSE ]
    ∧ UNCHANGED ⟨history, storage, nextRid⟩

\* compete on storage, winner become the leader
NewLeader(s) ≜
    \* Only if all server have a bounded clock skew(that is the assumption),
    \* the condition can be implementable on the clocks.
    ∧ ∀a ∈ Servers: states[a].validLease = FALSE
    ∧ storage' = storage + BatchSize
    ∧ states' = [ states EXCEPT ![s] =
                                    [ role ↦ Leader
                                    , validLease ↦ TRUE
                                    , nextSeq ↦ storage
                                    , maxSeq ↦ storage + BatchSize
                                    , in ↦ None
                                    , out ↦ None]
                                    ]
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

\* Verify Linearizability by Linearizable points.
LinearizableHistory ≜
    ∀e1, e2 ∈ DOMAIN history:
        history[e1].typ = LP ∧ history[e2].typ = LP ∧ e2 > e1
            ⇒ history[e2].seq > history[e1].seq

Inv ≜ LinearizableHistory

============================================================================
