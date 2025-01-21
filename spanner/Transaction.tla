-------------------- MODULE Transaction --------------------
EXTENDS Integers, TLC, FiniteSets, Sequences

--------------------------------------------------------
\* import TrueTime Module
CONSTANTS TTInitAbs, TTMaxSi, TTInterval
VARIABLES ttAbs, ttDrift, ttSi
INSTANCE TrueTime

--------------------------------------------------------
\* Utils
Max(s) ≜ CHOOSE x ∈ s: ∀y ∈ s: x ≥ y
Min(s) ≜ CHOOSE x ∈ s: ∀y ∈ s: x ≤ y

--------------------------------------------------------

(*
Key: Participant name and data key name
TxDef: Transaciont Name → Transaction Definition
*)
CONSTANTS Key, InitValue, TxDef, None

(* since Spanner use the wound-wait strategy to avoid deadlocks,
    that a need total-order priority relationship,
    but the timestamps could be same,
    for simplicity, we use the ordering of transaction names to define the lock priorities
    (there are other better choices but it doesn't affect correctness).
    so the Transaction names must be subset of Nat.
*)
ASSUME DOMAIN TxDef ⊆ Nat

(* txs: states of transactions,
    the states of a transaction is stored in a coordinator leader,
    and the transaction is drived by the coordinator leader.
*)
VARIABLES txs

(* ps: Participants,
    every participant contains only a single key instead of a key range,
    So participant name is the key name.
*)
VARIABLES ps

Status ≜ { "Reading", "Committing", "CommitWaiting", "Committed", "Aborted" }

------------------------------------------------------------
(* We abstract participant as a lineariable transactional KV Store,
    which can be implemented:
        1. read only happends on Leader
        2. Leader always apply replicated logs before returning
        3. make sure the lineariable points are always valid
    So TSafe doesn't need to check TPaxosSafe mentioned in paper.
*)
\* TSafe(key, readTs) ≜
\*     LET p ≜ Key[key]
\*         write ≜ ps[p].write
\*         data ≜ ps[p].data
\*         \* locks ≜ ps[]
\*     IN IF write[key] = None
\*        THEN

\* ReadValue(key, ts) ≜
\*     LET data ≜ ps[key].data
\*         tss ≜ DOMAIN data
\*         readTs ≜ CHOOSE x ∈ tss:
\*                     ∧ ts > x
\*                     ∧ ∀y ∈ tss: x ≥ y

\* wound-wait strategy: try to abort a low-priority transaction
AvoidDeadlock(tx, key) ≜
    ∧ txs[tx].status ∉ { "CommitWaiting", "Committed", "Aborted" }
    ∧ key ∈ TxDef[tx].read ∪ DOMAIN TxDef[tx].write
    ∧ ps[key].lock ≠ None
    ∧ ps[key].lock > tx
    ∧ txs[ps[key].lock].status ∉ { "CommitWaiting", "Committed", "Aborted" }
    ∧ txs' = [ txs EXCEPT ![ps[key].lock].status = "Aborted"]
    ∧ UNCHANGED ⟨ps⟩

ReadLatestValue(key) ≜
    LET data ≜ ps[key].data
    IN IF data = ⟨⟩
       THEN InitValue[key]
       ELSE data[Len(data)].value

Read(tx, key) ≜
    ∧ txs[tx].status = "Reading"
    ∧ key ∈ TxDef[tx].read
    ∧ key ∉ DOMAIN txs[tx].read
    (* wound-wait strategy: wait a high-priority transaction.
        If the lock holder is a low-priority transaction,
        AvoidDeadlock will try to abort it.
    *)
    ∧ ps[key].lock = None
    ∧ ps' = [ ps EXCEPT ![key].lock = tx ]
    ∧ txs' = [ txs EXCEPT ![tx].read = key :> ReadLatestValue(key) @@ @ ]

\* Start two-phase commit
StartCommit(tx) ≜
    ∧ txs[tx].status = "Reading"
    ∧ TxDef[tx].read = DOMAIN txs[tx].read
    ∧ txs' = [ txs EXCEPT
                    ![tx].status = "Committing",
                    ![tx].startCommitTs = TTNow.latest ]
    ∧ UNCHANGED ⟨ps⟩

\* prepare non-leader participant
Prepare(tx, key) ≜
    ∧ txs[tx].status = "Committing"
    ∧ txs[tx].coLeader ≠ key
    ∧ key ∈ DOMAIN TxDef[tx].write
    ∧ ps[key].lock = None ∨ ps[key].lock = tx
    ∧ ps' = [ ps EXCEPT ![key].lock = tx,
                        ![key].paxosTs = @ + 1,
                        ![key].prepared = [ ts ↦ ps[key].paxosTs
                                          , value ↦ TxDef[tx].write[key] ]
            ]
    ∧ UNCHANGED ⟨txs⟩

(* Require write lock, and write commit log,
    In paper, Coordinator Leader doesn't have prepare stage,
    here we re-use the prepared field to store
    some information in commit log and simplify clean stage.
*)
PrepareCoLeader(tx, key) ≜
    ∧ txs[tx].status = "Committing"
    ∧ txs[tx].coLeader = key
    ∧ key ∈ DOMAIN TxDef[tx].write
    ∧ ps[key].lock = None ∨ ps[key].lock = tx
    \* all non-leader participants have prepared
    ∧ LET nonLeaderPs ≜ DOMAIN TxDef[tx].write \ { key }
          maxPreparedTs ≜ IF nonLeaderPs = {}
                          THEN txs[tx].startCommitTs + 1
                          ELSE Max({ x.ts : x ∈ DOMAIN nonLeaderPs })
          commitTs ≜ Max({maxPreparedTs, txs[tx].startCommitTs + 1, ps[key].paxosTs})
      IN ∧ ∀ p ∈ nonLeaderPs: ps[p].lock = tx
         ∧ ps' = [ ps EXCEPT ![key].lock = tx,
                             ![key].paxosTs = @ + 1,
                             ![key].prepared = [ ts ↦ ps[key].paxosTs
                                               , value ↦ TxDef[tx].write[key] ]
                 ]
         ∧ txs' = [ txs EXCEPT
                        ![tx].commitTs = commitTs,
                        ![tx].status = "CommitWaiting" ]

\* Commit Wait
Commit(tx) ≜
    ∧ txs[tx].status = "CommitWaiting"
    ∧ TTAfter(txs[tx].commitTs)
    ∧ txs' = [ txs EXCEPT ![tx].status = "Committed" ]
    ∧ UNCHANGED ⟨ps⟩

TTAdvanceForCommitWait ≜ ∃tx ∈ DOMAIN txs:
    ∧ txs[tx].status = "CommitWaiting"
    ∧ ¬ TTAfter(txs[tx].commitTs)
    ∧ TTEventNext

\* Clean
CleanAborted(tx, key) ≜
    ∧ txs[tx].status = "Aborted"
    ∧ ps[key].lock = tx
    ∧ ps' = [ ps EXCEPT
                ![key].lock = None,
                ![key].prepared = None ]
    ∧ UNCHANGED ⟨txs⟩

CleanCommitted(tx, key) ≜
    ∧ txs[tx].status = "Committed"
    ∧ ps[key].lock = tx
    ∧ IF ps[key].prepared = None
      THEN ps' = [ ps EXCEPT ![key].lock = None ]
      ELSE ps' = [ ps EXCEPT
                    ![key].lock = None,
                    ![key].prepared = None,
                    ![key].data = Append(@, [ ts ↦  txs[tx].commitTs
                                            , value ↦ ps[key].prepared.value] ) ]
    ∧ UNCHANGED ⟨txs⟩

Init ≜
    ∧ TTInit
    ∧ txs = [ tx ∈ DOMAIN TxDef ↦
                [ status ↦  "Reading"
                \* Coordinator Leader(Participant)
                , coLeader ↦ CHOOSE k ∈ DOMAIN TxDef[tx].write: TRUE
                , read ↦ ⟨⟩
                , startCommitTs↦ None
                , commitTs ↦ None
                ] ]
    ∧ ps = [ p ∈ Key  ↦ 
                [ data ↦ ⟨⟩
                , lock ↦ None
                , prepared ↦ None
                (* paxos monotonical timestamp, we don't show the S_max
                    constraint here by simply assuming S_max will be big enough,
                    because it is a implemetation detail in paxos replication layer.
                *)
                , paxosTs ↦ TTNow.earliest 
                ] ]



TxNext ≜
    ∃tx ∈ DOMAIN TxDef:
        ∨ StartCommit(tx)
        ∨ Commit(tx)
        ∨ ∃key ∈ Key:
            ∨ Read(tx, key)
            ∨ AvoidDeadlock(tx, key)
            ∨ Prepare(tx, key)
            ∨ PrepareCoLeader(tx, key)
            ∨ CleanAborted(tx, key)
            ∨ CleanCommitted(tx, key)

Done ≜
    ∧ ∀tx ∈ DOMAIN TxDef: txs[tx].status ∈ { "Committed", "Aborted" }
    ∧ ∀key ∈ Key: ps[key].lock = None

Next ≜
    ∨ ∧ TTAdvanceForCommitWait
      ∧ UNCHANGED ⟨txs, ps⟩
    ∨ ∧ TxNext
      ∧ UNCHANGED ⟨ttAbs, ttDrift, ttSi⟩
    ∨ ∧ TTNext
      ∧ UNCHANGED ⟨txs, ps⟩

============================================================
