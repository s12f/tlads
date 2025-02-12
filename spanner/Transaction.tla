-------------------- MODULE Transaction --------------------
EXTENDS Integers, TLC, FiniteSets, Sequences

--------------------------------------------------------
\* import TrueTime Module
CONSTANTS TTInitAbs, TTMaxSi, TTInterval
VARIABLES ttAbs, ttDrift, ttSi
INSTANCE TrueTime

--------------------------------------------------------

(*
  Key: Participant name and data key name‥
  TxDefs: set of (Transaciont Name → Transaction Definition).
*)
CONSTANTS Key, InitValue, TxDefs, None

(* since Spanner use the wound-wait strategy to avoid deadlocks,
    that a need total-order priority relationship,
    but the timestamps could be same,
    for simplicity, we use the ordering of transaction names to define the lock priorities
    (there are other better choices but it doesn't affect correctness).
    so the Transaction names must be subset of Nat.
*)
ASSUME ∀def ∈ TxDefs: DOMAIN def ⊆ Nat

(* txs: states of transactions,
    the states of a transaction is stored in a coordinator leader,
    and the transaction is drived by the coordinator leader.
*)
VARIABLES txs

(* ps: Participants,
    every participant contains only a single key instead of a key range,
    So participant name is the key name.

    We abstract participant as a lineariable transactional KV Store,
    which can be implemented by:
        1. reading only happends on Leader
        2. Leader always apply replicated logs before returning
        3. make sure the lineariable points are always valid
*)
VARIABLES ps

--------------------------------------------------------
\* Utils
Max(s) ≜ CHOOSE x ∈ s: ∀y ∈ s: x ≥ y
Min(s) ≜ CHOOSE x ∈ s: ∀y ∈ s: x ≤ y
SafeChoose(s) ≜ 
    IF s = {}
    THEN None
    ELSE CHOOSE x ∈ s: TRUE

------------------------------------------------------------
(*
Reading: the transaction started, is requiring read lock and reading data.
Committing: the transaction have read and written data, starts committing.
CommitWaiting: the transaction archived the commit point, but needs to wait
    until TTAfter(commitTs).
Committed: the transaction is committed safely.
Aborted: the transaction is aborted.
 *)
Status ≜ {"Reading", "Committing", "CommitWaiting", "Committed", "Aborted"}

ReadLatestValue(key) ≜
    LET data ≜ ps[key].data
    IN IF data = ⟨⟩
       THEN InitValue[key]
       ELSE data[Len(data)].value

Read(tx, key) ≜
    ∧ txs[tx].status = "Reading"
    ∧ key ∈ txs[tx].rw.read
    ∧ key ∉ DOMAIN txs[tx].read
    (* wound-wait strategy: wait a high-priority transaction.
        If the lock holder is a low-priority transaction,
        AvoidDeadlock will try to abort it.
    *)
    ∧ ps[key].lock = None
    ∧ ps' = [ ps EXCEPT ![key].lock = tx ]
    ∧ txs' = [ txs EXCEPT ![tx].read = key :> ReadLatestValue(key) @@ @ ]

\* wound-wait strategy: try to abort a low-priority transaction
AvoidDeadlock(tx, key) ≜
    ∧ txs[tx].status ∉ { "CommitWaiting", "Committed", "Aborted" }
    ∧ key ∈ txs[tx].rw.read ∪ DOMAIN txs[tx].rw.write
    ∧ ps[key].lock ≠ None
    ∧ ps[key].lock > tx
    ∧ txs[ps[key].lock].status ∉ { "CommitWaiting", "Committed", "Aborted" }
    ∧ txs' = [ txs EXCEPT ![ps[key].lock].status = "Aborted"]
    ∧ UNCHANGED ⟨ps⟩

\* Start two-phase commit
StartCommit(tx) ≜
    ∧ txs[tx].status = "Reading"
    ∧ txs[tx].rw.read = DOMAIN txs[tx].read
    ∧ txs' = [ txs EXCEPT
                    ![tx].status = "Committing",
                    ![tx].startCommitTs = TTNow.latest ]
    ∧ UNCHANGED ⟨ps⟩

\* prepare non-leader participant
Prepare(tx, key) ≜
    ∧ txs[tx].status = "Committing"
    ∧ txs[tx].coLeader ≠ key
    ∧ key ∈ DOMAIN txs[tx].rw.write
    ∧ ps[key].lock = None ∨ ps[key].lock = tx
    ∧ ps[key].prepared = None
    ∧ LET ts ≜ Max({ps[key].lastTs, TTNow.latest})
      IN ps' = [ ps EXCEPT ![key].lock = tx,
                           ![key].lastTs = ts,
                           ![key].prepared = [ ts ↦ ts
                                             , value ↦ txs[tx].rw.write[key] ]
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
    ∧ key ∈ DOMAIN txs[tx].rw.write
    ∧ ps[key].lock = None ∨ ps[key].lock = tx
    \* all non-leader participants have prepared
    ∧ ∀p ∈ DOMAIN txs[tx].rw.write \ { key }:
        ∧ ps[p].lock = tx
        ∧ ps[p].prepared ≠ None
    ∧ LET nonLeaderPs ≜ DOMAIN txs[tx].rw.write \ { key }
          maxPreparedTs ≜ IF nonLeaderPs = {}
                          THEN -1
                          ELSE Max({ ps[x].prepared.ts : x ∈ nonLeaderPs })
          commitTs ≜ Max({ maxPreparedTs
                         , txs[tx].startCommitTs + 1
                         , ps[key].lastTs
                         })
      IN ∧ ps' = [ ps EXCEPT ![key].lock = tx,
                             ![key].lastTs = commitTs,
                             ![key].prepared = [ ts ↦ commitTs
                                               , value ↦ txs[tx].rw.write[key] ]
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

TTAdvanceForTxLiveness ≜ ∃tx ∈ DOMAIN txs:
    \* read-only transaction
    ∨ ∧ txs[tx].status = "Reading"
      ∧ txs[tx].rw.write = ⟨⟩
      ∧ txs[tx].startCommitTs ≠ None
      ∧ ¬ TTAfter(txs[tx].startCommitTs)
      ∧ TTEventNext
    \* read-write Transaction
    ∨ ∧ txs[tx].status = "CommitWaiting"
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
      THEN ps' = [ ps EXCEPT
                    ![key].lock = None,
                    ![key].lastTs = txs[tx].commitTs
                 ]
      ELSE ps' = [ ps EXCEPT
                    ![key].lock = None,
                    ![key].lastTs = txs[tx].commitTs,
                    ![key].prepared = None,
                    ![key].data = Append(@, [ ts ↦  txs[tx].commitTs
                                            , value ↦ ps[key].prepared.value] ) ]
    ∧ UNCHANGED ⟨txs⟩

CheckTSafe(key, ts) ≜
    IF ps[key].prepared = None
    THEN ts ≤ Max({TTNow.earliest, ps[key].lastTs})
    (* since we re-use the prepared filed in the coordinator leader,
        the ps[key].prepared.ts could be the commit timestamp,
        so ts is not valid if it equals the prepared timestamp.
    *)
    ELSE ts < ps[key].prepared.ts

ReadValue(key, ts) ≜
    LET data ≜ ps[key].data
        lts ≜ { idx ∈ DOMAIN data: data[idx].ts ≤ ts }
    IN IF ps[key].data = ⟨⟩ ∨ lts = {}
       THEN InitValue[key]
       ELSE data[Max(lts)].value

RoTxStart(tx) ≜
    ∧ txs[tx].status = "Reading"
    ∧ txs[tx].rw.write = ⟨⟩
    ∧ txs[tx].startCommitTs = None
    ∧ txs' = [ txs EXCEPT ![tx].startCommitTs = TTNow.latest ]
    ∧ UNCHANGED ⟨ps⟩

RoTxRead(tx) ≜
    ∧ txs[tx].status = "Reading"
    ∧ txs[tx].rw.write = ⟨⟩
    ∧ txs[tx].read = ⟨⟩
    ∧ txs[tx].startCommitTs ≠ None
    ∧ ∀key ∈ txs[tx].rw.read: CheckTSafe(key, txs[tx].startCommitTs)
    ∧ txs' = [ txs EXCEPT
                ![tx].read = [ k ∈ txs[tx].rw.read
                                    ↦ ReadValue(k, txs[tx].startCommitTs) ],
                ![tx].status = "Committed",
                ![tx].commitTs = txs[tx].startCommitTs
             ]
    ∧ UNCHANGED ⟨ps⟩

(* tx: transaction name/id
   rw: the definition of tx
 *)
TxInit(tx, rw) ≜
    [ status ↦  "Reading"
    , coLeader ↦ SafeChoose(DOMAIN rw.write) \* Coordinator Leader(Participant)
    , rw ↦ rw
    , read ↦ ⟨⟩
    , startCommitTs↦ None
    , commitTs ↦ None
    ]

Init ≜
    ∧ TTInit
    ∧ ∃def ∈ TxDefs: txs = [ tx ∈ DOMAIN def ↦ TxInit(tx, def[tx]) ]
    ∧ ps = [ p ∈ Key  ↦ 
                [ data ↦ ⟨⟩
                , lock ↦ None
                , prepared ↦ None
                (* paxos monotonical timestamp, we don't show the S_max
                    constraint here by simply assuming S_max will be big enough,
                    because it is a implemetation detail in paxos replication layer.
                *)
                , lastTs ↦ TTNow.earliest
                ] ]


TxNext ≜
    ∃tx ∈ DOMAIN txs:
        IF txs[tx].rw.write = ⟨⟩
        \* Read-Only
        THEN ∨ RoTxStart(tx)
             ∨ RoTxRead(tx)
        \* Read-Write
        ELSE ∨ StartCommit(tx)
             ∨ Commit(tx)
             ∨ ∃key ∈ Key:
                 ∨ Read(tx, key)
                 ∨ AvoidDeadlock(tx, key)
                 ∨ Prepare(tx, key)
                 ∨ PrepareCoLeader(tx, key)
                 ∨ CleanAborted(tx, key)
                 ∨ CleanCommitted(tx, key)

Done ≜
    ∧ ∀tx ∈ DOMAIN txs: txs[tx].status ∈ { "Committed", "Aborted" }
    ∧ ∀key ∈ Key: ps[key].lock = None

Next ≜
    ∨ ∧ TxNext
      ∧ UNCHANGED ⟨ttAbs, ttDrift, ttSi⟩
    ∨ ∧ TTAdvanceForTxLiveness
      ∧ UNCHANGED ⟨txs, ps⟩
    ∨ ∧ TTNext
      ∧ UNCHANGED ⟨txs, ps⟩

============================================================
