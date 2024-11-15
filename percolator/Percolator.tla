-------------------------------- MODULE Percolator ----------------------------
EXTENDS Integers, TLC, FiniteSets

-----------------------------------------------------------------------------
CONSTANT Key, Client
CONSTANT None
CONSTANT InitValue, Tx, TxOp

VARIABLE next_ts
VARIABLE rows
VARIABLE txs

-----------------------------------------------------------------------------
\* Utils
MaxUnder(s, ts) ≜
    CHOOSE x ∈ s:
        ∧ x < ts
        ∧ ∀y ∈ s: x ≥ y

-----------------------------------------------------------------------------
\* Transaction
Start(tx) ≜
    ∧ txs[tx].status = "pending"
    ∧ next_ts' = next_ts
    ∧ txs' = [ txs EXCEPT
        ![tx].start_ts = next_ts + 1,
        ![tx].status = "started"
        ![tx].read = [ k ∈ TxOp[tx].keys ↦ None ] ]
    ∧ UNCHANGED ⟨rows⟩

CanRead(k, ts) ≜ 
    ¬ ∃v ∈ DOMAIN rows[k].lock:
        ∧ v ≤ ts
        ∧ r[v].lock ≠ None

ReadKey(key, ts) ≜ 
    LET data ≜ rows[key].data
        max_before_ts ≜ MaxUnder(DOMAIN data, ts)
    IN data[max_before_ts]

ReadKeys(keys, ts) ≜
    IF ∀k ∈ keys: CanRead(k, ts)
    THEN [ key ∈ keys ↦ ReadKey(key, ts) ]
    ELSE None

\* Get(tx) ≜
\*     ∧ txs[tx].status = "started"
\*     \* check whether exists lock
\*     ∧ 

-----------------------------------------------------------------------------

\* TypeOK ≜
\*     ∧ oracle ∈ Nat

InitRow ≜
    [ data ↦ 0 :> InitValue
    , lock ↦ 0 :> None
    , write ↦ 0 :> None
    ]
    

TxStatus ≜ { "pending", "started", "prewriting", "committing", "committed", "aborted" }

InitTx ≜
    [ status ↦ "pending"
    , start_ts ↦ None
    , read ↦ None
    , write ↦ None
    ]

Init ≜
    ∧ oracle = 0
    ∧ rows = [ k ∈ Key ↦ InitRow ]
    ∧ ts = [ c ∈ Client ↦ InitTx ]

Next ≜ ∃tx ∈ Tx,
    ∧ Start(tx)
    ∧ Get(tx)
    ∧ PreWrite(tx)
    ∧ Commit(tx)

Inv ≜
    ∧ TypeOK
    ∧ Atomicity
    \* write Consistency
    \* read Consistency
    ∧ Consistency
    ∧ TxConsistency
    ∧ SnapshotIsolation
    ∧ ReadCommitted
    \* crash after committing
    ∧ Durability

============================================================================
