-------------------------------- MODULE Percolator ----------------------------
EXTENDS Integers, TLC, FiniteSets, Sequence

-----------------------------------------------------------------------------
CONSTANT Key, Client
CONSTANT None
CONSTANT InitValue, Tx, TxOp

VARIABLE next_ts
VARIABLE rows
VARIABLE txs

-----------------------------------------------------------------------------
\* Utils
\* MaxUnder_(s, )
\* 
\* MaxUnder(s, )

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
    ¬ ∃v ∈ DOMAIN rows[k]:
        ∧ v < ts
        ∧ r[v].lock ≠ None

ReadKey(key, ts) ≜
    LET lt_ts(x) ≜ x < ts
        SelectSeq(rows[key], )
    CHOOSE 

ReadKeys(keys, ts) ≜
    IF ∀k ∈ keys: CanRead(k, ts)
    THEN [ CHOOSE v ∈  : k ∈ keys ]
    ELSE None

Get(tx) ≜
    ∧ txs[tx].status = "started"
    \* check whether exists lock
    ∧ 

-----------------------------------------------------------------------------

\* TypeOK ≜
\*     ∧ oracle ∈ Nat

InitRow ≜
    ⟨[ data ↦ InitValue
     , lock ↦ None
     , write ↦ None
     ]
    ⟩

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
