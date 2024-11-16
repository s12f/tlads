-------------------------------- MODULE Percolator ----------------------------
EXTENDS Integers, TLC, FiniteSets

-----------------------------------------------------------------------------
CONSTANT Key
CONSTANT None
CONSTANT InitValue
CONSTANT Tx
CONSTANT TxOp

VARIABLE next_ts
VARIABLE rows
VARIABLE txs

-----------------------------------------------------------------------------
\* Utils
MaxUnder(s, ts) ≜
    CHOOSE x ∈ s:
        ∧ x < ts
        ∧ ∀y ∈ s: x ≥ y

\* Delete a key in the Function/Dictionary
DeleteKey(d, key) ≜
    [ k ∈ DOMAIN d \ {key} ↦ d[k] ]

-----------------------------------------------------------------------------
\* Transaction
Start(tx) ≜
    ∧ txs[tx].status = "pending"
    ∧ next_ts' = next_ts + 1
    ∧ txs' = [ txs EXCEPT
                ![tx].start_ts = next_ts,
                ![tx].status = "started",
                ![tx].read = [ k ∈ TxOp[tx].read ↦ None ]
            ]
    ∧ UNCHANGED ⟨rows⟩

CanRead(k, ts) ≜ 
    ¬ ∃v ∈ DOMAIN rows[k].lock: v < ts

ReadKey(key, ts) ≜ 
    LET data ≜ rows[key].data
        max_before_ts ≜ MaxUnder(DOMAIN data, ts)
    IN data[max_before_ts]

Get(tx) ≜
    ∧ txs[tx].status = "started"
    \* check whether exists lock
    ∧ ∀k ∈ TxOp.read: CanRead(k, txs[tx].start_ts)
    ∧ LET read ≜ [ key ∈ TxOp.read ↦ ReadKey(key, txs[tx].start_ts) ]
          write ≜ TxOp[tx].write[read]
          primary ≜ CHOOSE w ∈ DOMAIN write: TRUE
      IN ∧ txs' = [ txs EXCEPT
                    ![tx].status = "prewriting",
                    ![tx].read = read,
                    ![tx].write = write,
                    ![tx].primary = primary,
                    ![tx].pending_write = DOMAIN write,
                    ![tx].pending_commit = DOMAIN write ]
         ∧ UNCHANGED ⟨rows, next_ts⟩

CanLock(row, ts) ≜
    ∧ ¬ ∃v ∈ DOMAIN row.write: v > ts
    ∧ DOMAIN row.lock = {}

Lock(tx, key, data, primary, ts) ≜ 
    ∧ rows' = [ rows EXCEPT
                ![key].lock = @ @@ ts :> primary,
                ![key].data = @ @@ ts :> data ]
    ∧ txs' = [ txs EXCEPT ![tx].pending_write = @ \ { key } ]
    ∧ UNCHANGED ⟨next_ts⟩

StartCommit(tx) ≜ 
    ∧ txs' = [ txs EXCEPT
                ![tx].status = "committing",
                ![tx].commit_ts = next_ts ]
    ∧ next_ts' = next_ts + 1
    ∧ UNCHANGED ⟨rows⟩

Abort(tx) ≜
    ∧ txs' = [ txs EXCEPT ![tx].status = "aborted" ]
    \* TODO: clean locks
    ∧ UNCHANGED ⟨rows, next_ts⟩

PreWrite(tx) ≜
    ∧ txs[tx].status = "prewriting"
    ∧ IF txs[tx].pending_write = {}
      THEN StartCommit(tx)
      ELSE LET key ≜ CHOOSE key ∈ txs[tx].pending_write: TRUE
               data ≜ txs[tx].write[key]
               primary ≜ txs[tx].primary
               ts ≜ txs[tx].start_ts
           IN IF CanLock(rows[key], ts)
              THEN Lock(tx, key, data, primary, ts)
              ELSE Abort(tx)

LockIsValid(key, ts) ≜ ts ∈ DOMAIN rows[key].lock

CommitKey(key, start_ts, commit_ts) ≜
    ∧ rows' = [ rows EXCEPT 
               ![key].write = @ @@ commit_ts :> start_ts,
               ![key].lock = DeleteKey(@, start_ts) ]

CommitPrimary(tx, primary, start_ts, commit_ts) ≜
    ∧ CommitKey(primary, start_ts, commit_ts)
    ∧ txs' = [ txs EXCEPT
                    ![tx].status = "committed",
                    ![tx].pending_commit = @ \ { primary } ]
    ∧ UNCHANGED ⟨next_ts⟩

CommitSecondaries(tx) ≜
    ∧ txs[tx].status = "committed"
    ∧ txs[tx].pending_commit ≠ {}
    ∧ LET primary ≜ txs[tx].primary
          start_ts ≜ txs[tx].start_ts
          commit_ts ≜ txs[tx].commit_ts
      IN ∧ ∀key ∈ txs[tx].pending_commit: CommitKey(key, start_ts, commit_ts)
         ∧ txs' = [ txs EXCEPT ![tx].pending_commit = {} ]

Commit(tx) ≜
    ∧ txs[tx].status = "committing"
    ∧ LET primary ≜ txs[tx].primary
          start_ts ≜ txs[tx].start_ts
          commit_ts ≜ txs[tx].commit_ts
      IN IF LockIsValid(primary, start_ts)
         THEN CommitPrimary(tx, primary, start_ts, commit_ts)
         ELSE Abort(tx)

-----------------------------------------------------------------------------

InitRow ≜
    [ data ↦ 0 :> InitValue
    , lock ↦ ⟨⟩
    , write ↦ ⟨⟩
    ]

TxStatus ≜ { "pending", "started", "prewriting", "committing", "committed", "aborted" }

InitTx ≜
    [ status ↦ "pending"
    , start_ts ↦ None
    , commit_ts ↦ None
    , read ↦ None
    , write ↦ None
    , primary ↦ None
    , pending_write ↦ None
    , pending_commit ↦ None
    ]

Init ≜
    ∧ PrintT(Key)
    ∧ next_ts = 1
    ∧ rows = [ k ∈ Key ↦ InitRow ]
    ∧ txs = [ tx ∈ Tx ↦ InitTx ]

Next ≜ ∃tx ∈ Tx:
    ∧ Start(tx)
    ∧ Get(tx)
    ∧ PreWrite(tx)
    ∧ Commit(tx)

Spec ≜ Init ∧ □[Next]_⟨next_ts, rows, txs⟩

Inv ≜ TRUE

\* Inv ≜
\*     ∧ Atomicity
\*     \* write Consistency
\*     \* read Consistency
\*     ∧ Consistency
\*     ∧ TxConsistency
\*     ∧ SnapshotIsolation
\*     ∧ ReadCommitted
\*     \* crash after committing
\*     ∧ Durability

============================================================================
