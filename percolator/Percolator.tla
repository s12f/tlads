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
Max(s) ≜ CHOOSE x ∈ s: ∀y ∈ s: x ≥ y

\* Utils
MaxUnder(s, ts) ≜ Max({ x ∈ s : x < ts })

\* Delete a key in the Function/Dictionary
DeleteKey(d, key) ≜
    [ k ∈ DOMAIN d \ {key} ↦ d[k] ]

\* SafeChoose(s) ≜
\*     IF s = {}
\*     THEN None
\*     ELSE CHOOSE x ∈ s: TRUE

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

StartPreWrite(tx) ≜ 
    LET read ≜ txs[tx].read
        \* Compute All Writes
        write ≜ TxOp[tx].write[read]
        write_keys ≜ DOMAIN write
    IN ∧ IF write_keys = {}
         \* Read Only Transaction, Commit it directly
         THEN txs' = [ txs EXCEPT ![tx].status = "committed" ]
         \* Start PreWrite
         ELSE txs' = [ txs EXCEPT
                        ![tx].status = "prewriting",
                        ![tx].write = write,
                        ![tx].primary = CHOOSE w ∈ write_keys: TRUE,
                        ![tx].pending_write = write_keys,
                        ![tx].pending_commit = write_keys ]
       ∧ UNCHANGED ⟨rows, next_ts⟩

Get(tx) ≜
    ∧ txs[tx].status = "started"
    ∧ LET ts ≜ txs[tx].start_ts
          read ≜ txs[tx].read
          pending_read ≜ { k ∈ DOMAIN read: read[k] = None }
      IN IF pending_read = {}
         THEN StartPreWrite(tx)
         ELSE ∃k ∈ pending_read:
                \* check whether exists lock
                ∧ CanRead(k, ts)
                ∧ txs' = [ txs EXCEPT
                            ![tx].read = k :> ReadKey(k, txs[tx].start_ts) @@ @ ]
                ∧ UNCHANGED ⟨next_ts, rows⟩

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
    ∧ UNCHANGED ⟨next_ts⟩

Commit(tx) ≜
    ∧ txs[tx].status = "committing"
    ∧ LET primary ≜ txs[tx].primary
          start_ts ≜ txs[tx].start_ts
          commit_ts ≜ txs[tx].commit_ts
      IN IF LockIsValid(primary, start_ts)
         THEN CommitPrimary(tx, primary, start_ts, commit_ts)
         ELSE Abort(tx)

Unlock(k, ts) ≜
    ∧ rows' = [ rows EXCEPT
                ![k].data = DeleteKey(@, ts),
                ![k].lock = DeleteKey(@, ts) ]

Recover ≜ ∃k ∈ Key:
    ∧ rows[k].lock ≠ ⟨⟩
    ∧ LET start_ts ≜ CHOOSE l ∈ DOMAIN rows[k].lock: TRUE
          primary ≜ rows[k].lock[start_ts]
          cts ≜ { v ∈ DOMAIN rows[primary].write : rows[primary].write[v] = start_ts }
      IN IF start_ts ∈ DOMAIN rows[primary].lock
         \* Unlock primary row first
         THEN Unlock(primary, start_ts)
         ELSE IF cts = {}
              THEN Unlock(k, start_ts)
              ELSE ∃commit_ts ∈ cts: CommitKey(k, start_ts, commit_ts)
    ∧ UNCHANGED ⟨next_ts, txs⟩

Done ≜
    ∧ ∀tx ∈ Tx: txs[tx].status ∈ { "committed", "aborted" }
    ∧ UNCHANGED ⟨next_ts, rows, txs⟩

-----------------------------------------------------------------------------

InitRow ≜
    [ data ↦ 0 :> InitValue
    , lock ↦ ⟨⟩
    , write ↦ 1 :> 0
    ]

TxStatus ≜ { "pending", "started", "prewriting", "committing", "committed", "aborted" }

InitTx ≜
    [ status ↦ "pending"
    , start_ts ↦ None
    , commit_ts ↦ None
    , read ↦ ⟨⟩
    , write ↦ ⟨⟩
    , primary ↦ None
    , pending_write ↦ {}
    , pending_commit ↦ {}
    ]

Init ≜
    ∧ next_ts = 2
    ∧ rows = [ k ∈ Key ↦ InitRow ]
    ∧ txs = [ tx ∈ Tx ↦ InitTx ]

ClientAction ≜ ∃tx ∈ Tx:
    ∨ Start(tx)
    ∨ Get(tx)
    ∨ PreWrite(tx)
    ∨ Commit(tx)
    ∨ CommitSecondaries(tx)

Next ≜
    ∨ ClientAction
    ∨ Recover
    ∨ Done

Spec ≜ Init ∧ □[Next]_⟨next_ts, rows, txs⟩

TypeOK ≜
    ∧ next_ts ∈ Nat
    ∧ ∀tx ∈ Tx: txs[tx].status ∈ TxStatus

Inv ≜ TypeOK

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
