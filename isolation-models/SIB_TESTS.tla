--------------------- MODULE SIB_TESTS ------------------

SI ≜ INSTANCE SIB_ISOLATION

\* Write Skew
init ≜ [ k1 ↦ 0, k2 ↦ 0, k3 ↦ 0 ]

txs ≜
    { [ tid ↦ "t1", read ↦ [ k1 ↦ 0 ], write ↦ [ k2 ↦ 1 ] ]
    , [ tid ↦ "t2", read ↦ [ k2 ↦ 0 ], write ↦ [ k1 ↦ 1 ] ]
    }

ASSUME SI!ParallelSnapshotIsolation(init, txs)
ASSUME SI!SnapshotIsolation(init, txs)
ASSUME ¬ SI!SerializableIsolation(init, txs)

\* StrictSerializableExecution Tests1
\* failed_sser_init == [ k1 |-> 0, k2 |-> 0 ]
failed_sser_txs ≜
    { [ tid ↦ "t1", read ↦ [ k1 ↦ 0], write ↦ [k1 ↦ 1], startTs ↦ 0, commitTs ↦ 1]
    , [ tid ↦ "t2", read ↦ [ k1 ↦ 1, k2 ↦ 0], write ↦ ⟨⟩, startTs ↦ 4, commitTs ↦ 5]
    , [ tid ↦ "t3", read ↦ [ k2 ↦ 0], write ↦ [k2 ↦ 1], startTs ↦ 2, commitTs ↦ 3]
    }

ASSUME SI!SerializableIsolation(init, failed_sser_txs)
ASSUME ¬ SI!StrictSerializableIsolation(init, failed_sser_txs)

\* Partial Read
pr_txs ≜
    { [ tid ↦ "t1", read ↦ ⟨⟩, write ↦ [k1 ↦ 1, k2 ↦ 1]]
    , [ tid ↦ "t2", read ↦ [k1 ↦ 1, k2 ↦ 0], write ↦ ⟨⟩]
    }

ASSUME SI!ReadCommittedIsolation(init, pr_txs)
ASSUME ¬ SI!ReadAtomicIsolation(init, pr_txs)
ASSUME ¬ SI!ParallelSnapshotIsolation(init, pr_txs)

\* Write Conflict(Lost Update)
wc_txs ≜
    { [ tid ↦ "t1", read ↦ [k1 ↦ 0], write ↦ [k1 ↦ 1]]
    , [ tid ↦ "t2", read ↦ [k1 ↦ 0], write ↦ [k1 ↦ 2]]
    }

ASSUME SI!ReadAtomicIsolation(init, wc_txs)
ASSUME ¬ SI!ParallelSnapshotIsolation(init, wc_txs)

======================================================
