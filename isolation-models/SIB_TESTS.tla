--------------------- MODULE SIB_TESTS ------------------

init ≜ [ k1 ↦ 0, k2 ↦ 0, k3 ↦ 0 ]

txs ≜
    { [ read ↦ [ k1 ↦ 0 ], write ↦ [ k2 ↦ 1 ] ]
    , [ read ↦ [ k2 ↦ 0 ], write ↦ [ k1 ↦ 1 ] ]
    }

SI ≜ INSTANCE SIB_ISOLATION

ASSUME SI!SnapshotIsolation(init, txs)
ASSUME ¬ SI!SerializableIsolation(init, txs)

======================================================
