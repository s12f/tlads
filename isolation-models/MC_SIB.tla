--------------------- MODULE MC_SIB ------------------

VARIABLE x

init ≜ [ k1 ↦ 0, k2 ↦ 0, k3 ↦ 0 ]

txs ≜
    { [ read ↦ [ k1 ↦ 0 ], write ↦ [ k2 ↦ 1 ] ]
    , [ read ↦ [ k2 ↦ 0 ], write ↦ [ k1 ↦ 1 ] ]
    }

Init ≜ x = {}
Next ≜ x' = txs
Spec ≜ Init ∧ □[Next]_⟨x⟩

SI ≜ INSTANCE SIB_ISOLATION

Inv ≜ SI!SerializableIsolation(init, x)

======================================================
