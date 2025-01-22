-------------------- MODULE TxTest --------------------

CONSTANTS TTInitAbs, TTMaxSi, TTInterval
VARIABLES ttAbs, ttDrift, ttSi

CONSTANTS None
VARIABLES txs, ps

Key ≜ { "k1", "k2", "k3" }
InitValue ≜ [ k1 ↦ 0, k2 ↦ 0, k3 ↦ 0 ]
TxDefs ≜
    { \* non-conflict
     ⟨ [ read ↦ { "k1" }, write ↦ [ k1 ↦ 1 ] ]
     , [ read ↦ { "k2" }, write ↦ [ k2 ↦ 2 ] ]
     ⟩
     , \* write skew
     ⟨ [ read ↦ { "k1" }, write ↦ [ k1 ↦ 1 ] ]
     , [ read ↦ { "k2" }, write ↦ [ k2 ↦ 2 ] ]
     ⟩
     , \* multiple writes and RO transaction
     ⟨ [ read ↦ { "k1" }, write ↦ [ k1 ↦ 1, k2 ↦ 1 ] ]
     , [ read ↦ { "k2" }, write ↦ [ k1 ↦ 2, k2 ↦ 2 ] ]
     , [ read ↦ { "k1", "k2" }, write ↦ ⟨⟩ ]
     ⟩
     , \* circular reference
     ⟨ [ read ↦ { "k1" }, write ↦ [ k2 ↦ 1 ] ]
     , [ read ↦ { "k2" }, write ↦ [ k3 ↦ 2 ] ]
     , [ read ↦ { "k3" }, write ↦ [ k1 ↦ 3 ] ]
     ⟩
    }

INSTANCE Transaction

Fairness ≜
    ∧ WF_⟨txs, ps⟩(TxNext)
    \* ∧ SF_⟨ttAbs⟩(TTNextAbs)

Spec ≜ Init ∧ □[Next]_⟨ttAbs, ttDrift, ttSi, txs, ps⟩ ∧ Fairness

MapTx(tx) ≜ 
    [ id ↦ tx
    , read ↦ txs[tx].read
    , write ↦ txs[tx].rw.write
    , startTs ↦ txs[tx].commitTs
    , commitTs ↦ txs[tx].commitTs
    ]

committed_txs ≜  { tx ∈ DOMAIN txs: txs[tx].status = "Committed" }

mapped_txs ≜ { MapTx(tx) : tx ∈ committed_txs }

SIB ≜ INSTANCE SIB_ISOLATION

StrictSerializability ≜
    Done ⇒  \* ∧ PrintT(txs) ∧ PrintT(ttAbs)
            ∧ SIB!StrictSerializableIsolation(InitValue, mapped_txs)

Properties ≜ ◇(Done)

=======================================================
