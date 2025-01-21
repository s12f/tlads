-------------------- MODULE RwTest --------------------

CONSTANTS TTInitAbs, TTMaxSi, TTInterval
VARIABLES ttAbs, ttDrift, ttSi

CONSTANTS None
VARIABLES txs, ps

Key ≜ { "k1", "k2" }
InitValue ≜ [ k1 ↦ 0, k2 ↦ 0 ]
TxDef ≜ ⟨ [ read ↦ { "k1" }, write ↦ [ k2 ↦ 1 ] ]
        , [ read ↦ { "k2" }, write ↦ [ k1 ↦ 2 ] ]
        ⟩

INSTANCE Transaction

Fairness ≜
    ∧ WF_⟨txs, ps⟩(TxNext)
    \* ∧ SF_⟨ttAbs⟩(TTNextAbs)

Spec ≜ Init ∧ □[Next]_⟨ttAbs, ttDrift, ttSi, txs, ps⟩ ∧ Fairness

MapTx(tx) ≜ 
    [ id ↦ tx
    , read ↦ txs[tx].read
    , write ↦ TxDef[tx].write
    , startTs ↦ txs[tx].commitTs
    , commitTs ↦ txs[tx].commitTs
    ]

committed_txs ≜  { tx ∈ DOMAIN TxDef: txs[tx].status = "Committed" }

mapped_txs ≜ { MapTx(tx) : tx ∈ committed_txs }

SIB ≜ INSTANCE SIB_ISOLATION

StrictSerializability ≜
    Done ⇒  \* ∧ PrintT(txs) ∧ PrintT(ttAbs)
            ∧ SIB!StrictSerializableIsolation(InitValue, mapped_txs)

Properties ≜ ◇(Done)

=======================================================
