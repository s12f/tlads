-------------------------------- MODULE MC_SIB_SNAPSHOT ----------------------------
EXTENDS Integers, TLC, FiniteSets

-----------------------------------------------------------------------------
CONSTANT None

VARIABLE next_ts
VARIABLE rows
VARIABLE txs

Key ≜ {"k1", "k2", "k3"}
Tx ≜ {"t1", "t2", "t3"}
Value ≜ {0, 1, 2}

InitValue ≜ 0

TxOp ≜
    [ t1 ↦ [ read ↦ { "k1" },
             write ↦  [ r ∈ [ {"k1"} → Value ] ↦ [ k2 ↦ 1 ]]]
    , t2 ↦ [ read ↦ { "k2" },
             write ↦  [ r ∈ [ {"k2"} → Value ] ↦ [ k1 ↦ 2 ]]]
    , t3 ↦ [ read ↦ { "k2", "k3" },
             write ↦  [ r ∈ [ {"k2", "k3"} → Value ] ↦ [ k1 ↦ 0, k2 ↦ 2 ]]]
    ]

INSTANCE Percolator

-----------------------------------------------------------------------
SI ≜ INSTANCE SIB_ISOLATION

MapTx(tid, tx) ≜
    LET write ≜ IF tx.status = "committed" THEN tx.write ELSE ⟨⟩
    IN [ tid ↦ tid, read ↦ tx.read, write ↦ write]

MappedTxs ≜ { MapTx(tx, txs[tx]) : tx ∈ DOMAIN txs }
InitState ≜ [ k1 ↦ InitValue, k2 ↦ InitValue, k3 ↦InitValue ]

AllTxsDone ≜ ∀tx ∈ Tx: txs[tx].status ∈ { "committed", "aborted" }

SnapshotInv ≜ AllTxsDone ⇒
    ∧ SI!SnapshotIsolation(InitState, MappedTxs)
    ∧ SI!ReadCommittedIsolation(InitState, MappedTxs)
    \* SerializableIsolation will fail, Because exists write skew executions
    \* ∧ SI!SerializableIsolation(InitState, MappedTxs)

============================================================================
