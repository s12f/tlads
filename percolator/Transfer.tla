-------------------------------- MODULE Transfer ----------------------------
EXTENDS Integers, TLC, FiniteSets

-----------------------------------------------------------------------------
CONSTANT None

VARIABLE next_ts
VARIABLE rows
VARIABLE txs

Key ≜ {"k1", "k2", "k3"}
InitValue ≜ 10
Tx ≜ {"t1", "t2"}
TransferWrite(read) ≜ 
    LET read_keys ≜ DOMAIN read
        s ≜ CHOOSE k ∈ read_keys: TRUE
        r ≜ CHOOSE k ∈ read_keys: k ≠ s
    IN s :> read[s] - 1 @@ r :> read[r] + 1

TransferTx(keys) ≜ 
    [ read ↦ keys
    , write ↦ [ read ∈ [keys → 8‥12] ↦ TransferWrite(read)]
    ]

TxOp ≜
    [ t1 ↦ TransferTx({"k1", "k2"})
    , t2 ↦ TransferTx({"k2", "k3"})
    ]

INSTANCE Percolator

AtomicRead ≜
    ∨ ∃k ∈ Key: ¬ CanRead(k, next_ts)
    ∨ 30 = ReadKey("k1", next_ts)
            + ReadKey("k2", next_ts)
            + ReadKey("k3", next_ts)

TransferInv ≜ AtomicRead

============================================================================
