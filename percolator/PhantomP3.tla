-------------------------------- MODULE PhantomP3 ----------------------------
EXTENDS Integers, TLC, FiniteSets

-----------------------------------------------------------------------------
CONSTANT None

VARIABLE next_ts
VARIABLE rows
VARIABLE txs

Key ≜ {"k1", "k2"}
Tx ≜ {"t1", "t2"}
InitValue ≜ 10

TransferWrite(read) ≜ 
    LET read_keys ≜ DOMAIN read
        s ≜ CHOOSE k ∈ read_keys: TRUE
        r ≜ CHOOSE k ∈ read_keys: k ≠ s
    IN s :> read[s] - 1 @@ r :> read[r] + 1

TransferTx(keys) ≜ 
    [ read ↦ keys
    , write ↦ [ read ∈ [keys → 8‥12] ↦ TransferWrite(read)]
    ]

ReadOnlyTx(keys) ≜ 
    [ read ↦ keys
    , write ↦ [ read ∈ [keys → 8‥12] ↦ ⟨⟩]
    ]

TxOp ≜
    [ t1 ↦ TransferTx({"k1", "k2"})
    , t2 ↦ ReadOnlyTx({"k1", "k2"})
    ]

INSTANCE Percolator

PhantomP3Inv ≜
    ∨ txs["t2"].status ≠ "committed"
    ∨ LET r ≜ txs["t2"].read
      IN 20 = r["k1"] + r["k2"]

============================================================================
