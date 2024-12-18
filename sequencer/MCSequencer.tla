---- MODULE MCSequencer ----

EXTENDS TLC

CONSTANT None

VARIABLES states, history, storage, nextRid

Servers ≜ {"s1", "s2", "s3"}
BatchSize ≜ 3

INSTANCE Sequencer

Constraint ≜
    ∧ nextRid < 7
    ∧ storage < 7

====