--------------- MODULE MC ---------------

CONSTANT Value, Acceptor, Quorum, Ballot, Seq, Proposer, None

VARIABLE msgs,
         proposerStates,
         acceptorStates,
         committed

INSTANCE MultiPaxos

Constraint ≜
    ∧ ∀p ∈ Proposer: proposerStates[p].nextSeq ∈ Seq

Symmetry ≜ Permutations(Acceptor)
    ∪ Permutations(Proposer)
    ∪ Permutations(Value)

===============================================
