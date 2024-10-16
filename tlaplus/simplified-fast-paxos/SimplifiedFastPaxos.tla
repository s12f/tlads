-------------------------------- MODULE SimplifiedFastPaxos -----------------
EXTENDS Integers, TLC, FiniteSets

-----------------------------------------------------------------------------

CONSTANT Value, Acceptor, Ballot, None

ASSUME AcceptorSize ≜ Cardinality(Acceptor) ≥ 3

\* Fast Round Quorum, QfS = 3/4N + 1(N is Size of Acceptor)
Qf ≜ { s ∈ SUBSET(Acceptor): Cardinality(s) = (3 * Cardinality(Acceptor)) ÷ 4 + 1 }

\* Classic Round Quorum, QcS = N/2 + 1(N is Size of Acceptor)
Qc ≜ { s ∈ SUBSET(Acceptor): Cardinality(s) = Cardinality(Acceptor) ÷ 2 + 1 }
      
Message ≜ [type : {"1a"}, bal : Ballot]
        ∪ [type : {"1b"}, acc : Acceptor, bal : Ballot, 
              mbal : Ballot ∪ {-1}, mval : Value ∪ {None}]
        ∪ [type : {"2a"}, bal : Ballot, val : Value]
        ∪ [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]

AState ≜
    [ id: Acceptor
    , maxBal: Ballot ∪ {-1}
    , maxVBal: Ballot ∪ {-1}
    , maxVal: Value ∪ {None}
    ]

-----------------------------------------------------------------------------


\* GroupByKey(S, , rS) ≜ 

-----------------------------------------------------------------------------
VARIABLE aStates
VARIABLE msgs
VARIABLE committed

vars ≜ ⟨aStates, msgs, committed⟩

TypeOK ≜
    ∧ aStates ∈ [ Acceptor → AState ]
    ∧ msgs ⊆ Message
    ∧ committed ⊆ Value

Init ≜ 
    ∧ aStates = [ a ∈ Acceptor ↦
        [ id ↦ a, maxBal ↦ -1, maxVBal ↦ -1, maxVal ↦ None]]
    ∧ msgs = {}
    ∧ committed = {}

Send(m) ≜ msgs' = msgs ∪ {m}

Phase1a(b) ≜
    ∧ Send([type ↦ "1a", bal ↦ b])
    ∧ UNCHANGED ⟨aStates, committed⟩
                 
Phase1b(aState) ≜ ∃m ∈ msgs: 
    ∧ m.type = "1a"
    ∧ m.bal > aState.maxBal
    ∧ aStates' = [ aStates EXCEPT ![aState.id].maxBal = m.bal ]
    ∧ Send([type ↦ "1b", acc ↦ aState.id, bal ↦ m.bal, 
            mbal ↦ aState.maxVBal, mval ↦ aState.maxVal])
    ∧ UNCHANGED ⟨committed⟩

\* Only For Recovery
Phase2a(b) ≜
  ∧ ¬ ∃m ∈ msgs : m.type = "2a" ∧ m.bal = b
  ∧ LET ms ≜ {m ∈ msgs : ∧ m.type = "1b"
                           ∧ m.bal = b }
    IN ∃m ∈ ms:
        ∧ ∀mm ∈ ms: m.mbal ≥ mm.mbal
        ∧ m.mbal ≠ -1 \* Ballot 0 is always Fast Round
        ∧ ∨ ∧ m.mbal > 0 \* Classic Voted Round
            ∧ ∃Q ∈ Qc: ∀a ∈ Q: ∃mm ∈ ms: mm.acc = a
            ∧ Send([type ↦ "2a", bal ↦ b, val ↦ m.mval])
          ∨ ∧ m.mbal = 0 \* Fast Voted Round
            ∧ ∃Q ∈ Qc: ∀a ∈ Q: ∃mm ∈ ms: mm.acc = a
            ∧ LET g ≜ [ v ∈ Value ↦  Cardinality({mm ∈ ms: mm.mval = v}) ]
              IN ∃v ∈ Value:
                    ∧ ∀vv ∈ Value: g[v] ≥ g[vv]
                    ∧ Send([type ↦ "2a", bal ↦ b, val ↦ v])
  ∧ UNCHANGED ⟨aStates, committed⟩

FastPhase2a(v) ≜
  ∧ ¬ ∃ m ∈ msgs: m.type = "2a" ∧ m.bal = 0 ∧ m.val = v
  ∧ Send([type ↦ "2a", bal ↦ 0, val ↦ v])
  ∧ UNCHANGED ⟨aStates, committed⟩
  
Phase2b(a) ≜ ∃m ∈ msgs:
    ∧ m.type = "2a"
    ∧ m.bal ≥ a.maxBal
    ∧ m.bal > a.maxVBal
    ∧ aStates' = [ aStates EXCEPT ![a.id] =
        [ id ↦ a.id, maxBal ↦ m.bal, maxVBal ↦ m.bal, maxVal ↦ m.val] ]
    ∧ Send([type ↦ "2b", acc ↦ a.id, bal ↦ m.bal, val ↦ m.val]) 
    ∧ UNCHANGED ⟨committed⟩

CommitFastRound ≜ ∃v ∈ Value:
    ∧ v ∉ committed
    ∧ ∃Q ∈ Qf: ∀a ∈ Q: ∃m ∈ msgs:
        ∧ m.type = "2b"
        ∧ m.acc = a
        ∧ m.bal = 0
        ∧ m.val = v
    ∧ committed' = committed ∪ {v}
    ∧ UNCHANGED ⟨aStates, msgs⟩

CommitClassicRound ≜ ∃b ∈ Ballot, v ∈ Value:
    ∧ v ∉ committed
    ∧ b > 0
    ∧ ∃Q ∈ Qc: ∀a ∈ Q: ∃m ∈ msgs:
        ∧ m.type = "2b"
        ∧ m.acc = a
        ∧ m.val = v
        ∧ m.bal = b
    ∧ committed' = committed ∪ {v}
    ∧ UNCHANGED ⟨aStates, msgs⟩

Next ≜ ∨ ∃b ∈ Ballot \ {0} : ∨ Phase1a(b)
                             ∨ Phase2a(b)
       ∨ ∃a ∈ Acceptor: Phase1b(aStates[a]) ∨ Phase2b(aStates[a])
       ∨ ∃v ∈ Value: FastPhase2a(v)
       ∨ CommitFastRound ∨ CommitClassicRound

Spec ≜ Init ∧ □[Next]_vars
----------------------------------------------------------------------------

Inv ≜ ∧ TypeOK
      ∧ ∀ v1 ∈ committed, v2 ∈ committed: v1 = v2
============================================================================
