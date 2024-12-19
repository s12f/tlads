-------------------------------- MODULE PaxosEb0 ----------------------------
EXTENDS Integers, TLC, FiniteSets

-----------------------------------------------------------------------------
CONSTANT Value, Acceptor, Ballot, None

ASSUME AcceptorSize ≜ Cardinality(Acceptor) ≥ 3

Qc ≜ { s ∈ SUBSET(Acceptor): Cardinality(s) = Cardinality(Acceptor) ÷ 2 + 1 }
      
\* Message Type(Set)
Message ≜ [type : {"1a"}, bal : Ballot]
        ∪ [type : {"1b"}, acc : Acceptor, bal : Ballot, 
              mbal : Ballot ∪ {-1}, mval : Value ∪ {None}]
        ∪ [type : {"2a"}, bal : Ballot, val : Value]
        ∪ [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]

\* Acceptor State
AState ≜
    [ id: Acceptor
    , maxBal: Ballot ∪ {-1}
    , maxVBal: Ballot ∪ {-1}
    , maxVal: Value ∪ {None}
    ]

-----------------------------------------------------------------------------
\* Utils
MaxBy(S, n) ≜ CHOOSE x ∈ S: ∀xx ∈ S: x[n] ≥ xx[n]

-----------------------------------------------------------------------------

\* Acceptor → AState
VARIABLE aStates
VARIABLE msgs
\* all committed values
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

Phase2a(b) ≜
  ∧ ¬ ∃m ∈ msgs : m.type = "2a" ∧ m.bal = b
  ∧ LET ms ≜ {m ∈ msgs : m.type = "1b" ∧ m.bal = b }
    IN ∧ ms ≠ {}
       ∧ ∃Q ∈ Qc: ∀a ∈ Q: ∃mm ∈ ms: mm.acc = a
       ∧ LET m ≜ MaxBy(ms, "mbal")
         IN ∨ ∧ m.mbal = -1
              ∧ ∃v ∈ Value: Send([type ↦ "2a", bal ↦ b, val ↦ v])
            ∨ ∧ m.mbal ≥ 0
              ∧ Send([type ↦ "2a", bal ↦ b, val ↦ m.mval])
  ∧ UNCHANGED ⟨aStates, committed⟩

FastPhase2a(v) ≜
  ∧ ¬ ∃ m ∈ msgs: m.type = "2a" ∧ m.bal = 0
  ∧ Send([type ↦ "2a", bal ↦ 0, val ↦ v])
  ∧ UNCHANGED ⟨aStates, committed⟩
  
Phase2b(a) ≜ ∃m ∈ msgs:
    ∧ m.type = "2a"
    ∧ m.bal ≥ a.maxBal
    ∧ aStates' = [ aStates EXCEPT ![a.id] =
        [ id ↦ a.id, maxBal ↦ m.bal, maxVBal ↦ m.bal, maxVal ↦ m.val] ]
    ∧ Send([type ↦ "2b", acc ↦ a.id, bal ↦ m.bal, val ↦ m.val]) 
    ∧ UNCHANGED ⟨committed⟩

Commit ≜ ∃b ∈ Ballot, v ∈ Value:
    ∧ v ∉ committed
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
       ∨ Commit

Spec ≜ Init ∧ □[Next]_vars
----------------------------------------------------------------------------

Inv ≜ ∧ TypeOK
      ∧ ∀ v1 ∈ committed, v2 ∈ committed: v1 = v2
============================================================================
