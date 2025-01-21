-------------------- MODULE DisjointLeases --------------------

EXTENDS Integers, TLC, FiniteSets

--------------------------------------------------------
\* import TrueTime Module
CONSTANTS TTInitAbs, TTMaxSi, TTInterval
VARIABLES ttAbs, ttDrift, ttSi
INSTANCE TrueTime
TTVars ≜ ⟨ttAbs, ttDrift, ttSi⟩

--------------------------------------------------------
CONSTANTS Replica, LeaderInterval

\* Majority
Quorum ≜ { s ∈ SUBSET(Replica): Cardinality(s) = Cardinality(Replica) ÷ 2 + 1 }

\* variables
VARIABLES states, msgs, intervals

Leader ≜ "Leader"
Backup ≜ "Backup"

Vote(r) ≜
    ∧ states[r].role = Backup
    ∧ TTAfter(states[r].end)
    ∧ states' = [ states EXCEPT ![r].end = TTNow.latest + LeaderInterval ]
    ∧ msgs' = msgs ∪ {[ type ↦ "Vote"
                      , end ↦ TTNow.latest + LeaderInterval
                      , voter ↦ r ]}
    ∧ UNCHANGED ⟨intervals⟩

HandleVote(r) ≜
    ∧ states[r].role = Backup
    ∧ TTAfter(states[r].end)
    ∧ ∃m ∈ msgs:
        ∧ m.type = "Vote"
        ∧ states' = [ states EXCEPT ![r].end = TTNow.latest + LeaderInterval ]
        ∧ msgs' = msgs ∪ {[ type ↦ "Grant"
                          , end ↦ m.end
                          , voter ↦  m.voter
                          , acceptor ↦ r ]}
    ∧ UNCHANGED ⟨intervals⟩

BecomeLeader(r) ≜
    ∧ states[r].role = Backup
    ∧ ¬ TTAfter(states[r].end)
    ∧ ∃Q ∈ Quorum: ∀a ∈ Q: ∃m ∈ msgs:
        ∧ m.type = "Grant"
        ∧ m.voter = r
        ∧ m.acceptor = a
        ∧ m.end = states[r].end
        ∧ states' = [ states EXCEPT ![r].role = Leader ]
        ∧ intervals' = intervals ∪ {[ leader ↦ r
                                    , start ↦ m.end - LeaderInterval
                                    , end ↦ m.end ]}
    ∧ UNCHANGED ⟨msgs⟩

BecomeBackup(r) ≜
    ∧ states[r].role = Leader
    ∧ TTAfter(states[r].end)
    ∧ states' = [ states EXCEPT ![r].role = Backup ]
    ∧ UNCHANGED ⟨msgs, intervals⟩

Init ≜
    ∧ TTInit
    ∧ states =
        [ r ∈ Replica ↦ 
            [ role ↦ Backup
            , end ↦ 0
            ]
        ]
    ∧ msgs = {}
    ∧ intervals = {}

Next ≜
    ∨ ∧ TTNext
      ∧ UNCHANGED ⟨states, msgs, intervals⟩
    ∨ ∧ ∃r ∈ Replica:
            ∨ Vote(r)
            ∨ HandleVote(r)
            ∨ BecomeLeader(r)
            ∨ BecomeBackup(r)
      ∧ UNCHANGED ⟨TTVars⟩

Spec ≜ Init ∧ □[Next]_⟨TTVars, states, msgs, intervals⟩

--------------------------------------------------------

Disjointness ≜
    ∀i1, i2 ∈ intervals:
        ∧ i1.start < i2.start ⇒ i1.end < i2.start

========================================================
