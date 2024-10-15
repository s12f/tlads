-------------------------------- MODULE Paxos -------------------------------
EXTENDS Integers, TLC, FiniteSets

-----------------------------------------------------------------------------

CONSTANT Value, Acceptor, Quorum, Ballot

ASSUME AcceptorSize ≜ Cardinality(Acceptor) ≥ 3

\* Fast Round Quorum, QfS = 3/4N + 1(N is Size of Acceptor)
Qf ≜ { s ∈ SUBSET(Acceptor): Cardinality(s) = 3 * Cardinality(Acceptor) ÷ 4 + 1 }

\* Classic Round Quorum, QcS = N/2 + 1(N is Size of Acceptor)
Qc ≜ { s ∈ SUBSET(Acceptor): Cardinality(s) = Cardinality(Acceptor) ÷ 2 + 1 }
      
Message ≜ [type : {"1a"}, bal : Ballot]
        ∪ [type : {"1b"}, acc : Acceptor, bal : Ballot, 
              mbal : Ballot ∪ {-1}, mval : Value ∪ {None}]
        ∪ [type : {"2a"}, bal : Ballot, val : Value]
        ∪ [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]

None ≜ -1

-----------------------------------------------------------------------------
VARIABLE maxBal, 
         maxVBal,   \* <<maxVBal[a], maxVal[a]>> is the vote with the largest
         maxVal,    \* ballot number cast by a; it equals <<-1, None>> if
                    \* a has not cast any vote.
         msgs,      \* The set of all messages that have been sent.
         committed


vars ≜ ⟨maxBal, maxVBal, maxVal, msgs, committed⟩

TypeOK ≜ ∧ maxBal ∈ [Acceptor → Ballot ∪ {-1}]
         ∧ maxVBal ∈ [Acceptor → Ballot ∪ {-1}]
         ∧ maxVal ∈ [Acceptor → Value ∪ {None}]
         ∧ msgs ⊆ Message
         ∧ committed ⊆ Value

Init ≜ ∧ maxBal = [a ∈ Acceptor ↦ -1]
       ∧ maxVBal = [a ∈ Acceptor ↦ -1]
       ∧ maxVal = [a ∈ Acceptor ↦ None]
       ∧ msgs = {}
       ∧ committed = {}

Send(m) ≜ msgs' = msgs ∪ {m}

Phase1a(b) ≜ 
    ∧ Send([type ↦ "1a", bal ↦ b])
    ∧ UNCHANGED ⟨maxBal, maxVBal, maxVal, committed⟩
                 
Phase1b(a) ≜ ∧ ∃ m ∈ msgs : 
                  ∧ m.type = "1a"
                  ∧ m.bal > maxBal[a]
                  ∧ maxBal' = [maxBal EXCEPT ![a] = m.bal]
                  ∧ Send([type ↦ "1b", acc ↦ a, bal ↦ m.bal, 
                            mbal ↦ maxVBal[a], mval ↦ maxVal[a]])
             ∧ UNCHANGED ⟨maxVBal, maxVal, committed⟩

Phase2a(b, v) ≜
  ∧ ¬ ∃ m ∈ msgs : m.type = "2a" ∧ m.bal = b
  ∧ ∃ Q ∈ Quorum :
        LET Q1b ≜ {m ∈ msgs : ∧ m.type = "1b"
                              ∧ m.acc ∈ Q
                              ∧ m.bal = b}
            Q1bv ≜ {m ∈ Q1b : m.mbal ≥ 0}
        IN  ∧ ∀ a ∈ Q : ∃ m ∈ Q1b : m.acc = a 
            ∧ ∨ Q1bv = {}
              ∨ ∃ m ∈ Q1bv : 
                    ∧ m.mval = v
                    ∧ ∀ mm ∈ Q1bv : m.mbal ≥ mm.mbal 
  ∧ Send([type ↦ "2a", bal ↦ b, val ↦ v])
  ∧ UNCHANGED ⟨maxBal, maxVBal, maxVal, committed⟩

FastPhase2a(v) ≜
  ∧ ¬ ∃ m ∈ msgs : m.type = "2a" ∧ m.bal = 0
  ∧ Send([type ↦ "2a", bal ↦ 0, val ↦ v])
  ∧ UNCHANGED ⟨maxBal, maxVBal, maxVal, committed⟩
  
Vote(a, b, v) ≜
    ∧ maxBal' = [maxBal EXCEPT ![a] = b]
    ∧ maxVBal' = [maxVBal EXCEPT ![a] = b]
    ∧ maxVal' = [maxVal EXCEPT ![a] = v]
    ∧ Send([type ↦ "2b", acc ↦ a, bal ↦ b, val ↦ v]) 

Phase2b(a) ≜ ∃ m ∈ msgs :
    ∧ m.type = "2a"
    ∧ m.bal ≥ maxBal[a]
    ∧ Vote(a, m.bal, m.val)
    ∧ UNCHANGED ⟨committed⟩

votes ≜ [a ∈ Acceptor ↦  
           {⟨m.bal, m.val⟩ : m ∈ {mm ∈ msgs: ∧ mm.type = "2b"
                                             ∧ mm.acc = a }}]

VotedFor(a, b, v) ≜ ⟨b, v⟩ ∈ votes[a]

Commit(b, v) ≜
    ∧ ¬ ∃ cv ∈ committed: v = cv
    ∧ ∃ Q ∈ Quorum :
        ∀ a ∈ Q: ∃ m ∈ msgs: VotedFor(a, b, v)
    ∧ committed' = committed ∪ {v}
    ∧ UNCHANGED ⟨maxBal, maxVBal, maxVal, msgs⟩

Next ≜ ∨ ∃ b ∈ Ballot \ {0} : ∨ Phase1a(b)
                              ∨ ∃ v ∈ Value : Phase2a(b, v)
       ∨ ∃ a ∈ Acceptor : Phase1b(a) ∨ Phase2b(a)
       ∨ ∃ v ∈ Value: FastPhase2a(v)
       ∨ ∃ b ∈ Ballot, v ∈ Value: Commit(b, v)

Spec ≜ Init ∧ □[Next]_vars
----------------------------------------------------------------------------

OneValuePerBallot ≜  
    ∀ a1, a2 ∈ Acceptor, b ∈ Ballot, v1, v2 ∈ Value : 
       VotedFor(a1, b, v1) ∧ VotedFor(a2, b, v2) ⇒ (v1 = v2)

Inv ≜ ∧ TypeOK
      ∧ ∀ a ∈ Acceptor : IF maxVBal[a] = -1
                                THEN maxVal[a] = None
                                ELSE ⟨maxVBal[a], maxVal[a]⟩ ∈ votes[a]
       \* /\ \A m \in msgs : 
       \*       /\ (m.type = "1b") => /\ maxBal[m.acc] \geq m.bal
       \*                             /\ (m.mbal \geq 0) =>  
       \*                                 <<m.mbal, m.mval>> \in votes[m.acc]
       \*       /\ (m.type = "2a") => /\ \E Q \in Quorum : 
       \*                                   V!ShowsSafeAt(Q, m.bal, m.val)
       \*                             /\ \A mm \in msgs : /\ mm.type = "2a"
       \*                                                 /\ mm.bal = m.bal
       \*                                                 => mm.val = m.val
      ∧ OneValuePerBallot
      ∧ ∀ v1 ∈ committed, v2 ∈ committed: v1 = v2
============================================================================
