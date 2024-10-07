-------------------------------- MODULE MultiPaxos -------------------------------
EXTENDS Integers

CONSTANT Value, Acceptor, Quorum, Ballot, MaxSeq, Proposer

ASSUME QuorumAssumption ≜
    ∧ ∀ Q ∈ Quorum : Q ⊆ Acceptor
    ∧ ∀ Q1, Q2 ∈ Quorum : Q1 ∩ Q2 ≠ {} 
      
None ≜ -1

LEADER ≜ "Leader"
CANDIDATE ≜ "Candidate"

Seq ≜ (1‥MaxSeq)

\* lss: Last Success Sequence
ProposerState ≜
    [ id: Proposer
    , role: { LEADER, CANDIDATE }
    , lss: Seq ∪ { None }
    , nextSeq: Seq
    ]

AcceptorSeqState ≜
    [ maxBal: Ballot ∪ { None }
    , maxVBal: Ballot ∪ { None }
    , maxValue: Ballot ∪ { None }
    ]

AcceptorState ≜ [ Seq →  AcceptorSeqState ]

Msg1a ≜ [ type: {"1a"}, pid: Proposer, seq: Seq, bal : Ballot]

Msg1b ≜ [ type : {"1b"}, pid: Proposer, seq: Seq, acc : Acceptor, bal : Ballot
        , mbal : Ballot ∪ {-1}, mval : Value ∪ {None} ]

Msg2a ≜ [ type : {"2a"}, pid: Proposer, seq: Seq, bal : Ballot, val : Value]

Msg2b ≜ [ type : {"2b"}, pid: Proposer, seq: Seq, acc : Acceptor, bal : Ballot, val : Value]

Message ≜ Msg1a ∪ Msg1b ∪ Msg2a ∪ Msg2b

VARIABLE msgs,
         proposerStates,
         acceptorStates,
         committed

vars ≜ ⟨ msgs, proposerStates, acceptorStates, committed ⟩

TypeOK ≜ 
    ∧ msgs ⊆ Message
    ∧ proposerStates ∈ [ Proposer → ProposerState ]
    ∧ acceptorStates ∈ [ Acceptor → AcceptorState ]
    ∧ committed ⊆ [ Seq → Value ]
          
Constraint ≜
    ∧ ∀p ∈ Proposer: proposerStates[p].lss < MaxSeq
    ∧ ∀p ∈ Proposer: proposerStates[p].nextSeq < MaxSeq

Init ≜ ∧ maxBal = [a ∈ Acceptor ↦ -1]
       ∧ maxVBal = [a ∈ Acceptor ↦ -1]
       ∧ maxVal = [a ∈ Acceptor ↦ None]
       ∧ msgs = {}
       ∧ proposerStates = [ p ∈ Proposer ↦ [ role ↦ CANDIDATE, lss: None ] ]
       ∧ acceptorStates = [ a ∈ Acceptor ↦ [ s ∈ Seq ↦ {} ] ]
       ∧ committed = {}

Send(m) ≜ msgs' = msgs ∪ {m}

Max(S) ≜ CHOOSE x ∈ S: ∀y ∈ S: x ≥ y

LastCommittedSeq ≜ Max(DOMAIN committed)

LearnLastCommitted(p) ≜
    ∧ p.role = CANDIDATE
    ∧ IF committed ≠ {}
          THEN proposerStates' = [ proposerStates EXCEPT ![p].nextSeq = LastCommittedSeq ]
            \* ^ p.nextSeq' = LastCommittedSeq
          ELSE UNCHANGED proposerStates
    ∧ UNCHANGED ⟨msgs, acceptorStates, committed⟩

Phase1a(p) ≜ ∃b ∈ Ballot:
    ∧ b > 0
    ∧ p.role ≜ CANDIDATE
    ∧ ¬ ∃m ∈ msgs: m.pid = p.id ∧ m.seq = state.nextSeq ∧ m.bal = b
    ∧ Send([type ↦ "1a", pid ↦ p.id, seq ↦ nextSeq, bal ↦ b])
    ∧ UNCHANGED ⟨committed, proposerStates, acceptorStates⟩

Phase1b(a) ≜ ∃ m ∈ msgs :
    ∧ m.type = "1a"
    ∧ LET state = a[m.seq]
      IN ∧ m.bal > state.maxVal
         ∧ acceptorStates' = [ acceptorStates EXCEPT ![a][m.seq].maxBal = m.bal ]
         ∧ Send([type ↦ "1b", pid ↦ m.pid, seq ↦ m.seq, acc ↦ a,
                      bal ↦ m.bal, mbal ↦ maxVBal[a], mval ↦ maxVal[a]])
         ∧ UNCHANGED ⟨committed, proposerStates⟩

Phase2a(p) ≜ ∃b ∈ Ballot, b ∈ Value:
    ∧ ¬ ∃ m ∈ msgs : m.type = "2a" ∧ p.id = m.pid ∧ m.seq = p.nextSeq ∧ m.bal = b
    ∧ ∃ Q ∈ Quorum :
        LET Q1b ≜ {m ∈ msgs : ∧ m.type = "1b"
                              ∧ m.pid = p.id
                              ∧ m.seq = nextSeq
                              ∧ m.acc ∈ Q
                              ∧ m.bal = b }
            Q1bv ≜ {m ∈ Q1b : m.mbal ≥ 0}
        IN ∧ ∀ a ∈ Q : ∃ m ∈ Q1b : m.acc = a 
           ∧ ∨ Q1bv = {}
             ∨ ∃ m ∈ Q1bv : 
                   ∧ m.mval = v
                   ∧ ∀ mm ∈ Q1bv : m.mbal ≥ mm.mbal 
  ∧ Send([type ↦ "2a", pid ↦ p.id, seq ↦ p.nextSeq, bal ↦ b, val ↦ v])
  ∧ UNCHANGED ⟨committed, proposerStates, acceptorStates⟩

FastPhase2a(p) ≜ ∃v ∈ Value:
    ∧ p.role = LEADER
    ∧ p.nextSeq = p.lss + 1
    ∧ ¬ ∃ m ∈ msgs : m.type = "2a" ∧ m.pid = p.id ∧ m.sed = p.nextSeq ∧ m.bal = 0
    ∧ Send([type ↦ "2a", pid ↦ p.id, seq ↦ p.nextSeq, bal ↦ 0, val ↦ v])
    ∧ UNCHANGED ⟨committed, proposerStates, acceptorStates⟩
  
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
