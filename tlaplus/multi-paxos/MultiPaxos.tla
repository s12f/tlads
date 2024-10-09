-------------------------------- MODULE MultiPaxos -------------------------------
EXTENDS Integers, TLC, FiniteSets

CONSTANT Value, Acceptor, Quorum, Ballot, MaxSeq, Proposer, None

ASSUME QuorumAssumption ≜
    ∧ ∀ Q ∈ Quorum : Q ⊆ Acceptor
    ∧ ∀ Q1, Q2 ∈ Quorum : Q1 ∩ Q2 ≠ {} 
      
LEADER ≜ "Leader"
CANDIDATE ≜ "Candidate"

Seq ≜ (0‥MaxSeq)

Max(S) ≜ CHOOSE x ∈ S: ∀y ∈ S: x ≥ y
QS ≜ Cardinality(Acceptor) ÷ 2 + 1

\* lss: Last Success Sequence
ProposerState ≜
    [ id: Proposer
    , role: { LEADER, CANDIDATE }
    , lss: Seq ∪ { -1 }
    , nextSeq: Seq
    ]

AcceptorState ≜
    [ id: Acceptor
    , seqs: [ Seq →
        [ maxBal: Ballot ∪ { -1 }
        , maxVBal: Ballot ∪ { -1 }
        , maxVal: Value ∪ { None }
        , valSrc: Proposer ∪ { None }
        ] ]
    ]

EmptySeqState ≜ [ maxBal ↦ -1, maxVBal ↦ -1, maxVal ↦ None, valSrc ↦ None ]

Msg1a ≜ [ type: {"1a"}, pid: Proposer, seq: Seq, bal : Ballot]

Msg1b ≜ [ type : {"1b"}, pid: Proposer, seq: Seq, acc : Acceptor, bal : Ballot
        , mbal : Ballot ∪ {-1}, mval : Value ∪ {None}, valSrc: Proposer ∪ {None} ]

Msg2a ≜ [ type : {"2a"}, pid: Proposer, seq: Seq, bal: Ballot
        , val: Value, valSrc: Proposer]

Msg2b ≜ [ type : {"2b"}, pid: Proposer, seq: Seq, acc: Acceptor, bal: Ballot
        , val: Value, valSrc: Proposer]

Message ≜ Msg1a ∪ Msg1b ∪ Msg2a ∪ Msg2b

Committed ≜
    [ seq: Seq
    , pid: Proposer
    , val: Value
    ]

VARIABLE msgs,
         proposerStates,
         acceptorStates,
         committed

vars ≜ ⟨msgs, proposerStates, acceptorStates, committed⟩

TypeOK ≜ 
    ∧ msgs ⊆ Message
    ∧ proposerStates ∈ [ Proposer → ProposerState ]
    ∧ acceptorStates ∈ [ Acceptor → AcceptorState ]
    ∧ committed ⊆ Committed
          
Constraint ≜
    ∧ ∀p ∈ Proposer: proposerStates[p].lss < MaxSeq
    ∧ ∀p ∈ Proposer: proposerStates[p].nextSeq < MaxSeq

Symmetry ≜ Permutations(Acceptor)
    ∪ Permutations(Proposer)
    \* ∪ Permutations(Quorum)
    ∪ Permutations(Value)

Init ≜ ∧ msgs = {}
       ∧ proposerStates = [ p ∈ Proposer ↦ 
            [ id ↦ p, role ↦ CANDIDATE, lss ↦ -1, nextSeq ↦ 0 ] ]
       ∧ acceptorStates = [ a ∈ Acceptor ↦
            [ id ↦ a, seqs ↦  [ s ∈ Seq ↦ EmptySeqState] ] ]
       ∧ committed = {}

Init2 ≜ ∧ msgs = {}
        ∧ ∃lp ∈ Proposer: proposerStates = [ p ∈ Proposer ↦ 
            [ id ↦ p, role ↦ IF p = lp THEN LEADER ELSE CANDIDATE, lss ↦ -1, nextSeq ↦ 0 ] ]
        ∧ acceptorStates = [ a ∈ Acceptor ↦
            [ id ↦ a, seqs ↦  [ s ∈ Seq ↦ EmptySeqState] ] ]
        ∧ committed = {}

Send(m) ≜ msgs' = msgs ∪ {m}

LastCommittedSeq ≜ Max({ c.seq: c ∈ committed })

LearnLastCommitted(p) ≜
    ∧ p.role = CANDIDATE
    ∧ committed ≠ {}
    ∧ proposerStates' = [ proposerStates EXCEPT ![p.id].nextSeq = LastCommittedSeq ]
        \* ^ p.nextSeq' = LastCommittedSeq
    ∧ UNCHANGED ⟨msgs, acceptorStates, committed⟩

Phase1a(p) ≜ ∃b ∈ Ballot:
    ∧ b > 0
    ∧ p.role = CANDIDATE
    ∧ ¬ ∃m ∈ msgs: m.pid = p.id ∧ m.seq = p.nextSeq ∧ m.bal ≥ b
    ∧ Send([type ↦ "1a", pid ↦ p.id, seq ↦ p.nextSeq, bal ↦ b])
    ∧ UNCHANGED ⟨committed, proposerStates, acceptorStates⟩

Phase1b(a) ≜ ∃m ∈ msgs:
    ∧ m.type = "1a"
    ∧ LET state ≜ a.seqs[m.seq]
      IN ∧ m.bal > state.maxBal
         ∧ acceptorStates' = [acceptorStates EXCEPT ![a.id].seqs[m.seq].maxBal = m.bal]
         ∧ Send([type ↦ "1b", pid ↦ m.pid, seq ↦ m.seq, acc ↦ a.id, bal ↦ m.bal
                 , mbal ↦ state.maxVBal, mval ↦ state.maxVal, valSrc ↦ state.valSrc])
         ∧ UNCHANGED ⟨committed, proposerStates⟩

Phase2a(p) ≜ ∃b ∈ Ballot:
    ∧ p.role = CANDIDATE
    ∧ ¬ ∃ m ∈ msgs : m.type = "2a" ∧ p.id = m.pid ∧ m.seq = p.nextSeq ∧ m.bal ≥ b
    ∧ LET ms ≜ { m ∈ msgs: ∧ m.type = "1b"
                           ∧ m.pid = p.id
                           ∧ m.seq = p.nextSeq
                           ∧ m.bal = b }
      IN ∧ Cardinality(ms) ≥ QS
         ∧ ∃m ∈ ms: ∀mm ∈ ms:
            ∧ m.mbal ≥ mm.mbal
            ∧ IF m.mbal < 0
              THEN ∃v ∈ Value: Send([type ↦ "2a", pid ↦ p.id, seq ↦ p.nextSeq, bal ↦ b,
                                     val ↦ v, valSrc ↦ p.id])
              ELSE Send([type ↦ "2a", pid ↦ p.id, seq ↦ p.nextSeq, bal ↦ b,
                         val ↦ m.mval, valSrc ↦ m.valSrc])
    ∧ UNCHANGED ⟨committed, proposerStates, acceptorStates⟩

FastPhase2a(p) ≜ ∃v ∈ Value:
    ∧ p.role = LEADER
    ∧ p.nextSeq = p.lss + 1
    ∧ ¬ ∃m ∈ msgs : m.type = "2a" ∧ m.pid = p.id ∧ m.seq = p.nextSeq ∧ m.bal = 0
    ∧ Send([type ↦ "2a", pid ↦ p.id, seq ↦ p.nextSeq, bal ↦ 0, val ↦ v, valSrc ↦ p.id])
    ∧ UNCHANGED ⟨committed, proposerStates, acceptorStates⟩
  
Phase2b(a) ≜ ∃ m ∈ msgs: 
    ∧ m.type = "2a"
    ∧ m.bal ≥ a.seqs[m.seq].maxBal
    ∧ acceptorStates' = [ acceptorStates EXCEPT ![a.id].seqs[m.seq] =
        [ maxBal ↦ m.bal, maxVBal ↦ m.bal, maxVal ↦ m.val, valSrc ↦ m.valSrc ] ]
    ∧ Send([type ↦ "2b", pid ↦ m.pid, seq ↦ m.seq, acc ↦ a.id, bal ↦ m.bal,
            val ↦ m.val, valSrc ↦ m.valSrc]) 
    ∧ UNCHANGED ⟨committed, proposerStates⟩

\* votes ≜ [a ∈ Acceptor ↦  
\*     {⟨m.seq, m.bal, m.val⟩ : m ∈ {mm ∈ msgs: ∧ mm.type = "2b"
\*                                              ∧ mm.acc = a }}]
\* 
\* VotedFor(a, seq, b, v) ≜ ⟨seq, b, v⟩ ∈ votes[a]

Commit(p) ≜ ∃b ∈ Ballot, v ∈ Value, valSrc ∈ Proposer:
    ∧ ∃Q ∈ Quorum: ∀a ∈ Q: ∃m ∈ msgs:
        ∧ m.type = "2b"
        ∧ m.pid = p.id
        ∧ m.seq = p.nextSeq
        ∧ m.acc = a
        ∧ m.bal = b
        ∧ m.val = v
        ∧ m.valSrc = valSrc
    ∧ committed' = committed ∪ {[ seq ↦ p.nextSeq, pid ↦  p.id, val ↦ v]}
    ∧ LET newRole ≜ IF valSrc = p.id THEN LEADER ELSE CANDIDATE
        IN proposerStates' = [ proposerStates EXCEPT ![p.id] = 
            [ id ↦ p.id, role ↦ newRole, lss ↦ p.nextSeq, nextSeq ↦ p.nextSeq + 1 ]]
    ∧ UNCHANGED ⟨msgs, acceptorStates⟩

ProposerNext ≜ ∃pid ∈ Proposer: LET p ≜ proposerStates[pid] IN
    ∨ Phase1a(p)
    ∨ Phase2a(p)
    ∨ FastPhase2a(p)
    ∨ Commit(p)
    ∨ LearnLastCommitted(p)

AcceptorNext ≜ ∃aid ∈ Acceptor: LET a ≜ acceptorStates[aid] IN
    ∨ Phase1b(a)
    ∨ Phase2b(a)

Next ≜
    ∨ ProposerNext
    ∨ AcceptorNext

Spec ≜ Init2 ∧ □[Next]_vars
----------------------------------------------------------------------------

\* OneValuePerBallot ≜  
\*     ∀ a1, a2 ∈ Acceptor, b ∈ Ballot, v1, v2 ∈ Value: 
\*        VotedFor(a1, b, v1) ∧ VotedFor(a2, b, v2) ⇒ (v1 = v2)

Inv ≜ ∧ TypeOK
      \* ∧ ∀ a ∈ Acceptor : IF maxVBal[a] = -1
      \*                           THEN maxVal[a] = None
      \*                           ELSE ⟨maxVBal[a], maxVal[a]⟩ ∈ votes[a]
      \* /\ \A m \in msgs : 
      \*       /\ (m.type = "1b") => /\ maxBal[m.acc] \geq m.bal
      \*                             /\ (m.mbal \geq 0) =>  
      \*                                 <<m.mbal, m.mval>> \in votes[m.acc]
      \*       /\ (m.type = "2a") => /\ \E Q \in Quorum : 
      \*                                   V!ShowsSafeAt(Q, m.bal, m.val)
      \*                             /\ \A mm \in msgs : /\ mm.type = "2a"
      \*                                                 /\ mm.bal = m.bal
      \*                                                 => mm.val = m.val
      \* ∧ OneValuePerBallot
      ∧ ∀c1, c2 ∈ committed:
            c1.seq = c2.seq ⇒ c1.val = c2.val
============================================================================
