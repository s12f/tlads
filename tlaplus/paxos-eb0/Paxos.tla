-------------------------------- MODULE Paxos -------------------------------
(***************************************************************************)
(* This is a specification of the Paxos algorithm without explicit leaders *)
(* or learners.  It refines the spec in Voting                             *)
(***************************************************************************)
EXTENDS Integers
-----------------------------------------------------------------------------
(***************************************************************************)
(* The constant parameters and the set Ballots are the same as in Voting.  *)
(***************************************************************************)
CONSTANT Value, Acceptor, Quorum, Ballot

ASSUME QuorumAssumption ≜ ∧ ∀ Q ∈ Quorum : Q ⊆ Acceptor
                          ∧ ∀ Q1, Q2 ∈ Quorum : Q1 ∩ Q2 ≠ {} 
      
None ≜ -1
  (*************************************************************************)
  (* An unspecified value that is not a choosable value.                   *)
  (*************************************************************************)
  
(***************************************************************************)
(* This is a message-passing algorithm, so we begin by defining the set    *)
(* Message of all possible messages.  The messages are explained below     *)
(* with the actions that send them.                                        *)
(***************************************************************************)
Message ≜ [type : {"1a"}, bal : Ballot]
        ∪ [type : {"1b"}, acc : Acceptor, bal : Ballot, 
              mbal : Ballot ∪ {-1}, mval : Value ∪ {None}]
        ∪ [type : {"2a"}, bal : Ballot, val : Value]
        ∪ [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]

-----------------------------------------------------------------------------
VARIABLE maxBal, 
         maxVBal,   \* <<maxVBal[a], maxVal[a]>> is the vote with the largest
         maxVal,    \* ballot number cast by a; it equals <<-1, None>> if
                    \* a has not cast any vote.
         msgs,      \* The set of all messages that have been sent.
         committed

(***************************************************************************)
(* NOTE:                                                                   *)
(* The algorithm is easier to understand in terms of the set msgs of all   *)
(* messages that have ever been sent.  A more accurate model would use     *)
(* one or more variables to represent the messages actually in transit,    *)
(* and it would include actions representing message loss and duplication  *)
(* as well as message receipt.                                             *)
(*                                                                         *)
(* In the current spec, there is no need to model message loss because we  *)
(* are mainly concerned with the algorithm's safety property.  The safety  *)
(* part of the spec says only what messages may be received and does not   *)
(* assert that any message actually is received.  Thus, there is no        *)
(* difference between a lost message and one that is never received.  The  *)
(* liveness property of the spec that we check makes it clear what         *)
(* messages must be received (and hence either not lost or successfully    *)
(* retransmitted if lost) to guarantee progress.                           *)
(***************************************************************************)

vars ≜ ⟨maxBal, maxVBal, maxVal, msgs⟩
  (*************************************************************************)
  (* It is convenient to define some identifier to be the tuple of all     *)
  (* variables.  I like to use the identifier `vars'.                      *)
  (*************************************************************************)
  
(***************************************************************************)
(* The type invariant and initial predicate.                               *)
(***************************************************************************)
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

(***************************************************************************)
(* The actions.  We begin with the subaction (an action that will be used  *)
(* to define the actions that make up the next-state action.               *)
(***************************************************************************)
Send(m) ≜ msgs' = msgs ∪ {m}

(***************************************************************************)
(* In an implementation, there will be a leader process that orchestrates  *)
(* a ballot.  The ballot b leader performs actions Phase1a(b) and          *)
(* Phase2a(b).  The Phase1a(b) action sends a phase 1a message (a message  *)
(* m with m.type = "1a") that begins ballot b.                             *)
(***************************************************************************)
Phase1a(b) ≜ 
    ∧ Send([type ↦ "1a", bal ↦ b])
    ∧ UNCHANGED ⟨maxBal, maxVBal, maxVal, committed⟩
                 
(***************************************************************************)
(* Upon receipt of a ballot b phase 1a message, acceptor a can perform a   *)
(* Phase1b(a) action only if b > maxBal[a].  The action sets maxBal[a] to  *)
(* b and sends a phase 1b message to the leader containing the values of   *)
(* maxVBal[a] and maxVal[a].                                               *)
(***************************************************************************)
Phase1b(a) ≜ ∧ ∃ m ∈ msgs : 
                  ∧ m.type = "1a"
                  ∧ m.bal > maxBal[a]
                  ∧ maxBal' = [maxBal EXCEPT ![a] = m.bal]
                  ∧ Send([type ↦ "1b", acc ↦ a, bal ↦ m.bal, 
                            mbal ↦ maxVBal[a], mval ↦ maxVal[a]])
             ∧ UNCHANGED ⟨maxVBal, maxVal, committed⟩

(***************************************************************************)
(* The Phase2a(b, v) action can be performed by the ballot b leader if two *)
(* conditions are satisfied: (i) it has not already performed a phase 2a   *)
(* action for ballot b and (ii) it has received ballot b phase 1b messages *)
(* from some quorum Q from which it can deduce that the value v is safe at *)
(* ballot b.  These enabling conditions are the first two conjuncts in the *)
(* definition of Phase2a(b, v).  This second conjunct, expressing          *)
(* condition (ii), is the heart of the algorithm.  To understand it,       *)
(* observe that the existence of a phase 1b message m in msgs implies that *)
(* m.mbal is the highest ballot number less than m.bal in which acceptor   *)
(* m.acc has or ever will cast a vote, and that m.mval is the value it     *)
(* voted for in that ballot if m.mbal # -1.  It is not hard to deduce from *)
(* this that the second conjunct implies that there exists a quorum Q such *)
(* that ShowsSafeAt(Q, b, v) (where ShowsSafeAt is defined in module       *)
(* Voting).                                                                *)
(*                                                                         *)
(* The action sends a phase 2a message that tells any acceptor a that it   *)
(* can vote for v in ballot b, unless it has already set maxBal[a]         *)
(* greater than b (thereby promising not to vote in ballot b).             *)
(***************************************************************************)
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
  
(***************************************************************************)
(* The Phase2b(a) action is performed by acceptor a upon receipt of a      *)
(* phase 2a message.  Acceptor a can perform this action only if the       *)
(* message is for a ballot number greater than or equal to maxBal[a].  In  *)
(* that case, the acceptor votes as directed by the phase 2a message,      *)
(* setting maxVBal[a] and maxVal[a] to record that vote and sending a      *)
(* phase 2b message announcing its vote.  It also sets maxBal[a] to the    *)
(* message's.  ballot number                                               *)
(***************************************************************************)
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

(***************************************************************************)
(* In an implementation, there will be learner processes that learn from   *)
(* the phase 2b messages if a value has been committed.  The learners are     *)
(* omitted from this abstract specification of the algorithm.              *)
(***************************************************************************)

(***************************************************************************)
(* As we observed, votes are registered by sending phase 2b messages.  So  *)
(* the array `votes' describing the votes cast by the acceptors is defined *)
(* as follows.                                                             *)
(***************************************************************************)
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

(***************************************************************************)
(* Below are defined the next-state action and the complete spec.          *)
(***************************************************************************)
Next ≜ ∨ ∃ b ∈ Ballot \ {0} : ∨ Phase1a(b)
                              ∨ ∃ v ∈ Value : Phase2a(b, v)
       ∨ ∃ a ∈ Acceptor : Phase1b(a) ∨ Phase2b(a)
       ∨ ∃ v ∈ Value: FastPhase2a(v)
       ∨ ∃ b ∈ Ballot, v ∈ Value: Commit(b, v)

Spec ≜ Init ∧ □[Next]_vars
----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the refinement mapping under which this algorithm         *)
(* implements the specification in module Voting.                          *)
(***************************************************************************)

(***************************************************************************)
(* We now instantiate module Voting, substituting the constants Value,     *)
(* Acceptor, and Quorum declared in this module for the corresponding      *)
(* constants of that module Voting, and substituting the variable maxBal   *)
(* and the defined state function `votes' for the correspondingly-named    *)
(* variables of module Voting.                                             *)
(***************************************************************************)

\* V == INSTANCE Voting 

\* THEOREM Spec => V!Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* Here is a first attempt at an inductive invariant used to prove this    *)
(* theorem.                                                                *)
(***************************************************************************)
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
