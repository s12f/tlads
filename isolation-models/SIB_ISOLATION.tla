--------------- MODULE SIB_ISOLATION ---------------

EXTENDS Sequences, TLC, FiniteSets

----------------------------------------------------
\* Utils

(*
Convert the set S to a set containing all sequences containing the elements of S
exactly once and no other elements.
Examples:
    SetToSeqs({}), {<<>>}
    SetToSeqs({"t","l"}) = {<<"t","l">>, <<"l","t">>}
*)
SetToSeqs(S) ≜
  LET D ≜ 1..Cardinality(S)
  IN { f ∈ [D -> S]: ∀ i,j ∈ D: i ≠ j => f[i] ≠ f[j] }

----------------------------------------------------
\* States

ComputeNextState(tx, state) ≜
    LET WriteSet ≜ DOMAIN tx.write
        NextValue(k, v) ≜ IF k ∈ WriteSet THEN tx.write[k] ELSE v
    IN [ k ∈ DOMAIN state ↦ NextValue(k, state[k]) ]

ComputeStates(txs, states, idx) ≜
    IF Len(txs) < idx
    THEN states
    ELSE ComputeStates(
            txs,
            Append(states, ComputeNextState(txs[idx], states[idx])),
            idx + 1
         )

----------------------------------------------------
\* Commit Tests

(* Commit Test:
 for an execution e of a set T of transactions to be valid under a given
 isolation level I, each transaction T in e must satisfy the commit test
 CT(T, e) for I.
*)

(* Serializable Isolation Commit Test:
 Serializability requires the values observed by the operations in each
 transaction T to be consistent with those that would have been observed in a
 sequential execution. The commit test enforces this requirement through two
 complementary conditions on observable states. First, all of T ’s operations
 must read from the same state s (i.e., s must be a complete state for T ).
 Second, s must be the parent state of T , i.e., the state that T transitions
 from. These two conditions suffice to guarantee that T will observe the effects
 of all transactions that committed before it.
*)
SER_CT(tx, states) ≜ ∀k ∈ DOAMIN tx.read: tx.read[k] = Tail(states)[k]

(* Snapshot Isolation Commit Test
 *)
SI_CT(tx, states) ≜
    ∃idx ∈ DOAMIN states:
        ∀k ∈ DOAMIN tx.read:
            tx.read[k] = states[idx][k]

(* Read Committed Isolation Commit Test
 *)
RC_CT(tx, states) ≜
    ∀k ∈ DOAMIN tx.read:
        ∃idx ∈ DOAMIN states:
            tx.read[k] = states[idx][k]

(* Read Uncommitted Isolation Commit Test
 *)
RU_CT(tx, states) ≜ TRUE

----------------------------------------------------
\* Isolation Executions

IsolationExecution(e, CommitTest) ≜
    LET txs ≜ e.txs
        states ≜ ComputeStates(txs, ⟨e.init⟩, 1)
    IN ∀idx ∈ DOMAIN txs: CommitTest(txs[idx], SubSeq(states, 1, idx))

SerializableExecution(e) ≜ IsolationExecution(e, SER_CT)
SnapshotExecution(e) ≜ IsolationExecution(e, SI_CT)
ReadCommittedExecution(e) ≜ IsolationExecution(e, RC_CT)
ReadUnommittedExecution(e) ≜ IsolationExecution(e, RU_CT)

----------------------------------------------------
\* Isolation Levels

Isolation(init, transactions, CommitTest) ≜
    \* all possible executions from transactions
    ∃txs ∈ SetToSeqs(transitions):
        IsolationExecution([ init ↦ init, txs ↦ txs ], CommitTest)

SerializableIsolation(init, transactions) ≜ Isolation(transitions, SER_CT)
IsolationIsolation(init, transactions) ≜ Isolation(transitions, SI_CT)
ReadCommittedIsolation(init, transactions) ≜ Isolation(transitions, RC_CT)
ReadUncommittedIsolation(init, transactions) ≜ Isolation(transitions, RU_CT)

================================================
