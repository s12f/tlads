--------------- MODULE SIB_ISOLATION ---------------

EXTENDS Integers, Sequences, TLC, FiniteSets

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
  LET D ≜ 1 ‥ Cardinality(S)
  IN { f ∈ [D -> S]: ∀ i,j ∈ D: i ≠ j => f[i] ≠ f[j] }

----------------------------------------------------
\* States

ComputeNextState(tx, state) ≜
    LET WriteSet ≜ DOMAIN tx.write
        NextValue(k, v) ≜ IF k ∈ WriteSet THEN tx.write[k] ELSE v
    IN [ k ∈ DOMAIN state ↦ NextValue(k, state[k]) ]

RECURSIVE ComputeStates(_, _, _)
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
SER_CT(tx, states) ≜ ∀k ∈ DOMAIN tx.read: tx.read[k] = states[Len(states)][k]

(* Snapshot Isolation Commit Test:
 Like serializability, SI prevents transaction T from seeing the effects of
 concurrently running transactions. The commit test enforces this requirement
 by having all operations in T read from the same state s, produced by a
 transaction that precedes T in the execution e. However, SI no longer insists
 on that state s being T ’s parent state sp: other transactions, whose
 operations T will not observe, may commit in between s and sp. The commit
 test only forbids T from modifying any of the keys that changed value as the
 system’s state progressed from s to sp.
 *)
SI_CT(tx, states) ≜
    ∃idx ∈ DOMAIN states:
        ∧ ∀k ∈ DOMAIN tx.read: tx.read[k] = states[idx][k]
        \* NO-CONF
        ∧ ∀y ∈ idx + 1 ‥ Len(states) - 1:
            ∧ ∀wk ∈ DOMAIN tx.write: states[idx][wk] = states[y][wk]

(* Read Committed Isolation Commit Test:
 Read committed allows T to see the effects of concurrent transactions, as long
 as they are committed. The commit test therefore no longer constrains all
 operations in T to read from the same state; instead, it only requires each of
 them to read from a state that precedes T in the execution e.
 *)
RC_CT(tx, states) ≜
    ∀k ∈ DOMAIN tx.read:
        ∃idx ∈ DOMAIN states:
            tx.read[k] = states[idx][k]

(* Read Uncommitted Isolation Commit Test
 Read uncommitted allows T to see the effects of concurrent transactions,
 whether they have committed or not. The commit test reflects this
 permissiveness, to the point of allowing transactions to read arbitrary
 values.
 *)
RU_CT(tx, states) ≜ TRUE

----------------------------------------------------
\* Isolation Executions

IsolationExecution(e, CommitTest(_, _)) ≜
    LET txs ≜ e.txs
        states ≜ ComputeStates(txs, ⟨e.init⟩, 1)
    IN ∀idx ∈ DOMAIN txs: CommitTest(txs[idx], SubSeq(states, 1, idx))

SerializableExecution(e) ≜ IsolationExecution(e, SER_CT)
SnapshotExecution(e) ≜ IsolationExecution(e, SI_CT)
ReadCommittedExecution(e) ≜ IsolationExecution(e, RC_CT)
ReadUnommittedExecution(e) ≜ IsolationExecution(e, RU_CT)

----------------------------------------------------
\* Isolation Levels

Isolation(init, transactions, CommitTest(_, _)) ≜
    \* all possible executions from transactions
    ∃txs ∈ SetToSeqs(transactions):
        IsolationExecution([ init ↦ init, txs ↦ txs ], CommitTest)

SerializableIsolation(init, transactions) ≜ Isolation(init, transactions, SER_CT)
SnapshotIsolation(init, transactions) ≜ Isolation(init, transactions, SI_CT)
ReadCommittedIsolation(init, transactions) ≜ Isolation(init, transactions, RC_CT)
ReadUncommittedIsolation(init, transactions) ≜ Isolation(init, transactions, RU_CT)

================================================
