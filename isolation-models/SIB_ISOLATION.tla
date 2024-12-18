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
  IN { f ∈ [D → S]: ∀ i,j ∈ D: i ≠ j ⇒ f[i] ≠ f[j] }

SeqToSet(S) ≜ { S[x] : x ∈ S}

Max(S) ≜ CHOOSE x ∈ S: ∀ y ∈ S: x ≥ y

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
SER_CT(t, txs, states) ≜
    ∀k ∈ DOMAIN txs[t].read: txs[t].read[k] = states[t][k]

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
SI_CT(t, txs, states) ≜
    \* x: previous state index
    ∃x ∈ 1 ‥ t:
        ∧ ∀k ∈ DOMAIN txs[t].read: txs[t].read[k] = states[x][k]
        \* NO-CONF
        ∧ ∀y ∈ x + 1 ‥ t:
            ∧ ∀wk ∈ DOMAIN txs[t].write: states[x][wk] = states[y][wk]

(* Read Committed Isolation Commit Test:
 Read committed allows T to see the effects of concurrent transactions, as long
 as they are committed. The commit test therefore no longer constrains all
 operations in T to read from the same state; instead, it only requires each of
 them to read from a state that precedes T in the execution e.
*)
RC_CT(t, txs, states) ≜
    ∀k ∈ DOMAIN txs[t].read:
        ∃x ∈ 1 ‥ t:
            txs[t].read[k] = states[x][k]

(* Read Uncommitted Isolation Commit Test:
 Read uncommitted allows T to see the effects of concurrent transactions,
 whether they have committed or not. The commit test reflects this
 permissiveness, to the point of allowing transactions to read arbitrary
 values.
*)
RU_CT(t, txs, states) ≜ TRUE

(* Strict Serializable Isolation Commit Test:
 Strict serializability guarantees that the real-time order of transactions
 will be reflected in the final history or execution.
*)
SSER_CT(t, txs, states) ≜
    LET TxLess(tx1, tx2) ≜ tx1.commitTs < tx2.startTs
    IN ∧ SER_CT(t, txs, states)
       ∧ ∀ t1 ∈ DOMAIN txs: TxLess(txs[t1], txs[t]) ⇒ t1 < t

(* Parallel Snapshot Isolation Commit Test:
*)

TxPrecede(tx1, tx2) ≜ 
    DOMAIN tx1.write ∩ (DOMAIN tx2.read ∪ DOMAIN tx2.write) ≠ {}
\* ts: transaction set
ComputeDirectPrecedeSet(txs, tx, pending) ≜ { t1 ∈ pending : TxPrecede(txs[t1], txs[tx]) }
\* compute a precede set of some transactions
RECURSIVE ComputePrecedeSet(_, _, _)
ComputePrecedeSet(txs, pending, result) ≜
    LET new ≜ UNION { ComputeDirectPrecedeSet(txs, tx, pending) : tx ∈ result } IN 
    IF new = {}
    THEN result
    ELSE ComputePrecedeSet(txs, pending \ new, result ∪ new )

PSI_CT(t, txs, states) ≜
    ∧ RC_CT(t, txs, states)
    ∧ LET rs ≜ DOMAIN txs[t].read
           ws ≜ DOMAIN txs[t].write
           ps ≜ ComputePrecedeSet(txs, 1 ‥ t - 1, {t})
           \* operation set
           ops ≜ rs ∪ ws
           slo(ok) ≜ Max({ x ∈ 1 ‥ t: ok ∉ rs ∨ txs[t].read[ok] = states[x][ok] })
       IN ∧ ∀ t1 ∈ ps, ok ∈ ops:
            ok ∈ DOMAIN txs[t1].write ⇒ t1 + 1 ≤ slo(ok)

----------------------------------------------------
\* Isolation Executions

IsolationExecution(e, CommitTest(_, _, _)) ≜
    LET txs ≜ e.txs
        states ≜ ComputeStates(txs, ⟨e.init⟩, 1)
    IN ∀idx ∈ DOMAIN txs: CommitTest(idx, txs, states)

SerializableExecution(e) ≜ IsolationExecution(e, SER_CT)
SnapshotExecution(e) ≜ IsolationExecution(e, SI_CT)
ReadCommittedExecution(e) ≜ IsolationExecution(e, RC_CT)
ReadUncommittedExecution(e) ≜ IsolationExecution(e, RU_CT)
ParallelSnapshotExecution(e) ≜ IsolationExecution(e, PSI_CT)
StrictSerializableExecution(e) ≜ IsolationExecution(e, SSER_CT)

----------------------------------------------------
\* Isolation Levels

Isolation(init, transactions, IE(_)) ≜
    \* all possible executions from transactions
    ∃txs ∈ SetToSeqs(transactions): IE([ init ↦ init, txs ↦ txs ])

SerializableIsolation(init, transactions) ≜ Isolation(init, transactions, SerializableExecution)
SnapshotIsolation(init, transactions) ≜ Isolation(init, transactions, SnapshotExecution)
ReadCommittedIsolation(init, transactions) ≜ Isolation(init, transactions, ReadCommittedExecution)
ReadUncommittedIsolation(init, transactions) ≜ Isolation(init, transactions, ReadUncommittedExecution)
ParallelSnapshotIsolation(init, transactions) ≜ Isolation(init, transactions, ParallelSnapshotExecution)
StrictSerializableIsolation(init, transactions) ≜ Isolation(init, transactions, StrictSerializableExecution)

================================================