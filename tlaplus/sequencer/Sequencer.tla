-------------------------------- MODULE Sequencer -------------------------------

EXTENDS Integers, Sequences

CONSTANTS Servers, MaxEpoch, MaxSeq, BatchSize

VARIABLES states, epoch, output, diskSeq

PRIMARY ≜ "Primary"
SECONDARY ≜ "Secondary"

ServerState ≜ [ role: { PRIMARY }, seq: (1 ‥ MaxSeq + BatchSize) ]
            ∪ [ role: { SECONDARY } ]

TypeOK ≜
    ∧ epoch ∈ (1 ‥ MaxEpoch)
    ∧ states ∈ [ Servers → ServerState ]
    ∧ output ∈ Seq(1 ‥ MaxSeq)
    ∧ diskSeq ∈ 1‥MaxSeq + BatchSize

Init ≜ 
    ∧ states = [ s ∈ Servers ↦ [ role ↦ SECONDARY ] ]
    ∧ epoch = 1
    ∧ output = ⟨⟩
    ∧ diskSeq = 1

GetSeq(s) ≜
    ∧ states[s].role = PRIMARY
    ∧ states[s].seq < MaxSeq
    ∧ LET nextSeq ≜ states[s].seq
      IN ∧ ∨ output' = Append(output, nextSeq) \* response seq to client
           ∨ UNCHANGED⟨output⟩ \* failed response(e.g. msg loss, timeout, primary restart etc.)
         ∧ states' = [ states EXCEPT ![s].seq = nextSeq + 1 ]
         ∧ IF nextSeq - diskSeq < BatchSize
           THEN UNCHANGED diskSeq
           ELSE ∧ diskSeq' = nextSeq
    ∧ UNCHANGED epoch

PrimaryRestart(s) ≜
    ∧ states[s].role = PRIMARY
    ∧ states' = [states EXCEPT ![s] = [ role ↦ SECONDARY ]]
    ∧ UNCHANGED ⟨epoch, output, diskSeq⟩

Elect(s) ≜
    ∧ ∀a ∈ Servers: states[a].role = SECONDARY
    ∧ epoch' = epoch
    ∧ states' = [ states EXCEPT ![s] = [ role ↦ PRIMARY, seq ↦ diskSeq + BatchSize ] ]
    ∧ UNCHANGED ⟨diskSeq, output⟩

Next ≜ ∃s ∈ Servers:
    ∨ GetSeq(s)
    ∨ PrimaryRestart(s)
    ∨ Elect(s)

Spec ≜ Init ∧ □[Next]_⟨states, epoch, output, diskSeq⟩

SafePrimary ≜
    ∃x, y ∈ Servers:
        states[x].role = PRIMARY ∧ states[y].role = PRIMARY ⇒ x = y

SafeSeqs(s) ≜
    ∀x, y ∈ 1‥Len(s):
        x > y ⇒ s[x] > s[y]

Inv ≜
    ∧ TypeOK
    ∧ SafePrimary
    ∧ SafeSeqs(output)

============================================================================

