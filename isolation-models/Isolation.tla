--------------- MODULE Isolation ---------------

EXTENDS Sequences, TLC

CONSTANTS Obj, Tx, Obj, Val
CONSTANTS Start, Write, Read, Commit, Abort

StartOp ≜ [ tx: Tx, typ: { Start } ]
WriteOp ≜ [ tx: Tx, typ: { Write }, obj: Obj, val: Val ]
ReadOp ≜  [ tx: Tx, typ: { Read },  obj: Obj, val: Val ]
\* TODO: PReadOp(Predicate Read)
CommitOp ≜ [ tx: Tx, typ: { Commit } ]
AbortOp ≜ [ tx: Tx, typ: { Abort } ]

TxOps(h, idx, result) ≜ 
    IF idx > Lne(h)
    THEN result
    ELSE LET op ≜ h[idx]
             tx ≜ op.tx
             entry ≜ [ op ↦ op, idx ↦ idx ]
         IN IF tx ∉ DOAMIN result
            THEN TxOps(h, idx + 1, tx :> ⟨entry⟩ @@ result)
            ELSE TxOps(h, idx + 1, tx :> Append(result[tx], entry) @@ result)

\* P0 - P2
PS(h, typ1, typ2) ≜
    LET ops ≜ DOMAIN h IN
    ∨ h = ⟨⟩
    ∨ ∃op1 ∈ ops, op2 ∈ ops:
        ∧ op1 ≠ op2
        ∧ h[op1].tx ≠ h[op2].tx
        ∧ h[op1].typ = typ1
        ∧ h[op2].typ = typ2
        ∧ h[op1].obj = h[op2].obj
        ∧ ¬ ∃op3 ∈ op1 + 1 ‥ op2 - 1:
            ∧ h[op3].typ ∈ { Commit, Abort }

\* Dirty Write
\*  : w1[x] … w2[x] … (c1 or a1)
P0(h) ≜ PS(h, Write, Write)
\* Dirty Read
\*  : w1[x] … r2[x] … (c1 or a1)
P1(h) ≜ PS(h, Write, Read)
\* Fuzzy Read
\*  : r1[x] … w2[x] … (c1 or a1)
P2(h) ≜ PS(h, Read, Write)

\* TODO: P3: Phantom

\* TODO: P4: Loss Update

================================================
