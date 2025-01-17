-------------------- MODULE TrueTime --------------------

EXTENDS Integers

CONSTANT TTInitAbs, TTMaxAbs, TTInterval

ASSUME TTInitAbs - TTInterval >= 0

VARIABLES ttAbs, ttDrift

TTInit ≜
    ∧ ttAbs = TTInitAbs
    ∧ ttDrift = 0

TTNextAbs ≜
    ∧ ttAbs < TTMaxAbs
    ∧ ttAbs' = ttAbs + 1
    ∧ UNCHANGED ⟨ttDrift⟩

TTNext ≜
    ∨ TTNextAbs
    ∨ ∃x ∈ 0 ‥ TTInterval:
        ∧ ttDrift' = x
        ∧ UNCHANGED ⟨ttAbs⟩

TTNow ≜ [ earliest ↦ ttAbs - ttDrift, latest ↦ ttAbs + TTInterval - ttDrift]

TTAfter(t) ≜ t < TTNow.earliest

TTBefore(t) ≜ t > TTNow.latest

=========================================================
