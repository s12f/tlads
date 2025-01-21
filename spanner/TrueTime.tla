-------------------- MODULE TrueTime --------------------

EXTENDS Integers

CONSTANT TTInitAbs, TTMaxSi, TTInterval

ASSUME TTInitAbs - TTInterval >= 0

VARIABLES ttAbs, ttDrift, ttSi

TTInit ≜
    ∧ ttAbs = TTInitAbs
    ∧ ttDrift = 0
    ∧ ttSi = 0

TTEventNext ≜
    ∧ ttAbs' = ttAbs + 1
    ∧ UNCHANGED ⟨ttSi, ttDrift⟩

TTSiNext ≜
    ∧ ttSi < TTMaxSi
    ∧ ttSi' = ttSi + 1
    ∧ ttAbs' = ttAbs + 1
    ∧ UNCHANGED ⟨ttDrift⟩

TTDrift ≜ 
    ∃x ∈ 0 ‥ TTInterval:
        ∧ ttDrift' = x
        ∧ UNCHANGED ⟨ttAbs, ttSi⟩

TTNext ≜
    ∨ TTSiNext
    ∨ TTDrift

TTNow ≜ [ earliest ↦ ttAbs - ttDrift, latest ↦ ttAbs + TTInterval - ttDrift]

TTAfter(t) ≜ t < TTNow.earliest

TTBefore(t) ≜ t > TTNow.latest

=========================================================
