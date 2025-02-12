-------------------- MODULE TrueTime --------------------

EXTENDS Integers

\* Initial absolute time
CONSTANT TTInitAbs
\* Max self-incresed limitation
CONSTANT TTMaxSi
\* Interval of TrueTime
CONSTANT TTInterval

\* make sure timestamp is not negative
ASSUME TTInitAbs - TTInterval >= 0

\* absolute time
VARIABLES ttAbs
\* the drift compared with the absolute time
VARIABLES ttDrift
\* self-incresed counter
VARIABLES ttSi

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
