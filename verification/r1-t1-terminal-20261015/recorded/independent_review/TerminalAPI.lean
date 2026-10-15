import Jsp000404.R1DispatchT1

/-!
# R1-T1 terminal ExpectedAPI probe — independent GLM review, 2026-10-15

Strongly-typed restatement of the expected public API of the R1 T1
seven-point `Φ = 22` terminal.  Every binder below is written out
verbatim in the original-API shape (identical to the already-verified
T2 terminal `Jsp404.r1_seven_phi21_terminal`, with `potential = 22`).
Compilation succeeds only if `Jsp404.r1_seven_phi22_terminal` and
`Jsp404.r1_phi22_all_defect3` exist with exactly these types, and the
`#check` commands fail if any of the six `R2N4.r1cert_T1_*`
certificates is missing or renamed.

Acceptance: every `#print axioms` below must report only
`'propext, Classical.choice, Quot.sound'` (Std3).  Anything else —
in particular `sorryAx` — is a rejection, since three baseline
modules with pre-existing admissions
(`Jsp000404.Section4Legality`, `Jsp000404.Deletion`,
`Jsp000404.GeometricDeletion`) are inside this import closure and
must not be depended on.

This file contains no new definitions, no `sorry`/`axiom`/
`native_decide`/`unsafe`, and no mathematical changes.  It is a probe
to be compiled by Root in the pinned worktree
`.coordination/local-t1-20261015/worktree`
(baseline `13cb6cb371acd8b046b861a471ddba3b75cb4522` + 22-file
overlay, dispatch sha256
`34e73169df6ddbd414c1255c9167da3c1ea40290f0c7f550b6056e741f5029cc`).
-/

namespace Jsp404

/-- **ExpectedTerminal (verbatim original API).**  A seven-centre
`n = 4` legal configuration with saturated anchor `v`, defect-`2` row
`a`, all other tails of defect `≥ 3`, and potential `Φ = 22` yields
`False`. -/
theorem GLM_expected_seven_phi22_terminal
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 4)
    {c : Fin 7 → Plane₂} (hleg : Section4Legality c lam)
    {v a : Fin 7} (hva : v ≠ a)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (hda : rowDefect 4 lam (directionRow o e c a) = 2)
    (htail : ∀ w : Fin 7, w ≠ v → w ≠ a →
      3 ≤ rowDefect 4 lam (directionRow o e c w))
    (hF : potential lam (directionRows o e c) = 22) : False :=
  Jsp404.r1_seven_phi22_terminal o e he hlam hn hleg hva hsat hda htail hF

/-- **Potential-ledger bookkeeping (verbatim original API).**  `Φ = 22`
with this defect profile forces every remaining tail to defect `3`. -/
theorem GLM_expected_phi22_all_defect3
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 4)
    {c : Fin 7 → Plane₂} (hleg : Section4Legality c lam)
    {v a : Fin 7} (hva : v ≠ a)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (hda : rowDefect 4 lam (directionRow o e c a) = 2)
    (htail : ∀ w : Fin 7, w ≠ v → w ≠ a →
      3 ≤ rowDefect 4 lam (directionRow o e c w))
    (hF : potential lam (directionRows o e c) = 22) :
    ∀ w : Fin 7, w ≠ v → w ≠ a →
      rowDefect 4 lam (directionRow o e c w) = 3 :=
  Jsp404.r1_phi22_all_defect3 o e he hlam hn hleg hva hsat hda htail hF

end Jsp404

/- The six T1 spec certificates must exist with their published
statements (verified byte-identical to the baseline versions of these
files by the review; `#check` pins existence and exact type). -/

#check @R2N4.r1cert_T1_s2a0_s1a2_s1a4
#check @R2N4.r1cert_T1_s2a1_s1a5
#check @R2N4.r1cert_T1_s2a2_s1a4
#check @R2N4.r1cert_T1_s1a1_s2a3
#check @R2N4.r1cert_T1_s1a3_s2a4
#check @R2N4.r1cert_T1_s1a1_s1a3_s2a5

/- Axiom audits — all eight must be exactly Std3. -/

#print axioms Jsp404.r1_seven_phi22_terminal
#print axioms Jsp404.r1_phi22_all_defect3
#print axioms R2N4.r1cert_T1_s2a0_s1a2_s1a4
#print axioms R2N4.r1cert_T1_s2a1_s1a5
#print axioms R2N4.r1cert_T1_s2a2_s1a4
#print axioms R2N4.r1cert_T1_s1a1_s2a3
#print axioms R2N4.r1cert_T1_s1a3_s2a4
#print axioms R2N4.r1cert_T1_s1a1_s1a3_s2a5
