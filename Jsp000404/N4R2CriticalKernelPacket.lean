import Jsp000404.SatScalarModel

/-! The strict-between triangle alternatives imply the necessary four-packet
one-signflip property. This is a forward consequence of actual Model fields,
not an added geometric field or an inverse signotope realization theorem.
The proof covers all sixteen arm choices; no caller orientation is assumed. -/

set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.N4R2CriticalKernel
open SatScalarModel

def forward {m n : ℕ} (M : GenericModel m n) (a b c : Fin m) : Prop :=
  M.d a b < M.d a c ∧ M.d a c < M.d b c

def reverse {m n : ℕ} (M : GenericModel m n) (a b c : Fin m) : Prop :=
  M.d b c < M.d a c ∧ M.d a c < M.d a b

def packetMonotone {m n : ℕ} (M : GenericModel m n) (a b c d : Fin m) : Prop :=
  (forward M a b c ∧ forward M a b d ∧ forward M a c d ∧ forward M b c d) ∨
  (forward M a b c ∧ forward M a b d ∧ forward M a c d ∧ reverse M b c d) ∨
  (forward M a b c ∧ forward M a b d ∧ reverse M a c d ∧ reverse M b c d) ∨
  (forward M a b c ∧ reverse M a b d ∧ reverse M a c d ∧ reverse M b c d) ∨
  (reverse M a b c ∧ forward M a b d ∧ forward M a c d ∧ forward M b c d) ∨
  (reverse M a b c ∧ reverse M a b d ∧ forward M a c d ∧ forward M b c d) ∨
  (reverse M a b c ∧ reverse M a b d ∧ reverse M a c d ∧ forward M b c d) ∨
  (reverse M a b c ∧ reverse M a b d ∧ reverse M a c d ∧ reverse M b c d)

/-- All actual triangle arms on any four ordered indices have at most
one direction change in their packet order. -/
theorem model_packet_monotone {m n : ℕ} (M : GenericModel m n)
    (a b c d : Fin m) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    packetMonotone M a b c d := by
  have hac : a < c := lt_trans hab hbc
  have hbd : b < d := lt_trans hbc hcd
  unfold packetMonotone
  rcases M.triangle a b c hab hbc with h1 | h1
  ·
    rcases M.triangle a b d hab hbd with h2 | h2
    ·
      rcases M.triangle a c d hac hcd with h3 | h3
      ·
        rcases M.triangle b c d hbc hcd with h4 | h4
        ·
          exact Or.inl ⟨h1.2, h2.2, h3.2, h4.2⟩
        ·
          exact Or.inr (Or.inl ⟨h1.2, h2.2, h3.2, h4.2⟩)
      ·
        rcases M.triangle b c d hbc hcd with h4 | h4
        ·
          exfalso
          linarith only [h1.2.1, h1.2.2, h2.2.1, h2.2.2, h3.2.1, h3.2.2, h4.2.1, h4.2.2]
        ·
          exact Or.inr (Or.inr (Or.inl ⟨h1.2, h2.2, h3.2, h4.2⟩))
    ·
      rcases M.triangle a c d hac hcd with h3 | h3
      ·
        rcases M.triangle b c d hbc hcd with h4 | h4
        ·
          exfalso
          linarith only [h1.2.1, h1.2.2, h2.2.1, h2.2.2, h3.2.1, h3.2.2, h4.2.1, h4.2.2]
        ·
          exfalso
          linarith only [h1.2.1, h1.2.2, h2.2.1, h2.2.2, h3.2.1, h3.2.2, h4.2.1, h4.2.2]
      ·
        rcases M.triangle b c d hbc hcd with h4 | h4
        ·
          exfalso
          linarith only [h1.2.1, h1.2.2, h2.2.1, h2.2.2, h3.2.1, h3.2.2, h4.2.1, h4.2.2]
        ·
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1.2, h2.2, h3.2, h4.2⟩)))
  ·
    rcases M.triangle a b d hab hbd with h2 | h2
    ·
      rcases M.triangle a c d hac hcd with h3 | h3
      ·
        rcases M.triangle b c d hbc hcd with h4 | h4
        ·
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1.2, h2.2, h3.2, h4.2⟩))))
        ·
          exfalso
          linarith only [h1.2.1, h1.2.2, h2.2.1, h2.2.2, h3.2.1, h3.2.2, h4.2.1, h4.2.2]
      ·
        rcases M.triangle b c d hbc hcd with h4 | h4
        ·
          exfalso
          linarith only [h1.2.1, h1.2.2, h2.2.1, h2.2.2, h3.2.1, h3.2.2, h4.2.1, h4.2.2]
        ·
          exfalso
          linarith only [h1.2.1, h1.2.2, h2.2.1, h2.2.2, h3.2.1, h3.2.2, h4.2.1, h4.2.2]
    ·
      rcases M.triangle a c d hac hcd with h3 | h3
      ·
        rcases M.triangle b c d hbc hcd with h4 | h4
        ·
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1.2, h2.2, h3.2, h4.2⟩)))))
        ·
          exfalso
          linarith only [h1.2.1, h1.2.2, h2.2.1, h2.2.2, h3.2.1, h3.2.2, h4.2.1, h4.2.2]
      ·
        rcases M.triangle b c d hbc hcd with h4 | h4
        ·
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1.2, h2.2, h3.2, h4.2⟩))))))
        ·
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h1.2, h2.2, h3.2, h4.2⟩)))))))

#print axioms model_packet_monotone
end Jsp404.N4R2CriticalKernel
