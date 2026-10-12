import Jsp000404.MixedStarExclusion
import Jsp000404.S8Defs

set_option maxHeartbeats 40000000

/-!
# Extraction: eight-centre `SatChart` → `N8Model` (narrow core)

The `SatChart → N8Model` geometric bridge (n8T/n8σ/n8model and the
row-extraction lemmas) without the `S8Certs` certificate closure.
The three positional-class terminals remain in `S8Extraction`.
-/


namespace Jsp404

open Classical
open scoped EuclideanSpace

/-- A five-element list splits into its literals. -/
private theorem length_eq_five' {α : Type*} {l : List α}
    (h : l.length = 5) :
    ∃ a b c d e : α, l = [a, b, c, d, e] := by
  cases l with
  | nil => simp at h
  | cons a l' =>
    rw [List.length_cons] at h
    obtain ⟨b, c, d, e, rfl⟩ :=
      List.length_eq_four.mp (show l'.length = 4 by omega)
    exact ⟨a, b, c, d, e, rfl⟩

/-- A six-element list splits into its literals. -/
private theorem length_eq_six {α : Type*} {l : List α}
    (h : l.length = 6) :
    ∃ a b c d e f : α, l = [a, b, c, d, e, f] := by
  cases l with
  | nil => simp at h
  | cons a l' =>
    rw [List.length_cons] at h
    obtain ⟨b, c, d, e, f, rfl⟩ :=
      length_eq_five' (show l'.length = 5 by omega)
    exact ⟨a, b, c, d, e, f, rfl⟩

private theorem s7fl3 {lam g : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g) :
    ⌊g / lam⌋₊ = 3 ↔ 3 * lam ≤ g ∧ g < 4 * lam := by
  rw [Nat.floor_eq_iff (div_nonneg hg hlam.le)]
  constructor
  · rintro ⟨h1, h2⟩
    rw [le_div_iff₀ hlam] at h1; rw [div_lt_iff₀ hlam] at h2
    push_cast at h1 h2 ⊢; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩
    constructor
    · rw [le_div_iff₀ hlam]; exact_mod_cast h1
    · rw [div_lt_iff₀ hlam]; exact_mod_cast h2

private theorem s7fl2 {lam g : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g) :
    ⌊g / lam⌋₊ = 2 ↔ 2 * lam ≤ g ∧ g < 3 * lam := by
  rw [Nat.floor_eq_iff (div_nonneg hg hlam.le)]
  constructor
  · rintro ⟨h1, h2⟩
    rw [le_div_iff₀ hlam] at h1; rw [div_lt_iff₀ hlam] at h2
    push_cast at h1 h2 ⊢; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩
    constructor
    · rw [le_div_iff₀ hlam]; exact_mod_cast h1
    · rw [div_lt_iff₀ hlam]; exact_mod_cast h2

private theorem s7fl1 {lam g : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g) :
    ⌊g / lam⌋₊ ≤ 1 ↔ g < 2 * lam := by
  rw [show ⌊g / lam⌋₊ ≤ 1 ↔ ⌊g / lam⌋₊ < 2 from (Nat.lt_add_one_iff).symm,
    Nat.floor_lt (div_nonneg hg hlam.le), div_lt_iff₀ hlam]
  push_cast
  exact Iff.rfl


end Jsp404
