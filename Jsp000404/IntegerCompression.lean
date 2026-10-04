import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Order.Monotone.Defs
import Lean.Elab.Tactic.Omega

/-!
Finite integer-label compression for the six-centre scalar geometry.

For every used label we keep the cut immediately to its right and the cut
immediately to its left. Counting retained cuts preserves whether the distance
between two used labels is zero, one, or at least two. Fractional parts may thus
be carried separately by the geometric adapter; no realizability assertion is
made here.
-/

namespace Jsp404.IntegerCompression

/-- Cuts needed to preserve the two integer distance thresholds. -/
def cutEdges (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  S.erase n ∪ (S.erase 0).image (fun x => x - 1)

/-- The compressed integer coordinate counts retained cuts before a label. -/
def compress (S : Finset ℕ) (n k : ℕ) : ℕ :=
  (cutEdges S n ∩ Finset.range k).card

theorem compress_zero (S : Finset ℕ) (n : ℕ) : compress S n 0 = 0 := by
  simp [compress]

theorem compress_monotone (S : Finset ℕ) (n : ℕ) : Monotone (compress S n) := by
  intro a b hab
  apply Finset.card_le_card
  exact Finset.inter_subset_inter_left (Finset.range_mono hab)

theorem compress_succ_of_mem (S : Finset ℕ) (n k : ℕ)
    (hk : k ∈ cutEdges S n) : compress S n (k + 1) = compress S n k + 1 := by
  unfold compress
  rw [Finset.range_add_one, Finset.inter_insert_of_mem hk, Finset.card_insert_of_notMem]
  simp

theorem cutEdges_subset_range (S : Finset ℕ) (n : ℕ)
    (hS : ∀ k ∈ S, k ≤ n) : cutEdges S n ⊆ Finset.range n := by
  intro k hk
  rw [Finset.mem_range]
  rcases Finset.mem_union.mp hk with hk | hk
  · rcases Finset.mem_erase.mp hk with ⟨hne, hmem⟩
    have hle := hS k hmem
    omega
  · rcases Finset.mem_image.mp hk with ⟨x, hx, rfl⟩
    rcases Finset.mem_erase.mp hx with ⟨hne, hmem⟩
    have hle := hS x hmem
    omega

theorem compress_top (S : Finset ℕ) (n : ℕ)
    (hS : ∀ k ∈ S, k ≤ n) : compress S n n = (cutEdges S n).card := by
  unfold compress
  rw [Finset.inter_eq_left.mpr (cutEdges_subset_range S n hS)]

theorem used_right_cut (S : Finset ℕ) (n a : ℕ)
    (ha : a ∈ S) (han : a < n) : a ∈ cutEdges S n := by
  apply Finset.mem_union_left
  exact Finset.mem_erase.mpr ⟨by omega, ha⟩

theorem used_left_cut (S : Finset ℕ) (n b : ℕ)
    (hb : b ∈ S) (hb0 : 0 < b) : b - 1 ∈ cutEdges S n := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨b, Finset.mem_erase.mpr ⟨by omega, hb⟩, rfl⟩

theorem compress_used_lt (S : Finset ℕ) (n a b : ℕ)
    (hS : ∀ k ∈ S, k ≤ n) (ha : a ∈ S) (hb : b ∈ S)
    (hab : a < b) : compress S n a < compress S n b := by
  have han : a < n := lt_of_lt_of_le hab (hS b hb)
  have hs := compress_succ_of_mem S n a (used_right_cut S n a ha han)
  have hm := compress_monotone S n (show a + 1 ≤ b by omega)
  omega

theorem compress_used_adjacent (S : Finset ℕ) (n a b : ℕ)
    (hS : ∀ k ∈ S, k ≤ n) (ha : a ∈ S) (hb : b ∈ S)
    (hab : b = a + 1) : compress S n b = compress S n a + 1 := by
  have han : a < n := by have := hS b hb; omega
  rw [hab]
  exact compress_succ_of_mem S n a (used_right_cut S n a ha han)

theorem compress_used_separated (S : Finset ℕ) (n a b : ℕ)
    (hS : ∀ k ∈ S, k ≤ n) (ha : a ∈ S) (hb : b ∈ S)
    (hab : a + 2 ≤ b) : compress S n a + 2 ≤ compress S n b := by
  have han : a < n := by have := hS b hb; omega
  have hr := compress_succ_of_mem S n a (used_right_cut S n a ha han)
  have hl := compress_succ_of_mem S n (b - 1)
    (used_left_cut S n b hb (by omega))
  have hm := compress_monotone S n (show a + 1 ≤ b - 1 by omega)
  have heq : b - 1 + 1 = b := by omega
  rw [heq] at hl
  omega

theorem compress_one (S : Finset ℕ) (n : ℕ) (hn : 1 ≤ n)
    (h0 : 0 ∈ S) : compress S n 1 = 1 := by
  have h := compress_succ_of_mem S n 0 (used_right_cut S n 0 h0 (by omega))
  simpa [compress_zero] using h

theorem compress_penultimate (S : Finset ℕ) (n : ℕ)
    (hn : 1 ≤ n) (hN : n ∈ S) : compress S n (n - 1) + 1 = compress S n n := by
  have h := compress_succ_of_mem S n (n - 1) (used_left_cut S n n hN (by omega))
  simpa [Nat.sub_add_cancel hn] using h.symm

theorem pred_image_card (S : Finset ℕ) :
    ((S.erase 0).image (fun x => x - 1)).card = (S.erase 0).card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb heq
  have ha0 := (Finset.mem_erase.mp ha).1
  have hb0 := (Finset.mem_erase.mp hb).1
  dsimp at heq
  omega

theorem cutEdges_card_bound (S : Finset ℕ) (n : ℕ)
    (hn : 3 ≤ n) (h0 : 0 ∈ S) (h1 : 1 ∈ S)
    (hprev : n - 1 ∈ S) (hN : n ∈ S) (hcard : S.card ≤ 14) :
    (cutEdges S n).card ≤ 24 := by
  let R := S.erase n
  let L := (S.erase 0).image (fun x => x - 1)
  have hR : R.card + 1 = S.card := by
    dsimp [R]
    have h := Finset.card_erase_of_mem hN
    have hp : 0 < S.card := Finset.card_pos.mpr ⟨n, hN⟩
    omega
  have hL : L.card + 1 = S.card := by
    dsimp [L]
    rw [pred_image_card]
    have h := Finset.card_erase_of_mem h0
    have hp : 0 < S.card := Finset.card_pos.mpr ⟨0, h0⟩
    omega
  have h0R : 0 ∈ R := Finset.mem_erase.mpr ⟨by omega, h0⟩
  have hprevR : n - 1 ∈ R := Finset.mem_erase.mpr ⟨by omega, hprev⟩
  have h0L : 0 ∈ L := by
    exact Finset.mem_image.mpr ⟨1, Finset.mem_erase.mpr ⟨by omega, h1⟩, by omega⟩
  have hprevL : n - 1 ∈ L := by
    exact Finset.mem_image.mpr ⟨n, Finset.mem_erase.mpr ⟨by omega, hN⟩, rfl⟩
  have hpair : ({0, n - 1} : Finset ℕ) ⊆ R ∩ L := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨h0R, h0L⟩
    · exact Finset.mem_inter.mpr ⟨hprevR, hprevL⟩
  have hinter : 2 ≤ (R ∩ L).card := by
    have h := Finset.card_le_card hpair
    have hne : (0 : ℕ) ≠ n - 1 := by omega
    simpa [Finset.card_pair hne] using h
  have hunion := Finset.card_union_add_card_inter R L
  change (R ∪ L).card ≤ 24
  omega

theorem compress_top_bounds (S : Finset ℕ) (n : ℕ)
    (hn : 3 ≤ n) (h0 : 0 ∈ S) (h1 : 1 ∈ S)
    (hprev : n - 1 ∈ S) (hN : n ∈ S) (hcard : S.card ≤ 14)
    (hS : ∀ k ∈ S, k ≤ n) :
    3 ≤ compress S n n ∧ compress S n n ≤ 24 := by
  constructor
  · have hl := compress_used_separated S n 1 n hS h1 hN hn
    rw [compress_one S n (by omega) h0] at hl
    omega
  · rw [compress_top S n hS]
    exact cutEdges_card_bound S n hn h0 h1 hprev hN hcard

/-- The precise witness consumed by a fractional-coordinate adapter. -/
structure CompressedLabels (S : Finset ℕ) (n : ℕ) where
  top : ℕ
  f : ℕ → ℕ
  top_bounds : 3 ≤ top ∧ top ≤ 24
  monotone : Monotone f
  zero : f 0 = 0
  one : f 1 = 1
  top_eq : f n = top
  penultimate : f (n - 1) + 1 = top
  used_strict : ∀ a ∈ S, ∀ b ∈ S, a < b → f a < f b
  used_adjacent : ∀ a ∈ S, ∀ b ∈ S, b = a + 1 → f b = f a + 1
  used_separated : ∀ a ∈ S, ∀ b ∈ S, a + 2 ≤ b → f a + 2 ≤ f b

theorem CompressedLabels.strictMonoOn {S : Finset ℕ} {n : ℕ}
    (C : CompressedLabels S n) : StrictMonoOn C.f (S : Set ℕ) := by
  intro a ha b hb hab
  exact C.used_strict a ha b hb hab

theorem CompressedLabels.used_eq_iff {S : Finset ℕ} {n a b : ℕ}
    (C : CompressedLabels S n) (ha : a ∈ S) (hb : b ∈ S) :
    C.f a = C.f b ↔ a = b := by
  constructor
  · intro h
    rcases lt_trichotomy a b with hab | hab | hab
    · have := C.used_strict a ha b hb hab
      omega
    · exact hab
    · have := C.used_strict b hb a ha hab
      omega
  · rintro rfl
    rfl

theorem CompressedLabels.used_adjacent_iff {S : Finset ℕ} {n a b : ℕ}
    (C : CompressedLabels S n) (ha : a ∈ S) (hb : b ∈ S) :
    C.f b = C.f a + 1 ↔ b = a + 1 := by
  constructor
  · intro h
    by_cases hba : b ≤ a
    · have := C.monotone hba
      omega
    · by_cases hab : b = a + 1
      · exact hab
      · have := C.used_separated a ha b hb (show a + 2 ≤ b by omega)
        omega
  · exact C.used_adjacent a ha b hb

theorem CompressedLabels.used_separated_iff {S : Finset ℕ} {n a b : ℕ}
    (C : CompressedLabels S n) (ha : a ∈ S) (hb : b ∈ S) :
    C.f a + 2 ≤ C.f b ↔ a + 2 ≤ b := by
  constructor
  · intro h
    by_contra hab
    by_cases hba : b ≤ a
    · have := C.monotone hba
      omega
    · have heq : b = a + 1 := by omega
      have := C.used_adjacent a ha b hb heq
      omega
  · exact C.used_separated a ha b hb

/-- At most fourteen used labels compress into a strip of width at most 24. -/
def compressedLabels (S : Finset ℕ) (n : ℕ)
    (hn : 3 ≤ n) (h0 : 0 ∈ S) (h1 : 1 ∈ S)
    (hprev : n - 1 ∈ S) (hN : n ∈ S) (hcard : S.card ≤ 14)
    (hS : ∀ k ∈ S, k ≤ n) : CompressedLabels S n where
  top := compress S n n
  f := compress S n
  top_bounds := compress_top_bounds S n hn h0 h1 hprev hN hcard hS
  monotone := compress_monotone S n
  zero := compress_zero S n
  one := compress_one S n (by omega) h0
  top_eq := rfl
  penultimate := compress_penultimate S n (by omega) hN
  used_strict := fun a ha b hb hab => compress_used_lt S n a b hS ha hb hab
  used_adjacent := fun a ha b hb hab => compress_used_adjacent S n a b hS ha hb hab
  used_separated := fun a ha b hb hab => compress_used_separated S n a b hS ha hb hab

end Jsp404.IntegerCompression
