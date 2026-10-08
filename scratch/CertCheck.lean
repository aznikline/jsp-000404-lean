import Mathlib

/-!
# Farkas-certificate refutation checker — compact certificates.

Atom `a` over `x : Fin n → ℝ` means `Σᵢ a.coeffᵢ·xᵢ ≤ a.bound` (`<` when strict).
A `Cert` walks a fixed split table; `leaf w` carries Farkas weights proving the
accumulated atoms unsatisfiable. All checks are `decide +kernel`-computable.
-/

namespace CertCheck

/-- Linear atom: `Σᵢ coeff[i]·x i` versus `bound`, strict flag for `<`. -/
structure Atom where
  coeff : List Rat
  bound : Rat
  strict : Bool := false

namespace Atom

def lhs (a : Atom) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ((a.coeff.getD i.val 0 : Rat) : ℝ) * x i

def sem (a : Atom) (x : Fin n → ℝ) : Prop :=
  cond a.strict (a.lhs x < (a.bound : ℝ)) (a.lhs x ≤ (a.bound : ℝ))

end Atom

def coeffSumAt (atoms : List Atom) (w : List Rat) (i : Nat) : Rat :=
  ((atoms.zip w).map fun ⟨a, c⟩ => c * a.coeff.getD i 0).sum

def boundSum (atoms : List Atom) (w : List Rat) : Rat :=
  ((atoms.zip w).map fun ⟨a, c⟩ => c * a.bound).sum

/-- Farkas check: equal lengths, nonnegative weights, zero coefficient sum,
    contradictory bound sum (`<0`, or `≤0` with a strictly-weighted strict atom). -/
def checkFarkas (n : Nat) (atoms : List Atom) (w : List Rat) : Bool :=
  (atoms.length = w.length) && w.all (fun c => 0 ≤ c) &&
  (List.range n).all (fun i => coeffSumAt atoms w i = 0) &&
  (boundSum atoms w < 0 ||
    (boundSum atoms w ≤ 0 && (atoms.zip w).any fun ⟨a, c⟩ => a.strict && 0 < c))

/-! ### soundness of `checkFarkas` -/

theorem mul_lhs {n : ℕ} {x : Fin n → ℝ} (a : Atom) (c : Rat) :
    (c : ℝ) * a.lhs x =
      ∑ i : Fin n, ((c * a.coeff.getD i.val 0 : Rat) : ℝ) * x i := by
  rw [Atom.lhs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

/-- Double-sum swap: `Σⱼ wⱼ·lhsⱼ = Σᵢ coeffSum[i]·xᵢ`. -/
theorem weighted_lhs_eq {n : ℕ} {x : Fin n → ℝ} (l : List (Atom × Rat)) :
    ((l.map fun ⟨a, c⟩ => (c : ℝ) * a.lhs x).sum : ℝ) =
      ∑ i : Fin n, (((l.map fun ⟨a, c⟩ => c * a.coeff.getD i.val 0).sum : Rat) : ℝ) * x i := by
  induction l with
  | nil => simp
  | cons p t ih =>
    obtain ⟨a, c⟩ := p
    simp only [List.map_cons, List.sum_cons]
    rw [ih, mul_lhs, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring

/-- `Σ wⱼ·(lhsⱼ − bⱼ) ≤ 0` over a list of `(atom, weight)` pairs. -/
theorem defect_le {n : ℕ} {x : Fin n → ℝ} (l : List (Atom × Rat))
    (hp : ∀ p ∈ l, p.1.sem x ∧ (0 : Rat) ≤ p.2) :
    ((l.map fun ⟨a, c⟩ => (c : ℝ) * (a.lhs x - (a.bound : ℝ))).sum : ℝ) ≤ 0 := by
  induction l with
  | nil => simp
  | cons p t ih =>
    obtain ⟨a, c⟩ := p
    rw [List.map_cons, List.sum_cons]
    have ha := (hp (a, c) (List.mem_cons_self)).1
    have hc : (0 : Rat) ≤ c := (hp (a, c) (List.mem_cons_self)).2
    have hd0 : a.lhs x - (a.bound : ℝ) ≤ 0 := by
      cases hs : a.strict with
      | true =>
        have h : a.lhs x < (a.bound : ℝ) := by simpa [Atom.sem, hs, cond_true] using ha
        linarith
      | false =>
        have h : a.lhs x ≤ (a.bound : ℝ) := by simpa [Atom.sem, hs, cond_true] using ha
        linarith
    have hd : (c : ℝ) * (a.lhs x - (a.bound : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast hc) hd0
    have ihx := ih (fun p hp' => hp p (List.mem_cons_of_mem _ hp'))
    linarith [hd, ihx]

/-- Strict version: `Σ wⱼ·(lhsⱼ − bⱼ) < 0` when a strictly-weighted strict
    atom participates. -/
theorem defect_lt {n : ℕ} {x : Fin n → ℝ} (l : List (Atom × Rat))
    (hp : ∀ p ∈ l, p.1.sem x ∧ (0 : Rat) ≤ p.2)
    (hstr : ∃ p ∈ l, p.1.strict = true ∧ (0 : Rat) < p.2) :
    ((l.map fun ⟨a, c⟩ => (c : ℝ) * (a.lhs x - (a.bound : ℝ))).sum : ℝ) < 0 := by
  obtain ⟨⟨a, c⟩, hm, hastr, hc⟩ := hstr
  obtain ⟨l₁, l₂, rfl⟩ := List.mem_iff_append.mp hm
  rw [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  have ha : a.sem x := (hp (a, c) (by simp)).1
  have hd0 : a.lhs x - (a.bound : ℝ) < 0 := by
    have hastr2 : a.strict = true := hastr
    have h : a.lhs x < (a.bound : ℝ) := by
      unfold Atom.sem at ha
      rw [hastr2] at ha
      simpa using ha
    linarith
  have hmid : (c : ℝ) * (a.lhs x - (a.bound : ℝ)) < 0 :=
    mul_neg_of_pos_of_neg (by exact_mod_cast hc) hd0
  have hS1 := defect_le l₁ (fun p hp' => hp p (by
    rw [List.mem_append]; exact Or.inl hp'))
  have hS2 := defect_le l₂ (fun p hp' => hp p (by
    rw [List.mem_append]; exact Or.inr (List.mem_cons_of_mem _ hp')))
  linarith [hS1, hmid, hS2]

/-- Membership projections out of `List.zip`. -/
theorem fst_mem_zip {atoms : List Atom} {w : List Rat} {p : Atom × Rat}
    (h : p ∈ atoms.zip w) : p.1 ∈ atoms := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  rw [List.getElem_zip]
  exact List.getElem_mem _

theorem snd_mem_zip {atoms : List Atom} {w : List Rat} {p : Atom × Rat}
    (h : p ∈ atoms.zip w) : p.2 ∈ w := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  rw [List.getElem_zip]
  exact List.getElem_mem _

/-- Soundness: a passing Farkas check refutes semantic satisfaction. -/
theorem farkas_sound {n : ℕ} {x : Fin n → ℝ} (atoms : List Atom) (w : List Rat)
    (h : checkFarkas n atoms w = true) (hsem : ∀ a ∈ atoms, a.sem x) : False := by
  simp only [checkFarkas, Bool.and_eq_true, List.all_eq_true,
    Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hlen, hw⟩, hz⟩, hb⟩ := h
  have hS : (((atoms.zip w).map fun ⟨a, c⟩ => (c : ℝ) * a.lhs x).sum : ℝ) = 0 := by
    rw [weighted_lhs_eq]
    apply Finset.sum_eq_zero
    intro i _
    have hi : coeffSumAt atoms w i.val = 0 := hz i.val (List.mem_range.mpr i.isLt)
    have hci : ((atoms.zip w).map fun ⟨a, c⟩ => c * a.coeff.getD i.val 0).sum = 0 := hi
    rw [hci, Rat.cast_zero, zero_mul]
  have hpw : ∀ p ∈ atoms.zip w, p.1.sem x ∧ (0 : Rat) ≤ p.2 := fun p hp =>
    ⟨hsem p.1 (fst_mem_zip hp), hw p.2 (snd_mem_zip hp)⟩
  have hD := defect_le _ hpw
  have hDeq : ((atoms.zip w).map fun ⟨a, c⟩ => (c : ℝ) * (a.lhs x - (a.bound : ℝ))).sum =
      (((atoms.zip w).map fun ⟨a, c⟩ => (c : ℝ) * a.lhs x).sum : ℝ) -
        (boundSum atoms w : ℝ) := by
    rw [boundSum]
    induction atoms.zip w with
    | nil => simp
    | cons p t ihh =>
      obtain ⟨a, c⟩ := p
      simp only [List.map_cons, List.sum_cons] at ihh ⊢
      rw [ihh]
      push_cast
      ring
  rcases hb with hneg | ⟨hle, hstr⟩
  · rw [hS] at hDeq
    have hB : (0:ℝ) ≤ (boundSum atoms w : ℝ) := by
      have : (((atoms.zip w).map fun ⟨a, c⟩ =>
          (c : ℝ) * (a.lhs x - (a.bound : ℝ))).sum : ℝ) = (0:ℝ) - (boundSum atoms w) := hDeq
      linarith [hD]
    exact absurd hB (not_le.mpr (by exact_mod_cast hneg : (boundSum atoms w : ℝ) < 0))
  · obtain ⟨⟨a, c⟩, hm, hastr, hcpos⟩ := hstr
    have hDlt := defect_lt _ hpw ⟨(a, c), hm, hastr, hcpos⟩
    rw [hS] at hDeq
    have hB : (0:ℝ) < (boundSum atoms w : ℝ) := by linarith [hDlt]
    exact absurd hB (not_lt.mpr (by exact_mod_cast hle : (boundSum atoms w : ℝ) ≤ 0))

/-! ### decision tree over a split table -/

/-- Each split is a pair of atom *conjunctions* (each `htr` disjunct is 3 atoms). -/
inductive Cert where
  | leaf : List Rat → Cert
  | node : Nat → Cert → Cert → Cert

def check (n : Nat) (splits : List (List Atom × List Atom)) (ctx : List Atom) :
    Cert → Bool
  | .leaf w => checkFarkas n ctx w
  | .node i l r =>
    match splits[i]? with
    | some (la, ra) => check n splits (ctx ++ la) l && check n splits (ctx ++ ra) r
    | none => false

theorem check_sound {n : ℕ} {x : Fin n → ℝ}
    (splits : List (List Atom × List Atom)) (cert : Cert)
    (hsplit : ∀ (i : Nat) (la ra : List Atom), splits[i]? = some (la, ra) →
      (∀ a ∈ la, Atom.sem a x) ∨ (∀ a ∈ ra, Atom.sem a x)) :
    ∀ ctx : List Atom, check n splits ctx cert = true →
      (∀ a ∈ ctx, a.sem x) → False := by
  induction cert with
  | leaf w =>
    intro ctx h hc
    exact farkas_sound ctx w h hc
  | node i l r ihl ihr =>
    intro ctx h hc
    simp only [check] at h
    cases hs : splits[i]? with
    | none => simp [hs] at h
    | some p =>
      obtain ⟨la, ra⟩ := p
      simp only [hs] at h
      have ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp h
      rcases hsplit i la ra hs with hla | hra
      · exact ihl (ctx ++ la) hl (fun a ha => by
          rcases List.mem_append.mp ha with hm | hm
          · exact hc a hm
          · exact hla a hm)
      · exact ihr (ctx ++ ra) hr (fun a ha => by
          rcases List.mem_append.mp ha with hm | hm
          · exact hc a hm
          · exact hra a hm)

end CertCheck
