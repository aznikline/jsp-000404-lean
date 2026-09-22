import Jsp000404.GadgetCounterexample

/-!
# Nonnegative geometric gaps in a proper skeleton

Position injectivity makes the non-self positions a permutation. Angle
bounds then force every real gap q+r to be nonnegative, including the
wrap gap. Consequently strict remainders imply nonnegative integer
cells. In the closed relaxation, a negative cell can only be q=-1,
r=1, hence a zero real gap. No enumeration is used.
-/

namespace Jsp404

lemma Skeleton.Proper.pos_surjective {s : ℕ} {sk : Skeleton s}
    (hp : sk.Proper) (x : Fin s) (g : Fin (s - 1)) :
    ∃ a : Fin s, a ≠ x ∧ (sk.vtx x).pos a = g := by
  cases s with
  | zero => exact Fin.elim0 x
  | succ m =>
    let f : Fin m → Fin m := fun a => (sk.vtx x).pos (x.succAbove a)
    have hi : Function.Injective f := by
      intro a b he
      exact Fin.succAbove_right_injective
        (hp x _ _ (Fin.succAbove_ne x a) (Fin.succAbove_ne x b) he)
    obtain ⟨a, ha⟩ := Finite.surjective_of_injective hi g
    exact ⟨x.succAbove a, Fin.succAbove_ne x a, ha⟩

lemma ModeA.arc_sum_bounds {s n : ℕ} {sk : Skeleton s}
    {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ} (hA : ModeA n sk r δ)
    (x a b : Fin s) (hab : a ≠ b) :
    0 ≤ (∑ g ∈ (sk.vtx x).arc a b, (((sk.vtx x).q g : ℝ) + r x g)) ∧
      (∑ g ∈ (sk.vtx x).arc a b, (((sk.vtx x).q g : ℝ) + r x g)) ≤ n + δ := by
  have hlow := hA.ang_nn x a b hab
  have hhigh := hA.ang_le x a b hab
  by_cases hb : (sk.vtx x).bits a = (sk.vtx x).bits b
  · simp only [angleExpr, hb, ↓reduceIte] at hlow hhigh
    exact ⟨hlow, by linarith⟩
  · simp only [angleExpr, hb, ↓reduceIte] at hlow hhigh
    constructor <;> linarith

theorem ModeA.gap_nonnegative {s n : ℕ} {sk : Skeleton s}
    {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ) (hp : sk.Proper) (hδ : 0 ≤ δ)
    (x : Fin s) (g : Fin (s - 1)) : 0 ≤ ((sk.vtx x).q g : ℝ) + r x g := by
  let gap : Fin (s - 1) → ℝ := fun j => ((sk.vtx x).q j : ℝ) + r x j
  have hfan : ∑ j, gap j = (n : ℝ) + δ := by
    have hf := hA.fan x
    push_cast at hf
    simp only [gap, Finset.sum_add_distrib]
    linarith
  change 0 ≤ gap g
  by_cases hm : s - 1 = 1
  · have huniq : ∀ j : Fin (s - 1), j = g := by
      intro j
      apply Fin.ext
      omega
    have hu : (Finset.univ : Finset (Fin (s - 1))) = {g} := by
      ext j
      simp [huniq j]
    rw [hu, Finset.sum_singleton] at hfan
    rw [hfan]
    positivity
  have hm2 : 2 ≤ s - 1 := by have := g.isLt; omega
  by_cases hlast : g.val + 1 = s - 1
  · let z : Fin (s - 1) := ⟨0, by omega⟩
    obtain ⟨a, _, ha⟩ := hp.pos_surjective x z
    obtain ⟨b, _, hb⟩ := hp.pos_surjective x g
    have hzg : z < g := by change 0 < g.val; omega
    have hab : a ≠ b := by
      intro he
      have hpos : z = g := ha.symm.trans ((congrArg (sk.vtx x).pos he).trans hb)
      exact (ne_of_lt hzg) hpos
    have harc : (sk.vtx x).arc a b = Finset.univ.erase g := by
      simp only [VertexData.arc, ha, hb, inf_eq_left.mpr hzg.le,
        sup_eq_right.mpr hzg.le]
      ext j
      simp only [Finset.mem_Ico, Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · intro hj
        exact ne_of_lt hj.2
      · intro hj
        have hjv : j.val ≠ g.val := fun he => hj (Fin.ext he)
        constructor
        · change 0 ≤ j.val; omega
        · change j.val < g.val; have := j.isLt; omega
    have hbnd := (hA.arc_sum_bounds x a b hab).2
    change (∑ j ∈ (sk.vtx x).arc a b, gap j) ≤ (n : ℝ) + δ at hbnd
    rw [harc] at hbnd
    have he := Finset.add_sum_erase Finset.univ gap (Finset.mem_univ g)
    linarith
  · let k : Fin (s - 1) := ⟨g.val + 1, by have := g.isLt; omega⟩
    have hgk : g < k := by change g.val < g.val + 1; omega
    obtain ⟨a, _, ha⟩ := hp.pos_surjective x g
    obtain ⟨b, _, hb⟩ := hp.pos_surjective x k
    have hab : a ≠ b := by
      intro he
      have hpos : g = k := ha.symm.trans ((congrArg (sk.vtx x).pos he).trans hb)
      exact (ne_of_lt hgk) hpos
    have harc : (sk.vtx x).arc a b = {g} := by
      simp only [VertexData.arc, ha, hb, inf_eq_left.mpr hgk.le,
        sup_eq_right.mpr hgk.le]
      ext j
      simp only [Finset.mem_Ico, Finset.mem_singleton]
      constructor
      · intro hj
        apply Fin.ext
        change g.val ≤ j.val ∧ j.val < g.val + 1 at hj
        omega
      · intro he
        subst j
        exact ⟨le_rfl, hgk⟩
    have hbnd := (hA.arc_sum_bounds x a b hab).1
    simpa [harc, gap] using hbnd

/-- Strict floor remainders close the signed-cell gap in the faithful model. -/
theorem ModeA.q_nonnegative_of_strict {s n : ℕ} {sk : Skeleton s}
    {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ) (hp : sk.Proper) (hδ : 0 ≤ δ)
    (hr : ∀ x g, r x g < 1) (x : Fin s) (g : Fin (s - 1)) :
    0 ≤ (sk.vtx x).q g := by
  have hg := hA.gap_nonnegative hp hδ x g
  have hrg := hr x g
  by_contra h
  have hq : (sk.vtx x).q g ≤ -1 := by omega
  have hqr : ((sk.vtx x).q g : ℝ) ≤ -1 := by exact_mod_cast hq
  linarith

/-- In the closed relaxation a negative cell is only a zero-gap boundary. -/
theorem ModeA.negative_q_boundary {s n : ℕ} {sk : Skeleton s}
    {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ) (hp : sk.Proper) (hδ : 0 ≤ δ)
    (x : Fin s) (g : Fin (s - 1)) (hq : (sk.vtx x).q g < 0) :
    (sk.vtx x).q g = -1 ∧ r x g = 1 := by
  have hg := hA.gap_nonnegative hp hδ x g
  have hr := hA.r_le x g
  have hqr : (-1 : ℝ) ≤ ((sk.vtx x).q g : ℝ) := by linarith
  have hqi : (-1 : ℤ) ≤ (sk.vtx x).q g := by exact_mod_cast hqr
  have he : (sk.vtx x).q g = -1 := by omega
  refine ⟨he, ?_⟩
  rw [he] at hg
  norm_num at hg
  linarith

/-- Replace a negative integer cell by zero, retaining the fan positions and bits. -/
def Skeleton.nonnegative {s : ℕ} (sk : Skeleton s) : Skeleton s where
  vtx x := { sk.vtx x with q := fun g => max ((sk.vtx x).q g) 0 }

def Skeleton.normalizedR {s : ℕ} (sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) : Fin s → Fin (s - 1) → ℝ :=
  fun x g => r x g + ((sk.vtx x).q g : ℝ) - ((sk.nonnegative.vtx x).q g : ℝ)

lemma Skeleton.nonnegative_proper {s : ℕ} {sk : Skeleton s} (hp : sk.Proper) :
    sk.nonnegative.Proper := hp

lemma Skeleton.nonnegative_q {s : ℕ} (sk : Skeleton s) (x : Fin s)
    (g : Fin (s - 1)) : 0 ≤ (sk.nonnegative.vtx x).q g := le_max_right _ _

lemma Skeleton.normalized_gap {s : ℕ} (sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) (x : Fin s) (g : Fin (s - 1)) :
    ((sk.nonnegative.vtx x).q g : ℝ) + sk.normalizedR r x g =
      ((sk.vtx x).q g : ℝ) + r x g := by
  unfold normalizedR
  ring

lemma Skeleton.nonnegative_kexp {s : ℕ} (sk : Skeleton s) (x : Fin s) :
    (sk.nonnegative.vtx x).kexp = (sk.vtx x).kexp := by
  simp only [nonnegative, VertexData.kexp]
  apply Finset.sum_congr rfl
  intro g _
  omega

lemma Skeleton.nonnegative_W {s : ℕ} (sk : Skeleton s) (n : ℕ) :
    sk.nonnegative.W n = sk.W n := by
  simp only [Skeleton.W, Skeleton.d, nonnegative_kexp]

lemma Skeleton.normalized_angle {s n : ℕ} (sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) (δ : ℝ) (x a b : Fin s) :
    angleExpr n sk.nonnegative (sk.normalizedR r) δ x a b =
      angleExpr n sk r δ x a b := by
  have he : (∑ g ∈ (sk.vtx x).arc a b,
      (((sk.nonnegative.vtx x).q g : ℝ) + sk.normalizedR r x g)) =
      ∑ g ∈ (sk.vtx x).arc a b, (((sk.vtx x).q g : ℝ) + r x g) := by
    exact Finset.sum_congr rfl (fun g _ => sk.normalized_gap r x g)
  change (if (sk.vtx x).bits a = (sk.vtx x).bits b then
    ∑ g ∈ (sk.vtx x).arc a b,
      (((sk.nonnegative.vtx x).q g : ℝ) + sk.normalizedR r x g)
    else (n : ℝ) + δ - ∑ g ∈ (sk.vtx x).arc a b,
      (((sk.nonnegative.vtx x).q g : ℝ) + sk.normalizedR r x g)) = _
  rw [he]
  rfl

/-- Closed-box negative cells can be removed while preserving feasibility,
all angles, the chart order and the dyadic mass. -/
theorem ModeA.normalize {s n : ℕ} {sk : Skeleton s}
    {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ) (hp : sk.Proper) (hδ : 0 ≤ δ) :
    ModeA n sk.nonnegative (sk.normalizedR r) δ := by
  have hrem (x : Fin s) (g : Fin (s - 1)) :
      0 ≤ sk.normalizedR r x g ∧ sk.normalizedR r x g ≤ 1 := by
    by_cases hq : 0 ≤ (sk.vtx x).q g
    · simpa [Skeleton.normalizedR, Skeleton.nonnegative, max_eq_left hq]
        using And.intro (hA.r_nn x g) (hA.r_le x g)
    · obtain ⟨hq', hr'⟩ := hA.negative_q_boundary hp hδ x g (lt_of_not_ge hq)
      simp [Skeleton.normalizedR, Skeleton.nonnegative, hq', hr']
  refine ⟨fun x g => (hrem x g).1, fun x g => (hrem x g).2, ?_, ?_, ?_, ?_⟩
  · intro x
    have hsum : (∑ g, (((sk.nonnegative.vtx x).q g : ℝ) + sk.normalizedR r x g)) =
        ∑ g, (((sk.vtx x).q g : ℝ) + r x g) :=
      Finset.sum_congr rfl (fun g _ => sk.normalized_gap r x g)
    have hf := hA.fan x
    simp only [Finset.sum_add_distrib] at hsum
    push_cast at hf ⊢
    linarith
  · intro a b c hab hac hbc
    simpa only [Skeleton.normalized_angle] using hA.tri a b c hab hac hbc
  · intro x a b hab
    simpa only [Skeleton.normalized_angle] using hA.ang_le x a b hab
  · intro x a b hab
    simpa only [Skeleton.normalized_angle] using hA.ang_nn x a b hab

theorem Skeleton.Consistent.nonnegative {s n : ℕ} {sk : Skeleton s}
    (hc : sk.Consistent n) (hp : sk.Proper) : sk.nonnegative.Consistent n := by
  obtain ⟨r, δ, hδ, hδ1, hA⟩ := hc
  exact ⟨sk.normalizedR r, δ, hδ, hδ1, hA.normalize hp hδ⟩

/-- Gate Q for capacity proofs: every proper consistent signed-cell model
has a proper consistent nonnegative-cell model with exactly the same weight. -/
theorem exists_nonnegative_model {s n : ℕ} {sk : Skeleton s}
    (hp : sk.Proper) (hc : sk.Consistent n) :
    ∃ sk' : Skeleton s, sk'.Proper ∧ sk'.Consistent n ∧ sk'.W n = sk.W n ∧
      ∀ x g, 0 ≤ (sk'.vtx x).q g :=
  ⟨sk.nonnegative, Skeleton.nonnegative_proper hp, hc.nonnegative hp,
    sk.nonnegative_W n, sk.nonnegative_q⟩

/-- A capacity bound proved for nonnegative cells transfers to the entire
proper closed-remainder model, at the same delta and with the same weight.
This is a capacity transfer, not an unproved transport of gadget witnesses. -/
theorem capacity_of_nonnegative_models {s n : ℕ} {δ : ℝ} {B : ℚ}
    (hbound : ∀ sk' : Skeleton s, sk'.Proper → (∀ x g, 0 ≤ (sk'.vtx x).q g) →
      ∀ r', ModeA n sk' r' δ → sk'.W n ≤ B)
    {sk : Skeleton s} {r : Fin s → Fin (s - 1) → ℝ}
    (hp : sk.Proper) (hA : ModeA n sk r δ) (hδ : 0 ≤ δ) : sk.W n ≤ B := by
  have h := hbound sk.nonnegative (Skeleton.nonnegative_proper hp)
    sk.nonnegative_q (sk.normalizedR r) (hA.normalize hp hδ)
  simpa only [Skeleton.nonnegative_W] using h

#print axioms ModeA.gap_nonnegative
#print axioms ModeA.q_nonnegative_of_strict
#print axioms ModeA.negative_q_boundary
#print axioms ModeA.normalize
#print axioms exists_nonnegative_model
#print axioms capacity_of_nonnegative_models

end Jsp404
