import Jsp000404.R2SixCentreN3

/-!
# Extraction: six-centre `SatChart` → `N3Model`

Instantiates the scalar `n = 3` terminal model `N3Model` from a real
six-centre `SatChart`:

* `n3T` is the sorted list of the five non-anchor `theta` values, via
  `Finset.orderEmbOfFin` on the θ-image; `n3σ` picks the rank-to-index
  bijection with `theta (n3σ C i) = n3T i`.
* `d i j` is the shared chord `dirRep (σ i) (σ j)`; the corridor bound is
  `up_corridor` and the triple constraint combines `up_trans` betweenness
  with the `up_cap` `λ`-separation.
* `RowSig` of a defect-`2` row comes from `anchored_rowScore_eq_linear`:
  the linear gap score is `3 - 2 = 1`, and score `1` on a sorted four-chord
  rest means exactly one gap lies in `[2λ, 3λ)` and the others `< 2λ`.
-/

namespace Jsp404

open Classical
open scoped EuclideanSpace

section SixCentreN3

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
  {c : Fin 6 → Plane₂} {v : Fin 6} {theta : Fin 5 → ℝ}
  (C : SatChart o e 3 lam c v theta)

/-- `⌊g/λ⌋₊ = 2` means `g ∈ [2λ, 3λ)` and `⌊g/λ⌋₊ ≤ 1` means `g < 2λ`
(for `g ≥ 0`). -/
theorem floor_two_iff {lam g : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g) :
    ⌊g / lam⌋₊ = 2 ↔ 2 * lam ≤ g ∧ g < 3 * lam := by
  rw [Nat.floor_eq_iff (div_nonneg hg hlam.le)]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : (2:ℝ) ≤ g / lam := by exact_mod_cast h1
    have h2' : g / lam < (3:ℝ) := by
      have := h2
      push_cast at this ⊢; linarith
    rw [le_div_iff₀ hlam] at h1'
    rw [div_lt_iff₀ hlam] at h2'
    exact ⟨h1', h2'⟩
  · rintro ⟨h1, h2⟩
    have h1' : (2:ℝ) ≤ g / lam := by
      rw [le_div_iff₀ hlam]; exact h1
    have h2' : g / lam < (3:ℝ) := by
      rw [div_lt_iff₀ hlam]; exact h2
    exact ⟨by exact_mod_cast h1', by push_cast; linarith⟩

theorem floor_le_one_iff {lam g : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g) :
    ⌊g / lam⌋₊ ≤ 1 ↔ g < 2 * lam := by
  rw [show ⌊g / lam⌋₊ ≤ 1 ↔ ⌊g / lam⌋₊ < 2 from (Nat.lt_add_one_iff).symm]
  rw [Nat.floor_lt (div_nonneg hg hlam.le)]
  constructor
  · intro h; rw [div_lt_iff₀ hlam] at h; exact_mod_cast h
  · intro h; rw [div_lt_iff₀ hlam]; exact_mod_cast h

set_option maxHeartbeats 800000 in
/-- Score `1` on a sorted four-chord anchored row is the `RowSig`
signature: exactly one of the five primitive gaps lies in `[2λ, 3λ)`
and the others are `< 2λ`. -/
theorem rowSig_of_linearScore_one {lam θ : ℝ} (hlam : 0 < lam)
    {x0 x1 x2 x3 : ℝ}
    (hord : θ ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ θ + Real.pi)
    (hsc : linearGapScore lam θ (θ + Real.pi) [x0, x1, x2, x3] = 1) :
    RowSig lam Real.pi θ x0 x1 x2 x3 := by
  have hg0 : 0 ≤ x0 - θ := by linarith [hord.1]
  have hg1 : 0 ≤ x1 - x0 := by linarith [hord.2.1]
  have hg2 : 0 ≤ x2 - x1 := by linarith [hord.2.2.1]
  have hg3 : 0 ≤ x3 - x2 := by linarith [hord.2.2.2.1]
  have hg4 : 0 ≤ θ + Real.pi - x3 := by linarith [hord.2.2.2.2]
  have hsum : (⌊(x0 - θ) / lam⌋₊ - 1) + ((⌊(x1 - x0) / lam⌋₊ - 1) +
      ((⌊(x2 - x1) / lam⌋₊ - 1) + ((⌊(x3 - x2) / lam⌋₊ - 1) +
        (⌊(θ + Real.pi - x3) / lam⌋₊ - 1)))) = 1 := by
    have h := hsc
    simp only [linearGapScore, gapScore] at h
    omega
  have b0 : ⌊(x0 - θ) / lam⌋₊ ≤ 2 := by omega
  have b1 : ⌊(x1 - x0) / lam⌋₊ ≤ 2 := by omega
  have b2 : ⌊(x2 - x1) / lam⌋₊ ≤ 2 := by omega
  have b3 : ⌊(x3 - x2) / lam⌋₊ ≤ 2 := by omega
  have b4 : ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 2 := by omega
  have key :
      (⌊(x0 - θ) / lam⌋₊ = 2 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ = 2 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ = 2 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ = 2 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ = 2) := by
    by_cases k0 : ⌊(x0 - θ) / lam⌋₊ = 2
    · exact Or.inl ⟨k0, by omega, by omega, by omega, by omega⟩
    · by_cases k1 : ⌊(x1 - x0) / lam⌋₊ = 2
      · exact Or.inr (Or.inl ⟨by omega, k1, by omega, by omega, by omega⟩)
      · by_cases k2 : ⌊(x2 - x1) / lam⌋₊ = 2
        · exact Or.inr (Or.inr (Or.inl
            ⟨by omega, by omega, k2, by omega, by omega⟩))
        · by_cases k3 : ⌊(x3 - x2) / lam⌋₊ = 2
          · exact Or.inr (Or.inr (Or.inr (Or.inl
              ⟨by omega, by omega, by omega, k3, by omega⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr
              ⟨by omega, by omega, by omega, by omega, by omega⟩)))
  refine ⟨hord.1, hord.2.1, hord.2.2.1, hord.2.2.2.1, hord.2.2.2.2, ?_⟩
  rw [floor_two_iff hlam hg0, floor_two_iff hlam hg1, floor_two_iff hlam hg2,
    floor_two_iff hlam hg3, floor_two_iff hlam hg4] at key
  rw [floor_le_one_iff hlam hg0, floor_le_one_iff hlam hg1,
    floor_le_one_iff hlam hg2, floor_le_one_iff hlam hg3,
    floor_le_one_iff hlam hg4] at key
  obtain ⟨⟨p0, q0⟩, b1, b2, b3, b4⟩ | ⟨a1, ⟨p1, q1⟩, b2, b3, b4⟩ |
      ⟨a1, a2, ⟨p2, q2⟩, b3, b4⟩ | ⟨a1, a2, b1, ⟨p3, q3⟩, b4⟩ |
      ⟨a1, a2, b1, b2, ⟨p4, q4⟩⟩ := key
  · exact Or.inl ⟨p0, q0, b1, b2, b3, b4⟩
  · exact Or.inr (Or.inl ⟨a1, p1, q1, b2, b3, b4⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨a1, a2, p2, q2, b3, b4⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a1, a2, b1, p3, q3, b4⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a1, a2, b1, b2, p4, q4⟩)))

/-- Three pairwise-distinct `Fin 5` indices cannot all lie in a
two-element set `{lo, hi}`. -/
theorem n3_pigeon {lo hi a b c : Fin 5}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a = lo ∨ a = hi) (hb : b = lo ∨ b = hi)
    (hc : c = lo ∨ c = hi) : False := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> simp_all

include C

/-- Distinct non-anchor centres have distinct anchor directions:
`Up` runs in the direction of increasing `theta`. -/
theorem theta_injective : Function.Injective theta := by
  intro i j hij
  by_contra hne
  rcases up_or_up C hne with h | h
  · exact absurd hij (ne_of_lt (up_theta_lt C hne h))
  · exact absurd hij.symm (ne_of_lt (up_theta_lt C (Ne.symm hne) h))

/-- The five non-anchor `theta`s are distinct. -/
theorem n3Tcard : (Finset.image theta Finset.univ).card = 5 := by
  classical
  rw [Finset.card_image_of_injective _ (theta_injective C),
    Finset.card_univ, Fintype.card_fin]

/-- Sorted `theta` values as a strict-mono enumeration. -/
noncomputable def n3T : Fin 5 → ℝ :=
  (Finset.image theta Finset.univ).orderEmbOfFin (n3Tcard C)

theorem n3T_strictMono : StrictMono (n3T C) := fun _ _ h =>
  ((Finset.image theta Finset.univ).orderEmbOfFin _).strictMono h

/-- Rank-to-index bijection: `n3σ C i` is the centre whose `theta` is the
`i`-th smallest. -/
noncomputable def n3σ : Fin 5 → Fin 5 := fun i =>
  (Finset.mem_image.mp
    (Finset.orderEmbOfFin_mem _ (n3Tcard C) i)).choose

theorem n3σ_spec (i : Fin 5) : theta (n3σ C i) = n3T C i :=
  (Finset.mem_image.mp
    (Finset.orderEmbOfFin_mem _ (n3Tcard C) i)).choose_spec.2

theorem n3σ_injective : Function.Injective (n3σ C) := by
  intro i j hij
  apply (n3T_strictMono C).injective
  rw [← n3σ_spec C i, ← n3σ_spec C j, hij]

theorem n3σ_bijective : Function.Bijective (n3σ C) :=
  Finite.injective_iff_bijective.mp (n3σ_injective C)

theorem n3σ_ne {i j : Fin 5} (h : i ≠ j) : n3σ C i ≠ n3σ C j :=
  fun hh => h (n3σ_injective C hh)

/-- A lower-`theta` centre is always `Up` of a higher one, at `n3σ`-ranks. -/
theorem n3σ_up {i j : Fin 5} (hij : i < j) :
    Up o e c v (n3σ C i) (n3σ C j) := by
  have hlt : theta (n3σ C i) < theta (n3σ C j) := by
    rw [n3σ_spec C i, n3σ_spec C j]
    exact n3T_strictMono C hij
  exact up_of_theta_lt' C (n3σ_ne C hij.ne) hlt

/-- Corridor bounds in model coordinates. -/
theorem n3corridor {i j : Fin 5} (hij : i < j) :
    n3T C i + lam ≤
        dirRep o e (c ∘ v.succAbove) (n3σ C i) (n3σ C j) ∧
      dirRep o e (c ∘ v.succAbove) (n3σ C i) (n3σ C j) ≤
        Real.pi - lam + n3T C j := by
  have hcor := up_corridor C (n3σ_ne C hij.ne) (n3σ_up C hij)
  rwa [n3σ_spec C i, n3σ_spec C j] at hcor

/-- Triple `Up`-constraints in model coordinates. -/
theorem n3triple {i j k : Fin 5} (hij : i < j) (hjk : j < k) :
    (dirRep o e (c ∘ v.succAbove) (n3σ C i) (n3σ C j) + lam ≤
          dirRep o e (c ∘ v.succAbove) (n3σ C j) (n3σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n3σ C i) (n3σ C j) <
          dirRep o e (c ∘ v.succAbove) (n3σ C i) (n3σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n3σ C i) (n3σ C k) <
          dirRep o e (c ∘ v.succAbove) (n3σ C j) (n3σ C k)) ∨
      (dirRep o e (c ∘ v.succAbove) (n3σ C j) (n3σ C k) + lam ≤
          dirRep o e (c ∘ v.succAbove) (n3σ C i) (n3σ C j) ∧
        dirRep o e (c ∘ v.succAbove) (n3σ C j) (n3σ C k) <
          dirRep o e (c ∘ v.succAbove) (n3σ C i) (n3σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n3σ C i) (n3σ C k) <
          dirRep o e (c ∘ v.succAbove) (n3σ C i) (n3σ C j)) := by
  have hneij : n3σ C i ≠ n3σ C j := n3σ_ne C hij.ne
  have hnejk : n3σ C j ≠ n3σ C k := n3σ_ne C hjk.ne
  have hneik : n3σ C i ≠ n3σ C k := n3σ_ne C (hij.trans hjk).ne
  have hupij := n3σ_up C hij
  have hupjk := n3σ_up C hjk
  obtain ⟨-, hbetween⟩ := up_trans C hneij hnejk hneik hupij hupjk
  have hcap := up_cap C hneij hnejk hneik hupij hupjk
  rcases le_or_gt 0 (dirRep o e (c ∘ v.succAbove) (n3σ C j) (n3σ C k) -
    dirRep o e (c ∘ v.succAbove) (n3σ C i) (n3σ C j)) with hs | hs
  · rw [abs_of_nonneg hs] at hcap
    rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by linarith, h1, h2⟩
    · exfalso; linarith
  · rw [abs_of_neg hs] at hcap
    rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso; linarith
    · exact Or.inr ⟨by linarith, h1, h2⟩

/-- The scalar `n = 3` model of the six-centre configuration. -/
noncomputable def n3model : N3Model where
  lam := lam
  p := Real.pi
  hlam := C.hlam
  hp := by
    have h1 := C.hnl
    have h2 := C.hβ
    push_cast at h1 h2
    constructor <;> linarith
  t := n3T C
  ht := n3T_strictMono C
  ht0 := by
    have h := (C.htheta (n3σ C 0)).1.1
    rwa [n3σ_spec C 0] at h
  ht4 := by
    have h := (C.htheta (n3σ C 4)).1.2
    rw [n3σ_spec C 4] at h
    push_cast at h ⊢
    linarith
  d := fun i j => dirRep o e (c ∘ v.succAbove) (n3σ C i) (n3σ C j)
  hcor := fun _ _ h => n3corridor C h
  htr := fun _ _ _ h1 h2 => n3triple C h1 h2

theorem n3model_lam : (n3model C).lam = lam := rfl
theorem n3model_p : (n3model C).p = Real.pi := rfl
theorem n3model_t (i : Fin 5) : (n3model C).t i = n3T C i := rfl
theorem n3model_d (i j : Fin 5) :
    (n3model C).d i j =
      dirRep o e (c ∘ v.succAbove) (n3σ C i) (n3σ C j) := rfl

/-- Rank identification: `n3σ C r = u` iff the `r`-th sorted `theta`
value is `theta u`. -/
theorem n3σ_eq_iff (u r : Fin 5) :
    n3σ C r = u ↔ n3T C r = theta u := by
  constructor
  · intro h; rw [← n3σ_spec C r, h]
  · intro h
    exact theta_injective C ((n3σ_spec C r).trans h)

/-- Rank via bisection: if every smaller rank lies strictly below
`theta u` and `n3T C r` does not, then `n3T C r = theta u`. -/
theorem n3T_eq_of_bounds (u : Fin 5) (r : Fin 5)
    (hlo : ∀ s : Fin 5, s < r → n3T C s < theta u)
    (hhi : theta u ≤ n3T C r) :
    n3T C r = theta u := by
  obtain ⟨r', hr'⟩ : ∃ r' : Fin 5, n3T C r' = theta u := by
    have hmem : theta u ∈ Set.range
        ⇑((Finset.image theta Finset.univ).orderEmbOfFin (n3Tcard C)) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩)
    exact hmem
  rcases lt_trichotomy r' r with hlt | heq | hgt
  · exact absurd (hlo r' hlt) (by rw [hr']; exact lt_irrefl _)
  · exact heq ▸ hr'
  · have h2 := n3T_strictMono C hgt
    rw [hr'] at h2
    linarith

/-- A defect-`2` row at `n = 3` yields the sorted four-chord list of the
row at chart index `u = n3σ C r`, carrying `RowSig` and a `List.Perm`
onto the model chords. -/
theorem n3_row_exists {r u : Fin 5} (hu : n3σ C r = u)
    (hd : rowDefect 3 lam (directionRow o e c (v.succAbove u)) = 2) :
    ∃ x0 x1 x2 x3 : ℝ,
      List.Perm [x0, x1, x2, x3]
        (((List.finRange 5).erase r).map fun j => (n3model C).d r j) ∧
      RowSig lam Real.pi (n3T C r) x0 x1 x2 x3 := by
  classical
  have hTu : n3T C r = theta u := (n3σ_eq_iff C u r).mp hu
  have hlen : (directionRow o e (c ∘ v.succAbove) u).length = 4 := by
    have h := directionRow_length o e (c ∘ v.succAbove) u
    omega
  obtain ⟨x0, x1, x2, x3, hrest⟩ := List.length_eq_four.mp hlen
  have hsort := directionRow_sorted o e (c ∘ v.succAbove) u
  rw [hrest] at hsort
  obtain ⟨h01', hs1⟩ := List.sortedLE_cons.mp hsort
  obtain ⟨h12', hs2⟩ := List.sortedLE_cons.mp hs1
  obtain ⟨h23', -⟩ := List.sortedLE_cons.mp hs2
  have e01 : x0 ≤ x1 := h01' x1 (by simp)
  have e12 : x1 ≤ x2 := h12' x2 (by simp)
  have e23 : x2 ≤ x3 := h23' x3 (by simp)
  have hmem : ∀ x ∈ directionRow o e (c ∘ v.succAbove) u,
      lam ≤ x ∧ x < Real.pi := by
    intro x hx
    obtain ⟨j, hju, rfl⟩ := (mem_directionRow o e (c ∘ v.succAbove)).mp hx
    exact ⟨phi_ge_lam C (Ne.symm hju), (linRep_mem_Ico _).2⟩
  have hβ : Real.pi - 3 * lam < lam := by exact_mod_cast C.hβ
  have hx0ge : theta u ≤ x0 := by
    have hx := (hmem x0 (by rw [hrest]; simp)).1
    have hθ : theta u ≤ Real.pi - 3 * lam := by
      exact_mod_cast (C.htheta u).1.2
    linarith
  have hx3le : x3 ≤ theta u + Real.pi := by
    have hx := (hmem x3 (by rw [hrest]; simp)).2
    have hθ0 := (C.htheta u).1.1
    linarith
  have hlampi : lam < Real.pi := by
    have h1 := C.hnl; have h2 := C.hn3'; have h3 := C.hlam; nlinarith
  have htheta' : ∀ i, theta i ∈ Set.Icc 0 lam ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle) := by
    intro i
    refine ⟨?_, (C.htheta i).2⟩
    have h := (C.htheta i).1
    rw [Set.mem_Icc] at h ⊢
    have h2 : theta i ≤ Real.pi - 3 * lam := by exact_mod_cast h.2
    exact ⟨h.1, by linarith⟩
  have hscore := anchored_rowScore_eq_linear o e C.he c C.hleg.inj v C.hlam
    hlampi theta htheta' (fun a b hab => phi_ge_lam C hab) u
  have hcells := rowCells_directionRow_le_of_floor_eq o e c C.hlam
    (v.succAbove u) (by omega) C.hn
  have hsub := rowScore_eq_sub_defect lam C.hlam 3 _ hcells
  rw [hscore, hd] at hsub
  have hsc : linearGapScore lam (theta u) (theta u + Real.pi)
      [x0, x1, x2, x3] = 1 := by
    rw [hrest] at hsub; omega
  have hord : theta u ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧
      x3 ≤ theta u + Real.pi := ⟨hx0ge, e01, e12, e23, hx3le⟩
  have hS : RowSig lam Real.pi (theta u) x0 x1 x2 x3 :=
    rowSig_of_linearScore_one C.hlam hord hsc
  rw [← hTu] at hS
  refine ⟨x0, x1, x2, x3, ?_, hS⟩
  rw [← hrest]
  have hp1 : List.Perm (directionRow o e (c ∘ v.succAbove) u)
      (((List.finRange 5).erase u).map
        (dirRep o e (c ∘ v.succAbove) u)) :=
    List.perm_insertionSort _ _
  have hmap : List.Perm ((List.finRange 5).erase u)
      (((List.finRange 5).erase r).map (n3σ C)) := by
    apply List.Subperm.antisymm
    · apply List.Nodup.subperm ((List.nodup_finRange 5).erase u)
      intro x hx
      rw [(List.nodup_finRange 5).mem_erase_iff] at hx
      obtain ⟨j, hj⟩ := (n3σ_bijective C).surjective x
      refine List.mem_map.mpr ⟨j, ?_, hj⟩
      rw [(List.nodup_finRange 5).mem_erase_iff]
      exact ⟨fun hjr => hx.1 (by rw [← hj, hjr, hu]), List.mem_finRange _⟩
    · apply List.Nodup.subperm
        (((List.nodup_finRange 5).erase r).map (n3σ_injective C))
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨j, hje, rfl⟩ := hx
      rw [(List.nodup_finRange 5).mem_erase_iff] at hje ⊢
      exact ⟨fun hxu => hje.1 (n3σ_injective C (hxu.trans hu.symm)),
        List.mem_finRange _⟩
  have hp2 := hmap.map (dirRep o e (c ∘ v.succAbove) u)
  rw [List.map_map] at hp2
  refine hp1.trans (hp2.trans ?_)
  have hfeq : (dirRep o e (c ∘ v.succAbove) u ∘ n3σ C) =
      fun j => (n3model C).d r j := by
    funext j
    show dirRep o e (c ∘ v.succAbove) u (n3σ C j) = (n3model C).d r j
    rw [n3model_d C r j, hu]
  rw [hfeq]

/-- Chord symmetry in the model. -/
theorem n3d_comm (i j : Fin 5) (h : i ≠ j) :
    (n3model C).d i j = (n3model C).d j i := by
  have h' : n3σ C i ≠ n3σ C j := n3σ_ne C h
  exact phi_comm C h'

/-- All-above class: the two defect-`2` rows occupy ranks `0` and `1`. -/
theorem n3σ_zero_one_of_all_above {lo hi : Fin 5} (hθ : theta lo < theta hi)
    (hcl : ∀ z : Fin 5, z ≠ lo → z ≠ hi → theta hi < theta z) :
    n3σ C 0 = lo ∧ n3σ C 1 = hi := by
  have hge : ∀ z : Fin 5, theta lo ≤ theta z := by
    intro z
    rcases eq_or_ne z lo with rfl | h1
    · exact le_refl _
    · rcases eq_or_ne z hi with rfl | h2
      · exact hθ.le
      · exact (hθ.trans (hcl z h1 h2)).le
  have hT0 : n3T C 0 = theta lo := by
    apply n3T_eq_of_bounds C lo 0
    · intro s hs; exact absurd hs (Nat.not_lt_zero s.val)
    · rw [← n3σ_spec C 0]; exact hge _
  have hσ0 : n3σ C 0 = lo := (n3σ_eq_iff C lo 0).mpr hT0
  have hT1 : n3T C 1 = theta hi := by
    apply n3T_eq_of_bounds C hi 1
    · intro s hs
      have hs0 : s = 0 := Fin.ext (Nat.lt_one_iff.mp hs)
      rw [hs0, hT0]; exact hθ
    · rw [← n3σ_spec C 1]
      rcases eq_or_ne (n3σ C 1) lo with h1 | h1
      · exact absurd (n3σ_injective C (h1.trans hσ0.symm)) (by decide)
      · rcases eq_or_ne (n3σ C 1) hi with rfl | h2
        · exact le_refl _
        · exact (hcl _ h1 h2).le
  exact ⟨hσ0, (n3σ_eq_iff C hi 1).mpr hT1⟩

/-- All-below class: the two defect-`2` rows occupy ranks `3` and `4`. -/
theorem n3σ_three_four_of_all_below {lo hi : Fin 5} (hθ : theta lo < theta hi)
    (hcl : ∀ z : Fin 5, z ≠ lo → z ≠ hi → theta z < theta lo) :
    n3σ C 3 = lo ∧ n3σ C 4 = hi := by
  have hle : ∀ z : Fin 5, theta z ≤ theta hi := by
    intro z
    rcases eq_or_ne z hi with rfl | h1
    · exact le_refl _
    · rcases eq_or_ne z lo with rfl | h2
      · exact hθ.le
      · exact ((hcl z h2 h1).trans hθ).le
  have hT4 : n3T C 4 = theta hi := by
    apply n3T_eq_of_bounds C hi 4
    · intro s hs
      rw [← n3σ_spec C s]
      rcases eq_or_ne (n3σ C s) hi with h1 | h1
      · exfalso
        have hmax : n3T C 4 ≤ theta hi := by
          rw [← n3σ_spec C 4]; exact hle _
        have hlt : n3T C s < n3T C 4 := n3T_strictMono C hs
        rw [← n3σ_spec C s, h1] at hlt
        linarith
      · rcases eq_or_ne (n3σ C s) lo with rfl | h2
        · exact hθ
        · exact (hcl _ h2 h1).trans hθ
    · obtain ⟨r', hr'⟩ := (n3σ_bijective C).surjective hi
      have hle4 : r' ≤ (4 : Fin 5) := by
        rw [Fin.le_iff_val_le_val]
        exact Nat.le_of_lt_succ r'.isLt
      have hm := (n3T_strictMono C).monotone hle4
      rw [← n3σ_spec C r', hr'] at hm
      exact hm
  have hσ4 : n3σ C 4 = hi := (n3σ_eq_iff C hi 4).mpr hT4
  have hT3 : n3T C 3 = theta lo := by
    apply n3T_eq_of_bounds C lo 3
    · intro s hs
      rw [← n3σ_spec C s]
      by_contra hnn
      replace hnn := not_lt.mp hnn
      have h1 : n3σ C s = lo ∨ n3σ C s = hi := by
        rcases eq_or_ne (n3σ C s) lo with h | h
        · exact Or.inl h
        · rcases eq_or_ne (n3σ C s) hi with h' | h'
          · exact Or.inr h'
          · exact absurd (hcl _ h h') (not_lt.mpr hnn)
      have h3 : n3σ C 3 = lo ∨ n3σ C 3 = hi := by
        have hge3 : theta lo ≤ n3T C 3 := by
          have hlt := n3T_strictMono C hs
          rw [← n3σ_spec C s] at hlt
          linarith
        rw [← n3σ_spec C 3] at hge3
        rcases eq_or_ne (n3σ C 3) lo with h | h
        · exact Or.inl h
        · rcases eq_or_ne (n3σ C 3) hi with h' | h'
          · exact Or.inr h'
          · exact absurd (hcl _ h h') (not_lt.mpr hge3)
      have h4 : n3σ C 4 = lo ∨ n3σ C 4 = hi := by
        have hge4 : theta lo ≤ n3T C 4 := by
          have hlt := n3T_strictMono C
            (hs.trans (by decide : (3 : Fin 5) < 4))
          rw [← n3σ_spec C s] at hlt
          linarith
        rw [← n3σ_spec C 4] at hge4
        rcases eq_or_ne (n3σ C 4) lo with h | h
        · exact Or.inl h
        · rcases eq_or_ne (n3σ C 4) hi with h' | h'
          · exact Or.inr h'
          · exact absurd (hcl _ h h') (not_lt.mpr hge4)
      exact n3_pigeon
        (fun h => (ne_of_lt hs) (n3σ_injective C h))
        (fun h => (ne_of_lt (hs.trans (by decide : (3 : Fin 5) < 4)))
          (n3σ_injective C h))
        (fun h => absurd (n3σ_injective C h) (by decide))
        h1 h3 h4
    · rw [← n3σ_spec C 3]
      rcases eq_or_ne (n3σ C 3) hi with h3hi | h3hi
      · exact absurd (n3σ_injective C (h3hi.trans hσ4.symm)) (by decide)
      · rcases eq_or_ne (n3σ C 3) lo with rfl | h3lo
        · exact le_refl _
        · exfalso
          obtain ⟨r_l, hr_l⟩ := (n3σ_bijective C).surjective lo
          have hrl3 : r_l ≠ 3 := fun h => h3lo (h ▸ hr_l)
          have hrl4 : r_l ≠ 4 := fun h =>
            hθ.ne (by rw [← hr_l, ← hσ4, h])
          have hrl2 : r_l.val ≤ 2 := by
            have hlt5 := r_l.isLt
            have h3v : r_l.val ≠ 3 := fun hv => hrl3 (Fin.ext hv)
            have h4v : r_l.val ≠ 4 := fun hv => hrl4 (Fin.ext hv)
            omega
          have hlt : n3T C r_l < n3T C 3 := by
            apply n3T_strictMono C
            rw [Fin.lt_def]
            omega
          rw [← n3σ_spec C r_l, hr_l] at hlt
          have hcl3 : n3T C 3 < theta lo := by
            have h := hcl _ h3lo h3hi
            rwa [n3σ_spec C 3] at h
          linarith
  exact ⟨(n3σ_eq_iff C lo 3).mpr hT3, hσ4⟩

/-- Between class: the two defect-`2` rows occupy ranks `0` and `4`. -/
theorem n3σ_zero_four_of_between {lo hi : Fin 5} (hθ : theta lo < theta hi)
    (hcl : ∀ z : Fin 5, z ≠ lo → z ≠ hi →
      theta lo < theta z ∧ theta z < theta hi) :
    n3σ C 0 = lo ∧ n3σ C 4 = hi := by
  have hge : ∀ z : Fin 5, theta lo ≤ theta z := by
    intro z
    rcases eq_or_ne z lo with rfl | h1
    · exact le_refl _
    · rcases eq_or_ne z hi with rfl | h2
      · exact hθ.le
      · exact (hcl z h1 h2).1.le
  have hle : ∀ z : Fin 5, theta z ≤ theta hi := by
    intro z
    rcases eq_or_ne z hi with rfl | h1
    · exact le_refl _
    · rcases eq_or_ne z lo with rfl | h2
      · exact hθ.le
      · exact (hcl z h2 h1).2.le
  have hT0 : n3T C 0 = theta lo := by
    apply n3T_eq_of_bounds C lo 0
    · intro s hs; exact absurd hs (Nat.not_lt_zero s.val)
    · rw [← n3σ_spec C 0]; exact hge _
  have hT4 : n3T C 4 = theta hi := by
    apply n3T_eq_of_bounds C hi 4
    · intro s hs
      rw [← n3σ_spec C s]
      rcases eq_or_ne (n3σ C s) hi with h1 | h1
      · exfalso
        have hmax : n3T C 4 ≤ theta hi := by
          rw [← n3σ_spec C 4]; exact hle _
        have hlt : n3T C s < n3T C 4 := n3T_strictMono C hs
        rw [← n3σ_spec C s, h1] at hlt
        linarith
      · rcases eq_or_ne (n3σ C s) lo with rfl | h2
        · exact hθ
        · exact (hcl _ h2 h1).2
    · obtain ⟨r', hr'⟩ := (n3σ_bijective C).surjective hi
      have hle4 : r' ≤ (4 : Fin 5) := by
        rw [Fin.le_iff_val_le_val]
        exact Nat.le_of_lt_succ r'.isLt
      have hm := (n3T_strictMono C).monotone hle4
      rw [← n3σ_spec C r', hr'] at hm
      exact hm
  exact ⟨(n3σ_eq_iff C lo 0).mpr hT0, (n3σ_eq_iff C hi 4).mpr hT4⟩

end SixCentreN3

section N3Terminal

/-- **Six-centre `n = 3` terminal exclusion.**  A six-centre
configuration at `n = 3` with a saturated anchor and two defect-`2`
rows is impossible: `six_centre_theta_class` places the two low rows at
θ-ranks `(0,1)`, `(0,4)` or `(3,4)`, and each class contradicts the
`N3Model` leaf theorems (`n3_row1`, `n3_between`, `n3_row3`).  The
defect hypotheses are transported to the chart reference `e'` via
`rowDefect_directionRow_reference_eq`. -/
theorem six_centre_n3_terminal
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 3)
    {c : Fin 6 → Plane₂} (hleg : Section4Legality c lam)
    {v A B : Fin 6} (hvA : v ≠ A) (hvB : v ≠ B) (hAB : A ≠ B)
    (hsat : rowDefect 3 lam (directionRow o e c v) = 1)
    (hdA : rowDefect 3 lam (directionRow o e c A) = 2)
    (hdB : rowDefect 3 lam (directionRow o e c B) = 2) : False := by
  classical
  obtain ⟨e', he', theta, C, lo, hi, hswap, hθlt, hclass⟩ :=
    six_centre_theta_class o e he (le_refl 3) hlam hn hleg hvA hvB hAB
      hsat hdA hdB
  have href : ∀ x : Fin 6,
      rowDefect 3 lam (directionRow o e' c x) =
        rowDefect 3 lam (directionRow o e c x) :=
    fun x => rowDefect_directionRow_reference_eq o e' e he' he c
      hleg.inj x hlam (by omega) hn
  have hdlo : rowDefect 3 lam (directionRow o e' c (v.succAbove lo)) = 2 := by
    rcases hswap with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1, href] <;> assumption
  have hdhi : rowDefect 3 lam (directionRow o e' c (v.succAbove hi)) = 2 := by
    rcases hswap with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2, href] <;> assumption
  rcases hclass with hbelow | hbetween | habove
  · -- All-below: low rows at ranks `3` and `4`; row `3` alone is UNSAT.
    obtain ⟨hσ3, -⟩ := n3σ_three_four_of_all_below C hθlt hbelow
    obtain ⟨x0, x1, x2, x3, hperm, hS⟩ := n3_row_exists C hσ3 hdlo
    have hpl : List.Perm [x0, x1, x2, x3]
        [(n3model C).d 0 3, (n3model C).d 1 3, (n3model C).d 2 3,
         (n3model C).d 3 4] := by
      have h := hperm
      rw [show (((List.finRange 5).erase (3 : Fin 5)).map
            fun j => (n3model C).d 3 j) =
          [(n3model C).d 3 0, (n3model C).d 3 1, (n3model C).d 3 2,
           (n3model C).d 3 4] from rfl] at h
      rw [n3d_comm C 3 0 (by decide), n3d_comm C 3 1 (by decide),
        n3d_comm C 3 2 (by decide)] at h
      exact h
    exact n3_row3 (n3model C) hpl hS
  · -- Between: low rows at ranks `0` and `4`; the pair is UNSAT.
    obtain ⟨hσ0, hσ4⟩ := n3σ_zero_four_of_between C hθlt hbetween
    obtain ⟨x0, x1, x2, x3, hperm0, hS0⟩ := n3_row_exists C hσ0 hdlo
    obtain ⟨y0, y1, y2, y3, hperm4, hS4⟩ := n3_row_exists C hσ4 hdhi
    have hpl0 : List.Perm [x0, x1, x2, x3]
        [(n3model C).d 0 1, (n3model C).d 0 2, (n3model C).d 0 3,
         (n3model C).d 0 4] := by
      have h := hperm0
      rw [show (((List.finRange 5).erase (0 : Fin 5)).map
            fun j => (n3model C).d 0 j) =
          [(n3model C).d 0 1, (n3model C).d 0 2, (n3model C).d 0 3,
           (n3model C).d 0 4] from rfl] at h
      exact h
    have hpl4 : List.Perm [y0, y1, y2, y3]
        [(n3model C).d 0 4, (n3model C).d 1 4, (n3model C).d 2 4,
         (n3model C).d 3 4] := by
      have h := hperm4
      rw [show (((List.finRange 5).erase (4 : Fin 5)).map
            fun j => (n3model C).d 4 j) =
          [(n3model C).d 4 0, (n3model C).d 4 1, (n3model C).d 4 2,
           (n3model C).d 4 3] from rfl] at h
      rw [n3d_comm C 4 0 (by decide), n3d_comm C 4 1 (by decide),
        n3d_comm C 4 2 (by decide), n3d_comm C 4 3 (by decide)] at h
      exact h
    exact n3_between (n3model C) hpl0 hS0 hpl4 hS4
  · -- All-above: low rows at ranks `0` and `1`; row `1` alone is UNSAT.
    obtain ⟨-, hσ1⟩ := n3σ_zero_one_of_all_above C hθlt habove
    obtain ⟨x0, x1, x2, x3, hperm, hS⟩ := n3_row_exists C hσ1 hdhi
    have hpl : List.Perm [x0, x1, x2, x3]
        [(n3model C).d 0 1, (n3model C).d 1 2, (n3model C).d 1 3,
         (n3model C).d 1 4] := by
      have h := hperm
      rw [show (((List.finRange 5).erase (1 : Fin 5)).map
            fun j => (n3model C).d 1 j) =
          [(n3model C).d 1 0, (n3model C).d 1 2, (n3model C).d 1 3,
           (n3model C).d 1 4] from rfl] at h
      rw [n3d_comm C 1 0 (by decide)] at h
      exact h
    exact n3_row1 (n3model C) hpl hS

#print axioms six_centre_n3_terminal
#print axioms n3_row_exists
#print axioms rowSig_of_linearScore_one
#print axioms n3σ_three_four_of_all_below
#print axioms n3σ_zero_four_of_between
#print axioms n3σ_zero_one_of_all_above

end N3Terminal

end Jsp404
