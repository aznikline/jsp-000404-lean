import Jsp000404.S7Certs
import Jsp000404.S7ScoreLemmas
import Jsp000404.N4Extraction

set_option maxHeartbeats 40000000

/-!
# Extraction: seven-centre `SatChart` → `N7Model`

Instantiates the scalar `n = 4` terminal model `R2N4.N7Model` from a
real seven-centre `SatChart`, parallel to `N4Extraction`:

* `n7T` / `n7σ` are the sorted non-anchor `theta` values and the
  rank-to-index bijection.
* `d i j` is the shared chord `dirRep (σ i) (σ j)`; `n7corridor` and
  `n7triple` replay `up_corridor`, `up_trans` and `up_cap`.
* `n7_row2_exists` / `n7_row1_exists` extract the sorted five-chord
  row at a chart index together with its `RowSig2_7` (defect `2`,
  score `2`) or `RowSig1_7` (defect `3`, score `1`) signature and the
  `List.Perm` onto the model chords.
* The twelve terminal theorems `seven_centre_n4_AA2`–`AA5`,
  `…_AB0`–`AB3`, `…_BT1`–`BT4` close the residual geometric position
  classes: the two defect-`2` rows sit at θ-ranks `{0,1}`, `{4,5}`
  or `{0,5}` and the defect-`3` row at any of the remaining ranks,
  contradicted by the generated leaf certificates `s7cert_*`.
-/

namespace Jsp404

open Classical
open scoped EuclideanSpace

/-- A five-element list splits into its literals. -/
private theorem length_eq_five {α : Type*} {l : List α}
    (h : l.length = 5) :
    ∃ a b c d e : α, l = [a, b, c, d, e] := by
  cases l with
  | nil => simp at h
  | cons a l' =>
    rw [List.length_cons] at h
    obtain ⟨b, c, d, e, rfl⟩ :=
      List.length_eq_four.mp (show l'.length = 4 by omega)
    exact ⟨a, b, c, d, e, rfl⟩

section SevenCentreN4

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
  {c : Fin 7 → Plane₂} {v : Fin 7} {theta : Fin 6 → ℝ}
  (C : SatChart o e 4 lam c v theta)

include C

/-- Distinct non-anchor centres have distinct anchor directions. -/
theorem n7theta_injective : Function.Injective theta := by
  intro i j hij
  by_contra hne
  rcases up_or_up C hne with h | h
  · exact absurd hij (ne_of_lt (up_theta_lt C hne h))
  · exact absurd hij.symm (ne_of_lt (up_theta_lt C (Ne.symm hne) h))

/-- The six non-anchor `theta`s are distinct. -/
theorem n7Tcard : (Finset.image theta Finset.univ).card = 6 := by
  classical
  rw [Finset.card_image_of_injective _ (n7theta_injective C),
    Finset.card_univ, Fintype.card_fin]

/-- Sorted `theta` values as a strict-mono enumeration. -/
noncomputable def n7T : Fin 6 → ℝ :=
  (Finset.image theta Finset.univ).orderEmbOfFin (n7Tcard C)

theorem n7T_strictMono : StrictMono (n7T C) := fun _ _ h =>
  ((Finset.image theta Finset.univ).orderEmbOfFin _).strictMono h

/-- Rank-to-index bijection: `n7σ C i` is the centre whose `theta` is
the `i`-th smallest. -/
noncomputable def n7σ : Fin 6 → Fin 6 := fun i =>
  (Finset.mem_image.mp
    (Finset.orderEmbOfFin_mem _ (n7Tcard C) i)).choose

theorem n7σ_spec (i : Fin 6) : theta (n7σ C i) = n7T C i :=
  (Finset.mem_image.mp
    (Finset.orderEmbOfFin_mem _ (n7Tcard C) i)).choose_spec.2

theorem n7σ_injective : Function.Injective (n7σ C) := by
  intro i j hij
  apply (n7T_strictMono C).injective
  rw [← n7σ_spec C i, ← n7σ_spec C j, hij]

theorem n7σ_bijective : Function.Bijective (n7σ C) :=
  Finite.injective_iff_bijective.mp (n7σ_injective C)

theorem n7σ_ne {i j : Fin 6} (h : i ≠ j) : n7σ C i ≠ n7σ C j :=
  fun hh => h (n7σ_injective C hh)

/-- A lower-`theta` centre is always `Up` of a higher one, at
`n7σ`-ranks. -/
theorem n7σ_up {i j : Fin 6} (hij : i < j) :
    Up o e c v (n7σ C i) (n7σ C j) := by
  have hlt : theta (n7σ C i) < theta (n7σ C j) := by
    rw [n7σ_spec C i, n7σ_spec C j]
    exact n7T_strictMono C hij
  exact up_of_theta_lt' C (n7σ_ne C hij.ne) hlt

/-- Corridor bounds in model coordinates. -/
theorem n7corridor {i j : Fin 6} (hij : i < j) :
    n7T C i + lam ≤
        dirRep o e (c ∘ v.succAbove) (n7σ C i) (n7σ C j) ∧
      dirRep o e (c ∘ v.succAbove) (n7σ C i) (n7σ C j) ≤
        Real.pi - lam + n7T C j := by
  have hcor := up_corridor C (n7σ_ne C hij.ne) (n7σ_up C hij)
  rwa [n7σ_spec C i, n7σ_spec C j] at hcor

/-- Triple `Up`-constraints in model coordinates. -/
theorem n7triple {i j k : Fin 6} (hij : i < j) (hjk : j < k) :
    (dirRep o e (c ∘ v.succAbove) (n7σ C i) (n7σ C j) + lam ≤
          dirRep o e (c ∘ v.succAbove) (n7σ C j) (n7σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n7σ C i) (n7σ C j) <
          dirRep o e (c ∘ v.succAbove) (n7σ C i) (n7σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n7σ C i) (n7σ C k) <
          dirRep o e (c ∘ v.succAbove) (n7σ C j) (n7σ C k)) ∨
      (dirRep o e (c ∘ v.succAbove) (n7σ C j) (n7σ C k) + lam ≤
          dirRep o e (c ∘ v.succAbove) (n7σ C i) (n7σ C j) ∧
        dirRep o e (c ∘ v.succAbove) (n7σ C j) (n7σ C k) <
          dirRep o e (c ∘ v.succAbove) (n7σ C i) (n7σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n7σ C i) (n7σ C k) <
          dirRep o e (c ∘ v.succAbove) (n7σ C i) (n7σ C j)) := by
  have hl0 : 0 < lam := C.hlam
  have hneij : n7σ C i ≠ n7σ C j := n7σ_ne C hij.ne
  have hnejk : n7σ C j ≠ n7σ C k := n7σ_ne C hjk.ne
  have hneik : n7σ C i ≠ n7σ C k := n7σ_ne C (hij.trans hjk).ne
  have hupij := n7σ_up C hij
  have hupjk := n7σ_up C hjk
  obtain ⟨-, hbetween⟩ := up_trans C hneij hnejk hneik hupij hupjk
  have hcap := up_cap C hneij hnejk hneik hupij hupjk
  rcases le_or_gt 0 (dirRep o e (c ∘ v.succAbove) (n7σ C j) (n7σ C k) -
    dirRep o e (c ∘ v.succAbove) (n7σ C i) (n7σ C j)) with hs | hs
  · rw [abs_of_nonneg hs] at hcap
    rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by linarith, h1, h2⟩
    · exfalso; linarith
  · rw [abs_of_neg hs] at hcap
    rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso; linarith
    · exact Or.inr ⟨by linarith, h1, h2⟩

/-- The scalar `n = 4` model of the seven-centre configuration. -/
noncomputable def n7model : R2N4.N7Model where
  lam := lam
  p := Real.pi
  hlam := C.hlam
  hp := by
    have h1 := C.hnl
    have h2 := C.hπ
    push_cast at h1 h2
    constructor <;> linarith
  t := n7T C
  ht := n7T_strictMono C
  ht0 := by
    have h := (C.htheta (n7σ C 0)).1.1
    rwa [n7σ_spec C 0] at h
  ht5 := by
    have h := (C.htheta (n7σ C 5)).1.2
    rw [n7σ_spec C 5] at h
    push_cast at h ⊢
    linarith
  d := fun i j => dirRep o e (c ∘ v.succAbove) (n7σ C i) (n7σ C j)
  hcor := fun _ _ h => n7corridor C h
  htr := fun _ _ _ h1 h2 => n7triple C h1 h2

theorem n7model_lam : (n7model C).lam = lam := rfl
theorem n7model_p : (n7model C).p = Real.pi := rfl
theorem n7model_t (i : Fin 6) : (n7model C).t i = n7T C i := rfl
theorem n7model_d (i j : Fin 6) :
    (n7model C).d i j =
      dirRep o e (c ∘ v.succAbove) (n7σ C i) (n7σ C j) := rfl

/-- Rank identification: `n7σ C r = u` iff the `r`-th sorted `theta`
value is `theta u`. -/
theorem n7σ_eq_iff (u r : Fin 6) :
    n7σ C r = u ↔ n7T C r = theta u := by
  constructor
  · intro h; rw [← n7σ_spec C r, h]
  · intro h
    exact n7theta_injective C ((n7σ_spec C r).trans h)

/-- Rank via bisection: if every smaller rank lies strictly below
`theta u` and `n7T C r` does not, then `n7T C r = theta u`. -/
theorem n7T_eq_of_bounds (u : Fin 6) (r : Fin 6)
    (hlo : ∀ s : Fin 6, s < r → n7T C s < theta u)
    (hhi : theta u ≤ n7T C r) :
    n7T C r = theta u := by
  obtain ⟨r', hr'⟩ : ∃ r' : Fin 6, n7T C r' = theta u := by
    have hmem : theta u ∈ Set.range
        ⇑((Finset.image theta Finset.univ).orderEmbOfFin
          (n7Tcard C)) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩)
    exact hmem
  rcases lt_trichotomy r' r with hlt | heq | hgt
  · exact absurd (hlo r' hlt) (by rw [hr']; exact lt_irrefl _)
  · exact heq ▸ hr'
  · have h2 := n7T_strictMono C hgt
    rw [hr'] at h2
    linarith

/-- Chord symmetry in the model. -/
theorem n7d_comm (i j : Fin 6) (h : i ≠ j) :
    (n7model C).d i j = (n7model C).d j i := by
  have h' : n7σ C i ≠ n7σ C j := n7σ_ne C h
  exact phi_comm C h'

/-- Common core of `n7_row_exists`: the sorted five-chord list of the
row at chart index `u = n7σ C r`, with ordering and `List.Perm` onto
the model chords.  The score is returned for signature dispatch. -/
theorem n7_row_core {r u : Fin 6} (hu : n7σ C r = u)
    (hd : rowDefect 4 lam (directionRow o e c (v.succAbove u)) = 2 ∨
      rowDefect 4 lam (directionRow o e c (v.succAbove u)) = 3) :
    ∃ x0 x1 x2 x3 x4 : ℝ,
      (n7T C r ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧
        x4 ≤ n7T C r + Real.pi) ∧
      linearGapScore lam (n7T C r) (n7T C r + Real.pi)
          [x0, x1, x2, x3, x4] = 4 - rowDefect 4 lam
            (directionRow o e c (v.succAbove u)) ∧
      List.Perm [x0, x1, x2, x3, x4]
        (((List.finRange 6).erase r).map fun j =>
          (n7model C).d r j) := by
  classical
  have hTu : n7T C r = theta u := (n7σ_eq_iff C u r).mp hu
  have hlen : (directionRow o e (c ∘ v.succAbove) u).length = 5 := by
    have h := directionRow_length o e (c ∘ v.succAbove) u
    omega
  obtain ⟨x0, x1, x2, x3, x4, hrest⟩ := length_eq_five hlen
  have hsort := directionRow_sorted o e (c ∘ v.succAbove) u
  rw [hrest] at hsort
  obtain ⟨h01', hs1⟩ := List.sortedLE_cons.mp hsort
  obtain ⟨h12', hs2⟩ := List.sortedLE_cons.mp hs1
  obtain ⟨h23', hs3⟩ := List.sortedLE_cons.mp hs2
  obtain ⟨h34', -⟩ := List.sortedLE_cons.mp hs3
  have e01 : x0 ≤ x1 := h01' x1 (by simp)
  have e12 : x1 ≤ x2 := h12' x2 (by simp)
  have e23 : x2 ≤ x3 := h23' x3 (by simp)
  have e34 : x3 ≤ x4 := h34' x4 (by simp)
  have hmem : ∀ x ∈ directionRow o e (c ∘ v.succAbove) u,
      lam ≤ x ∧ x < Real.pi := by
    intro x hx
    obtain ⟨j, hju, rfl⟩ := (mem_directionRow o e
      (c ∘ v.succAbove)).mp hx
    exact ⟨phi_ge_lam C (Ne.symm hju), (linRep_mem_Ico _).2⟩
  have hβ : Real.pi - 4 * lam < lam := by exact_mod_cast C.hβ
  have hx0ge : theta u ≤ x0 := by
    have hx := (hmem x0 (by rw [hrest]; simp)).1
    have hθ : theta u ≤ Real.pi - 4 * lam := by
      exact_mod_cast (C.htheta u).1.2
    linarith
  have hx4le : x4 ≤ theta u + Real.pi := by
    have hx := (hmem x4 (by rw [hrest]; simp)).2
    have hθ0 := (C.htheta u).1.1
    linarith
  have hlampi : lam < Real.pi := by
    have h1 := C.hnl; have h2 := C.hn3'; have h3 := C.hlam; nlinarith
  have htheta' : ∀ i, theta i ∈ Set.Icc 0 lam ∧
      o.oangle e (c (v.succAbove i) - c v) =
        (theta i : Real.Angle) := by
    intro i
    refine ⟨?_, (C.htheta i).2⟩
    have h := (C.htheta i).1
    rw [Set.mem_Icc] at h ⊢
    have h2 : theta i ≤ Real.pi - 4 * lam := by exact_mod_cast h.2
    exact ⟨h.1, by linarith⟩
  have hscore := anchored_rowScore_eq_linear o e C.he c C.hleg.inj v
    C.hlam hlampi theta htheta' (fun a b hab => phi_ge_lam C hab) u
  have hcells := rowCells_directionRow_le_of_floor_eq o e c C.hlam
    (v.succAbove u) (by omega) C.hn
  have hsub := rowScore_eq_sub_defect lam C.hlam 4 _ hcells
  rw [hscore, hrest, ← hTu] at hsub
  refine ⟨x0, x1, x2, x3, x4, ?_, hsub, ?_⟩
  · rw [hTu]
    exact ⟨hx0ge, e01, e12, e23, e34, hx4le⟩
  have hp1 : List.Perm (directionRow o e (c ∘ v.succAbove) u)
      (((List.finRange 6).erase u).map
        (dirRep o e (c ∘ v.succAbove) u)) :=
    List.perm_insertionSort _ _
  rw [hrest] at hp1
  have hmap : List.Perm ((List.finRange 6).erase u)
      (((List.finRange 6).erase r).map (n7σ C)) := by
    apply List.Subperm.antisymm
    · apply List.Nodup.subperm ((List.nodup_finRange 6).erase u)
      intro x hx
      rw [(List.nodup_finRange 6).mem_erase_iff] at hx
      obtain ⟨j, hj⟩ := (n7σ_bijective C).surjective x
      refine List.mem_map.mpr ⟨j, ?_, hj⟩
      rw [(List.nodup_finRange 6).mem_erase_iff]
      exact ⟨fun hjr => hx.1 (by rw [← hj, hjr, hu]),
        List.mem_finRange _⟩
    · apply List.Nodup.subperm
        (((List.nodup_finRange 6).erase r).map (n7σ_injective C))
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨j, hje, rfl⟩ := hx
      rw [(List.nodup_finRange 6).mem_erase_iff] at hje ⊢
      exact ⟨fun hxu => hje.1 (n7σ_injective C (hxu.trans hu.symm)),
        List.mem_finRange _⟩
  have hp2 := hmap.map (dirRep o e (c ∘ v.succAbove) u)
  rw [List.map_map] at hp2
  refine hp1.trans (hp2.trans ?_)
  have hfeq : (dirRep o e (c ∘ v.succAbove) u ∘ n7σ C) =
      fun j => (n7model C).d r j := by
    funext j
    show dirRep o e (c ∘ v.succAbove) u (n7σ C j) =
      (n7model C).d r j
    rw [n7model_d C r j, hu]
  rw [hfeq]

/-- A defect-`2` row at `n = 4` yields a `RowSig2_7` witness list. -/
theorem n7_row2_exists {r u : Fin 6} (hu : n7σ C r = u)
    (hd : rowDefect 4 lam
      (directionRow o e c (v.succAbove u)) = 2) :
    ∃ x0 x1 x2 x3 x4 : ℝ,
      (n7T C r ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧
        x4 ≤ n7T C r + Real.pi) ∧
      R2N4.RowSig2_7 lam Real.pi (n7T C r) x0 x1 x2 x3 x4 ∧
      List.Perm [x0, x1, x2, x3, x4]
        (((List.finRange 6).erase r).map fun j =>
          (n7model C).d r j) := by
  obtain ⟨x0, x1, x2, x3, x4, hord, hlin, hperm⟩ :=
    n7_row_core C hu (Or.inl hd)
  refine ⟨x0, x1, x2, x3, x4, hord, ?_, hperm⟩
  rw [hd] at hlin
  exact rowSig2_7_of_linearScore_two C.hlam hord (by omega)

/-- A defect-`3` row at `n = 4` yields a `RowSig1_7` witness list. -/
theorem n7_row1_exists {r u : Fin 6} (hu : n7σ C r = u)
    (hd : rowDefect 4 lam
      (directionRow o e c (v.succAbove u)) = 3) :
    ∃ x0 x1 x2 x3 x4 : ℝ,
      (n7T C r ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧
        x4 ≤ n7T C r + Real.pi) ∧
      R2N4.RowSig1_7 lam Real.pi (n7T C r) x0 x1 x2 x3 x4 ∧
      List.Perm [x0, x1, x2, x3, x4]
        (((List.finRange 6).erase r).map fun j =>
          (n7model C).d r j) := by
  obtain ⟨x0, x1, x2, x3, x4, hord, hlin, hperm⟩ :=
    n7_row_core C hu (Or.inr hd)
  refine ⟨x0, x1, x2, x3, x4, hord, ?_, hperm⟩
  rw [hd] at hlin
  exact rowSig1_7_of_linearScore_one C.hlam hord (by omega)

/-- Rewrites the erased-index chord list of row `r` into min/max order
so it matches the certificate's literal chord lists. -/
theorem n7_row_perm {r : Fin 6} {x0 x1 x2 x3 x4 : ℝ}
    (h : List.Perm [x0, x1, x2, x3, x4]
      (((List.finRange 6).erase r).map fun j =>
        (n7model C).d r j)) :
    List.Perm [x0, x1, x2, x3, x4]
      (((List.finRange 6).erase r).map fun j =>
        (n7model C).d (min r j) (max r j)) := by
  have hmap : ((List.finRange 6).erase r).map
        (fun j => (n7model C).d r j) =
      ((List.finRange 6).erase r).map
        (fun j => (n7model C).d (min r j) (max r j)) := by
    apply List.map_congr_left
    intro j hj
    have hjr : j ≠ r := by
      rw [(List.nodup_finRange 6).mem_erase_iff] at hj
      exact hj.1
    rcases lt_or_ge r j with hlt | hge
    · rw [min_eq_left hlt.le, max_eq_right hlt.le]
    · rw [min_eq_right hge, max_eq_left hge]
      exact n7d_comm C r j hjr.symm
  rwa [hmap] at h

end SevenCentreN4

section S7Terminal

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
  {lam : ℝ} {theta : Fin 6 → ℝ} {c : Fin 7 → Plane₂} {v : Fin 7}

/-- **S7 position class `AA2` excluded.**  If the two defect-`2` rows
occupy θ-ranks `0, 1` and the defect-`3` row occupies rank `2` in a
seven-centre saturated `n = 4` chart, the canonical certificates
contradict the configuration. -/
theorem seven_centre_n4_AA2 (C : SatChart o e 4 lam c v theta)
    {u0 u1 u2 : Fin 6}
    (h0 : n7σ C 0 = u0) (h1 : n7σ C 1 = u1) (h2 : n7σ C 2 = u2)
    (hd0 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u0)) = 2)
    (hd1 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u1)) = 2)
    (hd2 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u2)) = 3) :
    False := by
  obtain ⟨x00, x01, x02, x03, x04, ho0, hs0, hp0⟩ :=
    n7_row2_exists C h0 hd0
  obtain ⟨x10, x11, x12, x13, x14, ho1, hs1, hp1⟩ :=
    n7_row2_exists C h1 hd1
  obtain ⟨x20, x21, x22, x23, x24, ho2, hs2, hp2⟩ :=
    n7_row1_exists C h2 hd2
  exact R2N4.s7cert_AA2 (n7model C) ho0 hs0 (n7_row_perm C hp0)
    ho1 hs1 (n7_row_perm C hp1) ho2 hs2 (n7_row_perm C hp2)

/-- **S7 position class `AA5` excluded.**  Defect-`2` rows at ranks
`0, 1`, defect-`3` row at rank `5`. -/
theorem seven_centre_n4_AA5 (C : SatChart o e 4 lam c v theta)
    {u0 u1 u5 : Fin 6}
    (h0 : n7σ C 0 = u0) (h1 : n7σ C 1 = u1) (h5 : n7σ C 5 = u5)
    (hd0 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u0)) = 2)
    (hd1 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u1)) = 2)
    (hd5 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u5)) = 3) :
    False := by
  obtain ⟨x00, x01, x02, x03, x04, ho0, hs0, hp0⟩ :=
    n7_row2_exists C h0 hd0
  obtain ⟨x10, x11, x12, x13, x14, ho1, hs1, hp1⟩ :=
    n7_row2_exists C h1 hd1
  obtain ⟨x50, x51, x52, x53, x54, ho5, hs5, hp5⟩ :=
    n7_row1_exists C h5 hd5
  exact R2N4.s7cert_AA5 (n7model C) ho0 hs0 (n7_row_perm C hp0)
    ho1 hs1 (n7_row_perm C hp1) ho5 hs5 (n7_row_perm C hp5)

/-- **S7 position class `AB0` excluded.**  Defect-`2` rows at ranks
`4, 5`, defect-`3` row at rank `0`. -/
theorem seven_centre_n4_AB0 (C : SatChart o e 4 lam c v theta)
    {u4 u5 u0 : Fin 6}
    (h4 : n7σ C 4 = u4) (h5 : n7σ C 5 = u5) (h0 : n7σ C 0 = u0)
    (hd4 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u4)) = 2)
    (hd5 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u5)) = 2)
    (hd0 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u0)) = 3) :
    False := by
  obtain ⟨x40, x41, x42, x43, x44, ho4, hs4, hp4⟩ :=
    n7_row2_exists C h4 hd4
  obtain ⟨x50, x51, x52, x53, x54, ho5, hs5, hp5⟩ :=
    n7_row2_exists C h5 hd5
  obtain ⟨x00, x01, x02, x03, x04, ho0, hs0, hp0⟩ :=
    n7_row1_exists C h0 hd0
  exact R2N4.s7cert_AB0 (n7model C) ho4 hs4 (n7_row_perm C hp4)
    ho5 hs5 (n7_row_perm C hp5) ho0 hs0 (n7_row_perm C hp0)

/-- **S7 position class `AB3` excluded.**  Defect-`2` rows at ranks
`4, 5`, defect-`3` row at rank `3`. -/
theorem seven_centre_n4_AB3 (C : SatChart o e 4 lam c v theta)
    {u4 u5 u3 : Fin 6}
    (h4 : n7σ C 4 = u4) (h5 : n7σ C 5 = u5) (h3 : n7σ C 3 = u3)
    (hd4 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u4)) = 2)
    (hd5 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u5)) = 2)
    (hd3 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u3)) = 3) :
    False := by
  obtain ⟨x40, x41, x42, x43, x44, ho4, hs4, hp4⟩ :=
    n7_row2_exists C h4 hd4
  obtain ⟨x50, x51, x52, x53, x54, ho5, hs5, hp5⟩ :=
    n7_row2_exists C h5 hd5
  obtain ⟨x30, x31, x32, x33, x34, ho3, hs3, hp3⟩ :=
    n7_row1_exists C h3 hd3
  exact R2N4.s7cert_AB3 (n7model C) ho4 hs4 (n7_row_perm C hp4)
    ho5 hs5 (n7_row_perm C hp5) ho3 hs3 (n7_row_perm C hp3)

/-- **S7 position class `AA3` excluded.**  Defect-`2` rows at ranks
`0, 1`, defect-`3` row at rank `3`. -/
theorem seven_centre_n4_AA3 (C : SatChart o e 4 lam c v theta)
    {u0 u1 u3 : Fin 6}
    (h0 : n7σ C 0 = u0) (h1 : n7σ C 1 = u1) (h3 : n7σ C 3 = u3)
    (hd0 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u0)) = 2)
    (hd1 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u1)) = 2)
    (hd3 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u3)) = 3) :
    False := by
  obtain ⟨x00, x01, x02, x03, x04, ho0, hs0, hp0⟩ :=
    n7_row2_exists C h0 hd0
  obtain ⟨x10, x11, x12, x13, x14, ho1, hs1, hp1⟩ :=
    n7_row2_exists C h1 hd1
  obtain ⟨x30, x31, x32, x33, x34, ho3, hs3, hp3⟩ :=
    n7_row1_exists C h3 hd3
  exact R2N4.s7cert_AA3 (n7model C) ho0 hs0 (n7_row_perm C hp0)
    ho1 hs1 (n7_row_perm C hp1) ho3 hs3 (n7_row_perm C hp3)

/-- **S7 position class `AA4` excluded.**  Defect-`2` rows at ranks
`0, 1`, defect-`3` row at rank `4`. -/
theorem seven_centre_n4_AA4 (C : SatChart o e 4 lam c v theta)
    {u0 u1 u4 : Fin 6}
    (h0 : n7σ C 0 = u0) (h1 : n7σ C 1 = u1) (h4 : n7σ C 4 = u4)
    (hd0 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u0)) = 2)
    (hd1 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u1)) = 2)
    (hd4 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u4)) = 3) :
    False := by
  obtain ⟨x00, x01, x02, x03, x04, ho0, hs0, hp0⟩ :=
    n7_row2_exists C h0 hd0
  obtain ⟨x10, x11, x12, x13, x14, ho1, hs1, hp1⟩ :=
    n7_row2_exists C h1 hd1
  obtain ⟨x40, x41, x42, x43, x44, ho4, hs4, hp4⟩ :=
    n7_row1_exists C h4 hd4
  exact R2N4.s7cert_AA4 (n7model C) ho0 hs0 (n7_row_perm C hp0)
    ho1 hs1 (n7_row_perm C hp1) ho4 hs4 (n7_row_perm C hp4)

/-- **S7 position class `AB1` excluded.**  Defect-`2` rows at ranks
`4, 5`, defect-`3` row at rank `1`. -/
theorem seven_centre_n4_AB1 (C : SatChart o e 4 lam c v theta)
    {u4 u5 u1 : Fin 6}
    (h4 : n7σ C 4 = u4) (h5 : n7σ C 5 = u5) (h1 : n7σ C 1 = u1)
    (hd4 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u4)) = 2)
    (hd5 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u5)) = 2)
    (hd1 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u1)) = 3) :
    False := by
  obtain ⟨x40, x41, x42, x43, x44, ho4, hs4, hp4⟩ :=
    n7_row2_exists C h4 hd4
  obtain ⟨x50, x51, x52, x53, x54, ho5, hs5, hp5⟩ :=
    n7_row2_exists C h5 hd5
  obtain ⟨x10, x11, x12, x13, x14, ho1, hs1, hp1⟩ :=
    n7_row1_exists C h1 hd1
  exact R2N4.s7cert_AB1 (n7model C) ho4 hs4 (n7_row_perm C hp4)
    ho5 hs5 (n7_row_perm C hp5) ho1 hs1 (n7_row_perm C hp1)

/-- **S7 position class `AB2` excluded.**  Defect-`2` rows at ranks
`4, 5`, defect-`3` row at rank `2`. -/
theorem seven_centre_n4_AB2 (C : SatChart o e 4 lam c v theta)
    {u4 u5 u2 : Fin 6}
    (h4 : n7σ C 4 = u4) (h5 : n7σ C 5 = u5) (h2 : n7σ C 2 = u2)
    (hd4 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u4)) = 2)
    (hd5 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u5)) = 2)
    (hd2 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u2)) = 3) :
    False := by
  obtain ⟨x40, x41, x42, x43, x44, ho4, hs4, hp4⟩ :=
    n7_row2_exists C h4 hd4
  obtain ⟨x50, x51, x52, x53, x54, ho5, hs5, hp5⟩ :=
    n7_row2_exists C h5 hd5
  obtain ⟨x20, x21, x22, x23, x24, ho2, hs2, hp2⟩ :=
    n7_row1_exists C h2 hd2
  exact R2N4.s7cert_AB2 (n7model C) ho4 hs4 (n7_row_perm C hp4)
    ho5 hs5 (n7_row_perm C hp5) ho2 hs2 (n7_row_perm C hp2)

/-- **S7 position class `BT1` excluded.**  Defect-`2` rows at ranks
`0, 5` (between), defect-`3` row at rank `1`. -/
theorem seven_centre_n4_BT1 (C : SatChart o e 4 lam c v theta)
    {u0 u5 u1 : Fin 6}
    (h0 : n7σ C 0 = u0) (h5 : n7σ C 5 = u5) (h1 : n7σ C 1 = u1)
    (hd0 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u0)) = 2)
    (hd5 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u5)) = 2)
    (hd1 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u1)) = 3) :
    False := by
  obtain ⟨x00, x01, x02, x03, x04, ho0, hs0, hp0⟩ :=
    n7_row2_exists C h0 hd0
  obtain ⟨x50, x51, x52, x53, x54, ho5, hs5, hp5⟩ :=
    n7_row2_exists C h5 hd5
  obtain ⟨x10, x11, x12, x13, x14, ho1, hs1, hp1⟩ :=
    n7_row1_exists C h1 hd1
  exact R2N4.s7cert_BT1 (n7model C) ho0 hs0 (n7_row_perm C hp0)
    ho5 hs5 (n7_row_perm C hp5) ho1 hs1 (n7_row_perm C hp1)

/-- **S7 position class `BT2` excluded.**  Defect-`2` rows at ranks
`0, 5`, defect-`3` row at rank `2`. -/
theorem seven_centre_n4_BT2 (C : SatChart o e 4 lam c v theta)
    {u0 u5 u2 : Fin 6}
    (h0 : n7σ C 0 = u0) (h5 : n7σ C 5 = u5) (h2 : n7σ C 2 = u2)
    (hd0 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u0)) = 2)
    (hd5 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u5)) = 2)
    (hd2 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u2)) = 3) :
    False := by
  obtain ⟨x00, x01, x02, x03, x04, ho0, hs0, hp0⟩ :=
    n7_row2_exists C h0 hd0
  obtain ⟨x50, x51, x52, x53, x54, ho5, hs5, hp5⟩ :=
    n7_row2_exists C h5 hd5
  obtain ⟨x20, x21, x22, x23, x24, ho2, hs2, hp2⟩ :=
    n7_row1_exists C h2 hd2
  exact R2N4.s7cert_BT2 (n7model C) ho0 hs0 (n7_row_perm C hp0)
    ho5 hs5 (n7_row_perm C hp5) ho2 hs2 (n7_row_perm C hp2)

/-- **S7 position class `BT3` excluded.**  Defect-`2` rows at ranks
`0, 5`, defect-`3` row at rank `3`. -/
theorem seven_centre_n4_BT3 (C : SatChart o e 4 lam c v theta)
    {u0 u5 u3 : Fin 6}
    (h0 : n7σ C 0 = u0) (h5 : n7σ C 5 = u5) (h3 : n7σ C 3 = u3)
    (hd0 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u0)) = 2)
    (hd5 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u5)) = 2)
    (hd3 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u3)) = 3) :
    False := by
  obtain ⟨x00, x01, x02, x03, x04, ho0, hs0, hp0⟩ :=
    n7_row2_exists C h0 hd0
  obtain ⟨x50, x51, x52, x53, x54, ho5, hs5, hp5⟩ :=
    n7_row2_exists C h5 hd5
  obtain ⟨x30, x31, x32, x33, x34, ho3, hs3, hp3⟩ :=
    n7_row1_exists C h3 hd3
  exact R2N4.s7cert_BT3 (n7model C) ho0 hs0 (n7_row_perm C hp0)
    ho5 hs5 (n7_row_perm C hp5) ho3 hs3 (n7_row_perm C hp3)

/-- **S7 position class `BT4` excluded.**  Defect-`2` rows at ranks
`0, 5`, defect-`3` row at rank `4`. -/
theorem seven_centre_n4_BT4 (C : SatChart o e 4 lam c v theta)
    {u0 u5 u4 : Fin 6}
    (h0 : n7σ C 0 = u0) (h5 : n7σ C 5 = u5) (h4 : n7σ C 4 = u4)
    (hd0 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u0)) = 2)
    (hd5 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u5)) = 2)
    (hd4 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u4)) = 3) :
    False := by
  obtain ⟨x00, x01, x02, x03, x04, ho0, hs0, hp0⟩ :=
    n7_row2_exists C h0 hd0
  obtain ⟨x50, x51, x52, x53, x54, ho5, hs5, hp5⟩ :=
    n7_row2_exists C h5 hd5
  obtain ⟨x40, x41, x42, x43, x44, ho4, hs4, hp4⟩ :=
    n7_row1_exists C h4 hd4
  exact R2N4.s7cert_BT4 (n7model C) ho0 hs0 (n7_row_perm C hp0)
    ho5 hs5 (n7_row_perm C hp5) ho4 hs4 (n7_row_perm C hp4)

end S7Terminal

end Jsp404
