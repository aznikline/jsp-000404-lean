import Jsp000404.S8Certs
import Jsp000404.S7ScoreLemmas
import Jsp000404.N4Extraction

set_option maxHeartbeats 40000000

/-!
# Extraction: eight-centre `SatChart` → `N8Model`

Instantiates the scalar `n = 4` terminal model `R2N4.N8Model` from a
real eight-centre `SatChart`, parallel to `S7Extraction`:

* `n8T` / `n8σ` are the sorted non-anchor `theta` values and the
  rank-to-index bijection.
* `d i j` is the shared chord `dirRep (σ i) (σ j)`; `n8corridor` and
  `n8triple` replay `up_corridor`, `up_trans` and `up_cap`.
* `n8_row2_exists` extracts the sorted six-chord row at a chart index
  together with its `RowSig2_8` (defect `2`, score `2`) signature and
  the `List.Perm` onto the model chords.
* The three terminal theorems `eight_centre_n4_AA`, `…_BT`, `…_AB`
  close the residual geometric position classes: the two defect-`2`
  rows sit at θ-ranks `{0,1}`, `{0,6}` or `{5,6}` respectively,
  contradicted by the generated leaf certificates `s8cert_*`.
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

section EightCentreN4

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
  {c : Fin 8 → Plane₂} {v : Fin 8} {theta : Fin 7 → ℝ}
  (C : SatChart o e 4 lam c v theta)

include C

/-- Distinct non-anchor centres have distinct anchor directions. -/
theorem n8theta_injective : Function.Injective theta := by
  intro i j hij
  by_contra hne
  rcases up_or_up C hne with h | h
  · exact absurd hij (ne_of_lt (up_theta_lt C hne h))
  · exact absurd hij.symm (ne_of_lt (up_theta_lt C (Ne.symm hne) h))

/-- The seven non-anchor `theta`s are distinct. -/
theorem n8Tcard : (Finset.image theta Finset.univ).card = 7 := by
  classical
  rw [Finset.card_image_of_injective _ (n8theta_injective C),
    Finset.card_univ, Fintype.card_fin]

/-- Sorted `theta` values as a strict-mono enumeration. -/
noncomputable def n8T : Fin 7 → ℝ :=
  (Finset.image theta Finset.univ).orderEmbOfFin (n8Tcard C)

theorem n8T_strictMono : StrictMono (n8T C) := fun _ _ h =>
  ((Finset.image theta Finset.univ).orderEmbOfFin _).strictMono h

/-- Rank-to-index bijection: `n8σ C i` is the centre whose `theta` is
the `i`-th smallest. -/
noncomputable def n8σ : Fin 7 → Fin 7 := fun i =>
  (Finset.mem_image.mp
    (Finset.orderEmbOfFin_mem _ (n8Tcard C) i)).choose

theorem n8σ_spec (i : Fin 7) : theta (n8σ C i) = n8T C i :=
  (Finset.mem_image.mp
    (Finset.orderEmbOfFin_mem _ (n8Tcard C) i)).choose_spec.2

theorem n8σ_injective : Function.Injective (n8σ C) := by
  intro i j hij
  apply (n8T_strictMono C).injective
  rw [← n8σ_spec C i, ← n8σ_spec C j, hij]

theorem n8σ_bijective : Function.Bijective (n8σ C) :=
  Finite.injective_iff_bijective.mp (n8σ_injective C)

theorem n8σ_ne {i j : Fin 7} (h : i ≠ j) : n8σ C i ≠ n8σ C j :=
  fun hh => h (n8σ_injective C hh)

/-- A lower-`theta` centre is always `Up` of a higher one, at
`n8σ`-ranks. -/
theorem n8σ_up {i j : Fin 7} (hij : i < j) :
    Up o e c v (n8σ C i) (n8σ C j) := by
  have hlt : theta (n8σ C i) < theta (n8σ C j) := by
    rw [n8σ_spec C i, n8σ_spec C j]
    exact n8T_strictMono C hij
  exact up_of_theta_lt' C (n8σ_ne C hij.ne) hlt

/-- Corridor bounds in model coordinates. -/
theorem n8corridor {i j : Fin 7} (hij : i < j) :
    n8T C i + lam ≤
        dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C j) ∧
      dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C j) ≤
        Real.pi - lam + n8T C j := by
  have hcor := up_corridor C (n8σ_ne C hij.ne) (n8σ_up C hij)
  rwa [n8σ_spec C i, n8σ_spec C j] at hcor

/-- Triple `Up`-constraints in model coordinates. -/
theorem n8triple {i j k : Fin 7} (hij : i < j) (hjk : j < k) :
    (dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C j) + lam ≤
          dirRep o e (c ∘ v.succAbove) (n8σ C j) (n8σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C j) <
          dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C k) <
          dirRep o e (c ∘ v.succAbove) (n8σ C j) (n8σ C k)) ∨
      (dirRep o e (c ∘ v.succAbove) (n8σ C j) (n8σ C k) + lam ≤
          dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C j) ∧
        dirRep o e (c ∘ v.succAbove) (n8σ C j) (n8σ C k) <
          dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C k) <
          dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C j)) := by
  have hl0 : 0 < lam := C.hlam
  have hneij : n8σ C i ≠ n8σ C j := n8σ_ne C hij.ne
  have hnejk : n8σ C j ≠ n8σ C k := n8σ_ne C hjk.ne
  have hneik : n8σ C i ≠ n8σ C k := n8σ_ne C (hij.trans hjk).ne
  have hupij := n8σ_up C hij
  have hupjk := n8σ_up C hjk
  obtain ⟨-, hbetween⟩ := up_trans C hneij hnejk hneik hupij hupjk
  have hcap := up_cap C hneij hnejk hneik hupij hupjk
  rcases le_or_gt 0 (dirRep o e (c ∘ v.succAbove) (n8σ C j) (n8σ C k) -
    dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C j)) with hs | hs
  · rw [abs_of_nonneg hs] at hcap
    rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by linarith, h1, h2⟩
    · exfalso; linarith
  · rw [abs_of_neg hs] at hcap
    rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso; linarith
    · exact Or.inr ⟨by linarith, h1, h2⟩

/-- The scalar `n = 4` model of the eight-centre configuration. -/
noncomputable def n8model : R2N4.N8Model where
  lam := lam
  p := Real.pi
  hlam := C.hlam
  hp := by
    have h1 := C.hnl
    have h2 := C.hπ
    push_cast at h1 h2
    constructor <;> linarith
  t := n8T C
  ht := n8T_strictMono C
  ht0 := by
    have h := (C.htheta (n8σ C 0)).1.1
    rwa [n8σ_spec C 0] at h
  ht6 := by
    have h := (C.htheta (n8σ C 6)).1.2
    rw [n8σ_spec C 6] at h
    push_cast at h ⊢
    linarith
  d := fun i j => dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C j)
  hcor := fun _ _ h => n8corridor C h
  htr := fun _ _ _ h1 h2 => n8triple C h1 h2

theorem n8model_lam : (n8model C).lam = lam := rfl
theorem n8model_p : (n8model C).p = Real.pi := rfl
theorem n8model_t (i : Fin 7) : (n8model C).t i = n8T C i := rfl
theorem n8model_d (i j : Fin 7) :
    (n8model C).d i j =
      dirRep o e (c ∘ v.succAbove) (n8σ C i) (n8σ C j) := rfl

/-- Rank identification: `n8σ C r = u` iff the `r`-th sorted `theta`
value is `theta u`. -/
theorem n8σ_eq_iff (u r : Fin 7) :
    n8σ C r = u ↔ n8T C r = theta u := by
  constructor
  · intro h; rw [← n8σ_spec C r, h]
  · intro h
    exact n8theta_injective C ((n8σ_spec C r).trans h)

/-- Rank via bisection: if every smaller rank lies strictly below
`theta u` and `n8T C r` does not, then `n8T C r = theta u`. -/
theorem n8T_eq_of_bounds (u : Fin 7) (r : Fin 7)
    (hlo : ∀ s : Fin 7, s < r → n8T C s < theta u)
    (hhi : theta u ≤ n8T C r) :
    n8T C r = theta u := by
  obtain ⟨r', hr'⟩ : ∃ r' : Fin 7, n8T C r' = theta u := by
    have hmem : theta u ∈ Set.range
        ⇑((Finset.image theta Finset.univ).orderEmbOfFin
          (n8Tcard C)) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩)
    exact hmem
  rcases lt_trichotomy r' r with hlt | heq | hgt
  · exact absurd (hlo r' hlt) (by rw [hr']; exact lt_irrefl _)
  · exact heq ▸ hr'
  · have h2 := n8T_strictMono C hgt
    rw [hr'] at h2
    linarith

/-- Chord symmetry in the model. -/
theorem n8d_comm (i j : Fin 7) (h : i ≠ j) :
    (n8model C).d i j = (n8model C).d j i := by
  have h' : n8σ C i ≠ n8σ C j := n8σ_ne C h
  exact phi_comm C h'

/-- Common core of `n8_row_exists`: the sorted six-chord list of the
row at chart index `u = n8σ C r`, with ordering and `List.Perm` onto
the model chords.  The score is returned for signature dispatch. -/
theorem n8_row_core {r u : Fin 7} (hu : n8σ C r = u)
    (hd : rowDefect 4 lam (directionRow o e c (v.succAbove u)) = 2 ∨
      rowDefect 4 lam (directionRow o e c (v.succAbove u)) = 3) :
    ∃ x0 x1 x2 x3 x4 x5 : ℝ,
      (n8T C r ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧
        x4 ≤ x5 ∧ x5 ≤ n8T C r + Real.pi) ∧
      linearGapScore lam (n8T C r) (n8T C r + Real.pi)
          [x0, x1, x2, x3, x4, x5] = 4 - rowDefect 4 lam
            (directionRow o e c (v.succAbove u)) ∧
      List.Perm [x0, x1, x2, x3, x4, x5]
        (((List.finRange 7).erase r).map fun j =>
          (n8model C).d r j) := by
  classical
  have hTu : n8T C r = theta u := (n8σ_eq_iff C u r).mp hu
  have hlen : (directionRow o e (c ∘ v.succAbove) u).length = 6 := by
    have h := directionRow_length o e (c ∘ v.succAbove) u
    omega
  obtain ⟨x0, x1, x2, x3, x4, x5, hrest⟩ := length_eq_six hlen
  have hsort := directionRow_sorted o e (c ∘ v.succAbove) u
  rw [hrest] at hsort
  obtain ⟨h01', hs1⟩ := List.sortedLE_cons.mp hsort
  obtain ⟨h12', hs2⟩ := List.sortedLE_cons.mp hs1
  obtain ⟨h23', hs3⟩ := List.sortedLE_cons.mp hs2
  obtain ⟨h34', hs4⟩ := List.sortedLE_cons.mp hs3
  obtain ⟨h45', -⟩ := List.sortedLE_cons.mp hs4
  have e01 : x0 ≤ x1 := h01' x1 (by simp)
  have e12 : x1 ≤ x2 := h12' x2 (by simp)
  have e23 : x2 ≤ x3 := h23' x3 (by simp)
  have e34 : x3 ≤ x4 := h34' x4 (by simp)
  have e45 : x4 ≤ x5 := h45' x5 (by simp)
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
  have hx5le : x5 ≤ theta u + Real.pi := by
    have hx := (hmem x5 (by rw [hrest]; simp)).2
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
  refine ⟨x0, x1, x2, x3, x4, x5, ?_, hsub, ?_⟩
  · rw [hTu]
    exact ⟨hx0ge, e01, e12, e23, e34, e45, hx5le⟩
  have hp1 : List.Perm (directionRow o e (c ∘ v.succAbove) u)
      (((List.finRange 7).erase u).map
        (dirRep o e (c ∘ v.succAbove) u)) :=
    List.perm_insertionSort _ _
  rw [hrest] at hp1
  have hmap : List.Perm ((List.finRange 7).erase u)
      (((List.finRange 7).erase r).map (n8σ C)) := by
    apply List.Subperm.antisymm
    · apply List.Nodup.subperm ((List.nodup_finRange 7).erase u)
      intro x hx
      rw [(List.nodup_finRange 7).mem_erase_iff] at hx
      obtain ⟨j, hj⟩ := (n8σ_bijective C).surjective x
      refine List.mem_map.mpr ⟨j, ?_, hj⟩
      rw [(List.nodup_finRange 7).mem_erase_iff]
      exact ⟨fun hjr => hx.1 (by rw [← hj, hjr, hu]),
        List.mem_finRange _⟩
    · apply List.Nodup.subperm
        (((List.nodup_finRange 7).erase r).map (n8σ_injective C))
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨j, hje, rfl⟩ := hx
      rw [(List.nodup_finRange 7).mem_erase_iff] at hje ⊢
      exact ⟨fun hxu => hje.1 (n8σ_injective C (hxu.trans hu.symm)),
        List.mem_finRange _⟩
  have hp2 := hmap.map (dirRep o e (c ∘ v.succAbove) u)
  rw [List.map_map] at hp2
  refine hp1.trans (hp2.trans ?_)
  have hfeq : (dirRep o e (c ∘ v.succAbove) u ∘ n8σ C) =
      fun j => (n8model C).d r j := by
    funext j
    show dirRep o e (c ∘ v.succAbove) u (n8σ C j) =
      (n8model C).d r j
    rw [n8model_d C r j, hu]
  rw [hfeq]

/-- A defect-`2` row at `n = 4` yields a `RowSig2_8` witness list. -/
theorem n8_row2_exists {r u : Fin 7} (hu : n8σ C r = u)
    (hd : rowDefect 4 lam
      (directionRow o e c (v.succAbove u)) = 2) :
    ∃ x0 x1 x2 x3 x4 x5 : ℝ,
      (n8T C r ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧
        x4 ≤ x5 ∧ x5 ≤ n8T C r + Real.pi) ∧
      R2N4.RowSig2_8 lam Real.pi (n8T C r) x0 x1 x2 x3 x4 x5 ∧
      List.Perm [x0, x1, x2, x3, x4, x5]
        (((List.finRange 7).erase r).map fun j =>
          (n8model C).d r j) := by
  obtain ⟨x0, x1, x2, x3, x4, x5, hord, hlin, hperm⟩ :=
    n8_row_core C hu (Or.inl hd)
  refine ⟨x0, x1, x2, x3, x4, x5, hord, ?_, hperm⟩
  rw [hd] at hlin
  exact rowSig2_8_of_linearScore_two C.hlam hord (by omega)

/-- Rewrites the erased-index chord list of row `r` into min/max order
so it matches the certificate's literal chord lists. -/
theorem n8_row_perm {r : Fin 7} {x0 x1 x2 x3 x4 x5 : ℝ}
    (h : List.Perm [x0, x1, x2, x3, x4, x5]
      (((List.finRange 7).erase r).map fun j =>
        (n8model C).d r j)) :
    List.Perm [x0, x1, x2, x3, x4, x5]
      (((List.finRange 7).erase r).map fun j =>
        (n8model C).d (min r j) (max r j)) := by
  have hmap : ((List.finRange 7).erase r).map
        (fun j => (n8model C).d r j) =
      ((List.finRange 7).erase r).map
        (fun j => (n8model C).d (min r j) (max r j)) := by
    apply List.map_congr_left
    intro j hj
    have hjr : j ≠ r := by
      rw [(List.nodup_finRange 7).mem_erase_iff] at hj
      exact hj.1
    rcases lt_or_ge r j with hlt | hge
    · rw [min_eq_left hlt.le, max_eq_right hlt.le]
    · rw [min_eq_right hge, max_eq_left hge]
      exact n8d_comm C r j hjr.symm
  rwa [hmap] at h

end EightCentreN4

section S8Terminal

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
  {lam : ℝ} {theta : Fin 7 → ℝ} {c : Fin 8 → Plane₂} {v : Fin 8}

/-- **S8 position class `AA` excluded.**  If the two defect-`2` rows
occupy θ-ranks `0, 1` in an eight-centre saturated `n = 4` chart, the
canonical certificates contradict the configuration. -/
theorem eight_centre_n4_AA (C : SatChart o e 4 lam c v theta)
    {u0 u1 : Fin 7}
    (h0 : n8σ C 0 = u0) (h1 : n8σ C 1 = u1)
    (hd0 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u0)) = 2)
    (hd1 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u1)) = 2) :
    False := by
  obtain ⟨x00, x01, x02, x03, x04, x05, ho0, hs0, hp0⟩ :=
    n8_row2_exists C h0 hd0
  obtain ⟨x10, x11, x12, x13, x14, x15, ho1, hs1, hp1⟩ :=
    n8_row2_exists C h1 hd1
  exact R2N4.s8cert_AA (n8model C) ho0 hs0 (n8_row_perm C hp0)
    ho1 hs1 (n8_row_perm C hp1)

/-- **S8 position class `BT` excluded.**  Defect-`2` rows at θ-ranks
`0, 6`. -/
theorem eight_centre_n4_BT (C : SatChart o e 4 lam c v theta)
    {u0 u6 : Fin 7}
    (h0 : n8σ C 0 = u0) (h6 : n8σ C 6 = u6)
    (hd0 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u0)) = 2)
    (hd6 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u6)) = 2) :
    False := by
  obtain ⟨x00, x01, x02, x03, x04, x05, ho0, hs0, hp0⟩ :=
    n8_row2_exists C h0 hd0
  obtain ⟨x60, x61, x62, x63, x64, x65, ho6, hs6, hp6⟩ :=
    n8_row2_exists C h6 hd6
  exact R2N4.s8cert_BT (n8model C) ho0 hs0 (n8_row_perm C hp0)
    ho6 hs6 (n8_row_perm C hp6)

/-- **S8 position class `AB` excluded.**  Defect-`2` rows at θ-ranks
`5, 6`. -/
theorem eight_centre_n4_AB (C : SatChart o e 4 lam c v theta)
    {u5 u6 : Fin 7}
    (h5 : n8σ C 5 = u5) (h6 : n8σ C 6 = u6)
    (hd5 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u5)) = 2)
    (hd6 : rowDefect 4 lam
      (directionRow o e c (v.succAbove u6)) = 2) :
    False := by
  obtain ⟨x50, x51, x52, x53, x54, x55, ho5, hs5, hp5⟩ :=
    n8_row2_exists C h5 hd5
  obtain ⟨x60, x61, x62, x63, x64, x65, ho6, hs6, hp6⟩ :=
    n8_row2_exists C h6 hd6
  exact R2N4.s8cert_AB (n8model C) ho5 hs5 (n8_row_perm C hp5)
    ho6 hs6 (n8_row_perm C hp6)

end S8Terminal

end Jsp404
