import Jsp000404.S8Extraction
import Jsp000404.R1Defs
import Jsp000404.R1ScoreLemmas

set_option maxHeartbeats 40000000

/-!
# Extraction: nine/ten/eleven-centre `SatChart` → `N{9,10,11}Model`

Mechanical size ports of `S8Extraction` for the R1 terminal
profiles, plus `n8_row1_exists` (the defect-`3` row producer S8 did
not need).
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

/-- A six-element list splits into its literals. -/
private theorem length_eq_six {α : Type*} {l : List α}
    (h : l.length = 6) :
    ∃ a b c d e f : α, l = [a, b, c, d, e, f] := by
  cases l with
  | nil => simp at h
  | cons a l' =>
    rw [List.length_cons] at h
    obtain ⟨b, c, d, e, f, rfl⟩ :=
      length_eq_five (show l'.length = 5 by omega)
    exact ⟨a, b, c, d, e, f, rfl⟩

/-- A seven-element list splits into its literals. -/
private theorem length_eq_seven {α : Type*} {l : List α}
    (h : l.length = 7) :
    ∃ a b c d e f g : α, l = [a, b, c, d, e, f, g] := by
  cases l with
  | nil => simp at h
  | cons a l' =>
    rw [List.length_cons] at h
    obtain ⟨b, c, d, e, f, g, rfl⟩ :=
      length_eq_six (show l'.length = 6 by omega)
    exact ⟨a, b, c, d, e, f, g, rfl⟩

/-- A eight-element list splits into its literals. -/
private theorem length_eq_eight {α : Type*} {l : List α}
    (h : l.length = 8) :
    ∃ a b c d e f g h : α, l = [a, b, c, d, e, f, g, h] := by
  cases l with
  | nil => simp at h
  | cons a l' =>
    rw [List.length_cons] at h
    obtain ⟨b, c, d, e, f, g, h, rfl⟩ :=
      length_eq_seven (show l'.length = 7 by omega)
    exact ⟨a, b, c, d, e, f, g, h, rfl⟩

/-- A nine-element list splits into its literals. -/
private theorem length_eq_nine {α : Type*} {l : List α}
    (h : l.length = 9) :
    ∃ a b c d e f g h i : α, l = [a, b, c, d, e, f, g, h, i] := by
  cases l with
  | nil => simp at h
  | cons a l' =>
    rw [List.length_cons] at h
    obtain ⟨b, c, d, e, f, g, h, i, rfl⟩ :=
      length_eq_eight (show l'.length = 8 by omega)
    exact ⟨a, b, c, d, e, f, g, h, i, rfl⟩


section N9CentreR1

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
  {c : Fin 9 → Plane₂} {v : Fin 9} {theta : Fin 8 → ℝ}
  (C : SatChart o e 4 lam c v theta)

include C

/-- Distinct non-anchor centres have distinct anchor directions. -/
theorem n9theta_injective : Function.Injective theta := by
  intro i j hij
  by_contra hne
  rcases up_or_up C hne with h | h
  · exact absurd hij (ne_of_lt (up_theta_lt C hne h))
  · exact absurd hij.symm (ne_of_lt (up_theta_lt C (Ne.symm hne) h))

/-- The eight non-anchor `theta`s are distinct. -/
theorem n9Tcard : (Finset.image theta Finset.univ).card = 8 := by
  classical
  rw [Finset.card_image_of_injective _ (n9theta_injective C),
    Finset.card_univ, Fintype.card_fin]

/-- Sorted `theta` values as a strict-mono enumeration. -/
noncomputable def n9T : Fin 8 → ℝ :=
  (Finset.image theta Finset.univ).orderEmbOfFin (n9Tcard C)

theorem n9T_strictMono : StrictMono (n9T C) := fun _ _ h =>
  ((Finset.image theta Finset.univ).orderEmbOfFin _).strictMono h

/-- Rank-to-index bijection: `n9σ C i` is the centre whose `theta`
is the `i`-th smallest. -/
noncomputable def n9σ : Fin 8 → Fin 8 := fun i =>
  (Finset.mem_image.mp
    (Finset.orderEmbOfFin_mem _ (n9Tcard C) i)).choose

theorem n9σ_spec (i : Fin 8) : theta (n9σ C i) = n9T C i :=
  (Finset.mem_image.mp
    (Finset.orderEmbOfFin_mem _ (n9Tcard C) i)).choose_spec.2

theorem n9σ_injective : Function.Injective (n9σ C) := by
  intro i j hij
  apply (n9T_strictMono C).injective
  rw [← n9σ_spec C i, ← n9σ_spec C j, hij]

theorem n9σ_bijective : Function.Bijective (n9σ C) :=
  Finite.injective_iff_bijective.mp (n9σ_injective C)

theorem n9σ_ne {i j : Fin 8} (h : i ≠ j) : n9σ C i ≠ n9σ C j :=
  fun hh => h (n9σ_injective C hh)

/-- A lower-`theta` centre is always `Up` of a higher one, at
`n9σ`-ranks. -/
theorem n9σ_up {i j : Fin 8} (hij : i < j) :
    Up o e c v (n9σ C i) (n9σ C j) := by
  have hlt : theta (n9σ C i) < theta (n9σ C j) := by
    rw [n9σ_spec C i, n9σ_spec C j]
    exact n9T_strictMono C hij
  exact up_of_theta_lt' C (n9σ_ne C hij.ne) hlt

/-- Corridor bounds in model coordinates. -/
theorem n9corridor {i j : Fin 8} (hij : i < j) :
    n9T C i + lam ≤
        dirRep o e (c ∘ v.succAbove) (n9σ C i) (n9σ C j) ∧
      dirRep o e (c ∘ v.succAbove) (n9σ C i) (n9σ C j) ≤
        Real.pi - lam + n9T C j := by
  have hcor := up_corridor C (n9σ_ne C hij.ne) (n9σ_up C hij)
  rwa [n9σ_spec C i, n9σ_spec C j] at hcor

/-- Triple `Up`-constraints in model coordinates. -/
theorem n9triple {i j k : Fin 8} (hij : i < j) (hjk : j < k) :
    (dirRep o e (c ∘ v.succAbove) (n9σ C i) (n9σ C j) + lam ≤
          dirRep o e (c ∘ v.succAbove) (n9σ C j) (n9σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n9σ C i) (n9σ C j) <
          dirRep o e (c ∘ v.succAbove) (n9σ C i) (n9σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n9σ C i) (n9σ C k) <
          dirRep o e (c ∘ v.succAbove) (n9σ C j) (n9σ C k)) ∨
      (dirRep o e (c ∘ v.succAbove) (n9σ C j) (n9σ C k) + lam ≤
          dirRep o e (c ∘ v.succAbove) (n9σ C i) (n9σ C j) ∧
        dirRep o e (c ∘ v.succAbove) (n9σ C j) (n9σ C k) <
          dirRep o e (c ∘ v.succAbove) (n9σ C i) (n9σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n9σ C i) (n9σ C k) <
          dirRep o e (c ∘ v.succAbove) (n9σ C i) (n9σ C j)) := by
  have hl0 : 0 < lam := C.hlam
  have hneij : n9σ C i ≠ n9σ C j := n9σ_ne C hij.ne
  have hnejk : n9σ C j ≠ n9σ C k := n9σ_ne C hjk.ne
  have hneik : n9σ C i ≠ n9σ C k := n9σ_ne C (hij.trans hjk).ne
  have hupij := n9σ_up C hij
  have hupjk := n9σ_up C hjk
  obtain ⟨-, hbetween⟩ := up_trans C hneij hnejk hneik hupij hupjk
  have hcap := up_cap C hneij hnejk hneik hupij hupjk
  rcases le_or_gt 0 (dirRep o e (c ∘ v.succAbove) (n9σ C j) (n9σ C k) -
    dirRep o e (c ∘ v.succAbove) (n9σ C i) (n9σ C j)) with hs | hs
  · rw [abs_of_nonneg hs] at hcap
    rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by linarith, h1, h2⟩
    · exfalso; linarith
  · rw [abs_of_neg hs] at hcap
    rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso; linarith
    · exact Or.inr ⟨by linarith, h1, h2⟩

/-- The scalar `n = 4` model of the nine-centre configuration. -/
noncomputable def n9model : R2N4.N9Model where
  lam := lam
  p := Real.pi
  hlam := C.hlam
  hp := by
    have h1 := C.hnl
    have h2 := C.hπ
    push_cast at h1 h2
    constructor <;> linarith
  t := n9T C
  ht := n9T_strictMono C
  ht0 := by
    have h := (C.htheta (n9σ C 0)).1.1
    rwa [n9σ_spec C 0] at h
  ht7 := by
    have h := (C.htheta (n9σ C 7)).1.2
    rw [n9σ_spec C 7] at h
    push_cast at h ⊢
    linarith
  d := fun i j => dirRep o e (c ∘ v.succAbove) (n9σ C i) (n9σ C j)
  hcor := fun _ _ h => n9corridor C h
  htr := fun _ _ _ h1 h2 => n9triple C h1 h2

theorem n9model_lam : (n9model C).lam = lam := rfl
theorem n9model_p : (n9model C).p = Real.pi := rfl
theorem n9model_t (i : Fin 8) : (n9model C).t i = n9T C i := rfl
theorem n9model_d (i j : Fin 8) :
    (n9model C).d i j =
      dirRep o e (c ∘ v.succAbove) (n9σ C i) (n9σ C j) := rfl

/-- Rank identification: `n9σ C r = u` iff the `r`-th sorted `theta`
value is `theta u`. -/
theorem n9σ_eq_iff (u r : Fin 8) :
    n9σ C r = u ↔ n9T C r = theta u := by
  constructor
  · intro h; rw [← n9σ_spec C r, h]
  · intro h
    exact n9theta_injective C ((n9σ_spec C r).trans h)

/-- Chord symmetry in the model. -/
theorem n9d_comm (i j : Fin 8) (h : i ≠ j) :
    (n9model C).d i j = (n9model C).d j i := by
  have h' : n9σ C i ≠ n9σ C j := n9σ_ne C h
  exact phi_comm C h'

/-- Common core of `n9_row_exists`: the sorted seven-chord list
of the row at chart index `u = n9σ C r`, with ordering and
`List.Perm` onto the model chords. -/
theorem n9_row_core {r u : Fin 8} (hu : n9σ C r = u)
    (hd : rowDefect 4 lam (directionRow o e c (v.succAbove u)) = 2 ∨
      rowDefect 4 lam (directionRow o e c (v.succAbove u)) = 3) :
    ∃ x0, x1, x2, x3, x4, x5, x6 : ℝ,
      (n9T C r ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧ x4 ≤ x5 ∧ x5 ≤ x6 ∧ x6 ≤ n9T C r + Real.pi) ∧
      linearGapScore lam (n9T C r) (n9T C r + Real.pi)
          [x0, x1, x2, x3, x4, x5, x6] = 4 - rowDefect 4 lam
            (directionRow o e c (v.succAbove u)) ∧
      List.Perm [x0, x1, x2, x3, x4, x5, x6]
        (((List.finRange 8).erase r).map fun j =>
          (n9model C).d r j) := by
  classical
  have hTu : n9T C r = theta u := (n9σ_eq_iff C u r).mp hu
  have hlen : (directionRow o e (c ∘ v.succAbove) u).length = 7 := by
    have h := directionRow_length o e (c ∘ v.succAbove) u
    omega
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, hrest⟩ := length_eq_seven hlen
  have hsort := directionRow_sorted o e (c ∘ v.succAbove) u
  rw [hrest] at hsort
  obtain ⟨h01', hs1⟩ := List.sortedLE_cons.mp hsort
  obtain ⟨h12', hs2⟩ := List.sortedLE_cons.mp hs1
  obtain ⟨h23', hs3⟩ := List.sortedLE_cons.mp hs2
  obtain ⟨h34', hs4⟩ := List.sortedLE_cons.mp hs3
  obtain ⟨h45', hs5⟩ := List.sortedLE_cons.mp hs4
  obtain ⟨h56', hs6⟩ := List.sortedLE_cons.mp hs5
  obtain ⟨h67', -⟩ := List.sortedLE_cons.mp hs6
  have e01 : x0 ≤ x1 := h01' x1 (by simp)
  have e12 : x1 ≤ x2 := h12' x2 (by simp)
  have e23 : x2 ≤ x3 := h23' x3 (by simp)
  have e34 : x3 ≤ x4 := h34' x4 (by simp)
  have e45 : x4 ≤ x5 := h45' x5 (by simp)
  have e56 : x5 ≤ x6 := h56' x6 (by simp)
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
  have hx6le : x6 ≤ theta u + Real.pi := by
    have hx := (hmem x6 (by rw [hrest]; simp)).2
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
  refine ⟨x0, x1, x2, x3, x4, x5, x6, ?_, hsub, ?_⟩
  · rw [hTu]
    exact ⟨hx0ge, e01, e12, e23, e34, e45, e56, hx6le⟩
  have hp1 : List.Perm (directionRow o e (c ∘ v.succAbove) u)
      (((List.finRange 8).erase u).map
        (dirRep o e (c ∘ v.succAbove) u)) :=
    List.perm_insertionSort _ _
  rw [hrest] at hp1
  have hmap : List.Perm ((List.finRange 8).erase u)
      (((List.finRange 8).erase r).map (n9σ C)) := by
    apply List.Subperm.antisymm
    · apply List.Nodup.subperm ((List.nodup_finRange 8).erase u)
      intro x hx
      rw [(List.nodup_finRange 8).mem_erase_iff] at hx
      obtain ⟨j, hj⟩ := (n9σ_bijective C).surjective x
      refine List.mem_map.mpr ⟨j, ?_, hj⟩
      rw [(List.nodup_finRange 8).mem_erase_iff]
      exact ⟨fun hjr => hx.1 (by rw [← hj, hjr, hu]),
        List.mem_finRange _⟩
    · apply List.Nodup.subperm
        (((List.nodup_finRange 8).erase r).map (n9σ_injective C))
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨j, hje, rfl⟩ := hx
      rw [(List.nodup_finRange 8).mem_erase_iff] at hje ⊢
      exact ⟨fun hxu => hje.1 (n9σ_injective C (hxu.trans hu.symm)),
        List.mem_finRange _⟩
  have hp2 := hmap.map (dirRep o e (c ∘ v.succAbove) u)
  rw [List.map_map] at hp2
  refine hp1.trans (hp2.trans ?_)
  have hfeq : (dirRep o e (c ∘ v.succAbove) u ∘ n9σ C) =
      fun j => (n9model C).d r j := by
    funext j
    show dirRep o e (c ∘ v.succAbove) u (n9σ C j) =
      (n9model C).d r j
    rw [n9model_d C r j, hu]
  rw [hfeq]

/-- A defect-`2` row at `n = 4` yields a `RowSig2_9` witness list. -/
theorem n9_row2_exists {r u : Fin 8} (hu : n9σ C r = u)
    (hd : rowDefect 4 lam
      (directionRow o e c (v.succAbove u)) = 2) :
    ∃ x0, x1, x2, x3, x4, x5, x6 : ℝ,
      (n9T C r ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧ x4 ≤ x5 ∧ x5 ≤ x6 ∧ x6 ≤ n9T C r + Real.pi) ∧
      R2N4.RowSig2_9 lam Real.pi (n9T C r) x0 x1 x2 x3 x4 x5 x6 ∧
      List.Perm [x0, x1, x2, x3, x4, x5, x6]
        (((List.finRange 8).erase r).map fun j =>
          (n9model C).d r j) := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, hord, hlin, hperm⟩ :=
    n9_row_core C hu (Or.inl hd)
  refine ⟨x0, x1, x2, x3, x4, x5, x6, hord, ?_, hperm⟩
  rw [hd] at hlin
  exact rowSig2_9_of_linearScore_two C.hlam hord (by omega)

/-- A defect-`3` row at `n = 4` yields a `RowSig1_9` witness list. -/
theorem n9_row1_exists {r u : Fin 8} (hu : n9σ C r = u)
    (hd : rowDefect 4 lam
      (directionRow o e c (v.succAbove u)) = 3) :
    ∃ x0, x1, x2, x3, x4, x5, x6 : ℝ,
      (n9T C r ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧ x4 ≤ x5 ∧ x5 ≤ x6 ∧ x6 ≤ n9T C r + Real.pi) ∧
      R2N4.RowSig1_9 lam Real.pi (n9T C r) x0 x1 x2 x3 x4 x5 x6 ∧
      List.Perm [x0, x1, x2, x3, x4, x5, x6]
        (((List.finRange 8).erase r).map fun j =>
          (n9model C).d r j) := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, hord, hlin, hperm⟩ :=
    n9_row_core C hu (Or.inr hd)
  refine ⟨x0, x1, x2, x3, x4, x5, x6, hord, ?_, hperm⟩
  rw [hd] at hlin
  exact rowSig1_9_of_linearScore_one C.hlam hord (by omega)

/-- Rewrites the erased-index chord list of row `r` into min/max
order so it matches the certificate's literal chord lists. -/
theorem n9_row_perm {r : Fin 8} {x0 x1 x2 x3 x4 x5 x6 : ℝ}
    (h : List.Perm [x0, x1, x2, x3, x4, x5, x6]
      (((List.finRange 8).erase r).map fun j =>
        (n9model C).d r j)) :
    List.Perm [x0, x1, x2, x3, x4, x5, x6]
      (((List.finRange 8).erase r).map fun j =>
        (n9model C).d (min r j) (max r j)) := by
  have hmap : ((List.finRange 8).erase r).map
        (fun j => (n9model C).d r j) =
      ((List.finRange 8).erase r).map
        (fun j => (n9model C).d (min r j) (max r j)) := by
    apply List.map_congr_left
    intro j hj
    have hjr : j ≠ r := by
      rw [(List.nodup_finRange 8).mem_erase_iff] at hj
      exact hj.1
    rcases lt_or_ge r j with hlt | hge
    · rw [min_eq_left hlt.le, max_eq_right hlt.le]
    · rw [min_eq_right hge, max_eq_left hge]
      exact n9d_comm C r j hjr.symm
  rwa [hmap] at h

end N9CentreR1


section N10CentreR1

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
  {c : Fin 10 → Plane₂} {v : Fin 10} {theta : Fin 9 → ℝ}
  (C : SatChart o e 4 lam c v theta)

include C

/-- Distinct non-anchor centres have distinct anchor directions. -/
theorem n10theta_injective : Function.Injective theta := by
  intro i j hij
  by_contra hne
  rcases up_or_up C hne with h | h
  · exact absurd hij (ne_of_lt (up_theta_lt C hne h))
  · exact absurd hij.symm (ne_of_lt (up_theta_lt C (Ne.symm hne) h))

/-- The nine non-anchor `theta`s are distinct. -/
theorem n10Tcard : (Finset.image theta Finset.univ).card = 9 := by
  classical
  rw [Finset.card_image_of_injective _ (n10theta_injective C),
    Finset.card_univ, Fintype.card_fin]

/-- Sorted `theta` values as a strict-mono enumeration. -/
noncomputable def n10T : Fin 9 → ℝ :=
  (Finset.image theta Finset.univ).orderEmbOfFin (n10Tcard C)

theorem n10T_strictMono : StrictMono (n10T C) := fun _ _ h =>
  ((Finset.image theta Finset.univ).orderEmbOfFin _).strictMono h

/-- Rank-to-index bijection: `n10σ C i` is the centre whose `theta`
is the `i`-th smallest. -/
noncomputable def n10σ : Fin 9 → Fin 9 := fun i =>
  (Finset.mem_image.mp
    (Finset.orderEmbOfFin_mem _ (n10Tcard C) i)).choose

theorem n10σ_spec (i : Fin 9) : theta (n10σ C i) = n10T C i :=
  (Finset.mem_image.mp
    (Finset.orderEmbOfFin_mem _ (n10Tcard C) i)).choose_spec.2

theorem n10σ_injective : Function.Injective (n10σ C) := by
  intro i j hij
  apply (n10T_strictMono C).injective
  rw [← n10σ_spec C i, ← n10σ_spec C j, hij]

theorem n10σ_bijective : Function.Bijective (n10σ C) :=
  Finite.injective_iff_bijective.mp (n10σ_injective C)

theorem n10σ_ne {i j : Fin 9} (h : i ≠ j) : n10σ C i ≠ n10σ C j :=
  fun hh => h (n10σ_injective C hh)

/-- A lower-`theta` centre is always `Up` of a higher one, at
`n10σ`-ranks. -/
theorem n10σ_up {i j : Fin 9} (hij : i < j) :
    Up o e c v (n10σ C i) (n10σ C j) := by
  have hlt : theta (n10σ C i) < theta (n10σ C j) := by
    rw [n10σ_spec C i, n10σ_spec C j]
    exact n10T_strictMono C hij
  exact up_of_theta_lt' C (n10σ_ne C hij.ne) hlt

/-- Corridor bounds in model coordinates. -/
theorem n10corridor {i j : Fin 9} (hij : i < j) :
    n10T C i + lam ≤
        dirRep o e (c ∘ v.succAbove) (n10σ C i) (n10σ C j) ∧
      dirRep o e (c ∘ v.succAbove) (n10σ C i) (n10σ C j) ≤
        Real.pi - lam + n10T C j := by
  have hcor := up_corridor C (n10σ_ne C hij.ne) (n10σ_up C hij)
  rwa [n10σ_spec C i, n10σ_spec C j] at hcor

/-- Triple `Up`-constraints in model coordinates. -/
theorem n10triple {i j k : Fin 9} (hij : i < j) (hjk : j < k) :
    (dirRep o e (c ∘ v.succAbove) (n10σ C i) (n10σ C j) + lam ≤
          dirRep o e (c ∘ v.succAbove) (n10σ C j) (n10σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n10σ C i) (n10σ C j) <
          dirRep o e (c ∘ v.succAbove) (n10σ C i) (n10σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n10σ C i) (n10σ C k) <
          dirRep o e (c ∘ v.succAbove) (n10σ C j) (n10σ C k)) ∨
      (dirRep o e (c ∘ v.succAbove) (n10σ C j) (n10σ C k) + lam ≤
          dirRep o e (c ∘ v.succAbove) (n10σ C i) (n10σ C j) ∧
        dirRep o e (c ∘ v.succAbove) (n10σ C j) (n10σ C k) <
          dirRep o e (c ∘ v.succAbove) (n10σ C i) (n10σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n10σ C i) (n10σ C k) <
          dirRep o e (c ∘ v.succAbove) (n10σ C i) (n10σ C j)) := by
  have hl0 : 0 < lam := C.hlam
  have hneij : n10σ C i ≠ n10σ C j := n10σ_ne C hij.ne
  have hnejk : n10σ C j ≠ n10σ C k := n10σ_ne C hjk.ne
  have hneik : n10σ C i ≠ n10σ C k := n10σ_ne C (hij.trans hjk).ne
  have hupij := n10σ_up C hij
  have hupjk := n10σ_up C hjk
  obtain ⟨-, hbetween⟩ := up_trans C hneij hnejk hneik hupij hupjk
  have hcap := up_cap C hneij hnejk hneik hupij hupjk
  rcases le_or_gt 0 (dirRep o e (c ∘ v.succAbove) (n10σ C j) (n10σ C k) -
    dirRep o e (c ∘ v.succAbove) (n10σ C i) (n10σ C j)) with hs | hs
  · rw [abs_of_nonneg hs] at hcap
    rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by linarith, h1, h2⟩
    · exfalso; linarith
  · rw [abs_of_neg hs] at hcap
    rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso; linarith
    · exact Or.inr ⟨by linarith, h1, h2⟩

/-- The scalar `n = 4` model of the ten-centre configuration. -/
noncomputable def n10model : R2N4.N10Model where
  lam := lam
  p := Real.pi
  hlam := C.hlam
  hp := by
    have h1 := C.hnl
    have h2 := C.hπ
    push_cast at h1 h2
    constructor <;> linarith
  t := n10T C
  ht := n10T_strictMono C
  ht0 := by
    have h := (C.htheta (n10σ C 0)).1.1
    rwa [n10σ_spec C 0] at h
  ht8 := by
    have h := (C.htheta (n10σ C 8)).1.2
    rw [n10σ_spec C 8] at h
    push_cast at h ⊢
    linarith
  d := fun i j => dirRep o e (c ∘ v.succAbove) (n10σ C i) (n10σ C j)
  hcor := fun _ _ h => n10corridor C h
  htr := fun _ _ _ h1 h2 => n10triple C h1 h2

theorem n10model_lam : (n10model C).lam = lam := rfl
theorem n10model_p : (n10model C).p = Real.pi := rfl
theorem n10model_t (i : Fin 9) : (n10model C).t i = n10T C i := rfl
theorem n10model_d (i j : Fin 9) :
    (n10model C).d i j =
      dirRep o e (c ∘ v.succAbove) (n10σ C i) (n10σ C j) := rfl

/-- Rank identification: `n10σ C r = u` iff the `r`-th sorted `theta`
value is `theta u`. -/
theorem n10σ_eq_iff (u r : Fin 9) :
    n10σ C r = u ↔ n10T C r = theta u := by
  constructor
  · intro h; rw [← n10σ_spec C r, h]
  · intro h
    exact n10theta_injective C ((n10σ_spec C r).trans h)

/-- Chord symmetry in the model. -/
theorem n10d_comm (i j : Fin 9) (h : i ≠ j) :
    (n10model C).d i j = (n10model C).d j i := by
  have h' : n10σ C i ≠ n10σ C j := n10σ_ne C h
  exact phi_comm C h'

/-- Common core of `n10_row_exists`: the sorted eight-chord list
of the row at chart index `u = n10σ C r`, with ordering and
`List.Perm` onto the model chords. -/
theorem n10_row_core {r u : Fin 9} (hu : n10σ C r = u)
    (hd : rowDefect 4 lam (directionRow o e c (v.succAbove u)) = 2 ∨
      rowDefect 4 lam (directionRow o e c (v.succAbove u)) = 3) :
    ∃ x0, x1, x2, x3, x4, x5, x6, x7 : ℝ,
      (n10T C r ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧ x4 ≤ x5 ∧ x5 ≤ x6 ∧ x6 ≤ x7 ∧ x7 ≤ n10T C r + Real.pi) ∧
      linearGapScore lam (n10T C r) (n10T C r + Real.pi)
          [x0, x1, x2, x3, x4, x5, x6, x7] = 4 - rowDefect 4 lam
            (directionRow o e c (v.succAbove u)) ∧
      List.Perm [x0, x1, x2, x3, x4, x5, x6, x7]
        (((List.finRange 9).erase r).map fun j =>
          (n10model C).d r j) := by
  classical
  have hTu : n10T C r = theta u := (n10σ_eq_iff C u r).mp hu
  have hlen : (directionRow o e (c ∘ v.succAbove) u).length = 8 := by
    have h := directionRow_length o e (c ∘ v.succAbove) u
    omega
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, hrest⟩ := length_eq_eight hlen
  have hsort := directionRow_sorted o e (c ∘ v.succAbove) u
  rw [hrest] at hsort
  obtain ⟨h01', hs1⟩ := List.sortedLE_cons.mp hsort
  obtain ⟨h12', hs2⟩ := List.sortedLE_cons.mp hs1
  obtain ⟨h23', hs3⟩ := List.sortedLE_cons.mp hs2
  obtain ⟨h34', hs4⟩ := List.sortedLE_cons.mp hs3
  obtain ⟨h45', hs5⟩ := List.sortedLE_cons.mp hs4
  obtain ⟨h56', hs6⟩ := List.sortedLE_cons.mp hs5
  obtain ⟨h67', hs7⟩ := List.sortedLE_cons.mp hs6
  obtain ⟨h78', -⟩ := List.sortedLE_cons.mp hs7
  have e01 : x0 ≤ x1 := h01' x1 (by simp)
  have e12 : x1 ≤ x2 := h12' x2 (by simp)
  have e23 : x2 ≤ x3 := h23' x3 (by simp)
  have e34 : x3 ≤ x4 := h34' x4 (by simp)
  have e45 : x4 ≤ x5 := h45' x5 (by simp)
  have e56 : x5 ≤ x6 := h56' x6 (by simp)
  have e67 : x6 ≤ x7 := h67' x7 (by simp)
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
  have hx7le : x7 ≤ theta u + Real.pi := by
    have hx := (hmem x7 (by rw [hrest]; simp)).2
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
  refine ⟨x0, x1, x2, x3, x4, x5, x6, x7, ?_, hsub, ?_⟩
  · rw [hTu]
    exact ⟨hx0ge, e01, e12, e23, e34, e45, e56, e67, hx7le⟩
  have hp1 : List.Perm (directionRow o e (c ∘ v.succAbove) u)
      (((List.finRange 9).erase u).map
        (dirRep o e (c ∘ v.succAbove) u)) :=
    List.perm_insertionSort _ _
  rw [hrest] at hp1
  have hmap : List.Perm ((List.finRange 9).erase u)
      (((List.finRange 9).erase r).map (n10σ C)) := by
    apply List.Subperm.antisymm
    · apply List.Nodup.subperm ((List.nodup_finRange 9).erase u)
      intro x hx
      rw [(List.nodup_finRange 9).mem_erase_iff] at hx
      obtain ⟨j, hj⟩ := (n10σ_bijective C).surjective x
      refine List.mem_map.mpr ⟨j, ?_, hj⟩
      rw [(List.nodup_finRange 9).mem_erase_iff]
      exact ⟨fun hjr => hx.1 (by rw [← hj, hjr, hu]),
        List.mem_finRange _⟩
    · apply List.Nodup.subperm
        (((List.nodup_finRange 9).erase r).map (n10σ_injective C))
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨j, hje, rfl⟩ := hx
      rw [(List.nodup_finRange 9).mem_erase_iff] at hje ⊢
      exact ⟨fun hxu => hje.1 (n10σ_injective C (hxu.trans hu.symm)),
        List.mem_finRange _⟩
  have hp2 := hmap.map (dirRep o e (c ∘ v.succAbove) u)
  rw [List.map_map] at hp2
  refine hp1.trans (hp2.trans ?_)
  have hfeq : (dirRep o e (c ∘ v.succAbove) u ∘ n10σ C) =
      fun j => (n10model C).d r j := by
    funext j
    show dirRep o e (c ∘ v.succAbove) u (n10σ C j) =
      (n10model C).d r j
    rw [n10model_d C r j, hu]
  rw [hfeq]

/-- A defect-`2` row at `n = 4` yields a `RowSig2_10` witness list. -/
theorem n10_row2_exists {r u : Fin 9} (hu : n10σ C r = u)
    (hd : rowDefect 4 lam
      (directionRow o e c (v.succAbove u)) = 2) :
    ∃ x0, x1, x2, x3, x4, x5, x6, x7 : ℝ,
      (n10T C r ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧ x4 ≤ x5 ∧ x5 ≤ x6 ∧ x6 ≤ x7 ∧ x7 ≤ n10T C r + Real.pi) ∧
      R2N4.RowSig2_10 lam Real.pi (n10T C r) x0 x1 x2 x3 x4 x5 x6 x7 ∧
      List.Perm [x0, x1, x2, x3, x4, x5, x6, x7]
        (((List.finRange 9).erase r).map fun j =>
          (n10model C).d r j) := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, hord, hlin, hperm⟩ :=
    n10_row_core C hu (Or.inl hd)
  refine ⟨x0, x1, x2, x3, x4, x5, x6, x7, hord, ?_, hperm⟩
  rw [hd] at hlin
  exact rowSig2_10_of_linearScore_two C.hlam hord (by omega)

/-- A defect-`3` row at `n = 4` yields a `RowSig1_10` witness list. -/
theorem n10_row1_exists {r u : Fin 9} (hu : n10σ C r = u)
    (hd : rowDefect 4 lam
      (directionRow o e c (v.succAbove u)) = 3) :
    ∃ x0, x1, x2, x3, x4, x5, x6, x7 : ℝ,
      (n10T C r ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧ x4 ≤ x5 ∧ x5 ≤ x6 ∧ x6 ≤ x7 ∧ x7 ≤ n10T C r + Real.pi) ∧
      R2N4.RowSig1_10 lam Real.pi (n10T C r) x0 x1 x2 x3 x4 x5 x6 x7 ∧
      List.Perm [x0, x1, x2, x3, x4, x5, x6, x7]
        (((List.finRange 9).erase r).map fun j =>
          (n10model C).d r j) := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, hord, hlin, hperm⟩ :=
    n10_row_core C hu (Or.inr hd)
  refine ⟨x0, x1, x2, x3, x4, x5, x6, x7, hord, ?_, hperm⟩
  rw [hd] at hlin
  exact rowSig1_10_of_linearScore_one C.hlam hord (by omega)

/-- Rewrites the erased-index chord list of row `r` into min/max
order so it matches the certificate's literal chord lists. -/
theorem n10_row_perm {r : Fin 9} {x0 x1 x2 x3 x4 x5 x6 x7 : ℝ}
    (h : List.Perm [x0, x1, x2, x3, x4, x5, x6, x7]
      (((List.finRange 9).erase r).map fun j =>
        (n10model C).d r j)) :
    List.Perm [x0, x1, x2, x3, x4, x5, x6, x7]
      (((List.finRange 9).erase r).map fun j =>
        (n10model C).d (min r j) (max r j)) := by
  have hmap : ((List.finRange 9).erase r).map
        (fun j => (n10model C).d r j) =
      ((List.finRange 9).erase r).map
        (fun j => (n10model C).d (min r j) (max r j)) := by
    apply List.map_congr_left
    intro j hj
    have hjr : j ≠ r := by
      rw [(List.nodup_finRange 9).mem_erase_iff] at hj
      exact hj.1
    rcases lt_or_ge r j with hlt | hge
    · rw [min_eq_left hlt.le, max_eq_right hlt.le]
    · rw [min_eq_right hge, max_eq_left hge]
      exact n10d_comm C r j hjr.symm
  rwa [hmap] at h

end N10CentreR1


section N11CentreR1

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
  {c : Fin 11 → Plane₂} {v : Fin 11} {theta : Fin 10 → ℝ}
  (C : SatChart o e 4 lam c v theta)

include C

/-- Distinct non-anchor centres have distinct anchor directions. -/
theorem n11theta_injective : Function.Injective theta := by
  intro i j hij
  by_contra hne
  rcases up_or_up C hne with h | h
  · exact absurd hij (ne_of_lt (up_theta_lt C hne h))
  · exact absurd hij.symm (ne_of_lt (up_theta_lt C (Ne.symm hne) h))

/-- The ten non-anchor `theta`s are distinct. -/
theorem n11Tcard : (Finset.image theta Finset.univ).card = 10 := by
  classical
  rw [Finset.card_image_of_injective _ (n11theta_injective C),
    Finset.card_univ, Fintype.card_fin]

/-- Sorted `theta` values as a strict-mono enumeration. -/
noncomputable def n11T : Fin 10 → ℝ :=
  (Finset.image theta Finset.univ).orderEmbOfFin (n11Tcard C)

theorem n11T_strictMono : StrictMono (n11T C) := fun _ _ h =>
  ((Finset.image theta Finset.univ).orderEmbOfFin _).strictMono h

/-- Rank-to-index bijection: `n11σ C i` is the centre whose `theta`
is the `i`-th smallest. -/
noncomputable def n11σ : Fin 10 → Fin 10 := fun i =>
  (Finset.mem_image.mp
    (Finset.orderEmbOfFin_mem _ (n11Tcard C) i)).choose

theorem n11σ_spec (i : Fin 10) : theta (n11σ C i) = n11T C i :=
  (Finset.mem_image.mp
    (Finset.orderEmbOfFin_mem _ (n11Tcard C) i)).choose_spec.2

theorem n11σ_injective : Function.Injective (n11σ C) := by
  intro i j hij
  apply (n11T_strictMono C).injective
  rw [← n11σ_spec C i, ← n11σ_spec C j, hij]

theorem n11σ_bijective : Function.Bijective (n11σ C) :=
  Finite.injective_iff_bijective.mp (n11σ_injective C)

theorem n11σ_ne {i j : Fin 10} (h : i ≠ j) : n11σ C i ≠ n11σ C j :=
  fun hh => h (n11σ_injective C hh)

/-- A lower-`theta` centre is always `Up` of a higher one, at
`n11σ`-ranks. -/
theorem n11σ_up {i j : Fin 10} (hij : i < j) :
    Up o e c v (n11σ C i) (n11σ C j) := by
  have hlt : theta (n11σ C i) < theta (n11σ C j) := by
    rw [n11σ_spec C i, n11σ_spec C j]
    exact n11T_strictMono C hij
  exact up_of_theta_lt' C (n11σ_ne C hij.ne) hlt

/-- Corridor bounds in model coordinates. -/
theorem n11corridor {i j : Fin 10} (hij : i < j) :
    n11T C i + lam ≤
        dirRep o e (c ∘ v.succAbove) (n11σ C i) (n11σ C j) ∧
      dirRep o e (c ∘ v.succAbove) (n11σ C i) (n11σ C j) ≤
        Real.pi - lam + n11T C j := by
  have hcor := up_corridor C (n11σ_ne C hij.ne) (n11σ_up C hij)
  rwa [n11σ_spec C i, n11σ_spec C j] at hcor

/-- Triple `Up`-constraints in model coordinates. -/
theorem n11triple {i j k : Fin 10} (hij : i < j) (hjk : j < k) :
    (dirRep o e (c ∘ v.succAbove) (n11σ C i) (n11σ C j) + lam ≤
          dirRep o e (c ∘ v.succAbove) (n11σ C j) (n11σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n11σ C i) (n11σ C j) <
          dirRep o e (c ∘ v.succAbove) (n11σ C i) (n11σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n11σ C i) (n11σ C k) <
          dirRep o e (c ∘ v.succAbove) (n11σ C j) (n11σ C k)) ∨
      (dirRep o e (c ∘ v.succAbove) (n11σ C j) (n11σ C k) + lam ≤
          dirRep o e (c ∘ v.succAbove) (n11σ C i) (n11σ C j) ∧
        dirRep o e (c ∘ v.succAbove) (n11σ C j) (n11σ C k) <
          dirRep o e (c ∘ v.succAbove) (n11σ C i) (n11σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n11σ C i) (n11σ C k) <
          dirRep o e (c ∘ v.succAbove) (n11σ C i) (n11σ C j)) := by
  have hl0 : 0 < lam := C.hlam
  have hneij : n11σ C i ≠ n11σ C j := n11σ_ne C hij.ne
  have hnejk : n11σ C j ≠ n11σ C k := n11σ_ne C hjk.ne
  have hneik : n11σ C i ≠ n11σ C k := n11σ_ne C (hij.trans hjk).ne
  have hupij := n11σ_up C hij
  have hupjk := n11σ_up C hjk
  obtain ⟨-, hbetween⟩ := up_trans C hneij hnejk hneik hupij hupjk
  have hcap := up_cap C hneij hnejk hneik hupij hupjk
  rcases le_or_gt 0 (dirRep o e (c ∘ v.succAbove) (n11σ C j) (n11σ C k) -
    dirRep o e (c ∘ v.succAbove) (n11σ C i) (n11σ C j)) with hs | hs
  · rw [abs_of_nonneg hs] at hcap
    rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by linarith, h1, h2⟩
    · exfalso; linarith
  · rw [abs_of_neg hs] at hcap
    rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso; linarith
    · exact Or.inr ⟨by linarith, h1, h2⟩

/-- The scalar `n = 4` model of the eleven-centre configuration. -/
noncomputable def n11model : R2N4.N11Model where
  lam := lam
  p := Real.pi
  hlam := C.hlam
  hp := by
    have h1 := C.hnl
    have h2 := C.hπ
    push_cast at h1 h2
    constructor <;> linarith
  t := n11T C
  ht := n11T_strictMono C
  ht0 := by
    have h := (C.htheta (n11σ C 0)).1.1
    rwa [n11σ_spec C 0] at h
  ht9 := by
    have h := (C.htheta (n11σ C 9)).1.2
    rw [n11σ_spec C 9] at h
    push_cast at h ⊢
    linarith
  d := fun i j => dirRep o e (c ∘ v.succAbove) (n11σ C i) (n11σ C j)
  hcor := fun _ _ h => n11corridor C h
  htr := fun _ _ _ h1 h2 => n11triple C h1 h2

theorem n11model_lam : (n11model C).lam = lam := rfl
theorem n11model_p : (n11model C).p = Real.pi := rfl
theorem n11model_t (i : Fin 10) : (n11model C).t i = n11T C i := rfl
theorem n11model_d (i j : Fin 10) :
    (n11model C).d i j =
      dirRep o e (c ∘ v.succAbove) (n11σ C i) (n11σ C j) := rfl

/-- Rank identification: `n11σ C r = u` iff the `r`-th sorted `theta`
value is `theta u`. -/
theorem n11σ_eq_iff (u r : Fin 10) :
    n11σ C r = u ↔ n11T C r = theta u := by
  constructor
  · intro h; rw [← n11σ_spec C r, h]
  · intro h
    exact n11theta_injective C ((n11σ_spec C r).trans h)

/-- Chord symmetry in the model. -/
theorem n11d_comm (i j : Fin 10) (h : i ≠ j) :
    (n11model C).d i j = (n11model C).d j i := by
  have h' : n11σ C i ≠ n11σ C j := n11σ_ne C h
  exact phi_comm C h'

/-- Common core of `n11_row_exists`: the sorted nine-chord list
of the row at chart index `u = n11σ C r`, with ordering and
`List.Perm` onto the model chords. -/
theorem n11_row_core {r u : Fin 10} (hu : n11σ C r = u)
    (hd : rowDefect 4 lam (directionRow o e c (v.succAbove u)) = 2 ∨
      rowDefect 4 lam (directionRow o e c (v.succAbove u)) = 3) :
    ∃ x0, x1, x2, x3, x4, x5, x6, x7, x8 : ℝ,
      (n11T C r ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧ x4 ≤ x5 ∧ x5 ≤ x6 ∧ x6 ≤ x7 ∧ x7 ≤ x8 ∧ x8 ≤ n11T C r + Real.pi) ∧
      linearGapScore lam (n11T C r) (n11T C r + Real.pi)
          [x0, x1, x2, x3, x4, x5, x6, x7, x8] = 4 - rowDefect 4 lam
            (directionRow o e c (v.succAbove u)) ∧
      List.Perm [x0, x1, x2, x3, x4, x5, x6, x7, x8]
        (((List.finRange 10).erase r).map fun j =>
          (n11model C).d r j) := by
  classical
  have hTu : n11T C r = theta u := (n11σ_eq_iff C u r).mp hu
  have hlen : (directionRow o e (c ∘ v.succAbove) u).length = 9 := by
    have h := directionRow_length o e (c ∘ v.succAbove) u
    omega
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, hrest⟩ := length_eq_nine hlen
  have hsort := directionRow_sorted o e (c ∘ v.succAbove) u
  rw [hrest] at hsort
  obtain ⟨h01', hs1⟩ := List.sortedLE_cons.mp hsort
  obtain ⟨h12', hs2⟩ := List.sortedLE_cons.mp hs1
  obtain ⟨h23', hs3⟩ := List.sortedLE_cons.mp hs2
  obtain ⟨h34', hs4⟩ := List.sortedLE_cons.mp hs3
  obtain ⟨h45', hs5⟩ := List.sortedLE_cons.mp hs4
  obtain ⟨h56', hs6⟩ := List.sortedLE_cons.mp hs5
  obtain ⟨h67', hs7⟩ := List.sortedLE_cons.mp hs6
  obtain ⟨h78', hs8⟩ := List.sortedLE_cons.mp hs7
  obtain ⟨h89', -⟩ := List.sortedLE_cons.mp hs8
  have e01 : x0 ≤ x1 := h01' x1 (by simp)
  have e12 : x1 ≤ x2 := h12' x2 (by simp)
  have e23 : x2 ≤ x3 := h23' x3 (by simp)
  have e34 : x3 ≤ x4 := h34' x4 (by simp)
  have e45 : x4 ≤ x5 := h45' x5 (by simp)
  have e56 : x5 ≤ x6 := h56' x6 (by simp)
  have e67 : x6 ≤ x7 := h67' x7 (by simp)
  have e78 : x7 ≤ x8 := h78' x8 (by simp)
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
  have hx8le : x8 ≤ theta u + Real.pi := by
    have hx := (hmem x8 (by rw [hrest]; simp)).2
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
  refine ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, ?_, hsub, ?_⟩
  · rw [hTu]
    exact ⟨hx0ge, e01, e12, e23, e34, e45, e56, e67, e78, hx8le⟩
  have hp1 : List.Perm (directionRow o e (c ∘ v.succAbove) u)
      (((List.finRange 10).erase u).map
        (dirRep o e (c ∘ v.succAbove) u)) :=
    List.perm_insertionSort _ _
  rw [hrest] at hp1
  have hmap : List.Perm ((List.finRange 10).erase u)
      (((List.finRange 10).erase r).map (n11σ C)) := by
    apply List.Subperm.antisymm
    · apply List.Nodup.subperm ((List.nodup_finRange 10).erase u)
      intro x hx
      rw [(List.nodup_finRange 10).mem_erase_iff] at hx
      obtain ⟨j, hj⟩ := (n11σ_bijective C).surjective x
      refine List.mem_map.mpr ⟨j, ?_, hj⟩
      rw [(List.nodup_finRange 10).mem_erase_iff]
      exact ⟨fun hjr => hx.1 (by rw [← hj, hjr, hu]),
        List.mem_finRange _⟩
    · apply List.Nodup.subperm
        (((List.nodup_finRange 10).erase r).map (n11σ_injective C))
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨j, hje, rfl⟩ := hx
      rw [(List.nodup_finRange 10).mem_erase_iff] at hje ⊢
      exact ⟨fun hxu => hje.1 (n11σ_injective C (hxu.trans hu.symm)),
        List.mem_finRange _⟩
  have hp2 := hmap.map (dirRep o e (c ∘ v.succAbove) u)
  rw [List.map_map] at hp2
  refine hp1.trans (hp2.trans ?_)
  have hfeq : (dirRep o e (c ∘ v.succAbove) u ∘ n11σ C) =
      fun j => (n11model C).d r j := by
    funext j
    show dirRep o e (c ∘ v.succAbove) u (n11σ C j) =
      (n11model C).d r j
    rw [n11model_d C r j, hu]
  rw [hfeq]

/-- A defect-`2` row at `n = 4` yields a `RowSig2_11` witness list. -/
theorem n11_row2_exists {r u : Fin 10} (hu : n11σ C r = u)
    (hd : rowDefect 4 lam
      (directionRow o e c (v.succAbove u)) = 2) :
    ∃ x0, x1, x2, x3, x4, x5, x6, x7, x8 : ℝ,
      (n11T C r ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧ x4 ≤ x5 ∧ x5 ≤ x6 ∧ x6 ≤ x7 ∧ x7 ≤ x8 ∧ x8 ≤ n11T C r + Real.pi) ∧
      R2N4.RowSig2_11 lam Real.pi (n11T C r) x0 x1 x2 x3 x4 x5 x6 x7 x8 ∧
      List.Perm [x0, x1, x2, x3, x4, x5, x6, x7, x8]
        (((List.finRange 10).erase r).map fun j =>
          (n11model C).d r j) := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, hord, hlin, hperm⟩ :=
    n11_row_core C hu (Or.inl hd)
  refine ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, hord, ?_, hperm⟩
  rw [hd] at hlin
  exact rowSig2_11_of_linearScore_two C.hlam hord (by omega)

/-- A defect-`3` row at `n = 4` yields a `RowSig1_11` witness list. -/
theorem n11_row1_exists {r u : Fin 10} (hu : n11σ C r = u)
    (hd : rowDefect 4 lam
      (directionRow o e c (v.succAbove u)) = 3) :
    ∃ x0, x1, x2, x3, x4, x5, x6, x7, x8 : ℝ,
      (n11T C r ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧ x4 ≤ x5 ∧ x5 ≤ x6 ∧ x6 ≤ x7 ∧ x7 ≤ x8 ∧ x8 ≤ n11T C r + Real.pi) ∧
      R2N4.RowSig1_11 lam Real.pi (n11T C r) x0 x1 x2 x3 x4 x5 x6 x7 x8 ∧
      List.Perm [x0, x1, x2, x3, x4, x5, x6, x7, x8]
        (((List.finRange 10).erase r).map fun j =>
          (n11model C).d r j) := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, hord, hlin, hperm⟩ :=
    n11_row_core C hu (Or.inr hd)
  refine ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, hord, ?_, hperm⟩
  rw [hd] at hlin
  exact rowSig1_11_of_linearScore_one C.hlam hord (by omega)

/-- Rewrites the erased-index chord list of row `r` into min/max
order so it matches the certificate's literal chord lists. -/
theorem n11_row_perm {r : Fin 10} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : ℝ}
    (h : List.Perm [x0, x1, x2, x3, x4, x5, x6, x7, x8]
      (((List.finRange 10).erase r).map fun j =>
        (n11model C).d r j)) :
    List.Perm [x0, x1, x2, x3, x4, x5, x6, x7, x8]
      (((List.finRange 10).erase r).map fun j =>
        (n11model C).d (min r j) (max r j)) := by
  have hmap : ((List.finRange 10).erase r).map
        (fun j => (n11model C).d r j) =
      ((List.finRange 10).erase r).map
        (fun j => (n11model C).d (min r j) (max r j)) := by
    apply List.map_congr_left
    intro j hj
    have hjr : j ≠ r := by
      rw [(List.nodup_finRange 10).mem_erase_iff] at hj
      exact hj.1
    rcases lt_or_ge r j with hlt | hge
    · rw [min_eq_left hlt.le, max_eq_right hlt.le]
    · rw [min_eq_right hge, max_eq_left hge]
      exact n11d_comm C r j hjr.symm
  rwa [hmap] at h

end N11CentreR1


section N8CentreR1

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
  {c : Fin 8 → Plane₂} {v : Fin 8} {theta : Fin 7 → ℝ}
  (C : SatChart o e 4 lam c v theta)

/-- A defect-`3` row at `n = 4` yields a `RowSig1_8` witness list
(the `n = 8` analogue S8 did not need). -/
theorem n8_row1_exists {r u : Fin 7} (hu : n8σ C r = u)
    (hd : rowDefect 4 lam
      (directionRow o e c (v.succAbove u)) = 3) :
    ∃ x0 x1 x2 x3 x4 x5 : ℝ,
      (n8T C r ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧ x4 ≤ x5 ∧ x5 ≤ n8T C r + Real.pi) ∧
      R2N4.RowSig1_8 lam Real.pi (n8T C r) x0 x1 x2 x3 x4 x5 ∧
      List.Perm [x0, x1, x2, x3, x4, x5]
        (((List.finRange 7).erase r).map fun j =>
          (n8model C).d r j) := by
  obtain ⟨x0, x1, x2, x3, x4, x5, hord, hlin, hperm⟩ :=
    n8_row_core C hu (Or.inr hd)
  refine ⟨x0, x1, x2, x3, x4, x5, hord, ?_, hperm⟩
  rw [hd] at hlin
  exact rowSig1_8_of_linearScore_one C.hlam hord (by omega)

end N8CentreR1

end Jsp404
