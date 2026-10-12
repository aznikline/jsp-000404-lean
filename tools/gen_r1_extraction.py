#!/usr/bin/env python3
"""Emit Jsp000404/R1Extraction.lean: N{9,10,11}Model scalar-model
extraction for the R1 terminal profiles — mechanical P-port of
S8Extraction (plus `n8_row1_exists` which S8 did not need).

Per P the section provides: sorted non-anchor thetas `n{P}T`, the
rank bijection `n{P}σ`, corridor/triple-order replay, the model
`n{P}model`, the row witness `n{P}_row_core`, signature producers
`n{P}_row{1,2}_exists` and the min/max chord perm `n{P}_row_perm`.
"""
import os

HERE = os.path.dirname(os.path.abspath(__file__))

WORDS = {3: 'three', 4: 'four', 5: 'five', 6: 'six', 7: 'seven',
         8: 'eight', 9: 'nine', 10: 'ten', 11: 'eleven'}
NUMS = {'three': 3, 'four': 4, 'five': 5, 'six': 6, 'seven': 7,
        'eight': 8, 'nine': 9, 'ten': 10, 'eleven': 11}


def len_split(n):
    """`length_eq_{word n}`: split an n-element list into literals."""
    w = WORDS[n]
    prev = WORDS[n - 1]
    names = ' '.join(chr(ord('a') + i) for i in range(n))
    cnames = ', '.join(chr(ord('a') + i) for i in range(n))
    lits = '[' + ', '.join(chr(ord('a') + i) for i in range(n)) + ']'
    plits = '[' + ', '.join(chr(ord('a') + i) for i in range(1, n)) + ']'
    prevn = ', '.join(chr(ord('a') + i) for i in range(1, n))
    if n == 5:
        inner = f'''  cases l with
  | nil => simp at h
  | cons a l' =>
    rw [List.length_cons] at h
    obtain ⟨b, c, d, e, rfl⟩ :=
      List.length_eq_four.mp (show l'.length = 4 by omega)
    exact ⟨a, b, c, d, e, rfl⟩'''
        return f'''/-- A {w}-element list splits into its literals. -/
private theorem length_eq_{w} {{α : Type*}} {{l : List α}}
    (h : l.length = {n}) :
    ∃ a b c d e : α, l = {lits} := by
{inner}'''
    inner = f'''  cases l with
  | nil => simp at h
  | cons a l' =>
    rw [List.length_cons] at h
    obtain ⟨{prevn}, rfl⟩ :=
      length_eq_{prev} (show l'.length = {n - 1} by omega)
    exact ⟨{cnames}, rfl⟩'''
    return f'''/-- A {w}-element list splits into its literals. -/
private theorem length_eq_{w} {{α : Type*}} {{l : List α}}
    (h : l.length = {n}) :
    ∃ {names} : α, l = {lits} := by
{inner}'''


def section(P):
    """Whole section for N{P}Model extraction."""
    M = P - 1          # non-anchor centres / t-vars / ranks
    N = P - 2          # row literals (chords per row)
    last = M - 1       # last t index (ht{last} field)
    xs = [f'x{i}' for i in range(N)]
    xs_sp = ' '.join(xs)
    xs_ls = '[' + ', '.join(xs) + ']'
    # ordering chain  T r ≤ x0 ≤ x1 ≤ … ≤ x{N-1} ≤ T r + π
    chain = [f'n{P}T C r ≤ {xs[0]}'] + \
        [f'{xs[i]} ≤ {xs[i + 1]}' for i in range(N - 1)] + \
        [f'{xs[N - 1]} ≤ n{P}T C r + Real.pi']
    ord_and = ' ∧ '.join(chain)
    # extraction of sorted-cons proofs
    cons_lines = []
    for i in range(N - 1):
        src = 'hsort' if i == 0 else f'hs{i}'
        cons_lines.append(
            f'  obtain ⟨h{i}{i + 1}\', hs{i + 1}⟩ := '
            f'List.sortedLE_cons.mp {src}')
    e_lines = []
    for i in range(N - 1):
        e_lines.append(
            f'  have e{i}{i + 1} : {xs[i]} ≤ {xs[i + 1]} := '
            f'h{i}{i + 1}\' {xs[i + 1]} (by simp)')
    exists_args = ', '.join(xs)
    tuple_args = ', '.join(xs)
    refine_ord = ('⟨' + ('hx0ge, ' if True else '') +
                  ', '.join(f'e{i}{i + 1}' for i in range(N - 1)) +
                  f', hx{N - 1}le⟩')
    # model ht field
    return f'''
section N{P}CentreR1

variable {{o : Orientation ℝ Plane₂ (Fin 2)}} {{e : Plane₂}} {{lam : ℝ}}
  {{c : Fin {P} → Plane₂}} {{v : Fin {P}}} {{theta : Fin {M} → ℝ}}
  (C : SatChart o e 4 lam c v theta)

include C

/-- Distinct non-anchor centres have distinct anchor directions. -/
theorem n{P}theta_injective : Function.Injective theta := by
  intro i j hij
  by_contra hne
  rcases up_or_up C hne with h | h
  · exact absurd hij (ne_of_lt (up_theta_lt C hne h))
  · exact absurd hij.symm (ne_of_lt (up_theta_lt C (Ne.symm hne) h))

/-- The {WORDS[M]} non-anchor `theta`s are distinct. -/
theorem n{P}Tcard : (Finset.image theta Finset.univ).card = {M} := by
  classical
  rw [Finset.card_image_of_injective _ (n{P}theta_injective C),
    Finset.card_univ, Fintype.card_fin]

/-- Sorted `theta` values as a strict-mono enumeration. -/
noncomputable def n{P}T : Fin {M} → ℝ :=
  (Finset.image theta Finset.univ).orderEmbOfFin (n{P}Tcard C)

theorem n{P}T_strictMono : StrictMono (n{P}T C) := fun _ _ h =>
  ((Finset.image theta Finset.univ).orderEmbOfFin _).strictMono h

/-- Rank-to-index bijection: `n{P}σ C i` is the centre whose `theta`
is the `i`-th smallest. -/
noncomputable def n{P}σ : Fin {M} → Fin {M} := fun i =>
  (Finset.mem_image.mp
    (Finset.orderEmbOfFin_mem _ (n{P}Tcard C) i)).choose

theorem n{P}σ_spec (i : Fin {M}) : theta (n{P}σ C i) = n{P}T C i :=
  (Finset.mem_image.mp
    (Finset.orderEmbOfFin_mem _ (n{P}Tcard C) i)).choose_spec.2

theorem n{P}σ_injective : Function.Injective (n{P}σ C) := by
  intro i j hij
  apply (n{P}T_strictMono C).injective
  rw [← n{P}σ_spec C i, ← n{P}σ_spec C j, hij]

theorem n{P}σ_bijective : Function.Bijective (n{P}σ C) :=
  Finite.injective_iff_bijective.mp (n{P}σ_injective C)

theorem n{P}σ_ne {{i j : Fin {M}}} (h : i ≠ j) : n{P}σ C i ≠ n{P}σ C j :=
  fun hh => h (n{P}σ_injective C hh)

/-- A lower-`theta` centre is always `Up` of a higher one, at
`n{P}σ`-ranks. -/
theorem n{P}σ_up {{i j : Fin {M}}} (hij : i < j) :
    Up o e c v (n{P}σ C i) (n{P}σ C j) := by
  have hlt : theta (n{P}σ C i) < theta (n{P}σ C j) := by
    rw [n{P}σ_spec C i, n{P}σ_spec C j]
    exact n{P}T_strictMono C hij
  exact up_of_theta_lt' C (n{P}σ_ne C hij.ne) hlt

/-- Corridor bounds in model coordinates. -/
theorem n{P}corridor {{i j : Fin {M}}} (hij : i < j) :
    n{P}T C i + lam ≤
        dirRep o e (c ∘ v.succAbove) (n{P}σ C i) (n{P}σ C j) ∧
      dirRep o e (c ∘ v.succAbove) (n{P}σ C i) (n{P}σ C j) ≤
        Real.pi - lam + n{P}T C j := by
  have hcor := up_corridor C (n{P}σ_ne C hij.ne) (n{P}σ_up C hij)
  rwa [n{P}σ_spec C i, n{P}σ_spec C j] at hcor

/-- Triple `Up`-constraints in model coordinates. -/
theorem n{P}triple {{i j k : Fin {M}}} (hij : i < j) (hjk : j < k) :
    (dirRep o e (c ∘ v.succAbove) (n{P}σ C i) (n{P}σ C j) + lam ≤
          dirRep o e (c ∘ v.succAbove) (n{P}σ C j) (n{P}σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n{P}σ C i) (n{P}σ C j) <
          dirRep o e (c ∘ v.succAbove) (n{P}σ C i) (n{P}σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n{P}σ C i) (n{P}σ C k) <
          dirRep o e (c ∘ v.succAbove) (n{P}σ C j) (n{P}σ C k)) ∨
      (dirRep o e (c ∘ v.succAbove) (n{P}σ C j) (n{P}σ C k) + lam ≤
          dirRep o e (c ∘ v.succAbove) (n{P}σ C i) (n{P}σ C j) ∧
        dirRep o e (c ∘ v.succAbove) (n{P}σ C j) (n{P}σ C k) <
          dirRep o e (c ∘ v.succAbove) (n{P}σ C i) (n{P}σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n{P}σ C i) (n{P}σ C k) <
          dirRep o e (c ∘ v.succAbove) (n{P}σ C i) (n{P}σ C j)) := by
  have hl0 : 0 < lam := C.hlam
  have hneij : n{P}σ C i ≠ n{P}σ C j := n{P}σ_ne C hij.ne
  have hnejk : n{P}σ C j ≠ n{P}σ C k := n{P}σ_ne C hjk.ne
  have hneik : n{P}σ C i ≠ n{P}σ C k := n{P}σ_ne C (hij.trans hjk).ne
  have hupij := n{P}σ_up C hij
  have hupjk := n{P}σ_up C hjk
  obtain ⟨-, hbetween⟩ := up_trans C hneij hnejk hneik hupij hupjk
  have hcap := up_cap C hneij hnejk hneik hupij hupjk
  rcases le_or_gt 0 (dirRep o e (c ∘ v.succAbove) (n{P}σ C j) (n{P}σ C k) -
    dirRep o e (c ∘ v.succAbove) (n{P}σ C i) (n{P}σ C j)) with hs | hs
  · rw [abs_of_nonneg hs] at hcap
    rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by linarith, h1, h2⟩
    · exfalso; linarith
  · rw [abs_of_neg hs] at hcap
    rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso; linarith
    · exact Or.inr ⟨by linarith, h1, h2⟩

/-- The scalar `n = 4` model of the {WORDS[P]}-centre configuration. -/
noncomputable def n{P}model : R2N4.N{P}Model where
  lam := lam
  p := Real.pi
  hlam := C.hlam
  hp := by
    have h1 := C.hnl
    have h2 := C.hπ
    push_cast at h1 h2
    constructor <;> linarith
  t := n{P}T C
  ht := n{P}T_strictMono C
  ht0 := by
    have h := (C.htheta (n{P}σ C 0)).1.1
    rwa [n{P}σ_spec C 0] at h
  ht{last} := by
    have h := (C.htheta (n{P}σ C {last})).1.2
    rw [n{P}σ_spec C {last}] at h
    push_cast at h ⊢
    linarith
  d := fun i j => dirRep o e (c ∘ v.succAbove) (n{P}σ C i) (n{P}σ C j)
  hcor := fun _ _ h => n{P}corridor C h
  htr := fun _ _ _ h1 h2 => n{P}triple C h1 h2

theorem n{P}model_lam : (n{P}model C).lam = lam := rfl
theorem n{P}model_p : (n{P}model C).p = Real.pi := rfl
theorem n{P}model_t (i : Fin {M}) : (n{P}model C).t i = n{P}T C i := rfl
theorem n{P}model_d (i j : Fin {M}) :
    (n{P}model C).d i j =
      dirRep o e (c ∘ v.succAbove) (n{P}σ C i) (n{P}σ C j) := rfl

/-- Rank identification: `n{P}σ C r = u` iff the `r`-th sorted `theta`
value is `theta u`. -/
theorem n{P}σ_eq_iff (u r : Fin {M}) :
    n{P}σ C r = u ↔ n{P}T C r = theta u := by
  constructor
  · intro h; rw [← n{P}σ_spec C r, h]
  · intro h
    exact n{P}theta_injective C ((n{P}σ_spec C r).trans h)

/-- Chord symmetry in the model. -/
theorem n{P}d_comm (i j : Fin {M}) (h : i ≠ j) :
    (n{P}model C).d i j = (n{P}model C).d j i := by
  have h' : n{P}σ C i ≠ n{P}σ C j := n{P}σ_ne C h
  exact phi_comm C h'

/-- Common core of `n{P}_row_exists`: the sorted {WORDS[N]}-chord list
of the row at chart index `u = n{P}σ C r`, with ordering and
`List.Perm` onto the model chords. -/
theorem n{P}_row_core {{r u : Fin {M}}} (hu : n{P}σ C r = u)
    (hd : rowDefect 4 lam (directionRow o e c (v.succAbove u)) = 2 ∨
      rowDefect 4 lam (directionRow o e c (v.succAbove u)) = 3) :
    ∃ {exists_args} : ℝ,
      ({ord_and}) ∧
      linearGapScore lam (n{P}T C r) (n{P}T C r + Real.pi)
          {xs_ls} = 4 - rowDefect 4 lam
            (directionRow o e c (v.succAbove u)) ∧
      List.Perm {xs_ls}
        (((List.finRange {M}).erase r).map fun j =>
          (n{P}model C).d r j) := by
  classical
  have hTu : n{P}T C r = theta u := (n{P}σ_eq_iff C u r).mp hu
  have hlen : (directionRow o e (c ∘ v.succAbove) u).length = {N} := by
    have h := directionRow_length o e (c ∘ v.succAbove) u
    omega
  obtain ⟨{tuple_args}, hrest⟩ := length_eq_{WORDS[N]} hlen
  have hsort := directionRow_sorted o e (c ∘ v.succAbove) u
  rw [hrest] at hsort
{chr(10).join(cons_lines)}
  obtain ⟨h{N - 1}{N}\', -⟩ := List.sortedLE_cons.mp hs{N - 1}
{chr(10).join(e_lines)}
  have hmem : ∀ x ∈ directionRow o e (c ∘ v.succAbove) u,
      lam ≤ x ∧ x < Real.pi := by
    intro x hx
    obtain ⟨j, hju, rfl⟩ := (mem_directionRow o e
      (c ∘ v.succAbove)).mp hx
    exact ⟨phi_ge_lam C (Ne.symm hju), (linRep_mem_Ico _).2⟩
  have hβ : Real.pi - 4 * lam < lam := by exact_mod_cast C.hβ
  have hx0ge : theta u ≤ {xs[0]} := by
    have hx := (hmem {xs[0]} (by rw [hrest]; simp)).1
    have hθ : theta u ≤ Real.pi - 4 * lam := by
      exact_mod_cast (C.htheta u).1.2
    linarith
  have hx{N - 1}le : {xs[N - 1]} ≤ theta u + Real.pi := by
    have hx := (hmem {xs[N - 1]} (by rw [hrest]; simp)).2
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
  refine ⟨{tuple_args}, ?_, hsub, ?_⟩
  · rw [hTu]
    exact {refine_ord}
  have hp1 : List.Perm (directionRow o e (c ∘ v.succAbove) u)
      (((List.finRange {M}).erase u).map
        (dirRep o e (c ∘ v.succAbove) u)) :=
    List.perm_insertionSort _ _
  rw [hrest] at hp1
  have hmap : List.Perm ((List.finRange {M}).erase u)
      (((List.finRange {M}).erase r).map (n{P}σ C)) := by
    apply List.Subperm.antisymm
    · apply List.Nodup.subperm ((List.nodup_finRange {M}).erase u)
      intro x hx
      rw [(List.nodup_finRange {M}).mem_erase_iff] at hx
      obtain ⟨j, hj⟩ := (n{P}σ_bijective C).surjective x
      refine List.mem_map.mpr ⟨j, ?_, hj⟩
      rw [(List.nodup_finRange {M}).mem_erase_iff]
      exact ⟨fun hjr => hx.1 (by rw [← hj, hjr, hu]),
        List.mem_finRange _⟩
    · apply List.Nodup.subperm
        (((List.nodup_finRange {M}).erase r).map (n{P}σ_injective C))
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨j, hje, rfl⟩ := hx
      rw [(List.nodup_finRange {M}).mem_erase_iff] at hje ⊢
      exact ⟨fun hxu => hje.1 (n{P}σ_injective C (hxu.trans hu.symm)),
        List.mem_finRange _⟩
  have hp2 := hmap.map (dirRep o e (c ∘ v.succAbove) u)
  rw [List.map_map] at hp2
  refine hp1.trans (hp2.trans ?_)
  have hfeq : (dirRep o e (c ∘ v.succAbove) u ∘ n{P}σ C) =
      fun j => (n{P}model C).d r j := by
    funext j
    show dirRep o e (c ∘ v.succAbove) u (n{P}σ C j) =
      (n{P}model C).d r j
    rw [n{P}model_d C r j, hu]
  rw [hfeq]

/-- A defect-`2` row at `n = 4` yields a `RowSig2_{P}` witness list. -/
theorem n{P}_row2_exists {{r u : Fin {M}}} (hu : n{P}σ C r = u)
    (hd : rowDefect 4 lam
      (directionRow o e c (v.succAbove u)) = 2) :
    ∃ {exists_args} : ℝ,
      ({ord_and}) ∧
      R2N4.RowSig2_{P} lam Real.pi (n{P}T C r) {xs_sp} ∧
      List.Perm {xs_ls}
        (((List.finRange {M}).erase r).map fun j =>
          (n{P}model C).d r j) := by
  obtain ⟨{tuple_args}, hord, hlin, hperm⟩ :=
    n{P}_row_core C hu (Or.inl hd)
  refine ⟨{tuple_args}, hord, ?_, hperm⟩
  rw [hd] at hlin
  exact rowSig2_{P}_of_linearScore_two C.hlam hord (by omega)

/-- A defect-`3` row at `n = 4` yields a `RowSig1_{P}` witness list. -/
theorem n{P}_row1_exists {{r u : Fin {M}}} (hu : n{P}σ C r = u)
    (hd : rowDefect 4 lam
      (directionRow o e c (v.succAbove u)) = 3) :
    ∃ {exists_args} : ℝ,
      ({ord_and}) ∧
      R2N4.RowSig1_{P} lam Real.pi (n{P}T C r) {xs_sp} ∧
      List.Perm {xs_ls}
        (((List.finRange {M}).erase r).map fun j =>
          (n{P}model C).d r j) := by
  obtain ⟨{tuple_args}, hord, hlin, hperm⟩ :=
    n{P}_row_core C hu (Or.inr hd)
  refine ⟨{tuple_args}, hord, ?_, hperm⟩
  rw [hd] at hlin
  exact rowSig1_{P}_of_linearScore_one C.hlam hord (by omega)

/-- Rewrites the erased-index chord list of row `r` into min/max
order so it matches the certificate's literal chord lists. -/
theorem n{P}_row_perm {{r : Fin {M}}} {{{xs_sp} : ℝ}}
    (h : List.Perm {xs_ls}
      (((List.finRange {M}).erase r).map fun j =>
        (n{P}model C).d r j)) :
    List.Perm {xs_ls}
      (((List.finRange {M}).erase r).map fun j =>
        (n{P}model C).d (min r j) (max r j)) := by
  have hmap : ((List.finRange {M}).erase r).map
        (fun j => (n{P}model C).d r j) =
      ((List.finRange {M}).erase r).map
        (fun j => (n{P}model C).d (min r j) (max r j)) := by
    apply List.map_congr_left
    intro j hj
    have hjr : j ≠ r := by
      rw [(List.nodup_finRange {M}).mem_erase_iff] at hj
      exact hj.1
    rcases lt_or_ge r j with hlt | hge
    · rw [min_eq_left hlt.le, max_eq_right hlt.le]
    · rw [min_eq_right hge, max_eq_left hge]
      exact n{P}d_comm C r j hjr.symm
  rwa [hmap] at h

end N{P}CentreR1
'''


def n8_row1():
    """The missing defect-3 row extraction for P = 8."""
    M, N = 7, 6
    xs = [f'x{i}' for i in range(N)]
    chain = ['n8T C r ≤ x0'] + \
        [f'{xs[i]} ≤ {xs[i + 1]}' for i in range(N - 1)] + \
        [f'{xs[N - 1]} ≤ n8T C r + Real.pi']
    return f'''
section N8CentreR1

variable {{o : Orientation ℝ Plane₂ (Fin 2)}} {{e : Plane₂}} {{lam : ℝ}}
  {{c : Fin 8 → Plane₂}} {{v : Fin 8}} {{theta : Fin 7 → ℝ}}
  (C : SatChart o e 4 lam c v theta)

/-- A defect-`3` row at `n = 4` yields a `RowSig1_8` witness list
(the `n = 8` analogue S8 did not need). -/
theorem n8_row1_exists {{r u : Fin 7}} (hu : n8σ C r = u)
    (hd : rowDefect 4 lam
      (directionRow o e c (v.succAbove u)) = 3) :
    ∃ x0 x1 x2 x3 x4 x5 : ℝ,
      ({' ∧ '.join(chain)}) ∧
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
'''


def main():
    out = ['''import Jsp000404.S8Extraction
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

''']
    for n in (5, 6, 7, 8, 9):
        out.append(len_split(n))
        out.append('')
    for P in (9, 10, 11):
        out.append(section(P))
    out.append(n8_row1())
    out.append('end Jsp404')
    path = os.path.join(HERE, '..', 'Jsp000404', 'R1Extraction.lean')
    with open(path, 'w') as f:
        f.write('\n'.join(out) + '\n')
    print('wrote', path, os.path.getsize(path))


if __name__ == '__main__':
    main()
