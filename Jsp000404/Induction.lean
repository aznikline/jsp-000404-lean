import Jsp000404.Base3Bridge
import Jsp000404.GeometricDeletion
import Jsp000404.Staircase

/-!
# P5 — induction skeleton: the potential bound modulo the certificate

This file assembles the arbitrary-`s` potential bound from:

* `Base3Bridge.base3_potential_le{,_big}` — the `s = 3` base (P0);
* `Section4Legality.erase` — hereditary legality under `succAbove` (P2);
* `potential_sub_config` / `potential_le_sub_config_iff` — the
  geometric deletion identity (P3);
* `removable_of_dichotomy` — `EmissionDichotomy` yields a removable
  vertex (pure bookkeeping, proved).

The **only** mathematical content not yet proved is packaged as
`CertExists`: on a legal configuration of `t ≥ 4` centers whose
potential exceeds the cap, the emission dichotomy holds.  Everything
else — the strong induction over vertex deletion, both cap regimes,
the `s = 3` anchor — is kernel-checked in this file.
-/

namespace Jsp404

open Finset
open scoped EuclideanGeometry

variable (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)

/-- The uniform Sendov cap `2^n + bonus`, `bonus = 2^{n-2}` in the
`1/2 ≤ δ` regime and `0` in the `δ < 1/2` regime. -/
def sendovCap (n : ℕ) (big : Bool) : ℕ :=
  2 ^ n + if big then 2 ^ (n - 2) else 0

/-- **The isolated P4 crux.**  On every legal `t ≥ 4` center
configuration whose potential exceeds the cap, the emission dichotomy
holds — equivalently (by `removable_of_dichotomy`) a removable vertex
exists.  This is the only remaining mathematical content of the
Sendov count bound; everything downstream is proved here. -/
def CertExists (n : ℕ) (big : Bool) (lam : ℝ) : Prop :=
  ∀ {t : ℕ} {c : Fin t → Plane₂}, 4 ≤ t →
    Section4Legality c lam →
    sendovCap n big < potential lam (directionRows o e c) →
    EmissionDichotomy lam
      (fun v i => deleteIndex o e c v i) (directionRows o e c)

/-- **P5 — the induction.**  For every legal configuration of `s ≥ 3`
centers, the potential is at most the Sendov cap, modulo the
certificate hypothesis `CertExists`.  The proof is strong induction on
`s`: the `s = 3` base is P0; for `s ≥ 4`, either the potential is
already under the cap, or the crux supplies a removable vertex whose
deletion preserves legality and does not decrease the potential, so
the inductive hypothesis closes the bound. -/
theorem potential_le_sendovCap {n : ℕ} (hn2 : 2 ≤ n) (big : Bool)
    {lam : ℝ} (hlam : 0 < lam) (hlampi : lam < Real.pi)
    (hn : Nat.floor (Real.pi / lam) = n)
    (hbig : big = false → Real.pi / lam - n < 1 / 2)
    (hcert : CertExists o e n big lam) (he : e ≠ 0) :
    ∀ {s : ℕ}, 3 ≤ s → ∀ {c : Fin s → Plane₂},
      Section4Legality c lam →
      potential lam (directionRows o e c) ≤ sendovCap n big := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
    intro hs c hlegal
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    by_cases ht : t = 2
    · -- `s = 3`: the P0 closed-form base.
      subst ht
      cases big with
      | false =>
          simp only [sendovCap]
          exact base3_potential_le (o := o) (e := e)
            hlegal he hlampi hn hn2 (hbig rfl)
      | true =>
          have h := base3_potential_le_big (o := o) (e := e)
            hlegal he hlampi hn hn2
          have heq : 2 ^ n + 2 ^ (n - 2) = 5 * 2 ^ (n - 2) := by
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
            simp only [Nat.add_sub_cancel, pow_add]
            ring
          rw [sendovCap, ite_eq_left rfl]
          rwa [heq]
    · -- `s = t + 1 ≥ 4`: delete a certificate vertex and induct.
      have ht3 : 3 ≤ t := by omega
      by_cases hF : potential lam (directionRows o e c) ≤ sendovCap n big
      · exact hF
      · push Not at hF
        have hdich := hcert (t := t + 1) (c := c) (by omega) hlegal hF
        obtain ⟨v, hrem⟩ := removable_of_dichotomy hlam
          (fun i => directionRow_sorted o e c i)
          (fun i b hb => Set.mem_Ico.mp (directionRow_mem_Ico o e c hb))
          (fun i => by rw [directionRow_length o e c i]; omega)
          (fun v i hi => deleteIndex_lt o e c hi)
          hdich
        have hle : potential lam (directionRows o e c) ≤
            potential lam (directionRows o e (c ∘ v.succAbove)) := by
          rw [potential_sub_config]; exact hrem
        exact hle.trans
          (IH t (by omega) ht3 (Section4Legality.erase hlegal v))

/-! ### The `circleDirs`/`directionRow` bridge

`exponents` is defined on `circleDirs` (deduplicated fans, with
`gapAfter` gaps); `potential` on `directionRow` (multiplicity fans,
with `cycGaps`).  Three bridges connect them: the gap sequence
identity `cycGaps = ofFn gapAfter`, the row identity
`circleDirs = directionRow.dedup`, and the dedup invariance
`rowScore_dedup`. -/

/-- `cyclicDiff` on a non-decreasing pair is the plain difference. -/
theorem cyclicDiff_eq_sub_of_le {a b : ℝ} (h : a ≤ b) :
    cyclicDiff a b = b - a := by
  unfold cyclicDiff
  by_cases h1 : a = b
  · rw [if_pos h1]; linarith
  · rw [if_neg h1, if_pos (lt_of_le_of_ne h h1)]

/-- For a sorted list, `cycGaps` coincides with the `gapAfter`
sequence: adjacent diffs plus the wrap gap `l[0] + π - l[last]`. -/
theorem cycGaps_eq_ofFn_gapAfter {l : List ℝ} (hs : l.SortedLE) :
    cycGaps l = List.ofFn (fun i : Fin l.length => gapAfter l i) := by
  rcases eq_or_ne l [] with rfl | hne
  · rfl
  · have hlen : (l.dropLast.zip l.tail).length = l.length - 1 := by
      rw [List.length_zip, List.length_dropLast, List.length_tail]
      omega
    have hcg : cycGaps l =
        (l.dropLast.zip l.tail).map (fun p => cyclicDiff p.1 p.2)
          ++ [wrapGap l hne] := by
      unfold cycGaps; rw [dif_neg hne]
    rw [hcg]
    have hl0 : 0 < l.length := List.length_pos_iff.mpr hne
    apply List.ext_getElem
    · rw [List.length_append, List.length_map, hlen,
        List.length_singleton, List.length_ofFn]
      omega
    · intro i h1 h2
      rw [List.length_ofFn] at h2
      rw [List.getElem_ofFn]
      by_cases hi : i < l.length - 1
      · -- adjacent gap `l[i+1] - l[i]`
        rw [List.getElem_append,
          dif_pos (by rw [List.length_map, hlen]; exact hi)]
        rw [List.getElem_map, List.getElem_zip,
          List.getElem_dropLast
            (by rw [List.length_dropLast]; omega : i < l.dropLast.length),
          List.getElem_tail
            (by rw [List.length_tail]; omega : i < l.tail.length)]
        have hle : l[i] ≤ l[i + 1] :=
          hs.getElem_le_getElem_of_le (by omega)
        rw [cyclicDiff_eq_sub_of_le hle]
        unfold gapAfter
        rw [dif_pos (by omega : i + 1 < l.length)]
        simp only [List.get_eq_getElem]
      · -- wrap gap `l[0] + π - l[l.length - 1]`
        have hi_eq : i = l.length - 1 := by omega
        subst hi_eq
        rw [List.getElem_append,
          dif_neg (by rw [List.length_map, hlen]; omega),
          List.getElem_singleton
            (by rw [List.length_map, hlen]; omega)]
        unfold gapAfter
        rw [dif_neg (by omega : ¬l.length - 1 + 1 < l.length)]
        simp only [List.get_eq_getElem]
        unfold wrapGap
        have hhead : l.head hne = l[0] := List.head_eq_getElem hne
        have hlast : l.getLast hne = l[l.length - 1] :=
          List.getLast_eq_getElem hne
        split_ifs with hall
        · -- all elements equal: `l[l.length - 1] = l[0]`
          have h0 : l[l.length - 1] = l[0] := by
            have hmem : l[l.length - 1] ∈ l := List.getElem_mem _
            rw [hall _ hmem, hhead]
          rw [h0]; ring
        · -- not all equal: `l[0] < l[l.length - 1]`, so
          -- `cyclicDiff last head = π + head - last`
          push Not at hall
          obtain ⟨x, hx, hxne⟩ := hall
          obtain ⟨j, rfl⟩ := List.get_of_mem hx
          rw [List.get_eq_getElem] at hxne
          have h0le : l[0] ≤ l[j.1] :=
            hs.getElem_le_getElem_of_le (Nat.zero_le _)
          have hjle : l[j.1] ≤ l[l.length - 1] :=
            hs.getElem_le_getElem_of_le (by have := j.2; omega)
          rw [hhead] at hxne
          have hlt : l[0] < l[l.length - 1] :=
            lt_of_lt_of_le (lt_of_le_of_ne h0le (Ne.symm hxne)) hjle
          unfold cyclicDiff
          rw [hlast, hhead]
          rw [if_neg (ne_of_gt hlt),
            if_neg (not_lt_of_gt hlt)]
          ring

/-- The `exponents` entry of a sorted fan equals its `rowScore`. -/
theorem exponents_entry_eq_rowScore {lam : ℝ} {l : List ℝ}
    (hs : l.SortedLE) :
    ∑ i : Fin l.length, (⌊gapAfter l i / lam⌋₊ - 1) = rowScore lam l := by
  unfold rowScore gapScore
  rw [cycGaps_eq_ofFn_gapAfter hs, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply]

/-- Gaps of a sorted list in `[0, π)` are nonnegative (duplicates
contribute `0`). -/
theorem gapAfter_nonneg {ds : List ℝ} (hsort : ds.SortedLE)
    (hmem : ∀ x ∈ ds, x ∈ Set.Ico 0 Real.pi) (hne : ds ≠ [])
    (j : Fin ds.length) : 0 ≤ gapAfter ds j := by
  have hsmono := List.sortedLE_iff_monotone_get.mp hsort
  have hds0 : 0 < ds.length :=
    Nat.pos_of_ne_zero fun h => hne (List.length_eq_zero_iff.mp h)
  unfold gapAfter
  by_cases hj : j.1 + 1 < ds.length
  · rw [dif_pos hj]
    have hfin : j < ⟨j.1 + 1, hj⟩ := by show j.1 < j.1 + 1; omega
    have := hsmono (le_of_lt hfin)
    linarith
  · rw [dif_neg hj]
    have hpi := (hmem _ (getElem_mem j)).2
    have h0' := (hmem _ (getElem_mem ⟨0, hds0⟩)).1
    linarith [Real.pi_pos]

/-- The cyclic gaps of a sorted nonempty list sum to `π`. -/
theorem cycGaps_sum_eq_pi {l : List ℝ} (hs : l.SortedLE) (hne : l ≠ []) :
    (cycGaps l).sum = Real.pi := by
  rw [cycGaps_eq_ofFn_gapAfter hs, List.sum_ofFn]
  exact gapAfter_sum hne

/-- Gaps of a sorted `[0,π)`-list are nonnegative, in `cycGaps` form. -/
theorem cycGaps_nonneg {l : List ℝ} (hs : l.SortedLE)
    (hmem : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi) (hne : l ≠ []) :
    ∀ g ∈ cycGaps l, 0 ≤ g := by
  rw [cycGaps_eq_ofFn_gapAfter hs]
  intro g hg
  obtain ⟨u, hu⟩ := Set.mem_range.mp ((List.mem_ofFn' _ _).mp hg)
  rw [← hu]
  exact gapAfter_nonneg hs hmem hne u

/-- Cells of a sorted row expressed over `gapAfter`. -/
theorem rowCells_eq_sum_floor {lam : ℝ} {l : List ℝ} (hs : l.SortedLE) :
    rowCells lam l = ∑ i : Fin l.length, ⌊gapAfter l i / lam⌋₊ := by
  unfold rowCells
  rw [cycGaps_eq_ofFn_gapAfter hs, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply]

/-- Every sorted direction list uses at most `⌊π/λ⌋` λ-cells —
`Σ ⌊g/λ⌋ ≤ ⌊Σ g/λ⌋ = ⌊π/λ⌋`.  This is the cell bound needed to
instantiate the Kraft form of the potential. -/
theorem rowCells_le_floor_pi {lam : ℝ} (hlam : 0 < lam) {l : List ℝ}
    (hs : l.SortedLE) (hmem : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi)
    (hne : l ≠ []) :
    rowCells lam l ≤ ⌊Real.pi / lam⌋₊ := by
  rw [rowCells_eq_sum_floor hs]
  have hgsum := gapAfter_sum (ds := l) hne
  have hnn : ∀ j : Fin l.length, 0 ≤ gapAfter l j :=
    gapAfter_nonneg hs hmem hne
  apply (Nat.le_floor_iff (div_nonneg Real.pi_pos.le hlam.le)).mpr
  push_cast
  rw [← hgsum, Finset.sum_div]
  apply Finset.sum_le_sum
  intro j _
  exact Nat.floor_le (div_nonneg (hnn j) hlam.le)

/-- Geometric direction rows satisfy the cell bound. -/
theorem rowCells_directionRow_le {s : ℕ} (c : Fin s → Plane₂)
    {lam : ℝ} (hlam : 0 < lam) (i : Fin s) (hs2 : 2 ≤ s) :
    rowCells lam (directionRow o e c i) ≤ ⌊Real.pi / lam⌋₊ := by
  apply rowCells_le_floor_pi hlam (directionRow_sorted o e c i)
    (fun x hx => directionRow_mem_Ico o e c hx)
  exact List.length_pos_iff.mp (by
    rw [directionRow_length o e c i]; omega)

/-- With `⌊π/λ⌋ = n`, each geometric row's cell count is `≤ n`, so
`k_i = n − c_i` with `c_i = rowDefect` and
`potential = 2^n · Σ (1/2)^{c_i}` by `potential_eq_two_pow_mul_kraft`. -/
theorem rowCells_directionRow_le_of_floor_eq {s n : ℕ} (c : Fin s → Plane₂)
    {lam : ℝ} (hlam : 0 < lam) (i : Fin s) (hs2 : 2 ≤ s)
    (hn : ⌊Real.pi / lam⌋₊ = n) :
    rowCells lam (directionRow o e c i) ≤ n := by
  rw [← hn]; exact rowCells_directionRow_le o e c hlam i hs2


/-! ### K2 — the saturation-geometry bridge

`rowDefect = 1` gives a dominant gap `G ≥ n·λ` (K1, `rowDefect_eq_one`).
Every forward arc `a → b` between row elements either misses `G` — so
has length `≤ π − G ≤ π − n·λ = δλ` — or contains it — so has length
`≥ G ≥ n·λ > π − λ`, which legality forbids.  Hence every angle at a
saturated center is `≤ δλ`, and two saturated centers force
`δ ≥ 1/2`. -/

/-- **Arc dichotomy.**  For a sorted direction list in `[0, π)` and a
gap `G ∈ cycGaps l`, the forward arc `a → b` between two elements
either misses `G` (then `≤ π − G`) or contains it (then `≥ G`). -/
theorem cyclicDiff_le_or_ge {l : List ℝ} (hs : l.SortedLE)
    (hmem : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi) (hne : l ≠ [])
    {G : ℝ} (hG : G ∈ cycGaps l)
    {a b : ℝ} (ha : a ∈ l) (hb : b ∈ l) :
    cyclicDiff a b ≤ Real.pi - G ∨ G ≤ cyclicDiff a b := by
  have hsmono := List.sortedLE_iff_monotone_get.mp hs
  have hm0 : 0 < l.length := List.length_pos_iff.mpr hne
  -- index of the big gap
  have hG' : G ∈ List.ofFn (fun i : Fin l.length => gapAfter l i) := by
    rw [← cycGaps_eq_ofFn_gapAfter hs]; exact hG
  obtain ⟨t, htG⟩ := Set.mem_range.mp ((List.mem_ofFn' _ _).mp hG')
  -- positions of a, b
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  -- extended value function: `f r = l[r]` for `r < l.length`, and
  -- `l[0] + π` at `l.length`
  set f : ℕ → ℝ := fun r =>
    if h : r < l.length then l[r]'h else l[0]'hm0 + Real.pi
    with hf
  have hgap : ∀ t : Fin l.length,
      gapAfter l t = f (t.1 + 1) - f t.1 := by
    intro t
    unfold gapAfter
    simp only [List.get_eq_getElem]
    by_cases h1 : t.1 + 1 < l.length
    · rw [dif_pos h1]
      simp only [hf]
      rw [dif_pos h1, dif_pos t.2]
    · rw [dif_neg h1]
      simp only [hf]
      rw [dif_neg h1, dif_pos t.2]
  have htGf : f (t.1 + 1) - f t.1 = G := by
    rw [← hgap t]; exact htG
  have hnn_term : ∀ r ∈ Finset.Ico 0 l.length, 0 ≤ f (r + 1) - f r := by
    intro r hr
    have hrm : r < l.length := (Finset.mem_Ico.mp hr).2
    rw [← hgap ⟨r, hrm⟩]
    exact gapAfter_nonneg hs hmem hne ⟨r, hrm⟩
  have hsum_Ico : ∀ i' j' : ℕ, i' ≤ j' → j' ≤ l.length →
      ∑ r ∈ Finset.Ico i' j', (f (r + 1) - f r) = f j' - f i' := by
    intro i' j' hij' hjm
    rw [Finset.sum_Ico_eq_sum_range]
    have hte := Finset.sum_range_sub (fun t => f (i' + t)) (j' - i')
    rw [Nat.add_sub_cancel' hij', Nat.add_zero] at hte
    rw [← hte]
    apply Finset.sum_congr rfl
    intro t _
    rw [Nat.add_assoc]
  have htot : ∑ r ∈ Finset.Ico 0 l.length, (f (r + 1) - f r) =
      Real.pi := by
    rw [hsum_Ico 0 l.length (Nat.zero_le _) le_rfl]
    simp only [hf]
    rw [dif_neg (lt_irrefl l.length), dif_pos hm0]
    ring
  have htin : t.1 ∈ Finset.Ico 0 l.length :=
    Finset.mem_Ico.mpr ⟨Nat.zero_le _, t.2⟩
  rcases lt_trichotomy (l[i]'hi) (l[j]'hj) with hab | hab | hab
  · -- `a < b`: forward arc is the contiguous range `Ico i j`.
    have hij : i < j := by
      by_contra h'
      push Not at h'
      have hle : l.get ⟨j, hj⟩ ≤ l.get ⟨i, hi⟩ := hsmono h'
      simp only [List.get_eq_getElem] at hle
      linarith
    have hcd : cyclicDiff (l[i]'hi) (l[j]'hj) = (l[j]'hj) - (l[i]'hi) := by
      unfold cyclicDiff
      rw [if_neg (ne_of_lt hab), if_pos hab]
    have hsum : ∑ r ∈ Finset.Ico i j, (f (r + 1) - f r) =
        (l[j]'hj) - (l[i]'hi) := by
      rw [hsum_Ico i j (le_of_lt hij) (le_of_lt hj)]
      simp only [hf]
      rw [dif_pos hj, dif_pos hi]
    by_cases ht : t.1 ∈ Finset.Ico i j
    · right
      have hle : f (t.1 + 1) - f t.1 ≤
          ∑ r ∈ Finset.Ico i j, (f (r + 1) - f r) :=
        Finset.single_le_sum (fun r hr => hnn_term r (Finset.mem_Ico.mpr
          ⟨Nat.zero_le _, lt_trans (Finset.mem_Ico.mp hr).2 hj⟩)) ht
      rw [hcd]
      linarith [htGf, hle, hsum]
    · left
      have hsub : Finset.Ico i j ⊆ Finset.Ico 0 l.length :=
        Finset.Ico_subset_Ico (Nat.zero_le i) (le_of_lt hj)
      have hle2 := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.insert_subset htin hsub)
        (fun x hx _ => hnn_term x hx)
      rw [Finset.sum_insert ht, htot] at hle2
      rw [hcd]
      linarith [htGf, hle2, hsum]
  · -- `a = b`: the arc is empty.
    left
    have hcyc : cyclicDiff (l[i]'hi) (l[j]'hj) = 0 := by
      unfold cyclicDiff; rw [if_pos hab]
    rw [hcyc]
    have hGle : G ≤ Real.pi := by
      rw [← cycGaps_sum_eq_pi hs hne]
      exact le_sum_of_mem_of_nonneg _ (cycGaps_nonneg hs hmem hne) hG
    linarith
  · -- `a > b`: forward arc wraps; its complement is `Ico j i`.
    have hji : j < i := by
      by_contra h'
      push Not at h'
      have hle : l.get ⟨i, hi⟩ ≤ l.get ⟨j, hj⟩ := hsmono h'
      simp only [List.get_eq_getElem] at hle
      linarith
    have hcd : cyclicDiff (l[i]'hi) (l[j]'hj) =
        Real.pi + (l[j]'hj) - (l[i]'hi) := by
      unfold cyclicDiff
      rw [if_neg (ne_of_gt hab), if_neg (not_lt_of_gt hab)]
    have hsum : ∑ r ∈ Finset.Ico j i, (f (r + 1) - f r) =
        (l[i]'hi) - (l[j]'hj) := by
      rw [hsum_Ico j i (le_of_lt hji) (le_of_lt hi)]
      simp only [hf]
      rw [dif_pos hi, dif_pos hj]
    by_cases ht : t.1 ∈ Finset.Ico j i
    · left
      have hle : f (t.1 + 1) - f t.1 ≤
          ∑ r ∈ Finset.Ico j i, (f (r + 1) - f r) :=
        Finset.single_le_sum (fun r hr => hnn_term r (Finset.mem_Ico.mpr
          ⟨Nat.zero_le _, lt_trans (Finset.mem_Ico.mp hr).2 hi⟩)) ht
      rw [hcd]
      linarith [htGf, hle, hsum]
    · right
      have hsub : Finset.Ico j i ⊆ Finset.Ico 0 l.length :=
        Finset.Ico_subset_Ico (Nat.zero_le j) (le_of_lt hi)
      have hle2 := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.insert_subset htin hsub)
        (fun x hx _ => hnn_term x hx)
      rw [Finset.sum_insert ht, htot] at hle2
      rw [hcd]
      linarith [htGf, hle2, hsum]

/-- **The saturated-angle bound.**  If row `i` is saturated
(`c_i = 1`), every angle `∠jik` at `i` is `≤ π − n·λ = δλ`. -/
theorem angle_le_pi_sub_of_saturation {s n : ℕ} (hn2 : 2 ≤ n)
    {lam : ℝ} (hlam : 0 < lam) (hn : ⌊Real.pi / lam⌋₊ = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (he : e ≠ 0)
    (hs2 : 2 ≤ s) {i j k : Fin s} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k)
    (hsat : rowDefect n lam (directionRow o e c i) = 1) :
    ∠ (c j) (c i) (c k) ≤ Real.pi - n * lam := by
  set l := directionRow o e c i
  have hsort : l.SortedLE := directionRow_sorted o e c i
  have hmem : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi :=
    fun x hx => directionRow_mem_Ico o e c hx
  have hlen : l.length = s - 1 := directionRow_length o e c i
  have hne : l ≠ [] :=
    List.ne_nil_of_length_pos (by rw [hlen]; omega)
  have hsum := cycGaps_sum_eq_pi hsort hne
  have hnn := cycGaps_nonneg hsort hmem hne
  have hcells : rowCells lam l ≤ n := by
    rw [← hn]
    exact rowCells_le_floor_pi hlam hsort hmem hne
  obtain ⟨G, hG, hGnl, _, _, _⟩ := rowDefect_eq_one hlam hn2 hcells
    hnn hsum hsat
  have hdj : dirRep o e c i j ∈ l :=
    (mem_directionRow o e c).mpr ⟨j, Ne.symm hij, rfl⟩
  have hdk : dirRep o e c i k ∈ l :=
    (mem_directionRow o e c).mpr ⟨k, Ne.symm hik, rfl⟩
  have hdich := cyclicDiff_le_or_ge hsort hmem hne hG hdj hdk
  have hcji : c j ≠ c i := fun e' => hij (hleg.inj e'.symm)
  have hcki : c k ≠ c i := fun e' => hik (hleg.inj e'.symm)
  have hcd := cyclicDiff_dirRep o e c he hcji hcki
  have hA := linRep_oangle_eq_angle_or_pi_sub (o := o) hcji hcki
  have hAub : ∠ (c j) (c i) (c k) ≤ Real.pi - lam :=
    hleg.triAngle j i k (Ne.symm hij) hik hjk
  have hpi : Real.pi < (n + 1) * lam := by
    have h := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn] at h
    rw [div_lt_iff₀ hlam] at h
    push_cast at h
    linarith
  rcases hA with hA | hA
  all_goals rcases hdich with hlow | hhigh
  all_goals rw [← hcd] at hA
  all_goals linarith

/-- **The `δ = 1/2` phase transition.**  Two saturated centers are
impossible when `δ < 1/2` (i.e. `π < (n + 1/2)·λ`): the two angle
bounds give `λ ≤ ∠jik + ∠ijk ≤ 2δλ < λ`, contradicting
`facing_lower`. -/
theorem not_two_saturated_of_delta_lt_half {s n : ℕ} (hn2 : 2 ≤ n)
    {lam : ℝ} (hlam : 0 < lam) (hn : ⌊Real.pi / lam⌋₊ = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (he : e ≠ 0)
    (hs3 : 3 ≤ s) {i j : Fin s} (hij : i ≠ j)
    (hsi : rowDefect n lam (directionRow o e c i) = 1)
    (hsj : rowDefect n lam (directionRow o e c j) = 1)
    (hdelta : Real.pi < ((n : ℝ) + 1/2) * lam) : False := by
  have hs2 : 2 ≤ s := by omega
  obtain ⟨k, hk⟩ : ∃ k : Fin s, k ∉ ({i, j} : Finset (Fin s)) := by
    by_contra hcon
    push Not at hcon
    have hsub : Finset.univ ⊆ {i, j} := fun x _ => hcon x
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    have h2 : ({i, j} : Finset (Fin s)).card ≤ 2 := by
      calc ({i, j} : Finset (Fin s)).card
          ≤ ({j} : Finset (Fin s)).card + 1 := Finset.card_insert_le _ _
        _ = 2 := by rw [Finset.card_singleton]
    omega
  rw [Finset.mem_insert, Finset.mem_singleton] at hk
  push Not at hk
  obtain ⟨hki, hkj⟩ := hk
  have h1 := angle_le_pi_sub_of_saturation o e hn2 hlam hn hleg he hs2
    hij (Ne.symm hki) (Ne.symm hkj) hsi
  have h2 := angle_le_pi_sub_of_saturation o e hn2 hlam hn hleg he hs2
    (Ne.symm hij) (Ne.symm hkj) (Ne.symm hki) hsj
  have h3 := hleg.facing_lower hij (Ne.symm hkj) (Ne.symm hki)
  linarith

/-- **Three saturated centers are impossible for `n ≥ 2`.**  All three
angles of the triangle `ijk` are then `≤ π − nλ`, so
`π ≤ 3(π − nλ)`, i.e. `3nλ ≤ 2π < 2(n+1)λ`, forcing `n < 2`.
Together with `not_two_saturated_of_delta_lt_half` this pins the
saturated-row count to `{0, 1, 2}`. -/
theorem not_three_saturated {s n : ℕ} (hn2 : 2 ≤ n)
    {lam : ℝ} (hlam : 0 < lam) (hn : ⌊Real.pi / lam⌋₊ = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (he : e ≠ 0)
    {i j k : Fin s} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hsi : rowDefect n lam (directionRow o e c i) = 1)
    (hsj : rowDefect n lam (directionRow o e c j) = 1)
    (hsk : rowDefect n lam (directionRow o e c k) = 1) : False := by
  have hs2 : 2 ≤ s := by
    have hcard := Finset.card_le_card
      (Finset.subset_univ ({i, j, k} : Finset (Fin s)))
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    have h3 : ({i, j, k} : Finset (Fin s)).card = 3 := by
      rw [Finset.card_insert_of_notMem
        (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hij, hik⟩),
        Finset.card_pair hjk]
    omega
  have hcij : c i ≠ c j := fun e' => hij (hleg.inj e')
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₃ := c k) hcij
  have h1 := angle_le_pi_sub_of_saturation o e hn2 hlam hn hleg he hs2
    hij hik hjk hsi
  have h2 := angle_le_pi_sub_of_saturation o e hn2 hlam hn hleg he hs2
    hjk (Ne.symm hij) (Ne.symm hik) hsj
  have h3 := angle_le_pi_sub_of_saturation o e hn2 hlam hn hleg he hs2
    (Ne.symm hik) (Ne.symm hjk) hij hsk
  have hpi : Real.pi < ((n : ℝ) + 1) * lam := by
    have h := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn] at h
    rw [div_lt_iff₀ hlam] at h
    push_cast at h
    linarith
  have hnl : (n : ℝ) * lam < 2 * lam := by linarith
  have : (n : ℝ) < 2 := lt_of_mul_lt_mul_right hnl hlam.le
  have : n < 2 := by exact_mod_cast this
  omega

/-- **Kraft form of the cap.**  For geometric direction rows with
`⌊π/λ⌋ = n`, the Sendov cap `potential ≤ 2^n (+2^{n−2})` is exactly
the Kraft inequality `Σᵢ (1/2)^{cᵢ} ≤ 1 (+1/4)` over the defects
`cᵢ = rowDefect`.  The geometric content of `CertExists` is therefore
a prefix-packing bound on the defect multiset. -/
theorem potential_le_sendovCap_iff_kraft {s n : ℕ} (hn2 : 2 ≤ n)
    (big : Bool) {lam : ℝ} (hlam : 0 < lam)
    (hn : ⌊Real.pi / lam⌋₊ = n) (c : Fin s → Plane₂) (hs2 : 2 ≤ s) :
    potential lam (directionRows o e c) ≤ sendovCap n big ↔
      ∑ i : Fin s, (1/2 : ℚ) ^ rowDefect n lam (directionRows o e c i) ≤
        1 + (if big then (1/4 : ℚ) else 0) := by
  have hcells : ∀ i, rowCells lam (directionRows o e c i) ≤ n :=
    fun i => rowCells_directionRow_le_of_floor_eq o e c hlam i hs2 hn
  have h := potential_eq_two_pow_mul_kraft hlam hcells
  have hcap : (sendovCap n big : ℚ) =
      2 ^ n * (1 + (if big then (1/4 : ℚ) else 0)) := by
    rcases big with _ | _
    · simp [sendovCap]
    · have h2 : (2 : ℚ) ^ n = 2 ^ (n - 2) * 4 := by
        have he : (2 : ℚ) ^ n = 2 ^ (n - 2) * 2 ^ 2 := by
          rw [← pow_add]; congr 1; exact (Nat.sub_add_cancel hn2).symm
        rw [he]; norm_num
      simp only [sendovCap, ite_true]
      push_cast
      rw [h2]; ring
  rw [← Nat.cast_le (α := ℚ), h, hcap]
  have hpos : (0 : ℚ) < 2 ^ n := by positivity
  constructor
  · intro h'
    exact le_of_mul_le_mul_left h' hpos
  · intro h'
    exact mul_le_mul_of_nonneg_left h' hpos.le

/-! ### K3 — the Kraft-packing crux, split into four cases

The remaining mathematical content is the prefix-packing bound on the
defect multiset `d i = rowDefect`.  By K2 (`not_two_saturated_of_delta_lt_half`)
and `not_three_saturated`, the number of saturated rows (`d i = 1`) is
`0` or `1` in the low regime (`π < (n + 1/2)·λ`) and `0`, `1`, or `2` in
the high regime.  The `KraftPacking` bundle records the four mutually
exclusive case bounds — each is an open theorem — and
`kraft_packing_of_legality` assembles them into the Sendov Kraft bound
`K ≤ 1 + ¼[δ ≥ 1/2]` with no further mathematical input. -/

/-- **The K3 hypothesis bundle** over an abstract defect function
`d : Fin s → ℕ`.  Each field is one of the open case theorems:

* `no_sat_low` — **K3-C (low)**: `δ < 1/2`, `∀ i, d i ≥ 2` implies
  `K ≤ 1`;
* `no_sat_high` — **K3-C (high)**: `∀ i, d i ≥ 2` implies `K ≤ 5/4`.
  The unconditional `K ≤ 1` is FALSE: all `c = 2` at `s = 5`
  (`d = 1` everywhere, `W = 5/2`) is LP-realizable at `δ = 1/2`,
  so `K = 5/4` is the tight no-saturated bound in the high regime;
* `one_sat_low` — **K3-B**: `δ < 1/2`, `d v = 1` implies the rest packs
  into `1/2`;
* `one_sat_high` — **K3-A1**: `d v = 1` implies the rest packs into
  `3/4`;
* `two_sat` — **K3-A2**: `d u = d v = 1` implies the rest packs into
  `1/4`. -/
structure KraftPacking {s n : ℕ} {lam : ℝ} (d : Fin s → ℕ) : Prop where
  no_sat_low : Real.pi < ((n : ℝ) + 1 / 2) * lam → (∀ i, 2 ≤ d i) →
    ∑ i, (1/2 : ℚ) ^ d i ≤ 1
  no_sat_high : (∀ i, 2 ≤ d i) →
    ∑ i, (1/2 : ℚ) ^ d i ≤ 5 / 4
  one_sat_low : Real.pi < ((n : ℝ) + 1 / 2) * lam → ∀ v, d v = 1 →
    ∑ i ∈ univ.erase v, (1/2 : ℚ) ^ d i ≤ 1 / 2
  one_sat_high : ∀ v, d v = 1 →
    ∑ i ∈ univ.erase v, (1/2 : ℚ) ^ d i ≤ 3 / 4
  two_sat : ∀ u v, u ≠ v → d u = 1 → d v = 1 →
    ∑ i ∈ (univ.erase u).erase v, (1/2 : ℚ) ^ d i ≤ 1 / 4

/-- **K3 assembly (proved glue).**  Given the four packing cases, the
defect multiset of any legal `s ≥ 3` configuration with `⌊π/λ⌋ = n ≥ 2`
satisfies `K ≤ 1 + ¼[δ ≥ 1/2]`.  Saturated rows number at most `1` in
the low regime (K2) and at most `2` for `n ≥ 2`
(`not_three_saturated`). -/
theorem kraft_packing_of_legality {s n : ℕ} (hn2 : 2 ≤ n) (big : Bool)
    {lam : ℝ} (hlam : 0 < lam) (hn : ⌊Real.pi / lam⌋₊ = n)
    (hbig : big = false → Real.pi / lam - (n : ℝ) < 1 / 2)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (he : e ≠ 0)
    (hs3 : 3 ≤ s)
    (P : KraftPacking (n := n) (lam := lam)
      fun i => rowDefect n lam (directionRows o e c i)) :
    ∑ i : Fin s, (1/2 : ℚ) ^ rowDefect n lam (directionRows o e c i) ≤
      1 + (if big then (1/4 : ℚ) else 0) := by
  classical
  have hcells : ∀ i : Fin s,
      rowCells lam (directionRows o e c i) ≤ n :=
    fun i => rowCells_directionRow_le_of_floor_eq o e c hlam i
      (by omega) hn
  have hd1 : ∀ i : Fin s,
      1 ≤ rowDefect n lam (directionRows o e c i) :=
    fun i => one_le_rowDefect lam hlam n _ (by omega) (hcells i)
  set satSet : Finset (Fin s) := univ.filter
    (fun i => rowDefect n lam (directionRows o e c i) = 1) with hsatSet
  have mem_satSet : ∀ i, i ∈ satSet ↔
      rowDefect n lam (directionRows o e c i) = 1 := by
    intro i
    rw [hsatSet, Finset.mem_filter]
    exact and_iff_right (Finset.mem_univ i)
  cases big with
  | false =>
    rw [if_neg (by decide), add_zero]
    have hlow : Real.pi < ((n : ℝ) + 1 / 2) * lam := by
      have h := hbig rfl
      have h' : Real.pi / lam < (n : ℝ) + 1 / 2 := by linarith
      exact (div_lt_iff₀ hlam).mp h'
    rcases Nat.lt_or_ge satSet.card 1 with h0 | h1
    · rw [Nat.lt_one_iff] at h0
      have hge : ∀ i, 2 ≤ rowDefect n lam (directionRows o e c i) := by
        intro i
        have hi1 := hd1 i
        have hi : i ∉ satSet := by
          rw [Finset.card_eq_zero.mp h0]; exact Finset.notMem_empty i
        rw [mem_satSet] at hi
        omega
      exact P.no_sat_low hlow hge
    · rcases Nat.lt_or_ge satSet.card 2 with hlt2 | h2
      · have hc1 : satSet.card = 1 := by omega
        obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc1
        have hvu : v ∈ satSet := by
          rw [hv]; exact Finset.mem_singleton_self v
        have hdv := (mem_satSet v).mp hvu
        have hsplit := Finset.add_sum_erase univ
          (fun i => (1/2 : ℚ) ^ rowDefect n lam (directionRows o e c i))
          (Finset.mem_univ v)
        rw [hdv, pow_one] at hsplit
        have hrest := P.one_sat_low hlow v hdv
        linarith
      · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h2
        exact (not_two_saturated_of_delta_lt_half o e hn2 hlam hn hleg he
          hs3 huv ((mem_satSet u).mp hu) ((mem_satSet v).mp hv)
          hlow).elim
  | true =>
    rw [if_pos rfl]
    rcases Nat.lt_or_ge satSet.card 1 with h0 | h1
    · rw [Nat.lt_one_iff] at h0
      have hge : ∀ i, 2 ≤ rowDefect n lam (directionRows o e c i) := by
        intro i
        have hi1 := hd1 i
        have hi : i ∉ satSet := by
          rw [Finset.card_eq_zero.mp h0]; exact Finset.notMem_empty i
        rw [mem_satSet] at hi
        omega
      have hle := P.no_sat_high hge
      linarith
    · rcases Nat.lt_or_ge satSet.card 2 with hlt2 | h2
      · have hc1 : satSet.card = 1 := by omega
        obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc1
        have hvu : v ∈ satSet := by
          rw [hv]; exact Finset.mem_singleton_self v
        have hdv := (mem_satSet v).mp hvu
        have hsplit := Finset.add_sum_erase univ
          (fun i => (1/2 : ℚ) ^ rowDefect n lam (directionRows o e c i))
          (Finset.mem_univ v)
        rw [hdv, pow_one] at hsplit
        have hrest := P.one_sat_high v hdv
        linarith
      · rcases Nat.lt_or_ge satSet.card 3 with hlt3 | h3
        · have hc2 : satSet.card = 2 := by omega
          obtain ⟨u, v, huv, hsuv⟩ := Finset.card_eq_two.mp hc2
          have huu : u ∈ satSet := by rw [hsuv]; simp
          have hvv : v ∈ satSet := by rw [hsuv]; simp
          have hdu := (mem_satSet u).mp huu
          have hdv := (mem_satSet v).mp hvv
          have hmem : v ∈ univ.erase u :=
            Finset.mem_erase.mpr ⟨Ne.symm huv, Finset.mem_univ v⟩
          have hsplit : ∑ i : Fin s,
              (1/2 : ℚ) ^ rowDefect n lam (directionRows o e c i) =
              (1/2 : ℚ) ^ rowDefect n lam (directionRows o e c u) +
                (1/2 : ℚ) ^ rowDefect n lam (directionRows o e c v) +
                ∑ i ∈ (univ.erase u).erase v,
                  (1/2 : ℚ) ^ rowDefect n lam (directionRows o e c i) := by
            rw [← Finset.add_sum_erase univ _
              (Finset.mem_univ u),
              ← Finset.add_sum_erase (univ.erase u) _ hmem]
            ring
          rw [hsplit, hdu, hdv, pow_one]
          have hrest := P.two_sat u v huv hdu hdv
          linarith
        · obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq h3
          obtain ⟨i, j, k, hij, hik, hjk, ht⟩ := Finset.card_eq_three.mp htc
          have hi : i ∈ satSet := hts (by rw [ht]; simp)
          have hj : j ∈ satSet := hts (by rw [ht]; simp)
          have hk : k ∈ satSet := hts (by rw [ht]; simp)
          exact (not_three_saturated o e hn2 hlam hn hleg he
            hij hik hjk ((mem_satSet i).mp hi) ((mem_satSet j).mp hj)
            ((mem_satSet k).mp hk)).elim

/-- **K4 — Kraft packing closes the Sendov cap.**  Composed with
`potential_le_sendovCap_iff_kraft`, the packing bundle gives
`potential ≤ sendovCap` directly — the `CertExists` route is no
longer needed for the main proof. -/
theorem potential_le_sendovCap_of_packing {s n : ℕ} (hn2 : 2 ≤ n)
    (big : Bool) {lam : ℝ} (hlam : 0 < lam) (hn : ⌊Real.pi / lam⌋₊ = n)
    (hbig : big = false → Real.pi / lam - (n : ℝ) < 1 / 2)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (he : e ≠ 0)
    (hs3 : 3 ≤ s)
    (P : KraftPacking (n := n) (lam := lam)
      fun i => rowDefect n lam (directionRows o e c i)) :
    potential lam (directionRows o e c) ≤ sendovCap n big := by
  rw [potential_le_sendovCap_iff_kraft o e hn2 big hlam hn c (by omega)]
  exact kraft_packing_of_legality o e hn2 big hlam hn hbig hleg he hs3 P

/-- The deduplicated `directionRow` is exactly `circleDirs`: both are
the sorted list of distinct projective directions to the other
centers. -/
theorem circleDirs_eq_dedup_directionRow (V : GCfg)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (hfN : V.forest.Nodup) (i : Fin V.forest.length) :
    circleDirs V o e (V.forest.get i) =
      (directionRow o e
        (fun j : Fin V.forest.length => (V.forest.get j).centerOf)
        i).dedup := by
  set c := fun j : Fin V.forest.length => (V.forest.get j).centerOf
    with hc
  refine List.Perm.eq_of_sortedLE (circleDirs_sorted V o e _)
    (((directionRow_sorted o e c i).pairwise.sublist
      (List.dedup_sublist _)).sortedLE) ?_
  rw [List.perm_iff_count]
  intro a
  rw [List.Nodup.count (circleDirs_nodup V o e _),
    List.Nodup.count (List.nodup_dedup _)]
  have hmem : a ∈ circleDirs V o e (V.forest.get i) ↔
      a ∈ (directionRow o e c i).dedup := by
    rw [List.mem_dedup, mem_circleDirs, mem_directionRow]
    constructor
    · rintro ⟨g, hg, hgn, rfl⟩
      obtain ⟨j, rfl⟩ := List.get_of_mem hg
      refine ⟨j, fun hji => hgn (by rw [hji]), rfl⟩
    · rintro ⟨j, hji, rfl⟩
      refine ⟨V.forest.get j, List.get_mem _ _, fun heq =>
        hji (List.nodup_iff_injective_get.mp hfN heq), rfl⟩
  by_cases ha : a ∈ circleDirs V o e (V.forest.get i)
  · rw [if_pos ha, if_pos (hmem.mp ha)]
  · rw [if_neg ha, if_neg (fun h => ha (hmem.mpr h))]

/-- The weighted exponent sum equals the potential of the geometric
row system — the last bridge between `StaircaseBound.tail` and the
deletion machinery. -/
theorem exponents_map_pow_sum (V : GCfg)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (lam : ℝ)
    (hfN : V.forest.Nodup) :
    ((exponents V o e lam).map (2 ^ ·)).sum =
      potential lam (directionRows o e
        (fun j : Fin V.forest.length => (V.forest.get j).centerOf)) := by
  have key : ∀ i : Fin V.forest.length,
      (∑ j : Fin (circleDirs V o e (V.forest.get i)).length,
          (⌊gapAfter (circleDirs V o e (V.forest.get i)) j / lam⌋₊ - 1))
        = rowScore lam (directionRow o e
            (fun j : Fin V.forest.length => (V.forest.get j).centerOf)
            i) := by
    intro i
    rw [exponents_entry_eq_rowScore (circleDirs_sorted V o e _),
      circleDirs_eq_dedup_directionRow V o e hfN i,
      rowScore_dedup lam (directionRow_sorted o e _ i)]
  rw [exponents, List.map_map]
  conv_lhs => rw [← List.ofFn_get V.forest]
  rw [List.map_ofFn, List.sum_ofFn]
  unfold potential exponentAt directionRows
  simp only [Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [key i]

/-- **The conditional staircase.**  `staircase_of_legality` modulo
`CertExists`: legality of the center system yields the staircase bound
on the exponent list.  The `top` field is unconditional; `tail` is
`potential ≤ cap` by `exponents_map_pow_sum` + `layerCake`, proved by
`potential_le_sendovCap` for `s ≥ 3` and directly for `s ≤ 2`.
Requires `2 ≤ n` — the `n = 1` cases (`N ≤ 6` in the final theorem)
are discharged separately. -/
theorem staircase_of_cert (V : GCfg)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (n : ℕ) (hn2 : 2 ≤ n)
    (big : Bool) (hlam : 0 < lam) (hlampi : lam < Real.pi)
    (hn : Nat.floor (Real.pi / lam) = n)
    (hbig : big = false → Real.pi / lam - n < 1 / 2)
    (hcert : CertExists o e n big lam)
    (hfN : V.forest.Nodup)
    (hlegal : Section4Legality
      (fun i : Fin V.forest.length => (V.forest.get i).centerOf) lam) :
    StaircaseBound n (exponents V o e lam) big := by
  have hn1 : 1 ≤ n := by
    have h1 : 1 ≤ Nat.floor (Real.pi / lam) := by
      rw [Nat.one_le_floor_iff, one_le_div_iff]
      exact Or.inl ⟨hlam, le_of_lt hlampi⟩
    omega
  have htop : ∀ k ∈ exponents V o e lam, k < n := by
    intro k hk
    rw [exponents, List.mem_map] at hk
    obtain ⟨ci, hci, rfl⟩ := hk
    have hle := exponent_le_floor (ds := circleDirs V o e ci)
      (circleDirs_sorted V o e ci) (circleDirs_nodup V o e ci)
      (fun x hx => circleDirs_mem_Ico V o e hx)
      (circleDirs_ne_nil V o e hfN hci) hlam
    rw [hn] at hle
    omega
  refine ⟨htop, ?_⟩
  rw [← layerCake htop, exponents_map_pow_sum V o e lam hfN]
  rcases Nat.lt_or_ge V.forest.length 3 with hs | hs
  · -- `s ≤ 2`: each exponent is `< n`, so `F ≤ s · 2^{n-1} ≤ 2^n`.
    have hbound : ∀ i : Fin V.forest.length,
        2 ^ exponentAt lam (directionRows o e
          (fun j : Fin V.forest.length => (V.forest.get j).centerOf)) i
          ≤ 2 ^ (n - 1) := by
      intro i
      have hmem : (∑ j : Fin (circleDirs V o e (V.forest.get i)).length,
          (⌊gapAfter (circleDirs V o e (V.forest.get i)) j / lam⌋₊ - 1))
          ∈ exponents V o e lam := by
        rw [exponents, List.mem_map]
        exact ⟨V.forest.get i, List.get_mem _ _, rfl⟩
      have hlt := htop _ hmem
      have hrow : exponentAt lam (directionRows o e
          (fun j : Fin V.forest.length => (V.forest.get j).centerOf)) i
          = (∑ j : Fin (circleDirs V o e (V.forest.get i)).length,
            (⌊gapAfter (circleDirs V o e (V.forest.get i)) j / lam⌋₊
              - 1)) := by
        unfold exponentAt directionRows
        rw [exponents_entry_eq_rowScore (circleDirs_sorted V o e _),
          circleDirs_eq_dedup_directionRow V o e hfN i,
          rowScore_dedup lam (directionRow_sorted o e _ i)]
      rw [hrow]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    unfold potential
    calc ∑ i : Fin V.forest.length,
          2 ^ exponentAt lam (directionRows o e
            (fun j : Fin V.forest.length => (V.forest.get j).centerOf)) i
        ≤ ∑ _i : Fin V.forest.length, 2 ^ (n - 1) :=
          Finset.sum_le_sum fun i _ => hbound i
      _ = V.forest.length * 2 ^ (n - 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
      _ ≤ 2 * 2 ^ (n - 1) := by
          exact Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ n := by
          have hn' : n = (n - 1) + 1 := by omega
          conv_rhs => rw [hn', pow_succ]
          ring
      _ ≤ 2 ^ n + (if big = true then 2 ^ (n - 2) else 0) :=
          Nat.le_add_right _ _
  · -- `s ≥ 3`: the induction.
    have hcap : potential lam (directionRows o e
        (fun j : Fin V.forest.length => (V.forest.get j).centerOf))
        ≤ sendovCap n big :=
      potential_le_sendovCap o e hn2 big hlam hlampi hn hbig hcert he hs
        hlegal
    rw [sendovCap] at hcap
    exact hcap

end Jsp404
