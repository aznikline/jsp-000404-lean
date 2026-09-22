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
