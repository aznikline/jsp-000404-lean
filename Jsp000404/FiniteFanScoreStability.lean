import Jsp000404.ActualScorePreservingExpansion
import Jsp000404.Induction
import Mathlib.Data.Fin.Tuple.Sort

/-! Exact finite fan score stability under a strictly smaller angle scale.
Every actual sorting permutation is covered by a finite intersection of
continuous fixed-permutation gap events. Duplicate values and the singleton
full-circle wrap are retained. No global cut-coordinate continuity, fixed
sorting permutation, or caller-supplied floor-stability event is assumed.
-/

open Filter Topology
open scoped BigOperators

namespace Jsp404.FiniteFanScoreStability

/-- The value tuple sorted by the internally chosen finite label permutation. -/
noncomputable def sortedTuple {n : ℕ} (a : Fin n → ℝ) : Fin n → ℝ :=
  a ∘ Tuple.sort a

/-- A multiplicity-preserving sorted fan. -/
noncomputable def sortedFan {n : ℕ} (a : Fin n → ℝ) : List ℝ :=
  List.ofFn (sortedTuple a)

/-- The genuine gap-after formula reindexed onto the fixed label count. -/
noncomputable def indexedGap {n : ℕ} (a : Fin n → ℝ) (i : Fin n) : ℝ :=
  gapAfter (List.ofFn a) (Fin.cast (by simp) i)

theorem sortedFan_sorted {n : ℕ} (a : Fin n → ℝ) : (sortedFan a).SortedLE := by
  exact List.sortedLE_ofFn_iff.mpr (Tuple.monotone_sort a)

/-- Continuity plus the proved strict margins gives a single floor event.
The zero-floor case only needs its strict upper margin. -/
private theorem eventually_floor_of_margins {f : ℝ → ℝ} {g lam lam' : ℝ}
    (hf : ContinuousAt f 0) (hzero : f 0 = g) (hlam' : 0 < lam')
    (hupper : g < ((⌊g / lam⌋₊ : ℝ) + 1) * lam')
    (hlower : 0 < ⌊g / lam⌋₊ → (⌊g / lam⌋₊ : ℝ) * lam' < g) :
    ∀ᶠ eps in 𝓝 (0 : ℝ), ⌊f eps / lam'⌋₊ = ⌊g / lam⌋₊ := by
  have hupper0 : f 0 < ((⌊g / lam⌋₊ : ℝ) + 1) * lam' := by
    rw [hzero]
    exact hupper
  have hu := hf.eventually_lt continuousAt_const hupper0
  by_cases hq : 0 < ⌊g / lam⌋₊
  · have hlower0 : (⌊g / lam⌋₊ : ℝ) * lam' < f 0 := by
      rw [hzero]
      exact hlower hq
    have hl := continuousAt_const.eventually_lt hf hlower0
    filter_upwards [hu, hl] with eps hup hlo
    apply (Nat.floor_eq_iff' (ne_of_gt hq)).mpr
    exact ⟨(le_div_iff₀ hlam').mpr hlo.le, (div_lt_iff₀ hlam').mpr hup⟩
  · have hz : ⌊g / lam⌋₊ = 0 := Nat.eq_zero_of_not_pos hq
    filter_upwards [hu] with eps hup
    rw [hz]
    apply Nat.floor_eq_zero.mpr
    apply (div_lt_one hlam').mpr
    simpa only [hz, Nat.cast_zero, zero_add, one_mul] using hup

/-- Every limiting gap of a nonempty cut-safe sorted tuple is nonnegative.
When all values coincide, the one wrap gap remains exactly pi. -/
theorem indexedGap_sorted_nonneg {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (hrange : ∀ i, a i ∈ Set.Ioo 0 Real.pi) (i : Fin n) :
    0 ≤ indexedGap (sortedTuple a) i := by
  apply gapAfter_nonneg (sortedFan_sorted a)
  · intro x hx
    rcases List.mem_ofFn.mp hx with ⟨j, rfl⟩
    exact ⟨(hrange (Tuple.sort a j)).1.le, (hrange (Tuple.sort a j)).2⟩
  · intro h
    have hlen := congrArg List.length h
    simp only [sortedFan, List.length_ofFn, List.length_nil] at hlen
    omega

/-- The complete analytic bridge: internally sort every actual finite fan,
and preserve every actual gap floor at one smaller parameter. A sorting
permutation may change arbitrarily inside a collided limiting class. -/
theorem exists_sorted_gap_floor_stability {n : ℕ} (hn : 0 < n)
    (A : ℝ → Fin n → ℝ)
    (hcont : ∀ i, ContinuousAt (fun eps => A eps i) 0)
    (hrange : ∀ i, A 0 i ∈ Set.Ioo 0 Real.pi)
    {lam tau : ℝ} (hlam : 0 < lam) (htau0 : 0 < tau) (htau : tau < lam) :
    ∃ lam' : ℝ, tau < lam' ∧ lam' < lam ∧
      ∀ᶠ eps in 𝓝 (0 : ℝ), ∀ i : Fin n,
        ⌊indexedGap (sortedTuple (A eps)) i / lam'⌋₊ =
          ⌊indexedGap (sortedTuple (A 0)) i / lam⌋₊ := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let gs : Fin (m + 1) → ℝ := indexedGap (sortedTuple (A 0))
  have hgs : ∀ i, 0 ≤ gs i :=
    indexedGap_sorted_nonneg (by omega) (A 0) hrange
  obtain ⟨lam', htau', hsmall, hm⟩ :=
    GapSplitFloorStability.exists_floor_stable_scale_with_margins
      (List.ofFn gs) hlam
      (fun g hg => by
        rcases List.mem_ofFn.mp hg with ⟨i, rfl⟩
        exact hgs i) htau0 htau
  have hlam' : 0 < lam' := htau0.trans htau'
  have hfixed : ∀ᶠ eps in 𝓝 (0 : ℝ), ∀ perm : Equiv.Perm (Fin (m + 1)),
      (List.ofFn (fun j => A 0 (perm j))).SortedLE → ∀ i,
        ⌊indexedGap (fun j => A eps (perm j)) i / lam'⌋₊ = ⌊gs i / lam⌋₊ := by
    apply eventually_all.mpr
    intro perm
    by_cases hs0 : (List.ofFn (fun j => A 0 (perm j))).SortedLE
    · have heq : (fun j => A 0 (perm j)) = sortedTuple (A 0) :=
        Tuple.comp_sort_eq_comp_iff_monotone.mpr (List.sortedLE_ofFn_iff.mp hs0)
      have hper : ∀ᶠ eps in 𝓝 (0 : ℝ), ∀ i,
          ⌊indexedGap (fun j => A eps (perm j)) i / lam'⌋₊ = ⌊gs i / lam⌋₊ := by
        apply eventually_all.mpr
        intro i
        have hc : ContinuousAt (fun eps => indexedGap (fun j => A eps (perm j)) i) 0 :=
          ActualScorePreservingExpansion.continuousAt_gapAfter_ofFn
            (fun j eps => A eps (perm j)) (fun j => hcont (perm j)) i
        have hz : indexedGap (fun j => A 0 (perm j)) i = gs i := by
          rw [heq]
        have hmargin := hm (gs i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
        exact eventually_floor_of_margins hc hz hlam' hmargin.2.1 hmargin.2.2
      exact hper.mono fun _ h _ => h
    · exact Eventually.of_forall fun _ h => False.elim (hs0 h)
  have hsortLimit := ActualScorePreservingExpansion.eventually_sorted_limit_of_sorted
    (fun i eps => A eps i) hcont
  refine ⟨lam', htau', hsmall, ?_⟩
  filter_upwards [hfixed, hsortLimit] with eps hfix hlim
  have hactual : (List.ofFn (sortedTuple (A eps))).SortedLE := sortedFan_sorted (A eps)
  have hlimit : (List.ofFn (fun j => A 0 (Tuple.sort (A eps) j))).SortedLE :=
    hlim (Tuple.sort (A eps)) hactual
  exact hfix (Tuple.sort (A eps)) hlimit

/-- The sorted fan's actual cyclic score is its fixed-cardinality gap sum.
The existing cyclic-gap bridge includes duplicates and singleton wrap. -/
theorem rowScore_sortedFan_eq_sum {n : ℕ} (a : Fin n → ℝ) (lam : ℝ) :
    rowScore lam (sortedFan a) =
      ∑ i : Fin n, (⌊indexedGap (sortedTuple a) i / lam⌋₊ - 1) := by
  rw [← exponents_entry_eq_rowScore (sortedFan_sorted a)]
  exact ((finCongr (List.length_ofFn (f := sortedTuple a)).symm).sum_comp
    (fun j => ⌊gapAfter (List.ofFn (sortedTuple a)) j / lam⌋₊ - 1)).symm

/-- Every nearby internally sorted fan has exactly the old cyclic row
score, at one strictly smaller parameter. The family is nonempty, including
cardinality one; no distinctness of limiting direction values is required. -/
theorem exists_sorted_score_stability {n : ℕ} (hn : 0 < n)
    (A : ℝ → Fin n → ℝ)
    (hcont : ∀ i, ContinuousAt (fun eps => A eps i) 0)
    (hrange : ∀ i, A 0 i ∈ Set.Ioo 0 Real.pi)
    {lam tau : ℝ} (hlam : 0 < lam) (htau0 : 0 < tau) (htau : tau < lam) :
    ∃ lam' : ℝ, tau < lam' ∧ lam' < lam ∧
      ∀ᶠ eps in 𝓝 (0 : ℝ),
        rowScore lam' (sortedFan (A eps)) = rowScore lam (sortedFan (A 0)) := by
  obtain ⟨lam', htau', hsmall, hevent⟩ :=
    exists_sorted_gap_floor_stability hn A hcont hrange hlam htau0 htau
  refine ⟨lam', htau', hsmall, hevent.mono ?_⟩
  intro eps hfloor
  rw [rowScore_sortedFan_eq_sum, rowScore_sortedFan_eq_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hfloor i]

/-- Reindex any finite label type internally; all multiplicities survive. -/
noncomputable def finiteSortedFan {α : Type*} [Fintype α] (a : α → ℝ) : List ℝ :=
  sortedFan (a ∘ (Fintype.equivFin α).symm)

/-- Public finite-label interface for the complete analytic score bridge. -/
theorem exists_finite_sorted_score_stability {α : Type*} [Fintype α] [Nonempty α]
    (A : ℝ → α → ℝ)
    (hcont : ∀ i, ContinuousAt (fun eps => A eps i) 0)
    (hrange : ∀ i, A 0 i ∈ Set.Ioo 0 Real.pi)
    {lam tau : ℝ} (hlam : 0 < lam) (htau0 : 0 < tau) (htau : tau < lam) :
    ∃ lam' : ℝ, tau < lam' ∧ lam' < lam ∧
      ∀ᶠ eps in 𝓝 (0 : ℝ),
        rowScore lam' (finiteSortedFan (A eps)) =
          rowScore lam (finiteSortedFan (A 0)) := by
  exact exists_sorted_score_stability Fintype.card_pos
    (fun eps i => A eps ((Fintype.equivFin α).symm i))
    (fun i => hcont ((Fintype.equivFin α).symm i))
    (fun i => hrange ((Fintype.equivFin α).symm i)) hlam htau0 htau

#print axioms indexedGap_sorted_nonneg
#print axioms exists_sorted_gap_floor_stability
#print axioms rowScore_sortedFan_eq_sum
#print axioms exists_sorted_score_stability
#print axioms exists_finite_sorted_score_stability

end Jsp404.FiniteFanScoreStability
