import Jsp000404.Section4Legality
import Mathlib.Analysis.Convex.Extreme

/-!
# Deletion potential for Section 4

The potential `F(Q) = ∑ i, 2^{k_i}` where `k_i` is computed from the cyclic
gap system of directions at each circle.  Deleting a point `v` removes one
direction from every other circle's cyclic list, merging its two adjacent
gaps.  This file develops:

* `gapScore_merge`: merging two gaps raises the score by `g ≤ 2` (floor
  arithmetic only).
* `cycGaps`/`cyclicDiff`: cyclic gaps via `zipWith` over `rotate 1`, making
  rotation invariance a `zipWith`/`rotate` commutation.
* `rowScore_erase_head`: erasing the head of `x :: l` merges the cyclic gaps
  `(pred → x)` and `(x → succ)` into `(pred → succ)`.
* `rowScore_eraseIdx`: the same at an arbitrary position.
* `sum_potential_erase`: the exact deletion identity
  `∑ v, F(Q-v) = ∑ i, 2^{k_i} ∑_{v≠i} 2^{g_{iv}}`.
* `removable_iff`: `F(Q) ≤ F(Q-v) ↔ 2^{k_v} ≤ ∑_{i≠v} 2^{k_i}(2^{g_{iv}}-1)`.
* the frozen crux `exists_removable_vertex`.
-/

namespace Jsp404

/-! ### 1. Gap score and merge arithmetic -/

/-- Score of a single angular gap `x` at scale `lam`: `(⌊x/λ⌋₊ - 1)`; natural
subtraction supplies the positive part. -/
noncomputable def gapScore (lam x : ℝ) : ℕ := ⌊x / lam⌋₊ - 1

/-- Merging two adjacent gaps `x, y` into `x + y` raises the score by `g ≤ 2`.
Pure floor arithmetic: `⌊a+b⌋₊ ∈ {⌊a⌋₊+⌊b⌋₊, ⌊a⌋₊+⌊b⌋₊+1}` followed by the
`(·-1)⁺` case split. -/
theorem gapScore_merge {lam x y : ℝ} (hlam : 0 < lam) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∃ g ≤ 2, gapScore lam (x + y) = gapScore lam x + gapScore lam y + g := by
  have hx' : 0 ≤ x / lam := div_nonneg hx hlam.le
  have hy' : 0 ≤ y / lam := div_nonneg hy hlam.le
  have hxy' : 0 ≤ (x + y) / lam := div_nonneg (add_nonneg hx hy) hlam.le
  have hdiv : (x + y) / lam = x / lam + y / lam := add_div x y lam
  have h1 : ⌊x / lam⌋₊ + ⌊y / lam⌋₊ ≤ ⌊(x + y) / lam⌋₊ := by
    rcases Nat.eq_zero_or_pos (⌊x / lam⌋₊ + ⌊y / lam⌋₊) with h | h
    · omega
    · rw [Nat.le_floor_iff' (Nat.ne_of_gt h), hdiv]
      push_cast
      exact add_le_add (Nat.floor_le hx') (Nat.floor_le hy')
  have h2 : ⌊(x + y) / lam⌋₊ ≤ ⌊x / lam⌋₊ + ⌊y / lam⌋₊ + 1 := by
    have h3 : ⌊(x + y) / lam⌋₊ < ⌊x / lam⌋₊ + ⌊y / lam⌋₊ + 2 := by
      rw [Nat.floor_lt hxy', hdiv]
      push_cast
      have hax := Nat.lt_floor_add_one (x / lam)
      have hay := Nat.lt_floor_add_one (y / lam)
      linarith
    omega
  refine ⟨⌊(x + y) / lam⌋₊ - 1 - (⌊x / lam⌋₊ - 1) - (⌊y / lam⌋₊ - 1), ?_, ?_⟩
  · omega
  · unfold gapScore; omega

/-! ### 2. Cyclic gaps -/

/-- Gap from direction `a` to the next direction `b` in the cyclic order on
`ℝ/π`: `b - a` when `a < b`, else the wrap-around `π + b - a`. -/
noncomputable def cyclicDiff (a b : ℝ) : ℝ := if a < b then b - a else Real.pi + b - a

/-- Cyclic gaps of a direction list: `l.zipWith cyclicDiff (l.rotate 1)`.  For
`l = [a₀,…,a_{m-1}]` this is `[a₁-a₀, …, a_{m-1}-a_{m-2}, π+a₀-a_{m-1}]`. -/
noncomputable def cycGaps (l : List ℝ) : List ℝ := l.zipWith cyclicDiff (l.rotate 1)

/-- Row score: sum of `gapScore` over the cyclic gaps. -/
noncomputable def rowScore (lam : ℝ) (l : List ℝ) : ℕ := ((cycGaps l).map (gapScore lam)).sum

theorem cyclicDiff_nonneg {a b : ℝ} (ha : a < Real.pi) (hb : 0 ≤ b) :
    0 ≤ cyclicDiff a b := by
  unfold cyclicDiff; split_ifs with h <;> linarith [Real.pi_pos]

/-- `zipWith` commutes with `rotate 1` (equal-length lists). -/
theorem zipWith_rotate_one {α β γ : Type*} (f : α → β → γ) :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length →
      (l₁.zipWith f l₂).rotate 1 = (l₁.rotate 1).zipWith f (l₂.rotate 1) := by
  intro l₁ l₂ h
  cases l₁ with
  | nil => cases l₂ <;> simp at h ⊢
  | cons a as =>
    cases l₂ with
    | nil => simp at h
    | cons b bs =>
      have h' : as.length = bs.length := by simpa using h
      have rot {c : α} {cs : List α} : (c :: cs).rotate 1 = cs ++ [c] := by
        rw [show (1 : ℕ) = 0 + 1 from rfl, List.rotate_cons_succ,
          List.rotate_zero]
      have rot' {c : β} {cs : List β} : (c :: cs).rotate 1 = cs ++ [c] := by
        rw [show (1 : ℕ) = 0 + 1 from rfl, List.rotate_cons_succ,
          List.rotate_zero]
      simp only [List.zipWith_cons_cons, rot, rot']
      rw [List.zipWith_append h']
      simp

/-- `zipWith` commutes with `rotate k`. -/
theorem zipWith_rotate {α β γ : Type*} (f : α → β → γ) (l₁ : List α) (l₂ : List β)
    (k : ℕ) (h : l₁.length = l₂.length) :
    (l₁.zipWith f l₂).rotate k = (l₁.rotate k).zipWith f (l₂.rotate k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hlen : (l₁.rotate k).length = (l₂.rotate k).length := by simp [h]
    rw [← List.rotate_rotate l₁ k 1, ← List.rotate_rotate l₂ k 1,
        ← List.rotate_rotate (l₁.zipWith f l₂) k 1, ih,
        zipWith_rotate_one _ _ _ hlen]

/-- Rotating a direction list rotates its cyclic gaps. -/
theorem cycGaps_rotate (l : List ℝ) (k : ℕ) :
    cycGaps (l.rotate k) = (cycGaps l).rotate k := by
  unfold cycGaps
  rw [List.rotate_rotate,
      zipWith_rotate _ _ _ _ (List.length_rotate l 1).symm,
      List.rotate_rotate, Nat.add_comm 1 k]

/-- `rowScore` is rotation invariant. -/
theorem rowScore_rotate (lam : ℝ) (l : List ℝ) (k : ℕ) :
    rowScore lam (l.rotate k) = rowScore lam l := by
  unfold rowScore
  rw [cycGaps_rotate]
  exact List.Perm.sum_eq ((List.rotate_perm _ _).map (gapScore lam))

/-! ### 3. Erasing one direction merges its two adjacent gaps -/

/-- Auxiliary split: `l.zipWith f (l.tail ++ [x])` peels off the last pair. -/
theorem zipWith_tail_append_singleton {α γ : Type*} (f : α → α → γ) :
    ∀ (l : List α) (hl : l ≠ []) (x : α),
      l.zipWith f (l.tail ++ [x]) =
        l.dropLast.zipWith f l.tail ++ [f (l.getLast hl) x] := by
  intro l hl x
  induction l with
  | nil => exact absurd rfl hl
  | cons a rest ih =>
    cases rest with
    | nil => simp
    | cons b rest' =>
      have hne : b :: rest' ≠ [] := List.cons_ne_nil _ _
      have ih' := ih hne
      simp only [List.tail_cons] at ih'
      rw [List.tail_cons, List.cons_append, List.zipWith_cons_cons, ih',
        List.dropLast_cons_of_ne_nil hne, List.zipWith_cons_cons,
        List.getLast_cons hne]
      rfl

/-- `cycGaps` of a nonempty list peeled to its last (wrap-around) gap. -/
theorem cycGaps_eq_dropLast_zipWith_tail (l : List ℝ) (hl : l ≠ []) :
    cycGaps l = l.dropLast.zipWith cyclicDiff l.tail ++
      [cyclicDiff (l.getLast hl) (l.head hl)] := by
  have hrot : l.rotate 1 = l.tail ++ [l.head hl] := by
    conv_lhs => rw [show l = l.head hl :: l.tail from
      (List.cons_head_tail hl).symm]
    rw [show (1 : ℕ) = 0 + 1 from rfl, List.rotate_cons_succ, List.rotate_zero]
  unfold cycGaps
  rw [hrot]
  exact zipWith_tail_append_singleton _ _ hl _

/-- `cycGaps` of a cons, exposing the head gap and the wrap-around gap. -/
theorem cycGaps_cons (a : ℝ) (l : List ℝ) (hl : l ≠ []) :
    cycGaps (a :: l) = cyclicDiff a (l.head hl) ::
      (l.dropLast.zipWith cyclicDiff l.tail ++
        [cyclicDiff (l.getLast hl) a]) := by
  have hrot : (a :: l).rotate 1 = l ++ [a] := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, List.rotate_cons_succ, List.rotate_zero]
  unfold cycGaps
  rw [hrot]
  rw [show l ++ [a] = l.head hl :: (l.tail ++ [a]) from by
    rw [← List.cons_append, List.cons_head_tail hl]]
  rw [List.zipWith_cons_cons]
  congr 1
  exact zipWith_tail_append_singleton _ _ hl _

/-- Erasing the head element `x` of `x :: l` merges its two incident cyclic
gaps `pred → x` and `x → succ` into `pred → succ`; the row score rises by
`g ≤ 2`.  The hypothesis `hmerge` is the exact gap-level merge equation. -/
theorem rowScore_erase_head {lam : ℝ} (hlam : 0 < lam) {x : ℝ} {l : List ℝ}
    (hl : l ≠ []) (hx : 0 ≤ x) (hx2 : x < Real.pi)
    (hhead : 0 ≤ l.head hl) (hhead2 : l.head hl < Real.pi)
    (hlast : 0 ≤ l.getLast hl) (hlast2 : l.getLast hl < Real.pi)
    (hmerge : cyclicDiff (l.getLast hl) (l.head hl)
        = cyclicDiff (l.getLast hl) x + cyclicDiff x (l.head hl)) :
    ∃ g ≤ 2, rowScore lam l = rowScore lam (x :: l) + g := by
  obtain ⟨g, hg, hgs⟩ := gapScore_merge hlam
    (cyclicDiff_nonneg hlast2 hx) (cyclicDiff_nonneg hx2 hhead)
  refine ⟨g, hg, ?_⟩
  unfold rowScore
  rw [cycGaps_cons x l hl, cycGaps_eq_dropLast_zipWith_tail l hl]
  simp only [List.map_cons, List.map_append, List.map_singleton,
    List.sum_cons, List.sum_append, List.sum_singleton]
  rw [← hmerge] at hgs
  omega

/-- Monotonicity of `getElem` along a strictly sorted list, non-strict in the
index. -/
theorem getElem_mono_of_pairwise {l : List ℝ} (hs : l.Pairwise (· < ·))
    {i j : ℕ} (hij : i ≤ j) (hj : j < l.length) :
    l[i]'(by omega) ≤ l[j] := by
  rcases Nat.eq_or_lt_of_le hij with h | h
  · subst h; exact le_rfl
  · exact le_of_lt (List.pairwise_iff_getElem.mp hs i j (by omega) hj h)

/-- `eraseIdx` is `take k ++ drop (k+1)`. -/
theorem eraseIdx_eq_take_drop {α : Type*} (l : List α) (k : ℕ) :
    l.eraseIdx k = l.take k ++ l.drop (k + 1) := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    cases k with
    | zero => simp [List.eraseIdx]
    | succ k => simp [List.eraseIdx, ih]

/-- Erasing `l[k]` merges its two incident cyclic gaps; the row score rises by
`g ≤ 2`. -/
theorem rowScore_eraseIdx {lam : ℝ} (hlam : 0 < lam) {l : List ℝ}
    (hs : l.Pairwise (· < ·)) (hall : ∀ b ∈ l, 0 ≤ b ∧ b < Real.pi)
    {k : ℕ} (hk : k < l.length) (h2 : 2 ≤ l.length) :
    ∃ g ≤ 2, rowScore lam (l.eraseIdx k) = rowScore lam l + g := by
  classical
  set rest := l.drop (k + 1) ++ l.take k with hrest
  have hrot : l.rotate k = l[k] :: rest := by
    rw [hrest, List.rotate_eq_rotate',
      List.rotate'_eq_drop_append_take (Nat.le_of_lt hk),
      List.drop_eq_getElem_cons hk, List.cons_append]
  have hrest_len : rest.length = l.length - 1 := by
    simp [hrest]
    rw [Nat.min_eq_left hk.le]
    omega
  have hrest_ne : rest ≠ [] := by
    intro h; rw [h] at hrest_len; simp at hrest_len; omega
  -- `rest` is a rotation of `l.eraseIdx k`
  have hrest_rot : rest = (l.eraseIdx k).rotate k := by
    rw [hrest, eraseIdx_eq_take_drop]
    have hlen : (l.take k ++ l.drop (k + 1)).length = l.length - 1 := by
      simp
      rw [Nat.min_eq_left hk.le]
      omega
    rw [List.rotate_eq_rotate',
      List.rotate'_eq_drop_append_take (by omega)]
    have htk : (l.take k ++ l.drop (k + 1)).take k = l.take k := by
      rw [List.take_append_of_le_length (by
        rw [List.length_take, Nat.min_eq_left hk.le])]
      simp
    have hdk : (l.take k ++ l.drop (k + 1)).drop k = l.drop (k + 1) := by
      rw [List.drop_append_of_le_length (by
        rw [List.length_take, Nat.min_eq_left hk.le])]
      simp
    rw [htk, hdk]
  -- hence rowScore rest = rowScore (l.eraseIdx k)
  have hscore_rest : rowScore lam rest = rowScore lam (l.eraseIdx k) := by
    rw [hrest_rot]; exact rowScore_rotate lam _ k
  -- head/last of `rest` are elements of `l`
  have hrest_sub : rest ⊆ l := by
    rw [hrest]
    exact List.append_subset.mpr ⟨List.drop_subset _ _, List.take_subset _ _⟩
  have hhead_mem : rest.head hrest_ne ∈ l := hrest_sub (List.head_mem _)
  have hlast_mem : rest.getLast hrest_ne ∈ l := hrest_sub (List.getLast_mem _)
  -- sorted comparisons via `pairwise_iff_getElem`
  have hpw := List.pairwise_iff_getElem.mp hs
  have hlne : l ≠ [] := by intro h; rw [h] at hk; simp at hk
  -- the cyclic merge equation `pred → succ = (pred → x) + (x → succ)`
  have hmerge : cyclicDiff (rest.getLast hrest_ne) (rest.head hrest_ne)
      = cyclicDiff (rest.getLast hrest_ne) l[k]
        + cyclicDiff l[k] (rest.head hrest_ne) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      -- `rest = l.drop 1 ++ l.take 0`; head `= l[1]`, last `= l[m-1]`
      have hB : rest.head hrest_ne = l[1] := by
        show (l.drop (0 + 1) ++ l.take 0).head hrest_ne = l[1]
        rw [List.head_append_left (by
            intro h; rw [List.drop_eq_nil_iff] at h; omega),
          List.head_drop]
      have hA : rest.getLast hrest_ne = l[l.length - 1] := by
        show (l.drop (0 + 1) ++ l.take 0).getLast hrest_ne = l[l.length - 1]
        rw [List.getLast_eq_getElem,
          List.getElem_append_left (by
            simp only [List.length_append, List.length_drop, List.length_take,
              Nat.min_eq_left (Nat.zero_le l.length)]; omega),
          List.getElem_drop]
        congr 1
        simp only [List.length_append, List.length_drop, List.length_take,
          Nat.min_eq_left (Nat.zero_le l.length)]
        omega
      rw [hB, hA]
      have e1 : l[0] < l[1] := hpw 0 1 (by omega) (by omega) (by omega)
      have e2 : l[0] < l[l.length - 1] :=
        hpw 0 _ (by omega) (by omega) (by omega)
      have e3 : l[1] ≤ l[l.length - 1] :=
        getElem_mono_of_pairwise hs (by omega) (by omega)
      unfold cyclicDiff; split_ifs <;> linarith
    · rcases Nat.lt_or_eq_of_le (Nat.le_sub_one_of_lt hk) with hkm | hkm
      · -- 0 < k < l.length - 1
        have hk1 : k + 1 < l.length := by omega
        have hB : rest.head hrest_ne = l[k + 1] := by
          show (l.drop (k + 1) ++ l.take k).head hrest_ne = l[k + 1]
          rw [List.head_append_left (by
              intro h; rw [List.drop_eq_nil_iff] at h; omega),
            List.head_drop]
        have htk : l.take k ≠ [] := by
          intro h; rw [List.take_eq_nil_iff] at h
          rcases h with h | h
          · omega
          · exact hlne h
        have hA : rest.getLast hrest_ne = l[k - 1] := by
          show (l.drop (k + 1) ++ l.take k).getLast hrest_ne = l[k - 1]
          rw [List.getLast_append_of_right_ne_nil _ _ htk,
            List.getLast_eq_getElem]
          simp only [List.length_take, Nat.min_eq_left hk.le,
            List.getElem_take]
        rw [hB, hA]
        have e1 : l[k - 1] < l[k] :=
          hpw (k - 1) k (by omega) (by omega) (by omega)
        have e2 : l[k] < l[k + 1] :=
          hpw k (k + 1) (by omega) (by omega) (by omega)
        unfold cyclicDiff; split_ifs <;> linarith
      · -- k = l.length - 1
        subst hkm
        have htk : l.take (l.length - 1) ≠ [] := by
          intro h; rw [List.take_eq_nil_iff] at h
          rcases h with h | h
          · omega
          · exact hlne h
        have hB : rest.head hrest_ne = l[0] := by
          show (l.drop (l.length - 1 + 1)
              ++ l.take (l.length - 1)).head hrest_ne = l[0]
          rw [List.head_append_right _ (by rw [List.drop_eq_nil_iff]; omega),
            List.head_take htk, List.head_eq_getElem]
        have hA : rest.getLast hrest_ne = l[l.length - 2] := by
          show (l.drop (l.length - 1 + 1)
              ++ l.take (l.length - 1)).getLast hrest_ne = l[l.length - 2]
          rw [List.getLast_append_of_right_ne_nil _ _ htk,
            List.getLast_eq_getElem]
          simp only [List.length_take,
            Nat.min_eq_left (by omega : l.length - 1 ≤ l.length),
            List.getElem_take]
          congr 1
        rw [hB, hA]
        have e1 : l[l.length - 2] < l[l.length - 1] :=
          hpw (l.length - 2) (l.length - 1) (by omega) (by omega) (by omega)
        have e2 : l[0] ≤ l[l.length - 2] :=
          getElem_mono_of_pairwise hs (by omega) (by omega)
        have e3 : l[0] < l[l.length - 1] :=
          hpw 0 (l.length - 1) (by omega) (by omega) (by omega)
        unfold cyclicDiff; split_ifs <;> linarith
  obtain ⟨g, hg, hgs⟩ := rowScore_erase_head hlam hrest_ne
    (hall _ (List.getElem_mem hk)).1 (hall _ (List.getElem_mem hk)).2
    (hall _ hhead_mem).1 (hall _ hhead_mem).2
    (hall _ hlast_mem).1 (hall _ hlast_mem).2 hmerge
  refine ⟨g, hg, ?_⟩
  rw [← hscore_rest, hgs, ← hrot, rowScore_rotate]

/-! ### 3. Gain functions -/

/-- Merge gain as a function, redeemed by `mergeGain_spec`: the existential
`gapScore_merge` pins its value uniquely, so the saturated subtraction in this
definition never escapes into downstream proofs. -/
noncomputable def mergeGain (lam x y : ℝ) : ℕ :=
  gapScore lam (x + y) - gapScore lam x - gapScore lam y

theorem mergeGain_spec {lam x y : ℝ} (hlam : 0 < lam) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    gapScore lam (x + y) = gapScore lam x + gapScore lam y + mergeGain lam x y := by
  obtain ⟨g, hg, hgs⟩ := gapScore_merge hlam hx hy
  have h : mergeGain lam x y = g := by unfold mergeGain; omega
  rw [h, hgs]

theorem mergeGain_le_two {lam x y : ℝ} (hlam : 0 < lam) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    mergeGain lam x y ≤ 2 := by
  obtain ⟨g, hg, hgs⟩ := gapScore_merge hlam hx hy
  have h : mergeGain lam x y = g := by unfold mergeGain; omega
  rw [h]; exact hg

/-- Both adjacent gaps `≥ λ` force a positive merge gain: the merged gap
scores at least one more than the parts.  This is the arithmetic half of the
Layer-2 interface `gain_pos ↔ facing geometry`. -/
theorem mergeGain_pos_of_ge {lam x y : ℝ} (hlam : 0 < lam)
    (hx : lam ≤ x) (hy : lam ≤ y) :
    1 ≤ mergeGain lam x y := by
  have hx0 : 0 ≤ x := hlam.le.trans hx
  have hy0 : 0 ≤ y := hlam.le.trans hy
  have hspec := mergeGain_spec hlam hx0 hy0
  have hfx : 1 ≤ ⌊x / lam⌋₊ := by
    rw [Nat.le_floor_iff' one_ne_zero, le_div_iff₀ hlam]
    simpa using hx
  have hfy : 1 ≤ ⌊y / lam⌋₊ := by
    rw [Nat.le_floor_iff' one_ne_zero, le_div_iff₀ hlam]
    simpa using hy
  have hdiv : (x + y) / lam = x / lam + y / lam := add_div x y lam
  have hfsum : ⌊x / lam⌋₊ + ⌊y / lam⌋₊ ≤ ⌊(x + y) / lam⌋₊ := by
    rw [Nat.le_floor_iff' (by omega : ⌊x / lam⌋₊ + ⌊y / lam⌋₊ ≠ 0), hdiv]
    push_cast
    exact add_le_add (Nat.floor_le (div_nonneg hx0 hlam.le))
      (Nat.floor_le (div_nonneg hy0 hlam.le))
  unfold gapScore at hspec
  omega

/-- Merged gap below `2λ` gives zero merge gain: all three scores are `0`. -/
theorem mergeGain_eq_zero_of_lt {lam x y : ℝ} (hlam : 0 < lam)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y < 2 * lam) :
    mergeGain lam x y = 0 := by
  have hx2 : x < 2 * lam := lt_of_le_of_lt (le_add_of_nonneg_right hy) hxy
  have hy2 : y < 2 * lam := lt_of_le_of_lt (le_add_of_nonneg_left hx) hxy
  have hfx : ⌊x / lam⌋₊ ≤ 1 := by
    rw [Nat.le_iff_lt_add_one, Nat.floor_lt (div_nonneg hx hlam.le),
      div_lt_iff₀ hlam]
    push_cast; linarith
  have hfy : ⌊y / lam⌋₊ ≤ 1 := by
    rw [Nat.le_iff_lt_add_one, Nat.floor_lt (div_nonneg hy hlam.le),
      div_lt_iff₀ hlam]
    push_cast; linarith
  have hfxy : ⌊(x + y) / lam⌋₊ ≤ 1 := by
    rw [Nat.le_iff_lt_add_one,
      Nat.floor_lt (div_nonneg (add_nonneg hx hy) hlam.le), div_lt_iff₀ hlam]
    push_cast; linarith
  unfold mergeGain gapScore
  omega

/-- Exponent gain of a single row when its `k`-th direction is erased. -/
noncomputable def rowGain (lam : ℝ) (l : List ℝ) (k : ℕ) : ℕ :=
  rowScore lam (l.eraseIdx k) - rowScore lam l

theorem rowScore_eraseIdx' {lam : ℝ} (hlam : 0 < lam) {l : List ℝ}
    (hs : l.Pairwise (· < ·)) (hall : ∀ b ∈ l, 0 ≤ b ∧ b < Real.pi)
    {k : ℕ} (hk : k < l.length) (h2 : 2 ≤ l.length) :
    rowScore lam (l.eraseIdx k) = rowScore lam l + rowGain lam l k := by
  obtain ⟨g, hg, hgs⟩ := rowScore_eraseIdx hlam hs hall hk h2
  have h : rowGain lam l k = g := by unfold rowGain; omega
  rw [h]; exact hgs

theorem rowGain_le_two {lam : ℝ} (hlam : 0 < lam) {l : List ℝ}
    (hs : l.Pairwise (· < ·)) (hall : ∀ b ∈ l, 0 ≤ b ∧ b < Real.pi)
    {k : ℕ} (hk : k < l.length) (h2 : 2 ≤ l.length) :
    rowGain lam l k ≤ 2 := by
  obtain ⟨g, hg, hgs⟩ := rowScore_eraseIdx hlam hs hall hk h2
  have h : rowGain lam l k = g := by unfold rowGain; omega
  rw [h]; exact hg

/-! ### 4. Potential and the exact deletion identity -/

/-- Exponent of center `i`: the cyclic-gap score of its direction list. -/
noncomputable def exponentAt {s : ℕ} (lam : ℝ) (row : Fin s → List ℝ)
    (i : Fin s) : ℕ :=
  rowScore lam (row i)

/-- The Section-4 potential `F(Q) = ∑ᵢ 2^{kᵢ}` over `s` centers, each carrying
its sorted cyclic direction list `row i`. -/
noncomputable def potential {s : ℕ} (lam : ℝ) (row : Fin s → List ℝ) : ℕ :=
  ∑ i : Fin s, 2 ^ exponentAt lam row i

theorem potential_eq_exponent_sum {s : ℕ} (lam : ℝ) (row : Fin s → List ℝ) :
    potential lam row = ∑ i : Fin s, 2 ^ exponentAt lam row i := rfl

/-- Potential after deleting center `v`: every other row `i` loses the
direction at position `del v i`, merging its two adjacent cyclic gaps. -/
noncomputable def potentialErase {s : ℕ} (lam : ℝ) (del : Fin s → Fin s → ℕ)
    (v : Fin s) (row : Fin s → List ℝ) : ℕ :=
  ∑ i : Fin s, if i = v then 0
    else 2 ^ rowScore lam ((row i).eraseIdx (del v i))

theorem sum_potential_erase {s : ℕ} {lam : ℝ} (hlam : 0 < lam) (del : Fin s → Fin s → ℕ)
    (row : Fin s → List ℝ)
    (hs : ∀ i, (row i).Pairwise (· < ·))
    (hall : ∀ i, ∀ b ∈ row i, 0 ≤ b ∧ b < Real.pi)
    (h2 : ∀ i, 2 ≤ (row i).length)
    (hdel : ∀ v i : Fin s, i ≠ v → del v i < (row i).length) :
    ∑ v : Fin s, potentialErase lam del v row
      = ∑ i : Fin s, 2 ^ exponentAt lam row i *
          ∑ v : Fin s, (if v = i then 0
            else 2 ^ rowGain lam (row i) (del v i)) := by
  have hstep : ∀ v : Fin s, potentialErase lam del v row
      = ∑ i : Fin s, if i = v then 0
          else 2 ^ exponentAt lam row i * 2 ^ rowGain lam (row i) (del v i) := by
    intro v
    unfold potentialErase
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : i = v
    · simp [h]
    · simp only [h]
      rw [show rowScore lam ((row i).eraseIdx (del v i))
          = exponentAt lam row i + rowGain lam (row i) (del v i)
        from rowScore_eraseIdx' hlam (hs i) (hall i) (hdel v i h) (h2 i),
        Nat.pow_add]
  rw [Finset.sum_congr rfl (fun v _ => hstep v), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : i = v
  · subst h; simp
  · have hv : v ≠ i := fun e => h e.symm
    simp [h, hv]

/-! ### 5. The removable-deletion equivalence -/

theorem removable_iff {s : ℕ} {lam : ℝ} (hlam : 0 < lam) (del : Fin s → Fin s → ℕ)
    (row : Fin s → List ℝ) (v : Fin s)
    (hs : ∀ i, (row i).Pairwise (· < ·))
    (hall : ∀ i, ∀ b ∈ row i, 0 ≤ b ∧ b < Real.pi)
    (h2 : ∀ i, 2 ≤ (row i).length)
    (hdel : ∀ i : Fin s, i ≠ v → del v i < (row i).length) :
    potential lam row ≤ potentialErase lam del v row
      ↔
    2 ^ exponentAt lam row v ≤
      ∑ i ∈ Finset.univ.erase v,
        2 ^ exponentAt lam row i *
          (2 ^ rowGain lam (row i) (del v i) - 1) := by
  classical
  -- decompose the potential at `v`
  have hpot : potential lam row
      = 2 ^ exponentAt lam row v
        + ∑ i ∈ Finset.univ.erase v, 2 ^ exponentAt lam row i := by
    unfold potential
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
  -- decompose the erased potential
  have hpe : potentialErase lam del v row
      = ∑ i ∈ Finset.univ.erase v,
          2 ^ rowScore lam ((row i).eraseIdx (del v i)) := by
    unfold potentialErase
    rw [Finset.sum_ite]
    simp only [Finset.filter_eq', Finset.mem_univ, ite_true,
      Finset.sum_singleton, Finset.filter_ne']
    simp
  have hpow : ∀ i : Fin s, (1 : ℕ) ≤ 2 ^ rowGain lam (row i) (del v i) :=
    fun i => Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  have hsplit : ∀ i ∈ Finset.univ.erase v,
      2 ^ rowScore lam ((row i).eraseIdx (del v i))
        = 2 ^ exponentAt lam row i
          + 2 ^ exponentAt lam row i *
            (2 ^ rowGain lam (row i) (del v i) - 1) := by
    intro i hi
    have hiv : i ≠ v := Finset.ne_of_mem_erase hi
    rw [rowScore_eraseIdx' hlam (hs i) (hall i) (hdel i hiv) (h2 i),
      Nat.pow_add, Nat.mul_sub_left_distrib, mul_one,
      Nat.add_sub_cancel' (Nat.le_mul_of_pos_right _ (hpow i))]
    rfl
  rw [hpot, hpe, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  omega

/-! ### 6. Charges and cheap certificates -/

/-- The charge row `i` contributes to the deletion of `v`:
`C_i(v) = 2^{k_i} (2^{g_{iv}} - 1)`, taking values `0 / 2^{k_i} / 3·2^{k_i}`
for `g = 0 / 1 / 2`. -/
noncomputable def charge {s : ℕ} (lam : ℝ) (del : Fin s → Fin s → ℕ)
    (row : Fin s → List ℝ) (i v : Fin s) : ℕ :=
  2 ^ exponentAt lam row i * (2 ^ rowGain lam (row i) (del v i) - 1)

/-- `v` is removable: its deletion does not decrease the potential. -/
def Removable {s : ℕ} (lam : ℝ) (del : Fin s → Fin s → ℕ)
    (row : Fin s → List ℝ) (v : Fin s) : Prop :=
  potential lam row ≤ potentialErase lam del v row

/-- `removable_iff` in charge language. -/
theorem removable_iff_charge {s : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (del : Fin s → Fin s → ℕ) (row : Fin s → List ℝ) (v : Fin s)
    (hs : ∀ i, (row i).Pairwise (· < ·))
    (hall : ∀ i, ∀ b ∈ row i, 0 ≤ b ∧ b < Real.pi)
    (h2 : ∀ i, 2 ≤ (row i).length)
    (hdel : ∀ i : Fin s, i ≠ v → del v i < (row i).length) :
    Removable lam del row v ↔
      2 ^ exponentAt lam row v
        ≤ ∑ i ∈ Finset.univ.erase v, charge lam del row i v :=
  removable_iff hlam del row v hs hall h2 hdel

theorem charge_eq_zero_of_gain_zero {s : ℕ} {lam : ℝ}
    (del : Fin s → Fin s → ℕ) (row : Fin s → List ℝ) (i v : Fin s)
    (hg : rowGain lam (row i) (del v i) = 0) :
    charge lam del row i v = 0 := by
  simp [charge, hg]

theorem charge_eq_of_gain_one {s : ℕ} {lam : ℝ}
    (del : Fin s → Fin s → ℕ) (row : Fin s → List ℝ) (i v : Fin s)
    (hg : rowGain lam (row i) (del v i) = 1) :
    charge lam del row i v = 2 ^ exponentAt lam row i := by
  simp [charge, hg]

theorem charge_eq_of_gain_two {s : ℕ} {lam : ℝ}
    (del : Fin s → Fin s → ℕ) (row : Fin s → List ℝ) (i v : Fin s)
    (hg : rowGain lam (row i) (del v i) = 2) :
    charge lam del row i v = 3 * 2 ^ exponentAt lam row i := by
  simp [charge, hg]; ring

theorem charge_lower {s : ℕ} {lam : ℝ}
    (del : Fin s → Fin s → ℕ) (row : Fin s → List ℝ) (i v : Fin s)
    (hg : 1 ≤ rowGain lam (row i) (del v i)) :
    2 ^ exponentAt lam row i ≤ charge lam del row i v := by
  unfold charge
  have h2g : (2 : ℕ) ≤ 2 ^ rowGain lam (row i) (del v i) :=
    Nat.pow_le_pow_right (by norm_num : (0:ℕ) < 2) hg
  have : 1 ≤ 2 ^ rowGain lam (row i) (del v i) - 1 := by omega
  calc 2 ^ exponentAt lam row i
      = 2 ^ exponentAt lam row i * 1 := (mul_one _).symm
    _ ≤ 2 ^ exponentAt lam row i * (2 ^ rowGain lam (row i) (del v i) - 1) :=
        Nat.mul_le_mul le_rfl this

theorem charge_le_three {s : ℕ} {lam : ℝ}
    (del : Fin s → Fin s → ℕ) (row : Fin s → List ℝ) (i v : Fin s)
    (hg : rowGain lam (row i) (del v i) ≤ 2) :
    charge lam del row i v ≤ 3 * 2 ^ exponentAt lam row i := by
  unfold charge
  rw [mul_comm]
  have : 2 ^ rowGain lam (row i) (del v i) - 1 ≤ 3 := by
    have h4 : 2 ^ rowGain lam (row i) (del v i) ≤ 2 ^ 2 :=
      Nat.pow_le_pow_right (by norm_num : (0:ℕ) < 2) hg
    omega
  exact Nat.mul_le_mul this le_rfl

/-- Certificate A: a single `gain ≥ 1` neighbor with exponent at least `k_v`
already covers the loss `2^{k_v}`. -/
theorem removable_of_gain1_ge {s : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (del : Fin s → Fin s → ℕ) (row : Fin s → List ℝ) (v : Fin s)
    (hs : ∀ i, (row i).Pairwise (· < ·))
    (hall : ∀ i, ∀ b ∈ row i, 0 ≤ b ∧ b < Real.pi)
    (h2 : ∀ i, 2 ≤ (row i).length)
    (hdel : ∀ i : Fin s, i ≠ v → del v i < (row i).length)
    (i : Fin s) (hi : i ≠ v) (hg : 1 ≤ rowGain lam (row i) (del v i))
    (hk : exponentAt lam row v ≤ exponentAt lam row i) :
    Removable lam del row v := by
  rw [removable_iff_charge hlam del row v hs hall h2 hdel]
  calc 2 ^ exponentAt lam row v
      ≤ 2 ^ exponentAt lam row i := Nat.pow_le_pow_right (by norm_num : (0:ℕ) < 2) hk
    _ ≤ charge lam del row i v := charge_lower del row i v hg
    _ ≤ ∑ j ∈ Finset.univ.erase v, charge lam del row j v :=
        Finset.single_le_sum (f := fun j => charge lam del row j v) (fun j _ => Nat.zero_le _)
          (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩)

/-- Certificate B: a single `gain = 2` neighbor with `k_i ≥ k_v - 1` covers the
loss, since `3·2^{k_i} ≥ 2^{k_i+1}`. -/
theorem removable_of_gain2 {s : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (del : Fin s → Fin s → ℕ) (row : Fin s → List ℝ) (v : Fin s)
    (hs : ∀ i, (row i).Pairwise (· < ·))
    (hall : ∀ i, ∀ b ∈ row i, 0 ≤ b ∧ b < Real.pi)
    (h2 : ∀ i, 2 ≤ (row i).length)
    (hdel : ∀ i : Fin s, i ≠ v → del v i < (row i).length)
    (i : Fin s) (hi : i ≠ v) (hg : rowGain lam (row i) (del v i) = 2)
    (hk : exponentAt lam row v ≤ exponentAt lam row i + 1) :
    Removable lam del row v := by
  rw [removable_iff_charge hlam del row v hs hall h2 hdel]
  calc 2 ^ exponentAt lam row v
      ≤ 2 ^ (exponentAt lam row i + 1) := Nat.pow_le_pow_right (by norm_num : (0:ℕ) < 2) hk
    _ = 2 * 2 ^ exponentAt lam row i := by rw [pow_succ, mul_comm]
    _ ≤ 3 * 2 ^ exponentAt lam row i := by omega
    _ = charge lam del row i v := (charge_eq_of_gain_two del row i v hg).symm
    _ ≤ ∑ j ∈ Finset.univ.erase v, charge lam del row j v :=
        Finset.single_le_sum (f := fun j => charge lam del row j v) (fun j _ => Nat.zero_le _)
          (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩)

/-- Certificate C: two `gain ≥ 1` neighbors each with `k ≥ k_v - 1` together
cover `2^{k_v} = 2^{k_v-1} + 2^{k_v-1}`. -/
theorem removable_of_two_gain1 {s : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (del : Fin s → Fin s → ℕ) (row : Fin s → List ℝ) (v : Fin s)
    (hs : ∀ i, (row i).Pairwise (· < ·))
    (hall : ∀ i, ∀ b ∈ row i, 0 ≤ b ∧ b < Real.pi)
    (h2 : ∀ i, 2 ≤ (row i).length)
    (hdel : ∀ i : Fin s, i ≠ v → del v i < (row i).length)
    (i j : Fin s) (hi : i ≠ v) (hj : j ≠ v) (hij : i ≠ j)
    (hgi : 1 ≤ rowGain lam (row i) (del v i))
    (hgj : 1 ≤ rowGain lam (row j) (del v j))
    (hki : exponentAt lam row v ≤ exponentAt lam row i + 1)
    (hkj : exponentAt lam row v ≤ exponentAt lam row j + 1) :
    Removable lam del row v := by
  rw [removable_iff_charge hlam del row v hs hall h2 hdel]
  have hci : 2 ^ exponentAt lam row i ≤ charge lam del row i v :=
    charge_lower del row i v hgi
  have hcj : 2 ^ exponentAt lam row j ≤ charge lam del row j v :=
    charge_lower del row j v hgj
  have hsum : charge lam del row i v + charge lam del row j v
      ≤ ∑ k ∈ Finset.univ.erase v, charge lam del row k v := by
    rw [← Finset.sum_pair (f := fun k => charge lam del row k v) hij]
    apply Finset.sum_le_sum_of_subset
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;>
      exact Finset.mem_erase.mpr ⟨by assumption, Finset.mem_univ _⟩
  have hkj' : 2 ^ exponentAt lam row v
      ≤ 2 ^ exponentAt lam row i + 2 ^ exponentAt lam row j := by
    rcases Nat.eq_zero_or_pos (exponentAt lam row v) with h0 | h0
    · rw [h0, pow_zero]
      exact le_trans (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num)))
        (Nat.le_add_right _ _)
    · have e : exponentAt lam row v - 1 + 1 = exponentAt lam row v := by omega
      have hi' : exponentAt lam row v - 1 ≤ exponentAt lam row i := by omega
      have hj' : exponentAt lam row v - 1 ≤ exponentAt lam row j := by omega
      calc 2 ^ exponentAt lam row v
          = 2 ^ (exponentAt lam row v - 1 + 1) := by rw [e]
        _ = 2 ^ (exponentAt lam row v - 1) + 2 ^ (exponentAt lam row v - 1) := by
            rw [pow_succ]; ring
        _ ≤ 2 ^ exponentAt lam row i + 2 ^ exponentAt lam row j :=
            Nat.add_le_add (Nat.pow_le_pow_right (by norm_num : (0:ℕ) < 2) hi')
              (Nat.pow_le_pow_right (by norm_num : (0:ℕ) < 2) hj')
  exact le_trans hkj' (le_trans (Nat.add_le_add hci hcj) hsum)

/-! ### 7½. Certificate predicates and the no-certificate constraints

Layer 1 of the contradiction argument: `CertA/CertB/CertC` package the three
sufficient conditions as predicates, and the `not_cert*` lemmas extract the
exponent constraints a victim `v` must satisfy when it carries no certificate.
No geometry yet — this is pure dyadic bookkeeping. -/

/-- Certificate A at `v`: a positive-gain partner at level `≥ k_v`. -/
def CertA {s : ℕ} (lam : ℝ) (del : Fin s → Fin s → ℕ) (row : Fin s → List ℝ)
    (v : Fin s) : Prop :=
  ∃ i : Fin s, i ≠ v ∧ 1 ≤ rowGain lam (row i) (del v i) ∧
    exponentAt lam row v ≤ exponentAt lam row i

/-- Certificate B at `v`: a gain-2 partner at level `≥ k_v - 1`. -/
def CertB {s : ℕ} (lam : ℝ) (del : Fin s → Fin s → ℕ) (row : Fin s → List ℝ)
    (v : Fin s) : Prop :=
  ∃ i : Fin s, i ≠ v ∧ rowGain lam (row i) (del v i) = 2 ∧
    exponentAt lam row v ≤ exponentAt lam row i + 1

/-- Certificate C at `v`: two distinct positive-gain partners each at level
`≥ k_v - 1`. -/
def CertC {s : ℕ} (lam : ℝ) (del : Fin s → Fin s → ℕ) (row : Fin s → List ℝ)
    (v : Fin s) : Prop :=
  ∃ i j : Fin s, i ≠ v ∧ j ≠ v ∧ i ≠ j ∧
    1 ≤ rowGain lam (row i) (del v i) ∧
    1 ≤ rowGain lam (row j) (del v j) ∧
    exponentAt lam row v ≤ exponentAt lam row i + 1 ∧
    exponentAt lam row v ≤ exponentAt lam row j + 1

/-- `¬CertA` forces every positive-gain partner of `v` strictly below `k_v`:
under global `¬CertA` every charge arc goes strictly *up* the exponent
ladder. -/
theorem partner_exponent_lt_of_not_certA {s : ℕ} {lam : ℝ}
    {del : Fin s → Fin s → ℕ} {row : Fin s → List ℝ} {v : Fin s}
    (hA : ¬ CertA lam del row v) {i : Fin s} (hi : i ≠ v)
    (hg : 1 ≤ rowGain lam (row i) (del v i)) :
    exponentAt lam row i < exponentAt lam row v := by
  exact Nat.lt_of_not_ge fun h => hA ⟨i, hi, hg, h⟩

/-- `¬CertB` forces every gain-2 partner of `v` at least two levels below. -/
theorem partner_exponent_add_one_lt_of_not_certB {s : ℕ} {lam : ℝ}
    {del : Fin s → Fin s → ℕ} {row : Fin s → List ℝ} {v : Fin s}
    (hB : ¬ CertB lam del row v) {i : Fin s} (hi : i ≠ v)
    (hg : rowGain lam (row i) (del v i) = 2) :
    exponentAt lam row i + 1 < exponentAt lam row v := by
  exact Nat.lt_of_not_ge fun h => hB ⟨i, hi, hg, h⟩

/-- `¬CertC`: among the positive-gain partners of `v`, no two distinct ones
can both sit at level `≥ k_v - 1`. -/
theorem not_two_near_partners_of_not_certC {s : ℕ} {lam : ℝ}
    {del : Fin s → Fin s → ℕ} {row : Fin s → List ℝ} {v : Fin s}
    (hC : ¬ CertC lam del row v) {i j : Fin s}
    (hi : i ≠ v) (hj : j ≠ v) (hij : i ≠ j)
    (hgi : 1 ≤ rowGain lam (row i) (del v i))
    (hgj : 1 ≤ rowGain lam (row j) (del v j)) :
    exponentAt lam row i + 1 < exponentAt lam row v ∨
      exponentAt lam row j + 1 < exponentAt lam row v := by
  by_contra h
  push_neg at h
  exact hC ⟨i, j, hi, hj, hij, hgi, hgj, h.1, h.2⟩

/-- Under `¬CertA ∧ ¬CertB ∧ ¬CertC`, the charge received by `v` decomposes
into at most one `2^{k_v-1}` term (a single gain-1 partner at level `k_v-1`)
plus partners at level `≤ k_v - 2` charging at most `3·2^{k_i}` each. -/
theorem charge_structure_of_no_cert {s : ℕ} {lam : ℝ}
    {del : Fin s → Fin s → ℕ} {row : Fin s → List ℝ} {v : Fin s}
    (hA : ¬ CertA lam del row v) (hB : ¬ CertB lam del row v)
    (hC : ¬ CertC lam del row v) {i : Fin s} (hi : i ≠ v)
    (hg : 1 ≤ rowGain lam (row i) (del v i)) :
    exponentAt lam row i ≤ exponentAt lam row v - 1 ∧
      (rowGain lam (row i) (del v i) = 2 →
        exponentAt lam row i ≤ exponentAt lam row v - 2) := by
  have h1 := partner_exponent_lt_of_not_certA hA hi hg
  refine ⟨by omega, fun h2 => ?_⟩
  have h3 := partner_exponent_add_one_lt_of_not_certB hB hi h2
  omega

/-- Global `¬CertA` kills all incoming gains at a minimum-exponent vertex:
nothing sits below it, so no arc can reach it. -/
theorem no_gain_into_min_exponent {s : ℕ} {lam : ℝ}
    {del : Fin s → Fin s → ℕ} {row : Fin s → List ℝ}
    (h : ∀ w : Fin s, ¬ CertA lam del row w) {v : Fin s}
    (hmin : ∀ i : Fin s, exponentAt lam row v ≤ exponentAt lam row i)
    {i : Fin s} (hi : i ≠ v) :
    rowGain lam (row i) (del v i) = 0 := by
  by_contra hg
  have hg1 : 1 ≤ rowGain lam (row i) (del v i) := Nat.pos_of_ne_zero hg
  exact h v ⟨i, hi, hg1, hmin i⟩

/-- Global `¬CertA` silences a maximum-exponent vertex: every arc it emits
would have to land strictly higher, and nothing is higher. -/
theorem no_gain_from_max_exponent {s : ℕ} {lam : ℝ}
    {del : Fin s → Fin s → ℕ} {row : Fin s → List ℝ}
    (h : ∀ w : Fin s, ¬ CertA lam del row w) {i : Fin s}
    (hmax : ∀ v : Fin s, exponentAt lam row v ≤ exponentAt lam row i)
    {v : Fin s} (hi : i ≠ v) :
    rowGain lam (row i) (del v i) = 0 := by
  by_contra hg
  have hg1 : 1 ≤ rowGain lam (row i) (del v i) := Nat.pos_of_ne_zero hg
  have hlt := partner_exponent_lt_of_not_certA (h v) hi hg1
  exact absurd (hmax v) (not_le.mpr hlt)

/-! ### 7¾. The emission dichotomy and the reduced crux

The checker statistic `emNoAC = 0` on every legal nonflat sample with
`s ≥ 4` says exactly: either some positive-gain arc fails to climb the
exponent ladder (a down/level arc, which is certificate A at its receiver),
or some vertex collects two "close" arcs — partners sitting exactly one
level below (which is certificate C).  B is not needed.  This dichotomy is
the geometric heart; the assembly below is pure bookkeeping. -/

/-- The emission dichotomy: the form in which `Section4Legality` will supply
the certificate.  First disjunct is literally `∃ v, CertA v`; the second is
`∃ v, CertC v` witnessed by arcs of jump exactly one. -/
def EmissionDichotomy {s : ℕ} (lam : ℝ) (del : Fin s → Fin s → ℕ)
    (row : Fin s → List ℝ) : Prop :=
  (∃ i v : Fin s, i ≠ v ∧ 1 ≤ rowGain lam (row i) (del v i) ∧
      exponentAt lam row v ≤ exponentAt lam row i) ∨
  (∃ i j v : Fin s, i ≠ v ∧ j ≠ v ∧ i ≠ j ∧
      1 ≤ rowGain lam (row i) (del v i) ∧
      1 ≤ rowGain lam (row j) (del v j) ∧
      exponentAt lam row i + 1 = exponentAt lam row v ∧
      exponentAt lam row j + 1 = exponentAt lam row v)

/-- The dichotomy assembles into a certificate by pure bookkeeping: a
down/level arc is `CertA`; two jump-one arcs give `CertC` since
`k_i + 1 = k_v` implies `k_v ≤ k_i + 1`. -/
theorem certA_or_C_of_dichotomy {s : ℕ} {lam : ℝ}
    {del : Fin s → Fin s → ℕ} {row : Fin s → List ℝ}
    (h : EmissionDichotomy lam del row) :
    ∃ v : Fin s, CertA lam del row v ∨ CertC lam del row v := by
  rcases h with ⟨i, v, hi, hg, hk⟩ | ⟨i, j, v, hi, hj, hij, hgi, hgj, hki, hkj⟩
  · exact ⟨v, Or.inl ⟨i, hi, hg, hk⟩⟩
  · exact ⟨v, Or.inr ⟨i, j, hi, hj, hij, hgi, hgj,
      Nat.le_of_eq hki.symm, Nat.le_of_eq hkj.symm⟩⟩

/-- A certificate yields removability: the three sufficient lemmas rephrased
in `CertA/CertB/CertC` language. -/
theorem removable_of_cert {s : ℕ} {lam : ℝ} (hlam : 0 < lam)
    {del : Fin s → Fin s → ℕ} {row : Fin s → List ℝ} {v : Fin s}
    (hs : ∀ i, (row i).Pairwise (· < ·))
    (hall : ∀ i, ∀ b ∈ row i, 0 ≤ b ∧ b < Real.pi)
    (h2 : ∀ i, 2 ≤ (row i).length)
    (hdel : ∀ i : Fin s, i ≠ v → del v i < (row i).length)
    (hcert : CertA lam del row v ∨ CertB lam del row v ∨ CertC lam del row v) :
    Removable lam del row v := by
  rcases hcert with ⟨i, hi, hg, hk⟩ | ⟨i, hi, hg, hk⟩ | ⟨i, j, hi, hj, hij, hgi, hgj, hki, hkj⟩
  · exact removable_of_gain1_ge hlam del row v hs hall h2 hdel i hi hg hk
  · exact removable_of_gain2 hlam del row v hs hall h2 hdel i hi hg hk
  · exact removable_of_two_gain1 hlam del row v hs hall h2 hdel i j hi hj hij hgi hgj hki hkj

/-! ### 7. Flat branch and the frozen crux -/

/-- `Q` is flat when every row exponent is zero: `F(Q) = s`, the trivial end of
the induction. -/
def Flat {s : ℕ} (lam : ℝ) (row : Fin s → List ℝ) : Prop :=
  ∀ i, exponentAt lam row i = 0

/-- On a flat configuration the potential collapses to `s`. -/
theorem flat_potential {s : ℕ} (lam : ℝ) (row : Fin s → List ℝ)
    (h : Flat lam row) : potential lam row = s := by
  unfold potential
  rw [Finset.sum_congr rfl (fun i _ => by rw [h i, pow_zero])]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- The flat branch reduces to a cardinality bound `s ≤ cap`, which legality
must supply.  Deliberately *not* `s ≤ 2n+1`: small `n` breaks that route. -/
theorem flat_potential_bound {s : ℕ} {lam : ℝ} (row : Fin s → List ℝ)
    (hflat : Flat lam row) (cap : ℕ) (hs : s ≤ cap) :
    potential lam row ≤ cap := by
  rw [flat_potential lam row hflat]; exact hs

/-- `v` is a hull vertex of the center configuration `Q`: an extreme point of
`convexHull (range Q)`.  For a finite set these are exactly the vertices of
the convex polygon. -/
def IsHullVertex {V : Type*} [AddCommGroup V] [Module ℝ V]
    {s : ℕ} (Q : Fin s → V) (v : Fin s) : Prop :=
  Q v ∈ Set.extremePoints ℝ (convexHull ℝ (Set.range Q))

/-- The dichotomy closes the whole arithmetic side: it yields a certificate
(`certA_or_C_of_dichotomy`) and the certificate yields removability
(`removable_of_cert`).  Hence `exists_removable_vertex` is *equivalent* to
the geometric statement `EmissionDichotomy` — the only remaining content. -/
theorem removable_of_dichotomy {s : ℕ} {lam : ℝ} (hlam : 0 < lam)
    {del : Fin s → Fin s → ℕ} {row : Fin s → List ℝ}
    (hs : ∀ i, (row i).Pairwise (· < ·))
    (hall : ∀ i, ∀ b ∈ row i, 0 ≤ b ∧ b < Real.pi)
    (h2 : ∀ i, 2 ≤ (row i).length)
    (hdel : ∀ v i : Fin s, i ≠ v → del v i < (row i).length)
    (hd : EmissionDichotomy lam del row) :
    ∃ v : Fin s, Removable lam del row v := by
  obtain ⟨v, hv⟩ := certA_or_C_of_dichotomy hd
  exact ⟨v, removable_of_cert hlam hs hall h2 (hdel v) (hv.elim Or.inl
    fun hC => Or.inr (Or.inr hC))⟩

/-- The remaining crux: every non-flat legal configuration with `s ≥ 4` has a
removable vertex.  By `removable_of_dichotomy` this follows from
`EmissionDichotomy` — the geometric fact that the charge-arc digraph cannot
consist entirely of strictly-upward arcs with at most one jump-1 arc per
receiver. -/
theorem exists_removable_vertex {s : ℕ} (lam : ℝ) (hlam : 0 < lam)
    (del : Fin s → Fin s → ℕ) (row : Fin s → List ℝ)
    (hs : 4 ≤ s) (hflat : ¬ Flat lam row) :
    ∃ v : Fin s, Removable lam del row v := by
  sorry

/-- The stronger hull version, matching the checker observation that a
removable witness can always be chosen on the convex hull. -/
theorem exists_removable_hull_vertex {V : Type*} [AddCommGroup V] [Module ℝ V]
    {s : ℕ} (lam : ℝ) (hlam : 0 < lam)
    (Q : Fin s → V)
    (del : Fin s → Fin s → ℕ) (row : Fin s → List ℝ)
    (hs : 4 ≤ s) (hflat : ¬ Flat lam row) :
    ∃ v : Fin s, IsHullVertex Q v ∧ Removable lam del row v := by
  sorry

end Jsp404
