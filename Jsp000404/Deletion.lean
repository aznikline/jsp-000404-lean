import Jsp000404.Section4Legality

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

/-! ### 6. The frozen crux -/

/-- `Q` is flat when every row exponent is zero: `F(Q) = s`, the trivial end of
the induction. -/
def Flat {s : ℕ} (lam : ℝ) (row : Fin s → List ℝ) : Prop :=
  ∀ i, exponentAt lam row i = 0

/-- `v` is a hull vertex of the center configuration — geometric predicate,
fixed here as the target of the remaining crux. -/
def IsHullVertex {s : ℕ} (row : Fin s → List ℝ) (v : Fin s) : Prop :=
  True  -- placeholder: geometric hull membership is supplied by `Section4Legality`

/-- The remaining crux: every non-flat legal configuration with `s ≥ 4` has a
removable vertex.  Isolated on purpose; do not prove in this iteration. -/
theorem exists_removable_vertex {s : ℕ} (lam : ℝ) (hlam : 0 < lam)
    (del : Fin s → Fin s → ℕ) (row : Fin s → List ℝ)
    (hs : 4 ≤ s) (hflat : ¬ Flat lam row) :
    ∃ v : Fin s, potential lam row ≤ potentialErase lam del v row := by
  sorry

/-- The stronger hull version, matching the checker observation that a
removable witness can always be chosen on the convex hull. -/
theorem exists_removable_hull_vertex {s : ℕ} (lam : ℝ) (hlam : 0 < lam)
    (del : Fin s → Fin s → ℕ) (row : Fin s → List ℝ)
    (hs : 4 ≤ s) (hflat : ¬ Flat lam row) :
    ∃ v : Fin s, IsHullVertex row v ∧
      potential lam row ≤ potentialErase lam del v row := by
  sorry

end Jsp404
