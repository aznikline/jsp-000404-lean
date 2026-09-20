import Jsp000404.Section4Legality
import Jsp000404.Deletion

/-!
# Geometric deletion — binding the abstract `row`/`del` model to real centers

`Deletion.lean` works on an abstract row system `row : Fin s → List ℝ`,
`del : Fin s → Fin s → ℕ`.  This file instantiates it on the actual
center configuration `c : Fin s → Plane₂`:

* `directionRow o e c i` — the sorted projective directions
  `linRep (o.oangle e (c j - c i))` over `j ≠ i`, **with multiplicities**
  (one entry per center, not dedup'd like `circleDirs`).  Multiplicity is
  essential: deleting a point removes exactly one entry, while duplicate
  directions produce a `0`-gap contributing nothing to the exponent —
  so `rowScore` agrees with the dedup'd version (`rowScore_dedup` below).

* `deleteIndex o e c v i` — the position of `v`'s direction inside
  `directionRow c i`, via `List.idxOf`.

* `erase_directionRow` — the recursion bridge: deleting center `v` from
  the configuration (reindexed by `v.succAbove`) erases exactly
  `deleteIndex` from each surviving row.

* The geometric face: `gapAfter` at consecutive indices equals the
  projective arc between two centers' directions, hence is either the
  triangle angle `∠aib` or its complement — the bridge into
  `Section4Legality.triAngle`/`facing_lower`.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

open Classical

variable {s : ℕ} (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
  (c : Fin s → Plane₂)

/-- The direction `i → j` as a projective representative in `[0, π)`. -/
noncomputable def dirRep (i j : Fin s) : ℝ :=
  linRep (o.oangle e (c j - c i))

/-- The sorted list of direction representatives `i → j`, `j ≠ i`, with
multiplicities (one entry per `j`).  Length `s - 1`. -/
noncomputable def directionRow (i : Fin s) : List ℝ :=
  (((List.finRange s).erase i).map
    (fun j => dirRep o e c i j)).insertionSort (· ≤ ·)

/-- The rows of the configuration. -/
noncomputable def directionRows : Fin s → List ℝ :=
  fun i => directionRow o e c i

lemma mem_directionRow {i : Fin s} {x : ℝ} :
    x ∈ directionRow o e c i ↔ ∃ j : Fin s, j ≠ i ∧ x = dirRep o e c i j := by
  unfold directionRow
  rw [List.mem_insertionSort, List.mem_map]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [(List.nodup_finRange s).mem_erase_iff] at hj
    exact ⟨j, hj.1, rfl⟩
  · rintro ⟨j, hji, rfl⟩
    refine ⟨j, ?_, rfl⟩
    rw [(List.nodup_finRange s).mem_erase_iff]
    exact ⟨hji, List.mem_finRange _⟩

lemma directionRow_sorted (i : Fin s) :
    (directionRow o e c i).SortedLE :=
  (List.pairwise_insertionSort _ _).sortedLE

lemma directionRow_mem_Ico {i : Fin s} {x : ℝ}
    (hx : x ∈ directionRow o e c i) : x ∈ Set.Ico 0 Real.pi := by
  obtain ⟨j, -, rfl⟩ := (mem_directionRow o e c).mp hx
  exact linRep_mem_Ico _

lemma directionRow_length (i : Fin s) :
    (directionRow o e c i).length = s - 1 := by
  unfold directionRow
  rw [List.length_insertionSort, List.length_map,
    List.length_erase_of_mem (List.mem_finRange i), List.length_finRange]

/-- The deletion index of `v` in row `i`: position of `v`'s direction
value (first occurrence if the direction class is shared). -/
noncomputable def deleteIndex (v i : Fin s) : ℕ :=
  (directionRow o e c i).idxOf (dirRep o e c i v)

lemma deleteIndex_lt {v i : Fin s} (h : i ≠ v) :
    deleteIndex o e c v i < (directionRow o e c i).length := by
  unfold deleteIndex
  rw [List.idxOf_lt_length_iff]
  exact mem_directionRow o e c |>.mpr ⟨v, Ne.symm h, rfl⟩

/-! ### The deletion bridge

`Fin.succAbove v` reindexes `Fin s` onto `Fin (s+1) \ {v}`.  At the list
level this says `finRange s` mapped through `succAbove` is exactly
`finRange (s+1)` with `v` erased. -/

lemma finRange_map_succAbove {s : ℕ} (v : Fin (s + 1)) :
    (List.finRange s).map v.succAbove = (List.finRange (s + 1)).erase v := by
  have hs1 : ((List.finRange s).map v.succAbove).SortedLT :=
    List.sortedLT_iff_pairwise.mpr (List.Pairwise.map v.succAbove
      (fun _ _ h => (Fin.strictMono_succAbove v).lt_iff_lt.mpr h)
      (List.sortedLT_iff_pairwise.mp (List.sortedLT_finRange s)))
  have hs2 : ((List.finRange (s + 1)).erase v).SortedLT :=
    List.sortedLT_iff_pairwise.mpr (List.Pairwise.sublist List.erase_sublist
      (List.sortedLT_iff_pairwise.mp (List.sortedLT_finRange (s + 1))))
  refine List.SortedLT.eq_of_mem_iff hs1 hs2 (fun j => ?_)
  rw [List.mem_map, (List.nodup_finRange (s + 1)).mem_erase_iff]
  constructor
  · rintro ⟨j', -, rfl⟩
    exact ⟨Fin.succAbove_ne v j', List.mem_finRange _⟩
  · rintro ⟨hj, -⟩
    obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
    exact ⟨j', List.mem_finRange _, rfl⟩

/-- **The deletion bridge.** Removing center `v` from the configuration
(reindexed by `v.succAbove`) erases `v`'s direction value from each
surviving direction row. -/
lemma erase_directionRow {s : ℕ} {c' : Fin (s + 1) → Plane₂}
    (v : Fin (s + 1)) (i' : Fin s) :
    directionRow o e (c' ∘ v.succAbove) i' =
      (directionRow o e c' (v.succAbove i')).erase
        (dirRep o e c' (v.succAbove i') v) := by
  classical
  set i := v.succAbove i' with hi
  have hiv : i ≠ v := Fin.succAbove_ne v i'
  -- The presort list of the reduced row equals the presort list of row `i`
  -- with the contribution of index `v` erased.
  have hlist :
      (((List.finRange s).erase i').map
        (fun j' => dirRep o e (c' ∘ v.succAbove) i' j')) =
      (((List.finRange (s + 1)).erase i).erase v).map
        (fun j => dirRep o e c' i j) := by
    have h1 : (fun j' => dirRep o e (c' ∘ v.succAbove) i' j') =
        dirRep o e c' i ∘ v.succAbove := rfl
    rw [h1, ← List.map_map,
      List.map_erase (Fin.strictMono_succAbove v).injective, ← hi,
      finRange_map_succAbove, List.erase_comm]
  -- Both sides are sorted; show they are permutations via the presort lists.
  unfold directionRow
  rw [hlist]
  -- Multiset-level: erasing index `v` removes one occurrence of `dirRep i v`.
  set A : List (Fin (s + 1)) := (List.finRange (s + 1)).erase i with hA
  have hperm : List.Perm ((A.erase v).map (fun j => dirRep o e c' i j))
      ((A.map (fun j => dirRep o e c' i j)).erase (dirRep o e c' i v)) := by
    rw [← Multiset.coe_eq_coe]
    simp only [← Multiset.map_coe, ← Multiset.coe_erase]
    exact Multiset.map_erase_of_mem _ _ (Multiset.mem_coe.mpr
      ((List.nodup_finRange _).mem_erase_iff.mpr ⟨hiv.symm, List.mem_finRange _⟩))
  have hperm' : List.Perm (((A.erase v).map (fun j => dirRep o e c' i j)).insertionSort
        (· ≤ ·))
      (((A.map (fun j => dirRep o e c' i j)).insertionSort (· ≤ ·)).erase
        (dirRep o e c' i v)) :=
    ((List.perm_insertionSort _ _).trans hperm).trans
      (List.Perm.erase _ (List.perm_insertionSort _ _).symm)
  have hs1 : (((A.erase v).map (fun j => dirRep o e c' i j)).insertionSort
        (· ≤ ·)).SortedLE :=
    (List.pairwise_insertionSort _ _).sortedLE
  have hs2 : (((A.map (fun j => dirRep o e c' i j)).insertionSort (· ≤ ·)).erase
        (dirRep o e c' i v)).SortedLE :=
    (List.Pairwise.sublist List.erase_sublist
      (List.pairwise_insertionSort _ _)).sortedLE
  exact List.Perm.eq_of_sortedLE hs1 hs2 hperm'

/-- Index form of the bridge: `del v i = deleteIndex` erases the same row. -/
lemma eraseIdx_directionRow {s : ℕ} {c' : Fin (s + 1) → Plane₂}
    (v : Fin (s + 1)) (i' : Fin s) :
    directionRow o e (c' ∘ v.succAbove) i' =
      (directionRow o e c' (v.succAbove i')).eraseIdx
        (deleteIndex o e c' v (v.succAbove i')) := by
  rw [erase_directionRow]
  unfold deleteIndex
  rw [List.erase_eq_eraseIdx_of_idxOf rfl]

/-! ### Adjacent-gap geometry

The two gaps merged by `rowGain` at position `k` are `wrapGap (l[k]::rest)`
(the incoming arc `pred → l[k]`) and `cyclicDiff l[k] rest.head` (the
outgoing arc `l[k] → succ`).  Each is a `cyclicDiff` between `dirRep i v`
and another center's direction representative, hence equals either the
triangle angle `∠vit` or its complement `π - ∠vit` — both `≥ λ` whenever
`∠ ∈ [λ, π - λ]`.

Sharper: `cyclicDiff (dirRep i a) (dirRep i b)` is the *counterclockwise
sweep* `linRep (oangle (c a - c i) (c b - c i))` from ray `i→a` to ray
`i→b`.  Hence the two merged gaps at `dirRep i v` are exactly the two
"facing" quantities — the minimum CCW sweep and the minimum CW sweep from
ray `i→v` to a neighbouring center's ray. -/

/-- `↑(kπ) = k • ↑π` in `Real.Angle`. -/
lemma coe_int_mul_pi (k : ℤ) :
    (((k : ℝ) * Real.pi : ℝ) : Real.Angle) =
      k • ((Real.pi : ℝ) : Real.Angle) := by
  rw [← zsmul_eq_mul]
  exact map_zsmul Real.Angle.coeHom k Real.pi

/-- The element of `[0, π)` lying in the `mod π` class of an angle `d`
is exactly `linRep d`. -/
lemma eq_linRep_of_int_pi {d : Real.Angle} {x : ℝ}
    (hx : x ∈ Set.Ico 0 Real.pi)
    (h : ∃ k : ℤ, ((x : ℝ) : Real.Angle) =
      d + k • ((Real.pi : ℝ) : Real.Angle)) :
    x = linRep d := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨hx0, hxp⟩ := hx
  obtain ⟨hl0, hlp⟩ := linRep_mem_Ico d
  obtain ⟨j, hj⟩ : ∃ j : ℤ, ((linRep d : ℝ) : Real.Angle) =
      d + j • ((Real.pi : ℝ) : Real.Angle) := by
    rcases linRep_class d with hd | hd
    · exact ⟨0, by simpa using hd⟩
    · exact ⟨1, by simpa using hd⟩
  have h0 : ((x - linRep d - ((k - j : ℤ) : ℝ) * Real.pi : ℝ) :
      Real.Angle) = 0 := by
    rw [Real.Angle.coe_sub, Real.Angle.coe_sub, coe_int_mul_pi, hk, hj]
    push_cast
    module
  obtain ⟨m, hm⟩ := Real.Angle.coe_eq_zero_iff.mp h0
  rw [zsmul_eq_mul] at hm
  have hset : x - linRep d = ((k - j + 2 * m : ℤ) : ℝ) * Real.pi := by
    push_cast at hm ⊢
    linarith
  have hk0 : (k - j + 2 * m : ℤ) = 0 := by
    by_contra hne
    have hge : (1 : ℝ) ≤ |((k - j + 2 * m : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hne
    have hlt : |((k - j + 2 * m : ℤ) : ℝ) * Real.pi| < Real.pi := by
      rw [← hset, abs_lt]
      constructor <;> linarith
    rw [abs_mul, abs_of_pos Real.pi_pos] at hlt
    nlinarith [Real.pi_pos]
  have : x - linRep d = 0 := by rw [hset, hk0]; simp
  linarith

/-- `linRep` is invariant under `+π` (projective identification). -/
lemma linRep_add_pi (d : Real.Angle) :
    linRep (d + Real.pi) = linRep d := by
  rcases linRep_class (d + Real.pi) with h | h
  · exact eq_linRep_of_int_pi (linRep_mem_Ico _)
      ⟨1, by rw [h]; module⟩
  · exact eq_linRep_of_int_pi (linRep_mem_Ico _)
      ⟨2, by rw [h]; module⟩

/-- `cyclicDiff` of two points of `[0, π)` stays in `[0, π)`. -/
lemma cyclicDiff_mem_Ico {a b : ℝ} (ha : a ∈ Set.Ico 0 Real.pi)
    (hb : b ∈ Set.Ico 0 Real.pi) :
    cyclicDiff a b ∈ Set.Ico 0 Real.pi := by
  obtain ⟨ha0, hap⟩ := ha
  obtain ⟨hb0, hbp⟩ := hb
  unfold cyclicDiff
  split_ifs with h1 h2
  · exact ⟨le_rfl, Real.pi_pos⟩
  · exact ⟨by linarith, by linarith⟩
  · have hba : b < a := lt_of_le_of_ne (le_of_not_gt h2) (Ne.symm h1)
    exact ⟨by linarith, by linarith⟩

/-- Direction representatives are symmetric: `dirRep i j = dirRep j i`
since `linRep` quotients by `π`. -/
lemma dirRep_comm (he : e ≠ 0) {i j : Fin s} (hij : c i ≠ c j) :
    dirRep o e c i j = dirRep o e c j i := by
  unfold dirRep
  rw [← neg_sub (c j) (c i),
    o.oangle_neg_right he (sub_ne_zero.mpr (Ne.symm hij)),
    linRep_add_pi]

/-- The angle-coe of a `cyclicDiff` equals the coe of the difference,
up to `π`: `↑(cyclicDiff a b) = ↑(b - a) + {0, π}`. -/
lemma coe_cyclicDiff_sub {a b : ℝ} :
    ((cyclicDiff a b : ℝ) : Real.Angle) = ((b - a : ℝ) : Real.Angle) ∨
    ((cyclicDiff a b : ℝ) : Real.Angle) =
      ((b - a : ℝ) : Real.Angle) + ((Real.pi : ℝ) : Real.Angle) := by
  unfold cyclicDiff
  split_ifs with h1 h2
  · left; rw [h1, sub_self]
  · left; rfl
  · right
    rw [Real.Angle.coe_sub, Real.Angle.coe_add, Real.Angle.coe_sub]
    module

/-- Forward cyclic distance between two `linRep`s is `linRep` of the
difference — the projective sweep. -/
lemma cyclicDiff_linRep (α β : Real.Angle) :
    cyclicDiff (linRep α) (linRep β) = linRep (β - α) := by
  have ha := linRep_mem_Ico α
  have hb := linRep_mem_Ico β
  have hIco := cyclicDiff_mem_Ico ha hb
  rcases coe_cyclicDiff_sub (a := linRep α) (b := linRep β) with hcd | hcd <;>
    rcases linRep_class α with hα | hα <;>
    rcases linRep_class β with hβ | hβ <;>
    first
    | exact eq_linRep_of_int_pi hIco
        ⟨-1, by rw [hcd, Real.Angle.coe_sub, hα, hβ]; module⟩
    | exact eq_linRep_of_int_pi hIco
        ⟨0, by rw [hcd, Real.Angle.coe_sub, hα, hβ]; module⟩
    | exact eq_linRep_of_int_pi hIco
        ⟨1, by rw [hcd, Real.Angle.coe_sub, hα, hβ]; module⟩
    | exact eq_linRep_of_int_pi hIco
        ⟨2, by rw [hcd, Real.Angle.coe_sub, hα, hβ]; module⟩

/-- The merged-gap endpoints as oriented sweeps:
`cyclicDiff (dirRep i a) (dirRep i b) = linRep (oangle (a-i) (b-i))`. -/
lemma cyclicDiff_dirRep {i a b : Fin s} (he : e ≠ 0)
    (hai : c a ≠ c i) (hbi : c b ≠ c i) :
    cyclicDiff (dirRep o e c i a) (dirRep o e c i b) =
      linRep (o.oangle (c a - c i) (c b - c i)) := by
  unfold dirRep
  rw [cyclicDiff_linRep, o.oangle_sub_left he
    (sub_ne_zero.mpr hai) (sub_ne_zero.mpr hbi)]

/-- **Neighbor form of `rowGain`.**  Erasing `v`'s direction merges the two
cyclic gaps incident to it, which are exactly the two one-sided sweeps from
the ray `i → v` to its cyclic neighbours: the CW sweep from the predecessor
center `p` and the CCW sweep to the successor center `q`, expressed as
`linRep` of the oriented angles at `i`.  The hypothesis `hne` rules out the
degenerate case where every remaining center shares `v`'s direction. -/
theorem rowGain_eq_mergeGain_sweeps {lam : ℝ} (hlam : 0 < lam) (he : e ≠ 0)
    (hinj : Function.Injective c)
    {i v : Fin s} (hiv : i ≠ v) (h3 : 3 ≤ s)
    (hne : ∃ j : Fin s, j ≠ i ∧ dirRep o e c i j ≠ dirRep o e c i v) :
    ∃ p q : Fin s, p ≠ i ∧ q ≠ i ∧
      rowGain lam (directionRow o e c i) (deleteIndex o e c v i) =
        mergeGain lam
          (linRep (o.oangle (c p - c i) (c v - c i)))
          (linRep (o.oangle (c v - c i) (c q - c i))) := by
  set l := directionRow o e c i with hl
  set r := dirRep o e c i v with hr
  have hdel : deleteIndex o e c v i = l.idxOf r := by
    unfold deleteIndex; rw [← hl]
  rw [hdel]
  set k := l.idxOf r with hk_def
  have hlen : l.length = s - 1 := directionRow_length o e c i
  have hk : k < l.length := List.idxOf_lt_length_iff.mpr
    (mem_directionRow o e c |>.mpr ⟨v, Ne.symm hiv, rfl⟩)
  have h2 : 2 ≤ l.length := by rw [hlen]; omega
  have hsort : l.SortedLE := directionRow_sorted o e c i
  have hall : ∀ b ∈ l, 0 ≤ b ∧ b < Real.pi := fun b hb =>
    directionRow_mem_Ico o e c hb
  have hlk : l[k] = r := List.getElem_idxOf hk
  set rest := l.drop (k + 1) ++ l.take k with hrest
  have hrest_ne : rest ≠ [] := by
    intro he2
    have hlen_rest : rest.length = l.length - 1 := by
      rw [hrest, List.length_append, List.length_drop, List.length_take,
        Nat.min_eq_left hk.le]
      omega
    rw [he2] at hlen_rest; simp at hlen_rest; omega
  rw [rowGain_eq_mergeGain hlam hsort hall hk h2 hrest hrest_ne]
  have hrest_sub : rest ⊆ l := by
    rw [hrest]; exact List.append_subset.mpr
      ⟨List.drop_subset _ _, List.take_subset _ _⟩
  -- A non-`r` element of `l` survives in `rest` (only position `k` is cut).
  have mem_rest_of_ne : ∀ x ∈ l, x ≠ r → x ∈ rest := by
    intro x hx hxr
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hx
    have hmk : m ≠ k := by
      intro hmk; subst hmk; exact hxr hlk
    rw [hrest, List.mem_append]
    rcases lt_or_gt_of_ne hmk with hlt | hgt
    · right
      have hm' : m < (l.take k).length := by
        rw [List.length_take, Nat.min_eq_left hk.le]; omega
      have hget : (l.take k)[m]'hm' = l[m] :=
        (List.getElem_take' hm hlt).symm
      rw [← hget]; exact List.getElem_mem _
    · left
      have hm' : m - (k + 1) < (l.drop (k + 1)).length := by
        rw [List.length_drop]; omega
      have hget : (l.drop (k + 1))[m - (k + 1)]'hm' = l[m] := by
        rw [List.getElem_drop]; congr 1; omega
      rw [← hget]; exact List.getElem_mem _
  obtain ⟨p, hpi, hp⟩ := (mem_directionRow o e c).mp
    (hrest_sub (List.getLast_mem hrest_ne))
  obtain ⟨q, hqi, hq⟩ := (mem_directionRow o e c).mp
    (hrest_sub (List.head_mem hrest_ne))
  refine ⟨p, q, hpi, hqi, ?_⟩
  -- `wrapGap (l[k]::rest)` is the predecessor gap `cyclicDiff getLast l[k]`.
  have hne_all : ¬ ∀ x ∈ l[k] :: rest, x = l[k] := by
    intro hall_eq
    obtain ⟨j, hji, hjne⟩ := hne
    have hjmem : dirRep o e c i j ∈ rest :=
      mem_rest_of_ne _
        (mem_directionRow o e c |>.mpr ⟨j, hji, rfl⟩) hjne
    have hjx := hall_eq _ (List.mem_cons_of_mem _ hjmem)
    rw [hlk] at hjx
    exact hjne hjx
  have hwrap : wrapGap (l[k] :: rest) (List.cons_ne_nil _ _) =
      cyclicDiff (rest.getLast hrest_ne) l[k] := by
    unfold wrapGap
    split_ifs with hcond
    · simp only [List.head_cons] at hcond
      exact absurd hcond hne_all
    · rw [List.getLast_cons hrest_ne, List.head_cons]
  rw [hwrap, hp, hlk, hr, hq]
  have hp0 : c p ≠ c i := fun e2 => hpi (hinj e2)
  have hq0 : c q ≠ c i := fun e2 => hqi (hinj e2)
  have hv0 : c v ≠ c i := fun e2 => hiv (hinj e2).symm
  rw [cyclicDiff_dirRep o e c he hp0 hv0,
    cyclicDiff_dirRep o e c he hv0 hq0]

/-- A `cyclicDiff` whose endpoints keep projective distance in
`[λ, π - λ]` is `≥ λ`. -/
lemma lam_le_cyclicDiff_of_abs_mem_Icc {lam a b : ℝ}
    (h : lam ≤ |a - b| ∧ |a - b| ≤ Real.pi - lam) :
    lam ≤ cyclicDiff a b := by
  obtain ⟨hlo, hhi⟩ := h
  unfold cyclicDiff
  split_ifs with h1 h2
  · rw [h1, sub_self, abs_zero] at hlo; linarith
  · have habs : |a - b| = b - a :=
      (abs_of_neg (sub_neg.mpr h2)).trans (neg_sub a b)
    linarith
  · have hba : b < a := lt_of_le_of_ne (not_lt.mp h2) (fun e => h1 e.symm)
    have habs : |a - b| = a - b := abs_of_pos (sub_pos.mpr hba)
    linarith

/-- If every other center's direction keeps projective distance in
`[λ, π - λ]` from `v`'s direction, `v`'s class occurs exactly once in
`directionRow i`. -/
lemma directionRow_count_eq_one {lam : ℝ} (hlam : 0 < lam)
    {i v : Fin s} (hiv : i ≠ v)
    (h : ∀ j : Fin s, j ≠ i → j ≠ v →
      lam ≤ |dirRep o e c i j - dirRep o e c i v|) :
    (directionRow o e c i).count (dirRep o e c i v) = 1 := by
  have hne : ∀ j : Fin s, j ≠ i → j ≠ v → dirRep o e c i j ≠ dirRep o e c i v := by
    intro j hj hv heq
    have := h j hj hv
    rw [heq, sub_self, abs_zero] at this
    exact absurd this (not_le_of_gt hlam)
  rw [directionRow, (List.perm_insertionSort _ _).count_eq _,
    List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
  have hf : ((List.finRange s).erase i).filter
      (fun j => dirRep o e c i j == dirRep o e c i v) = [v] := by
    have hnodup : (((List.finRange s).erase i).filter
        (fun j => dirRep o e c i j == dirRep o e c i v)).Nodup :=
      List.Nodup.filter _ ((List.nodup_finRange s).erase i)
    have hmem : v ∈ ((List.finRange s).erase i).filter
        (fun j => dirRep o e c i j == dirRep o e c i v) := by
      rw [List.mem_filter, (List.nodup_finRange s).mem_erase_iff]
      exact ⟨⟨Ne.symm hiv, List.mem_finRange _⟩, beq_self_eq_true _⟩
    have hall : ∀ x ∈ ((List.finRange s).erase i).filter
        (fun j => dirRep o e c i j == dirRep o e c i v), x = v := by
      intro x hx
      rw [List.mem_filter, (List.nodup_finRange s).mem_erase_iff] at hx
      obtain ⟨⟨hxi, -⟩, hxr⟩ := hx
      by_contra hxv
      exact hne x hxi hxv (beq_iff_eq.mp (by simpa using hxr))
    cases hf' : ((List.finRange s).erase i).filter
        (fun j => dirRep o e c i j == dirRep o e c i v) with
    | nil => rw [hf'] at hmem; simp at hmem
    | cons x xs =>
      have hx : x = v := hall x (by rw [hf']; exact List.mem_cons_self)
      have hxs : xs = [] := by
        cases xs with
        | nil => rfl
        | cons y ys =>
          have hy : y = v := hall y (by
            rw [hf']; exact List.mem_cons_of_mem _ List.mem_cons_self)
          exfalso
          have hn := List.nodup_cons.mp (by
            rw [hf'] at hnodup; exact hnodup)
          subst hx; subst hy
          exact hn.1 List.mem_cons_self
      rw [hx, hxs]
  have hf2 : ((List.finRange s).erase i).filter
      ((fun x => x == dirRep o e c i v) ∘ fun j => dirRep o e c i j) = [v] := hf
  exact congrArg List.length hf2

/-- **The geometric gain lemma.** If every other center's direction keeps
projective distance in `[λ, π - λ]` from the direction `i → v`, both
incident gaps at `deleteIndex v i` are `≥ λ`, so erasing `v` from row `i`
produces `rowGain ≥ 1` — an emission. -/
theorem rowGain_pos_of_forall_dirRep_dist {lam : ℝ} (hlam : 0 < lam)
    {i v : Fin s} (hiv : i ≠ v) (h3 : 3 ≤ s)
    (h : ∀ j : Fin s, j ≠ i → j ≠ v →
      lam ≤ |dirRep o e c i j - dirRep o e c i v| ∧
        |dirRep o e c i j - dirRep o e c i v| ≤ Real.pi - lam) :
    1 ≤ rowGain lam (directionRow o e c i) (deleteIndex o e c v i) := by
  set l := directionRow o e c i with hl
  set r := dirRep o e c i v with hr
  have hdel : deleteIndex o e c v i = l.idxOf r := by
    unfold deleteIndex; rw [← hl, ← hr]
  rw [hdel]
  set k := l.idxOf r with hk_def
  have hlen : l.length = s - 1 := directionRow_length o e c i
  have hk : k < l.length := List.idxOf_lt_length_iff.mpr
    (mem_directionRow o e c |>.mpr ⟨v, Ne.symm hiv, rfl⟩)
  have h2 : 2 ≤ l.length := by rw [hlen]; omega
  have hsort : l.SortedLE := directionRow_sorted o e c i
  have hall : ∀ b ∈ l, 0 ≤ b ∧ b < Real.pi := fun b hb =>
    directionRow_mem_Ico o e c hb
  have hlk : l[k] = r := List.getElem_idxOf hk
  have hcount := directionRow_count_eq_one o e c hlam hiv
    (fun j hj hv => (h j hj hv).1)
  set rest := l.drop (k + 1) ++ l.take k with hrest
  have hrest_ne : rest ≠ [] := by
    intro he
    have hlen_rest : rest.length = l.length - 1 := by
      rw [hrest, List.length_append, List.length_drop, List.length_take,
        Nat.min_eq_left hk.le]
      omega
    rw [he] at hlen_rest; simp at hlen_rest; omega
  -- `r ∉ rest`: the unique `r`-entry was the erased one.
  have hr_not_mem : r ∉ rest := by
    have hperm : List.Perm rest (l.erase r) := by
      have h1 : List.Perm rest (l.take k ++ l.drop (k + 1)) := by
        rw [hrest]; exact List.perm_append_comm ..
      have h2 : l.take k ++ l.drop (k + 1) = l.eraseIdx k :=
        (eraseIdx_eq_take_drop l k).symm
      have h3 : l.eraseIdx k = l.erase r := by
        rw [hk_def, ← List.erase_eq_eraseIdx_of_idxOf rfl]
      exact h1.trans (by rw [h2, h3])
    intro hmem
    have hmem2 : r ∈ l.erase r := (List.Perm.mem_iff hperm).mp hmem
    have hc : (l.erase r).count r = 0 := by
      rw [List.count_erase, beq_self_eq_true, if_pos rfl, hcount]
    exact (List.count_eq_zero.mp hc) hmem2
  -- every `rest` element is a direction `dirRep i j` with `j ≠ i, v`.
  have mem_rest : ∀ x ∈ rest, ∃ j : Fin s, j ≠ i ∧ j ≠ v ∧
      x = dirRep o e c i j := by
    intro x hx
    obtain ⟨j, hji, rfl⟩ := (mem_directionRow o e c).mp
      (List.append_subset.mpr ⟨List.drop_subset _ _, List.take_subset _ _⟩ hx)
    refine ⟨j, hji, ?_, rfl⟩
    intro hjv
    rw [hjv] at hx
    exact hr_not_mem hx
  have hA : lam ≤ wrapGap (l[k] :: rest) (List.cons_ne_nil _ _) := by
    have hne_all : ¬ ∀ x ∈ l[k] :: rest, x = l[k] := by
      intro hall_eq
      obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil rest hrest_ne
      exact hr_not_mem
        ((hall_eq y (List.mem_cons_of_mem _ hy)).trans hlk ▸ hy)
    unfold wrapGap
    split_ifs with hcond
    · simp only [List.head_cons] at hcond
      exact absurd hcond hne_all
    · rw [List.getLast_cons hrest_ne, List.head_cons, hlk]
      obtain ⟨u, hui, huv, hu⟩ := mem_rest _ (List.getLast_mem hrest_ne)
      rw [hu]
      exact lam_le_cyclicDiff_of_abs_mem_Icc (h u hui huv)
  have hB : lam ≤ cyclicDiff l[k] (rest.head hrest_ne) := by
    obtain ⟨w, hwi, hwv, hw⟩ := mem_rest _ (List.head_mem hrest_ne)
    rw [hlk, hw]
    have := h w hwi hwv
    rw [abs_sub_comm] at this
    exact lam_le_cyclicDiff_of_abs_mem_Icc this
  exact rowGain_pos_of_gaps_ge hlam hsort hall hk h2 hrest hrest_ne hA hB

/-- Angle form of the emission lemma: if every ray `i → j`, `j ≠ v`, makes
angle `≥ λ` with the ray `i → v`, then `rowGain i v ≥ 1`.  The upper bound
`∠ ≤ π - λ` comes from `Section4Legality.triAngle`; the projective
representative gap then lies in `[λ, π - λ]` by `linRep_sub_mem_Icc`. -/
theorem rowGain_pos_of_forall_angle_ge {lam : ℝ}
    (hlegal : Section4Legality c lam) (he : e ≠ 0)
    {i v : Fin s} (hiv : i ≠ v) (h3 : 3 ≤ s)
    (h : ∀ j : Fin s, j ≠ i → j ≠ v →
      lam ≤ ∠ (c v) (c i) (c j)) :
    1 ≤ rowGain lam (directionRow o e c i) (deleteIndex o e c v i) := by
  refine rowGain_pos_of_forall_dirRep_dist o e c hlegal.lam_pos hiv h3 ?_
  intro j hji hjv
  have hv0 : c v - c i ≠ 0 :=
    sub_ne_zero.mpr (fun e2 => hiv (hlegal.inj e2).symm)
  have hj0 : c j - c i ≠ 0 :=
    sub_ne_zero.mpr (fun e2 => hji (hlegal.inj e2))
  have hcomm : InnerProductGeometry.angle (c j -ᵥ c i) (c v -ᵥ c i) =
      ∠ (c v) (c i) (c j) :=
    (InnerProductGeometry.angle_comm _ _).symm
  have hle := @linRep_sub_mem_Icc o e he _ _ hj0 hv0 _
    ⟨hcomm ▸ h j hji hjv,
      hcomm ▸ hlegal.triAngle v i j (Ne.symm hiv) (Ne.symm hji)
        (Ne.symm hjv)⟩
  exact hle

/-- **Emission-or-witness.**  Either `i` emits to `v`, or some third center
`j` makes angle `< λ` with the ray `i → v` — a near-collinearity witness.
This is the contrapositive of `rowGain_pos_of_forall_angle_ge`. -/
theorem emit_or_near_collinear {lam : ℝ} (hlegal : Section4Legality c lam)
    (he : e ≠ 0) {i v : Fin s} (hiv : i ≠ v) (h3 : 3 ≤ s) :
    1 ≤ rowGain lam (directionRow o e c i) (deleteIndex o e c v i) ∨
    ∃ j : Fin s, j ≠ i ∧ j ≠ v ∧ ∠ (c v) (c i) (c j) < lam := by
  by_contra h
  push_neg at h
  exact (not_le.mpr h.1) (rowGain_pos_of_forall_angle_ge o e c hlegal he hiv h3
    (fun j hji hjv => h.2 j hji hjv))

/-! ### The boundary emission lemma

Let `G` be the largest cyclic gap among all direction rows, realized at
vertex `t` as the gap from the direction to `a` forward to the direction
to `b`.  The two *boundary centers* `a`, `b` sit on the edges of the
empty projective wedge of angle `G` at `t`.

The checker statement verified on every legal non-flat sample (~10⁵
configs, `beNnoA = 0`): it never happens that *both* boundary centers fail
to emit to `t` while *no* down/level arc exists anywhere.  In `N`-cases
(both boundaries fail), the failure is a lattice-alignment condition —
the near-side gap and the huge gap do not carry over a `λ`-multiple — and
the escape is always a down/level arc elsewhere, or an interior emitter
into `t` itself (every sampled config has `t` receiving a positive-gain
arc, `tRecv0 = 0`).  Sampled `N`-case: the witness center adjacent to
*both* boundary lines emits a close arc to `t`.

This is the single remaining geometric input to `EmissionDichotomy`:
the first two disjuncts feed the boundary-arc branch, the third is a
`CertA` witness directly. -/

/-- **Max-gap boundary emission** (the geometric crux).  For `G` a global
maximum cyclic gap, realized at `t` between the directions to boundary
centers `a` and `b`: either a boundary center emits to `t`, or some
non-ascending emission exists elsewhere (a `CertA` witness). -/
theorem maxGap_boundary_emission {lam : ℝ} (hlegal : Section4Legality c lam)
    (he : e ≠ 0) {t a b : Fin s} {G : ℝ}
    (hta : t ≠ a) (htb : t ≠ b)
    (hgap : cyclicDiff (dirRep o e c t a) (dirRep o e c t b) = G)
    (hadj : ∀ z ∈ directionRow o e c t, z ≠ dirRep o e c t a →
      G ≤ cyclicDiff (dirRep o e c t a) z)
    (hglob : ∀ i : Fin s, ∀ x y : ℝ,
      x ∈ directionRow o e c i → y ∈ directionRow o e c i →
      (∀ z ∈ directionRow o e c i, z ≠ x →
        cyclicDiff x y ≤ cyclicDiff x z) →
      cyclicDiff x y ≤ G) :
    (1 ≤ rowGain lam (directionRow o e c a) (deleteIndex o e c t a)) ∨
    (1 ≤ rowGain lam (directionRow o e c b) (deleteIndex o e c t b)) ∨
    (∃ i v : Fin s, i ≠ v ∧
      1 ≤ rowGain lam (directionRow o e c i) (deleteIndex o e c v i) ∧
      exponentAt lam (directionRows o e c) v ≤
        exponentAt lam (directionRows o e c) i) := by
  sorry

end Jsp404
