import Jsp000404.Induction
import Jsp000404.GadgetCounterexample
import Jsp000404.Integration

/-!
# Geometry → Skeleton bridge (JSP404-GEOMETRY-SKELETON-BRIDGE-01)

From a `Section4Legality` planar configuration `c : Fin s → Plane₂` with
`⌊π/λ⌋₊ = n`, `lam ≤ π`, and a nonzero chart direction `e`, we build a
`Skeleton s` whose `pos`/`bits`/`q` fields are the *actual* geometric
fan data of `c`:

* `pos x a` = rank of `a` in the sorted `dirRep` order of row `x`
  (self slot filled by a fixed `other x`, see CONTRACT_MAP);
* `bits x a` = whether `dirRep`'s lift of the oriented angle differs by `+π`;
* `q x g` = `⌊gapAfter (directionRow x) g / λ⌋₊` — canonical floor cells;
* `r x g` = `gapAfter g / λ − q g` — the strict remainder `0 ≤ r < 1`;
* `δ = π/λ − n`.

The main theorem `geomSkeleton_modeA` proves `ModeA n sk r δ` — including
the self-slot cases of `ang_le`/`ang_nn` (`x = a`, `x = b`), which reduce
to genuine geometric angles at the substituted index `other x` — and
`bridgeSkeleton_proper` proves `Skeleton.Proper`.  Together with the strict
`δ` bounds this gives `geomSkeleton_consistent`.

The weight correspondence identifies `sk.W n = potential / 2^{n-1}`
(rationals), where `potential` is the deletion-theoretic `Σᵢ 2^{rowScore}`.
No `GadgetSelection`, `CertExists`, or `KraftPacking` hypothesis is used.

The packaging theorem `gadgetSelection_of_selectionP` is *conditional*:
it consumes the (open) selection propositions via the proved soundness
theorems `selection_low_soundP` / `selection_high_soundP`.
-/

namespace Jsp404

open Classical Finset
open scoped EuclideanGeometry EuclideanSpace

noncomputable section

variable {s : ℕ} (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
  (c : Fin s → Plane₂) (lam : ℝ) (n : ℕ)

/-! ### The fan order list -/

/-- The other vertices of `x`, sorted by `dirRep` (non-strict: duplicate
directions keep a consistent but arbitrary relative order — index
injectivity, not strictness, is what `Proper` needs). -/
def fanOrder (x : Fin s) : List (Fin s) :=
  ((List.finRange s).erase x).insertionSort
    (fun a b => dirRep o e c x a ≤ dirRep o e c x b)

theorem fanOrder_perm (x : Fin s) :
    List.Perm (fanOrder o e c x) ((List.finRange s).erase x) :=
  List.perm_insertionSort _ _

theorem fanOrder_nodup (x : Fin s) : (fanOrder o e c x).Nodup :=
  (fanOrder_perm o e c x).nodup_iff.mpr ((List.nodup_finRange s).erase x)

theorem mem_fanOrder {x a : Fin s} :
    a ∈ fanOrder o e c x ↔ a ≠ x := by
  rw [fanOrder, List.mem_insertionSort, (List.nodup_finRange s).mem_erase_iff]
  exact and_iff_left (List.mem_finRange a)

theorem fanOrder_length (x : Fin s) :
    (fanOrder o e c x).length = s - 1 := by
  rw [fanOrder, List.length_insertionSort,
    List.length_erase_of_mem (List.mem_finRange x), List.length_finRange]

/-- The `dirRep`-values of `fanOrder` are sorted. -/
theorem fanOrder_map_sorted (x : Fin s) :
    ((fanOrder o e c x).map (dirRep o e c x)).SortedLE := by
  haveI : Std.Total (fun a b : Fin s =>
      dirRep o e c x a ≤ dirRep o e c x b) :=
    ⟨fun a b => le_total _ _⟩
  haveI : IsTrans (Fin s) (fun a b : Fin s =>
      dirRep o e c x a ≤ dirRep o e c x b) :=
    ⟨fun _ _ _ hab hbc => le_trans hab hbc⟩
  have h : (fanOrder o e c x).Pairwise
      (fun a b => dirRep o e c x a ≤ dirRep o e c x b) :=
    List.pairwise_insertionSort _ _
  rw [List.sortedLE_iff_pairwise]
  exact (List.pairwise_map).mpr h

/-- `fanOrder` evaluated through `dirRep` is exactly `directionRow`:
both are sorted lists on the same multiset. -/
theorem fanOrder_map_eq (x : Fin s) :
    (fanOrder o e c x).map (dirRep o e c x) = directionRow o e c x :=
  List.Perm.eq_of_sortedLE (fanOrder_map_sorted o e c x)
    (directionRow_sorted o e c x)
    (((fanOrder_perm o e c x).map (dirRep o e c x)).trans
      (List.perm_insertionSort _ _).symm)

/-! ### Self-slot substitution -/

/-- A fixed vertex distinct from `x` (exists since `2 ≤ s`); the
geometrically meaningless self slots of `pos`/`bits` are filled with
`other x`'s data, so `angleExpr x x b = angleExpr x (other x) b`
definitionally and self-slot bounds reduce to genuine angles. -/
def other (hs : 2 ≤ s) (x : Fin s) : Fin s :=
  if x.1 = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩

theorem other_ne (hs : 2 ≤ s) (x : Fin s) : other hs x ≠ x := by
  unfold other
  split_ifs with h
  · intro hcon
    have hv := Fin.ext_iff.mp hcon
    simp at hv
    omega
  · intro hcon
    exact h (Fin.ext_iff.mp hcon).symm

/-- `a` if `a ≠ x`, else `other x`: pushes `pos`/`bits` arguments off
the self slot. -/
def selfIdx (hs : 2 ≤ s) (x a : Fin s) : Fin s :=
  if a = x then other hs x else a

theorem selfIdx_ne (hs : 2 ≤ s) (x a : Fin s) : selfIdx hs x a ≠ x := by
  unfold selfIdx
  split_ifs with h
  · exact other_ne hs x
  · exact h

theorem selfIdx_of_ne (hs : 2 ≤ s) {x a : Fin s} (h : a ≠ x) :
    selfIdx hs x a = a := if_neg h

theorem selfIdx_self (hs : 2 ≤ s) (x : Fin s) :
    selfIdx hs x x = other hs x := if_pos rfl

/-! ### The lift bit -/

/-- Whether `dirRep`'s representative of `Θ x j = oangle e (c j − c x)`
is the `+π` class rather than `Θ` itself. -/
def rawBit (x j : Fin s) : Bool :=
  if ((dirRep o e c x j : ℝ) : Real.Angle) =
      o.oangle e (c j - c x) + ((Real.pi : ℝ) : Real.Angle)
  then true else false

/-- `Θ x j` recovered from `dirRep` and the lift bit:
`Θ = ↑d − bit·π`. -/
theorem oangle_eq_dirRep_sub_bit (x j : Fin s) :
    o.oangle e (c j - c x) =
      (dirRep o e c x j : Real.Angle) -
        (((if rawBit o e c x j then (1 : ℝ) else 0) * Real.pi : ℝ) :
          Real.Angle) := by
  rcases linRep_class (o.oangle e (c j - c x)) with h | h
  · -- `↑d = Θ`: the bit is false since `Θ ≠ Θ + π`.
    have hb : rawBit o e c x j = false := by
      apply if_neg
      intro hcon
      have hcon' : ((linRep (o.oangle e (c j - c x)) : ℝ) : Real.Angle) =
          o.oangle e (c j - c x) + (↑Real.pi : Real.Angle) := hcon
      rw [h] at hcon'
      have h0 : (↑Real.pi : Real.Angle) = 0 :=
        add_left_cancel_iff.mp (hcon'.symm.trans (add_zero _).symm)
      exact Real.Angle.pi_ne_zero h0
    rw [hb]
    have h0 : (((if false then (1 : ℝ) else 0) * Real.pi : ℝ) :
        Real.Angle) = 0 := by simp
    rw [h0, sub_zero]
    exact h.symm
  · -- `↑d = Θ + ↑π`: the bit is true.
    have hb : rawBit o e c x j = true := if_pos h
    rw [hb]
    have h1 : (((if true then (1 : ℝ) else 0) * Real.pi : ℝ) :
        Real.Angle) = (↑Real.pi : Real.Angle) := by simp
    rw [h1]
    exact eq_sub_iff_add_eq.mpr h.symm

/-! ### The bridge vertex data -/

/-- The vertex data of center `x`: `pos` is the rank in `fanOrder`,
`bits` the lift bit, `q` the canonical floor cell of each `gapAfter`. -/
def bridgeVtx (hs : 2 ≤ s) (x : Fin s) : VertexData s where
  pos a := ⟨(fanOrder o e c x).idxOf (selfIdx hs x a), by
    have h : (fanOrder o e c x).idxOf (selfIdx hs x a) <
        (fanOrder o e c x).length :=
      List.idxOf_lt_length_iff.mpr
        ((mem_fanOrder o e c).mpr (selfIdx_ne hs x a))
    rwa [fanOrder_length o e c x] at h⟩
  bits a := rawBit o e c x (selfIdx hs x a)
  q g := (⌊gapAfter (directionRow o e c x)
      ⟨g.1, by rw [directionRow_length]; exact g.2⟩ / lam⌋₊ : ℤ)

/-- The geometric skeleton of a legal configuration. -/
def bridgeSkeleton (hs : 2 ≤ s) : Skeleton s :=
  ⟨fun x => bridgeVtx o e c lam hs x⟩

/-- The canonical remainder `r x g = gapAfter g / λ − q g`. -/
def bridgeR (hs : 2 ≤ s) : Fin s → Fin (s - 1) → ℝ :=
  fun x g =>
    gapAfter (directionRow o e c x)
        ⟨g.1, by rw [directionRow_length]; exact g.2⟩ / lam -
      (((bridgeVtx o e c lam hs x).q g : ℤ) : ℝ)

/-- The canonical `δ = π/λ − n`. -/
def bridgeDelta : ℝ := Real.pi / lam - n

/-! ### `pos`/`bits` unfoldings -/

theorem pos_val_eq_idxOf (hs : 2 ≤ s) (x a : Fin s) :
    (((bridgeSkeleton o e c lam hs).vtx x).pos a).val =
      (fanOrder o e c x).idxOf (selfIdx hs x a) :=
  rfl

theorem bits_eq_rawBit (hs : 2 ≤ s) (x a : Fin s) :
    ((bridgeSkeleton o e c lam hs).vtx x).bits a =
      rawBit o e c x (selfIdx hs x a) :=
  rfl

/-- `fanOrder` at position `pos a` is the substituted index. -/
theorem fanOrder_get_pos (hs : 2 ≤ s) (x a : Fin s) :
    (fanOrder o e c x).get
        ⟨(((bridgeSkeleton o e c lam hs).vtx x).pos a).val,
          by rw [fanOrder_length o e c x]; exact Fin.isLt _⟩ =
      selfIdx hs x a :=
  List.getElem_idxOf _

/-- `getElem` transport along a list equality (proof-irrelevant
bounds). -/
theorem getElem_list_eq {l₁ l₂ : List ℝ} (h : l₁ = l₂) (i : ℕ)
    (h1 : i < l₁.length) (h2 : i < l₂.length) :
    l₁[i]'h1 = l₂[i]'h2 := by
  subst h
  rfl

/-- `directionRow` at position `pos a` is `dirRep` of the substituted
index. -/
theorem dirRep_of_pos (hs : 2 ≤ s) (x a : Fin s)
    (i : Fin (directionRow o e c x).length)
    (hi : i.1 = (fanOrder o e c x).idxOf (selfIdx hs x a)) :
    (directionRow o e c x).get i = dirRep o e c x (selfIdx hs x a) := by
  have hlt : (fanOrder o e c x).idxOf (selfIdx hs x a) <
      (fanOrder o e c x).length :=
    List.idxOf_lt_length_iff.mpr
      ((mem_fanOrder o e c).mpr (selfIdx_ne hs x a))
  have hlt2 : (fanOrder o e c x).idxOf (selfIdx hs x a) <
      ((fanOrder o e c x).map (dirRep o e c x)).length := by
    rwa [List.length_map]
  have hm : ((fanOrder o e c x).map (dirRep o e c x))[
      (fanOrder o e c x).idxOf (selfIdx hs x a)]'hlt2 =
      dirRep o e c x (selfIdx hs x a) := by
    rw [List.getElem_map, List.getElem_idxOf hlt]
  have hFi : i = ⟨(fanOrder o e c x).idxOf (selfIdx hs x a), by
      rw [directionRow_length, ← fanOrder_length o e c x];
      exact hlt⟩ :=
    Fin.ext hi
  rw [hFi, List.get_eq_getElem]
  rw [getElem_list_eq (fanOrder_map_eq o e c x).symm _ _ hlt2, hm]

/-! ### `Skeleton.Proper` -/

theorem bridgeSkeleton_proper (hs : 2 ≤ s) :
    (bridgeSkeleton o e c lam hs).Proper := by
  intro v a b ha hb hpos
  have hval := congrArg Fin.val hpos
  rw [pos_val_eq_idxOf, pos_val_eq_idxOf, selfIdx_of_ne hs ha,
    selfIdx_of_ne hs hb] at hval
  exact (List.idxOf_inj
    ((mem_fanOrder o e c).mpr ha)).mp hval

/-! ### Canonical `q`/`r` -/

theorem rowIdx_gapAfter_nonneg (hlam : 0 < lam) (hs : 2 ≤ s) (x : Fin s)
    (g : Fin (s - 1)) :
    0 ≤ gapAfter (directionRow o e c x)
      ⟨g.1, by rw [directionRow_length]; exact g.2⟩ := by
  apply Jsp404.gapAfter_nonneg (directionRow_sorted o e c x)
    (fun y hy => directionRow_mem_Ico o e c hy)
  intro hne
  have := directionRow_length o e c x
  rw [hne] at this
  simp at this
  omega

theorem q_nonneg (x : Fin s) (hs : 2 ≤ s) (g : Fin (s - 1)) :
    0 ≤ ((bridgeSkeleton o e c lam hs).vtx x).q g :=
  Int.natCast_nonneg _

theorem r_nn (hlam : 0 < lam) (hs : 2 ≤ s) (x : Fin s) (g : Fin (s - 1)) :
    0 ≤ bridgeR o e c lam hs x g := by
  show gapAfter (directionRow o e c x)
      ⟨g.1, by rw [directionRow_length]; exact g.2⟩ / lam -
    (⌊gapAfter (directionRow o e c x)
        ⟨g.1, by rw [directionRow_length]; exact g.2⟩ / lam⌋₊ : ℤ) ≥ 0
  have hG := rowIdx_gapAfter_nonneg o e c lam hlam hs x g
  have hd : 0 ≤ gapAfter (directionRow o e c x)
      ⟨g.1, by rw [directionRow_length]; exact g.2⟩ / lam :=
    div_nonneg hG hlam.le
  have h := Nat.floor_le hd
  push_cast at h ⊢
  linarith

theorem r_lt_one (hs : 2 ≤ s) (x : Fin s) (g : Fin (s - 1)) :
    bridgeR o e c lam hs x g < 1 := by
  show gapAfter (directionRow o e c x)
      ⟨g.1, by rw [directionRow_length]; exact g.2⟩ / lam -
    (⌊gapAfter (directionRow o e c x)
        ⟨g.1, by rw [directionRow_length]; exact g.2⟩ / lam⌋₊ : ℤ) < 1
  have h := Nat.lt_floor_add_one (gapAfter (directionRow o e c x)
    ⟨g.1, by rw [directionRow_length]; exact g.2⟩ / lam)
  push_cast at h ⊢
  linarith

/-- `q + r` reconstructs the normalized gap. -/
theorem q_add_r (hs : 2 ≤ s) (x : Fin s) (g : Fin (s - 1)) :
    (((bridgeSkeleton o e c lam hs).vtx x).q g : ℝ) +
        bridgeR o e c lam hs x g =
      gapAfter (directionRow o e c x)
        ⟨g.1, by rw [directionRow_length]; exact g.2⟩ / lam := by
  show ((⌊gapAfter (directionRow o e c x)
        ⟨g.1, by rw [directionRow_length]; exact g.2⟩ / lam⌋₊ : ℤ) : ℝ) +
      (gapAfter (directionRow o e c x)
        ⟨g.1, by rw [directionRow_length]; exact g.2⟩ / lam -
        ((⌊gapAfter (directionRow o e c x)
          ⟨g.1, by rw [directionRow_length]; exact g.2⟩ / lam⌋₊ : ℤ) : ℝ)) =
    gapAfter (directionRow o e c x)
      ⟨g.1, by rw [directionRow_length]; exact g.2⟩ / lam
  ring

/-! ### The fan identity -/

/-- Sum transport: skeleton gap slots index the row gaps, whose cyclic
sum is `π`. -/
theorem sum_gapAfter_eq_pi (hs : 2 ≤ s) (x : Fin s) :
    ∑ g : Fin (s - 1),
        gapAfter (directionRow o e c x)
          ⟨g.1, by rw [directionRow_length]; exact g.2⟩ = Real.pi := by
  have hlen := directionRow_length o e c x
  have hne : directionRow o e c x ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
    omega
  have h := gapAfter_sum (ds := directionRow o e c x) hne
  rw [← h]
  exact Equiv.sum_comp (finCongr hlen.symm)
    (fun j : Fin (directionRow o e c x).length => gapAfter _ j)

/-- `ModeA.fan` for the canonical `q`/`r`/`δ`. -/
theorem fan_eq (hs : 2 ≤ s) (x : Fin s) :
    (∑ g, bridgeR o e c lam hs x g) - bridgeDelta lam n =
      (n : ℝ) -
        ↑(∑ g, ((bridgeSkeleton o e c lam hs).vtx x).q g) := by
  have h1 : ∀ g : Fin (s - 1), bridgeR o e c lam hs x g =
      gapAfter (directionRow o e c x)
          ⟨g.1, by rw [directionRow_length]; exact g.2⟩ / lam -
        ((((bridgeSkeleton o e c lam hs).vtx x).q g : ℤ) : ℝ) :=
    fun _ => rfl
  rw [Finset.sum_congr rfl (fun g _ => h1 g), Finset.sum_sub_distrib,
    ← Finset.sum_div, sum_gapAfter_eq_pi o e c hs x]
  rw [Int.cast_sum]
  unfold bridgeDelta
  ring

/-! ### Interval telescoping -/

/-- Sums over `Finset.Ico` in `Fin m` pull back to `ℕ`-intervals. -/
theorem sum_Ico_fin_eq {m : ℕ} (F : ℕ → ℝ) (p q : Fin m) :
    ∑ g ∈ Finset.Ico p q, F g.1 = ∑ t ∈ Finset.Ico p.1 q.1, F t := by
  have h := Finset.sum_map (Finset.Ico p q) Fin.valEmbedding F
  rw [Fin.map_valEmbedding_Ico] at h
  exact h.symm

/-- Telescoping `gapAfter` over a `ℕ`-interval below `l.length`: no wrap
gap occurs, so the sum is the endpoint difference. -/
theorem sum_Ico_gapAfter {l : List ℝ} {i j : ℕ} (hij : i ≤ j)
    (hj : j < l.length) :
    ∑ t ∈ Finset.Ico i j,
        (if h : t < l.length then gapAfter l ⟨t, h⟩ else 0) =
      l.get ⟨j, hj⟩ - l.get ⟨i, lt_of_le_of_lt hij hj⟩ := by
  set g : ℕ → ℝ := fun t => if h : t < l.length then l.get ⟨t, h⟩ else 0
    with hg
  have hterm : ∀ t ∈ Finset.Ico i j,
      (if h : t < l.length then gapAfter l ⟨t, h⟩ else 0) =
        g (t + 1) - g t := by
    intro t ht
    rw [Finset.mem_Ico] at ht
    have ht1 : t + 1 < l.length := by omega
    have htt : t < l.length := by omega
    rw [dif_pos htt]
    unfold gapAfter
    rw [dif_pos ht1]
    rw [hg]
    simp only [dif_pos ht1, dif_pos htt]
  rw [Finset.sum_congr rfl hterm, Finset.sum_Ico_sub g hij]
  have hgi : g i = l.get ⟨i, lt_of_le_of_lt hij hj⟩ := dif_pos _
  have hgj : g j = l.get ⟨j, hj⟩ := dif_pos _
  rw [hgi, hgj]

/-- The arc gap sum: `∑_{g ∈ arc a b} gapAfter = |d_{b'} − d_{a'}|`. -/
theorem arc_gapAfter (hs : 2 ≤ s) (x a b : Fin s) :
    ∑ g ∈ ((bridgeSkeleton o e c lam hs).vtx x).arc a b,
        gapAfter (directionRow o e c x)
          ⟨g.1, by rw [directionRow_length]; exact g.2⟩ =
      |dirRep o e c x (selfIdx hs x b) - dirRep o e c x (selfIdx hs x a)| := by
  have hlen : (directionRow o e c x).length = s - 1 :=
    directionRow_length o e c x
  have key : ∀ g : Fin (s - 1),
      (g : ℕ) < (directionRow o e c x).length :=
    fun g => by rw [directionRow_length]; exact g.2
  have hconv : ∀ g : Fin (s - 1),
      gapAfter (directionRow o e c x)
          ⟨g.1, by rw [directionRow_length]; exact g.2⟩ =
        (if h : g.1 < (directionRow o e c x).length then
          gapAfter (directionRow o e c x) ⟨g.1, h⟩ else 0) :=
    fun g => by rw [dif_pos (key g)]
  unfold VertexData.arc
  rcases le_total (((bridgeSkeleton o e c lam hs).vtx x).pos a)
      (((bridgeSkeleton o e c lam hs).vtx x).pos b) with hpq | hpq
  · rw [inf_eq_left.mpr hpq, sup_eq_right.mpr hpq]
    rw [Finset.sum_congr rfl (fun g _ => hconv g),
      sum_Ico_fin_eq (fun t => if h : t < (directionRow o e c x).length then
        gapAfter (directionRow o e c x) ⟨t, h⟩ else 0)]
    have hlt : (((bridgeSkeleton o e c lam hs).vtx x).pos b).1 <
        (directionRow o e c x).length := by
      rw [hlen]; exact Fin.isLt _
    rw [sum_Ico_gapAfter hpq hlt]
    rw [dirRep_of_pos o e c hs x b ⟨_, hlt⟩
        (pos_val_eq_idxOf o e c lam hs x b),
      dirRep_of_pos o e c hs x a ⟨_, lt_of_le_of_lt hpq hlt⟩
        (pos_val_eq_idxOf o e c lam hs x a)]
    have hle : dirRep o e c x (selfIdx hs x a) ≤
        dirRep o e c x (selfIdx hs x b) := by
      have ea := dirRep_of_pos o e c hs x a
        ⟨_, lt_of_le_of_lt hpq hlt⟩
        (pos_val_eq_idxOf o e c lam hs x a)
      have eb := dirRep_of_pos o e c hs x b ⟨_, hlt⟩
        (pos_val_eq_idxOf o e c lam hs x b)
      rw [← ea, ← eb]
      exact getElem_mono_of_sortedLE (directionRow_sorted o e c x) hpq hlt
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
  · rw [inf_eq_right.mpr hpq, sup_eq_left.mpr hpq]
    rw [Finset.sum_congr rfl (fun g _ => hconv g),
      sum_Ico_fin_eq (fun t => if h : t < (directionRow o e c x).length then
        gapAfter (directionRow o e c x) ⟨t, h⟩ else 0)]
    have hlt : (((bridgeSkeleton o e c lam hs).vtx x).pos a).1 <
        (directionRow o e c x).length := by
      rw [hlen]; exact Fin.isLt _
    rw [sum_Ico_gapAfter hpq hlt]
    rw [dirRep_of_pos o e c hs x a ⟨_, hlt⟩
        (pos_val_eq_idxOf o e c lam hs x a),
      dirRep_of_pos o e c hs x b ⟨_, lt_of_le_of_lt hpq hlt⟩
        (pos_val_eq_idxOf o e c lam hs x b)]
    have hle : dirRep o e c x (selfIdx hs x b) ≤
        dirRep o e c x (selfIdx hs x a) := by
      have eb := dirRep_of_pos o e c hs x b
        ⟨_, lt_of_le_of_lt hpq hlt⟩
        (pos_val_eq_idxOf o e c lam hs x b)
      have ea := dirRep_of_pos o e c hs x a ⟨_, hlt⟩
        (pos_val_eq_idxOf o e c lam hs x a)
      rw [← eb, ← ea]
      exact getElem_mono_of_sortedLE (directionRow_sorted o e c x) hpq hlt
    rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]

/-- `Σ_arc (q + r)` is `|d_{b'} − d_{a'}| / λ`. -/
theorem arcSum_qr (hs : 2 ≤ s) (x a b : Fin s) :
    ∑ g ∈ ((bridgeSkeleton o e c lam hs).vtx x).arc a b,
        ((((bridgeSkeleton o e c lam hs).vtx x).q g : ℝ) +
          bridgeR o e c lam hs x g) =
      |dirRep o e c x (selfIdx hs x b) - dirRep o e c x (selfIdx hs x a)| /
        lam := by
  rw [Finset.sum_congr rfl (fun g _ => q_add_r o e c lam hs x g)]
  rw [← Finset.sum_div, arc_gapAfter o e c lam hs]

/-! ### The angle correspondence -/

/-- `|toReal ↑(x − π)| = π − |x|` for `x ∈ (−π, π)`. -/
theorem abs_toReal_coe_sub_pi {x : ℝ} (hx1 : -Real.pi < x)
    (hx2 : x < Real.pi) :
    |((x - Real.pi : ℝ) : Real.Angle).toReal| = Real.pi - |x| := by
  rw [Real.Angle.toReal_coe]
  by_cases hx : 0 < x
  · rw [(toIocMod_eq_self Real.two_pi_pos).mpr
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
      abs_of_nonpos (by linarith), abs_of_pos hx]
    ring
  · push_neg at hx
    have h1 : x - Real.pi = x + Real.pi - (1 : ℤ) • (2 * Real.pi) := by
      rw [one_zsmul]; ring
    rw [h1, toIocMod_sub_zsmul,
      (toIocMod_eq_self Real.two_pi_pos).mpr
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
      abs_of_nonneg (by linarith), abs_of_nonpos hx]
    ring

/-- The oriented sweep `a' → b'` at `x` as a real lift: the `dirRep`
difference corrected by the lift bits. -/
theorem oangle_sub_eq_dirRep (hs : 2 ≤ s) (he : e ≠ 0)
    (hinj : Function.Injective c) (x a b : Fin s) :
    o.oangle (c (selfIdx hs x a) - c x) (c (selfIdx hs x b) - c x) =
      ((dirRep o e c x (selfIdx hs x b) - dirRep o e c x (selfIdx hs x a)) +
        (((if rawBit o e c x (selfIdx hs x a) then (1 : ℝ) else 0) -
          (if rawBit o e c x (selfIdx hs x b) then (1 : ℝ) else 0)) *
          Real.pi : ℝ) : Real.Angle) := by
  have ha' : c (selfIdx hs x a) - c x ≠ 0 :=
    sub_ne_zero.mpr (hinj.ne (selfIdx_ne hs x a))
  have hb' : c (selfIdx hs x b) - c x ≠ 0 :=
    sub_ne_zero.mpr (hinj.ne (selfIdx_ne hs x b))
  rw [← o.oangle_sub_left he ha' hb',
    oangle_eq_dirRep_sub_bit o e c x (selfIdx hs x b),
    oangle_eq_dirRep_sub_bit o e c x (selfIdx hs x a)]
  simp only [← Real.Angle.coe_sub]
  congr 1
  ring

/-- The geometric angle equals `|d_b' − d_a'|` when the lift bits agree
and `π − |d_b' − d_a'|` otherwise — exactly the `angleExpr` cases. -/
theorem angle_eq_dirRep (hs : 2 ≤ s) (he : e ≠ 0)
    (hinj : Function.Injective c) (x a b : Fin s) :
    ∠ (c (selfIdx hs x a)) (c x) (c (selfIdx hs x b)) =
      if rawBit o e c x (selfIdx hs x a) =
          rawBit o e c x (selfIdx hs x b)
      then |dirRep o e c x (selfIdx hs x b) -
          dirRep o e c x (selfIdx hs x a)|
      else Real.pi - |dirRep o e c x (selfIdx hs x b) -
          dirRep o e c x (selfIdx hs x a)| := by
  have ha' : c (selfIdx hs x a) - c x ≠ 0 :=
    sub_ne_zero.mpr (hinj.ne (selfIdx_ne hs x a))
  have hb' : c (selfIdx hs x b) - c x ≠ 0 :=
    sub_ne_zero.mpr (hinj.ne (selfIdx_ne hs x b))
  have hangle : ∠ (c (selfIdx hs x a)) (c x) (c (selfIdx hs x b)) =
      |(o.oangle (c (selfIdx hs x a) - c x)
        (c (selfIdx hs x b) - c x)).toReal| := by
    show InnerProductGeometry.angle _ _ = _
    rw [vsub_eq_sub, vsub_eq_sub]
    exact o.angle_eq_abs_oangle_toReal ha' hb'
  rw [hangle, oangle_sub_eq_dirRep o e c hs he hinj x a b,
    ← Real.Angle.coe_sub, ← Real.Angle.coe_add]
  have hDa0 : 0 ≤ dirRep o e c x (selfIdx hs x a) := (linRep_mem_Ico _).1
  have hDa1 : dirRep o e c x (selfIdx hs x a) < Real.pi := (linRep_mem_Ico _).2
  have hDb0 : 0 ≤ dirRep o e c x (selfIdx hs x b) := (linRep_mem_Ico _).1
  have hDb1 : dirRep o e c x (selfIdx hs x b) < Real.pi := (linRep_mem_Ico _).2
  set D := dirRep o e c x (selfIdx hs x b) - dirRep o e c x (selfIdx hs x a)
    with hD
  have hD1 : -Real.pi < D := by rw [hD]; linarith
  have hD2 : D < Real.pi := by rw [hD]; linarith
  by_cases hbit : rawBit o e c x (selfIdx hs x a) =
      rawBit o e c x (selfIdx hs x b)
  · rw [if_pos hbit]
    have h0 : (if rawBit o e c x (selfIdx hs x a) then (1 : ℝ) else 0) -
        (if rawBit o e c x (selfIdx hs x b) then (1 : ℝ) else 0) = 0 := by
      rw [hbit, sub_self]
    have hE : (↑(D + ((if rawBit o e c x (selfIdx hs x a) then (1 : ℝ) else 0) -
        (if rawBit o e c x (selfIdx hs x b) then (1 : ℝ) else 0)) *
          Real.pi) : Real.Angle) = (↑D : Real.Angle) := by
      congr 1
      rw [h0]
      ring
    rw [hE, Real.Angle.toReal_coe,
      (toIocMod_eq_self Real.two_pi_pos).mpr ⟨hD1, by linarith⟩]
  · rw [if_neg hbit]
    cases hb1 : rawBit o e c x (selfIdx hs x a) <;>
      cases hb2 : rawBit o e c x (selfIdx hs x b)
    · exact absurd (hb1.trans hb2.symm) hbit
    · have hE : (↑(D + ((if false then (1 : ℝ) else 0) -
          (if true then (1 : ℝ) else 0)) * Real.pi) : Real.Angle) =
          ↑(D - Real.pi) := by
        congr 1
        show D + ((0 : ℝ) - 1) * Real.pi = D - Real.pi
        ring
      rw [hE]
      exact abs_toReal_coe_sub_pi hD1 hD2
    · have hE : (↑(D + ((if true then (1 : ℝ) else 0) -
          (if false then (1 : ℝ) else 0)) * Real.pi) : Real.Angle) =
          ↑(D - Real.pi) := by
        rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub]
        refine ⟨1, ?_⟩
        show D + ((1 : ℝ) - 0) * Real.pi - (D - Real.pi) =
          2 * Real.pi * ((1 : ℤ) : ℝ)
        push_cast
        ring
      rw [hE]
      exact abs_toReal_coe_sub_pi hD1 hD2
    · exact absurd (hb1.trans hb2.symm) hbit

/-- The main correspondence: `angleExpr` equals the actual geometric
angle divided by `λ`, for *all* `a b` (self slots included — they fall
back to the substituted `other x` index). -/
theorem angleExpr_eq (hs : 2 ≤ s) (he : e ≠ 0)
    (hinj : Function.Injective c) (x a b : Fin s) :
    angleExpr n (bridgeSkeleton o e c lam hs) (bridgeR o e c lam hs)
        (bridgeDelta lam n) x a b =
      ∠ (c (selfIdx hs x a)) (c x) (c (selfIdx hs x b)) / lam := by
  unfold angleExpr
  rw [bits_eq_rawBit, bits_eq_rawBit, arcSum_qr o e c lam hs,
    angle_eq_dirRep o e c hs he hinj]
  split_ifs with h
  · rfl
  · rw [sub_div]
    unfold bridgeDelta
    ring

/-- When the substituted indices coincide, the arc is empty and the
expression vanishes. -/
theorem angleExpr_eq_zero_of_selfIdx_eq (hs : 2 ≤ s) {x a b : Fin s}
    (h : selfIdx hs x a = selfIdx hs x b) :
    angleExpr n (bridgeSkeleton o e c lam hs) (bridgeR o e c lam hs)
        (bridgeDelta lam n) x a b = 0 := by
  unfold angleExpr
  rw [bits_eq_rawBit, bits_eq_rawBit]
  have hpos : ((bridgeSkeleton o e c lam hs).vtx x).pos a =
      ((bridgeSkeleton o e c lam hs).vtx x).pos b := by
    apply Fin.ext
    rw [pos_val_eq_idxOf, pos_val_eq_idxOf, h]
  have harc : ((bridgeSkeleton o e c lam hs).vtx x).arc a b = ∅ := by
    unfold VertexData.arc
    rw [hpos, inf_idem, sup_idem, Finset.Ico_self]
  rw [harc, Finset.sum_empty]
  split_ifs with hbit
  · rfl
  · exfalso
    rw [h] at hbit
    exact hbit rfl

/-! ### `ModeA` -/

/-- The bridge skeleton satisfies `ModeA` under the strip hypotheses
`lam ≤ π` and `⌊π/λ⌋₊ = n`. -/
theorem geomSkeleton_modeA (hs : 2 ≤ s) (he : e ≠ 0)
    (hleg : Section4Legality c lam) (hlam_pi : lam ≤ Real.pi)
    (hn : ⌊Real.pi / lam⌋₊ = n) :
    ModeA n (bridgeSkeleton o e c lam hs) (bridgeR o e c lam hs)
      (bridgeDelta lam n) := by
  have hlam := hleg.lam_pos
  have hn1 : 1 ≤ n := by
    have h1 : (1 : ℝ) ≤ Real.pi / lam := by
      rw [one_le_div hlam]; exact hlam_pi
    have := Nat.floor_mono h1
    rw [Nat.floor_one, hn] at this
    exact this
  have hδ0 : 0 ≤ bridgeDelta lam n := by
    unfold bridgeDelta
    rw [sub_nonneg, ← hn]
    exact Nat.floor_le (div_nonneg Real.pi_nonneg hlam.le)
  have hdelta : (n : ℝ) + bridgeDelta lam n = Real.pi / lam := by
    unfold bridgeDelta; ring
  refine ⟨fun v g => r_nn o e c lam hlam hs v g,
    fun v g => (r_lt_one o e c lam hs v g).le,
    fun v => fan_eq o e c lam n hs v, ?_, ?_, ?_⟩
  · intro a b h hab hah hbh
    rw [angleExpr_eq o e c lam n hs he hleg.inj a b h,
      angleExpr_eq o e c lam n hs he hleg.inj b a h,
      angleExpr_eq o e c lam n hs he hleg.inj h a b,
      selfIdx_of_ne hs (Ne.symm hab), selfIdx_of_ne hs (Ne.symm hah),
      selfIdx_of_ne hs hab, selfIdx_of_ne hs (Ne.symm hbh),
      selfIdx_of_ne hs hah, selfIdx_of_ne hs hbh, hdelta,
      ← add_div, ← add_div]
    have hsum : ∠ (c b) (c a) (c h) + ∠ (c a) (c h) (c b) +
        ∠ (c h) (c b) (c a) = Real.pi :=
      EuclideanGeometry.angle_add_angle_add_angle_eq_pi (c h)
        (hleg.inj.ne hab)
    rw [EuclideanGeometry.angle_comm (c h) (c b) (c a)] at hsum
    rw [div_eq_iff (ne_of_gt hlam), div_mul_cancel₀ _ (ne_of_gt hlam)]
    linarith [hsum]
  · intro x a b hab
    by_cases hself : selfIdx hs x a = selfIdx hs x b
    · rw [angleExpr_eq_zero_of_selfIdx_eq o e c lam n hs hself]
      have hn1r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      linarith [hδ0]
    · rw [angleExpr_eq o e c lam n hs he hleg.inj x a b]
      have htri := hleg.triAngle (selfIdx hs x a) x (selfIdx hs x b)
        (selfIdx_ne hs x a) (Ne.symm (selfIdx_ne hs x b)) hself
      have hdiv : ∠ (c (selfIdx hs x a)) (c x) (c (selfIdx hs x b)) /
          lam ≤ (Real.pi - lam) / lam := by
        rw [div_le_iff₀ hlam, div_mul_cancel₀ _ (ne_of_gt hlam)]
        exact htri
      have hd2 : (Real.pi - lam) / lam = Real.pi / lam - 1 := by
        rw [sub_div, div_self (ne_of_gt hlam)]
      rw [hd2] at hdiv
      have hn1r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      linarith [hdelta]
  · intro x a b hab
    rw [angleExpr_eq o e c lam n hs he hleg.inj x a b]
    exact div_nonneg (EuclideanGeometry.angle_nonneg _ _ _) hlam.le

/-- Consistency of the bridge skeleton: the strip δ lives in `[0, 1)`
and `ModeA` holds. -/
theorem geomSkeleton_consistent (hs : 2 ≤ s) (he : e ≠ 0)
    (hleg : Section4Legality c lam) (hlam_pi : lam ≤ Real.pi)
    (hn : ⌊Real.pi / lam⌋₊ = n) :
    (bridgeSkeleton o e c lam hs).Consistent n := by
  refine ⟨bridgeR o e c lam hs, bridgeDelta lam n, ?_, ?_,
    geomSkeleton_modeA o e c lam n hs he hleg hlam_pi hn⟩
  · unfold bridgeDelta
    rw [sub_nonneg, ← hn]
    exact Nat.floor_le (div_nonneg Real.pi_nonneg hleg.lam_pos.le)
  · unfold bridgeDelta
    rw [← hn]
    linarith [Nat.lt_floor_add_one (Real.pi / lam)]

/-! ### Exponents, defect, weight -/

/-- `max (↑m − 1) 0 = ↑(m − 1)` on `ℤ`/`ℕ`. -/
theorem int_max_coe_sub_one (m : ℕ) :
    max ((m : ℤ) - 1) 0 = ((m - 1 : ℕ) : ℤ) := by
  rcases Nat.eq_zero_or_pos m with h | h
  · rw [h]; simp
  · have hm : (m : ℤ) - 1 = ((m - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub h, Nat.cast_one]
    have h0 : (0 : ℤ) ≤ (m : ℤ) - 1 := by
      rw [hm]; exact Int.natCast_nonneg _
    rw [← hm, max_eq_left h0]

/-- The gadget exponent `kexp` is the geometric row score. -/
theorem bridgeVtx_kexp (hs : 2 ≤ s) (x : Fin s) :
    ((bridgeSkeleton o e c lam hs).vtx x).kexp =
      (rowScore lam (directionRow o e c x) : ℤ) := by
  unfold VertexData.kexp
  have hterm : ∀ g : Fin (s - 1),
      max (((bridgeSkeleton o e c lam hs).vtx x).q g - 1) 0 =
        ((⌊gapAfter (directionRow o e c x)
            ⟨g.1, by rw [directionRow_length]; exact g.2⟩ / lam⌋₊ - 1 : ℕ) :
          ℤ) :=
    fun g => int_max_coe_sub_one _
  rw [Finset.sum_congr rfl (fun g _ => hterm g), ← Nat.cast_sum]
  congr 1
  rw [← exponents_entry_eq_rowScore (directionRow_sorted o e c x)]
  exact Equiv.sum_comp (finCongr (directionRow_length o e c x).symm)
    (fun j : Fin (directionRow o e c x).length =>
      ⌊gapAfter (directionRow o e c x) j / lam⌋₊ - 1)

/-- The gadget defect `d` is the geometric `rowDefect − 1`. -/
theorem bridgeSkeleton_d (hlam : 0 < lam) (hs : 2 ≤ s)
    (hn : ⌊Real.pi / lam⌋₊ = n) (x : Fin s) :
    (bridgeSkeleton o e c lam hs).d n x =
      (rowDefect n lam (directionRow o e c x) : ℤ) - 1 := by
  unfold Skeleton.d
  rw [bridgeVtx_kexp o e c lam hs x]
  have hcells := rowCells_directionRow_le_of_floor_eq o e c hlam x hs hn
  have hsc := rowScore_eq_sub_defect lam hlam n _ hcells
  have hcle := rowDefect_le lam hlam n _ hcells
  rw [hsc, Nat.cast_sub hcle]
  ring

/-- The gadget weight `W` is the geometric potential normalized by
`2^{n−1}` — the exact `W/K` factor. -/
theorem bridgeSkeleton_W (hlam : 0 < lam) (hs : 2 ≤ s)
    (hn : ⌊Real.pi / lam⌋₊ = n) (hn1 : 1 ≤ n) :
    (bridgeSkeleton o e c lam hs).W n =
      ((potential lam (directionRows o e c) : ℕ) : ℚ) / (2 : ℚ) ^ (n - 1) := by
  have h1 : ∀ v : Fin s,
      (2 : ℚ) ^ (-((bridgeSkeleton o e c lam hs).d n v)) =
        ((2 : ℚ) ^ rowScore lam (directionRow o e c v)) /
          (2 : ℚ) ^ (n - 1) := by
    intro v
    rw [bridgeSkeleton_d o e c lam n hlam hs hn v]
    have hcells := rowCells_directionRow_le_of_floor_eq o e c hlam v hs hn
    have hsc := rowScore_eq_sub_defect lam hlam n _ hcells
    have hcle := rowDefect_le lam hlam n _ hcells
    have hexp : -(((rowDefect n lam (directionRow o e c v) : ℕ) : ℤ) - 1) =
        ((rowScore lam (directionRow o e c v) : ℕ) : ℤ) -
          ((n - 1 : ℕ) : ℤ) := by
      rw [hsc, Nat.cast_sub hcle, Nat.cast_sub hn1, Nat.cast_one]
      ring
    rw [hexp,
      zpow_natCast_sub_natCast₀ (show (2 : ℚ) ≠ 0 by norm_num)]
  have h2 : (bridgeSkeleton o e c lam hs).W n =
      ∑ v : Fin s, ((2 : ℚ) ^ rowScore lam (directionRow o e c v)) /
        (2 : ℚ) ^ (n - 1) := by
    unfold Skeleton.W
    exact Finset.sum_congr rfl (fun v _ => h1 v)
  rw [h2, ← Finset.sum_div]
  congr 1
  unfold potential exponentAt directionRows
  rw [Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Nat.cast_pow, Nat.cast_ofNat]

/-! ### Packaging -/

/-- If both selection propositions hold (for all sizes and tree
depths), the geometry-to-skeleton bridge produces the `GadgetSelection`
fields — the geometric bound `Σ 2^{score} ≤ cap` follows from the
gadget bound on `W` via the weight correspondence. -/
theorem gadgetSelection_of_selectionP
    (hlow : ∀ s n, GadgetSelectionLowP s n)
    (hhigh : ∀ s n, GadgetSelectionHighP s n) :
    GadgetSelection := by
  constructor
  · intro V o' e' lam' n' he' hlam' hleg' hN' hn' hδ'
    have hs2 : 2 ≤ V.forest.length := V.forest_len
    have hn1 : 1 ≤ n' := by
      have h1 : (1 : ℝ) ≤ Real.pi / lam' := by
        rw [one_le_div hleg'.lam_pos]; exact hlam'
      have := Nat.floor_mono h1
      rw [Nat.floor_one, hn'] at this
      exact this
    have hproper := bridgeSkeleton_proper o' e'
      (fun i : Fin V.forest.length => (V.forest.get i).centerOf) lam' hs2
    have hmodeA := geomSkeleton_modeA o' e'
      (fun i : Fin V.forest.length => (V.forest.get i).centerOf)
      lam' n' hs2 he' hleg' hlam' hn'
    have hδ0 : 0 ≤ bridgeDelta lam' n' := by
      unfold bridgeDelta
      rw [sub_nonneg, ← hn']
      exact Nat.floor_le (div_nonneg Real.pi_nonneg hleg'.lam_pos.le)
    have hδ1 : bridgeDelta lam' n' < 1 := by
      unfold bridgeDelta
      rw [← hn']
      linarith [Nat.lt_floor_add_one (Real.pi / lam')]
    have hWid := bridgeSkeleton_W o' e'
      (fun i : Fin V.forest.length => (V.forest.get i).centerOf)
      lam' n' hleg'.lam_pos hs2 hn' hn1
    rw [exponents_map_pow_sum V o' e' lam' hN']
    by_cases hW : (2 : ℚ) <
        (bridgeSkeleton o' e'
          (fun i : Fin V.forest.length => (V.forest.get i).centerOf)
          lam' hs2).W n'
    · exfalso
      have hsnd := selection_low_soundP (hlow _ n') hproper hmodeA hδ0 hδ1 hW
      unfold bridgeDelta at hsnd
      linarith
    · push_neg at hW
      rw [hWid] at hW
      have hpot : ((potential lam' (directionRows o' e'
          (fun i : Fin V.forest.length => (V.forest.get i).centerOf)) : ℕ) : ℚ) ≤
          (2 : ℚ) ^ n' := by
        rw [div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ (n' - 1))] at hW
        calc _ ≤ 2 * 2 ^ (n' - 1) := hW
          _ = 2 ^ n' := by rw [← pow_succ', Nat.sub_add_cancel hn1]
      exact_mod_cast hpot
  · intro V o' e' lam' n' he' hlam' hleg' hN' hn' hδ'
    have hs2 : 2 ≤ V.forest.length := V.forest_len
    have hn1 : 1 ≤ n' := by
      have h1 : (1 : ℝ) ≤ Real.pi / lam' := by
        rw [one_le_div hleg'.lam_pos]; exact hlam'
      have := Nat.floor_mono h1
      rw [Nat.floor_one, hn'] at this
      exact this
    have hproper := bridgeSkeleton_proper o' e'
      (fun i : Fin V.forest.length => (V.forest.get i).centerOf) lam' hs2
    have hmodeA := geomSkeleton_modeA o' e'
      (fun i : Fin V.forest.length => (V.forest.get i).centerOf)
      lam' n' hs2 he' hleg' hlam' hn'
    have hδ0 : 0 ≤ bridgeDelta lam' n' := by
      unfold bridgeDelta
      rw [sub_nonneg, ← hn']
      exact Nat.floor_le (div_nonneg Real.pi_nonneg hleg'.lam_pos.le)
    have hδ1 : bridgeDelta lam' n' < 1 := by
      unfold bridgeDelta
      rw [← hn']
      linarith [Nat.lt_floor_add_one (Real.pi / lam')]
    have hWid := bridgeSkeleton_W o' e'
      (fun i : Fin V.forest.length => (V.forest.get i).centerOf)
      lam' n' hleg'.lam_pos hs2 hn' hn1
    rw [exponents_map_pow_sum V o' e' lam' hN']
    by_cases hW : ((5 : ℚ) / 2) <
        (bridgeSkeleton o' e'
          (fun i : Fin V.forest.length => (V.forest.get i).centerOf)
          lam' hs2).W n'
    · exfalso
      have hsnd := selection_high_soundP (hhigh _ n') hproper hmodeA hδ0
        hδ1 hW
      unfold bridgeDelta at hsnd
      linarith
    · push_neg at hW
      rw [hWid] at hW
      have hcap : (5 : ℚ) / 2 * 2 ^ (n' - 1) ≤ 2 ^ n' + 2 ^ (n' - 2) := by
        rcases Nat.eq_or_lt_of_le hn1 with hn1' | hn2
        · subst hn1'
          norm_num
        · have hA : (2 : ℚ) ^ n' = (2 : ℚ) ^ (n' - 2) * 4 := by
            conv_lhs => rw [show n' = (n' - 2) + 2 from by omega]
            rw [pow_add]
            norm_num
          have hB : (2 : ℚ) ^ (n' - 1) = (2 : ℚ) ^ (n' - 2) * 2 := by
            conv_lhs => rw [show n' - 1 = (n' - 2) + 1 from by omega]
            rw [pow_succ]
          rw [hA, hB]
          have hnn : (0 : ℚ) ≤ 2 ^ (n' - 2) := by positivity
          linarith
      have hpot : ((potential lam' (directionRows o' e'
          (fun i : Fin V.forest.length => (V.forest.get i).centerOf)) : ℕ) : ℚ) ≤
          2 ^ n' + 2 ^ (n' - 2) := by
        rw [div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ (n' - 1))] at hW
        exact hW.trans hcap
      exact_mod_cast hpot

end

end Jsp404
