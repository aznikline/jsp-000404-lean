import Jsp000404.WingBound
import Jsp000404.CrossCircle

/-!
# Lemma 3.7 — the per-circle point bound

For a range-1 circle `C` of a GC `V` all of whose generalized angles are
at most `π - lam`, every generalized direction `GD p p'` of two points
inside `C` stays at line-distance `≥ lam` from every center line `o_i o_j`
(two orderings of `GA` give `angle(GD, o_j - o_i) ∈ [lam, π - lam]`).

Covering the gaps between consecutive center-line directions (mod `π`)
by consecutive wings of width `lam`, the wing-sector partition bound
gives `N_i ≤ 2^{k'(i)}` with `k'(i) = Σ_j (⌊g_j / lam⌋ - 1)₊`, the
`uψ/2`-formula of Sendov (3.10) in radians.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

/-- Representative of the line class of a directed angle in `[0, π)`. -/
noncomputable def linRep (d : Real.Angle) : ℝ :=
  if d.toReal < 0 then d.toReal + Real.pi
  else if d.toReal = Real.pi then 0 else d.toReal

lemma linRep_mem_Ico (d : Real.Angle) : linRep d ∈ Set.Ico 0 Real.pi := by
  have h := d.toReal_mem_Ioc
  unfold linRep
  by_cases h1 : d.toReal < 0
  · rw [if_pos h1]
    constructor <;> linarith [Real.pi_pos, h.1, h.2]
  · rw [if_neg h1]
    by_cases h2 : d.toReal = Real.pi
    · rw [if_pos h2]
      exact ⟨le_refl _, Real.pi_pos⟩
    · rw [if_neg h2]
      exact ⟨by linarith, lt_of_le_of_ne h.2 h2⟩

/-- The representative lies in the same line class (mod `π`). -/
lemma linRep_class (d : Real.Angle) :
    ((linRep d : ℝ) : Real.Angle) = d ∨
    ((linRep d : ℝ) : Real.Angle) = d + Real.pi := by
  unfold linRep
  by_cases h1 : d.toReal < 0
  · right
    rw [if_pos h1, Real.Angle.coe_add, Real.Angle.coe_toReal]
  · rw [if_neg h1]
    by_cases h2 : d.toReal = Real.pi
    · right
      rw [if_pos h2]
      have hd : d = ((Real.pi : ℝ) : Real.Angle) := by
        rw [← Real.Angle.coe_toReal d, h2]
      rw [hd, ← Real.Angle.coe_add]
      rw [show (Real.pi + Real.pi : ℝ) = 2 * Real.pi from by ring]
      rw [Real.Angle.coe_two_pi]
      exact Real.Angle.coe_zero.symm
    · left
      rw [if_neg h2, Real.Angle.coe_toReal]

/-- `|toReal|` of `↑(x + kπ)` is either `|x|` or `π - |x|` for
`x ∈ (-π, π)`, `k ∈ {-1, 0, 1}`. -/
lemma abs_toReal_add_int_pi {x : ℝ} (hx : x ∈ Set.Ioo (-Real.pi) Real.pi)
    {k : ℤ} (hk : k = 0 ∨ k = 1 ∨ k = -1) :
    |(((x + k * Real.pi : ℝ) : Real.Angle)).toReal| = |x| ∨
    |(((x + k * Real.pi : ℝ) : Real.Angle)).toReal| = Real.pi - |x| := by
  obtain ⟨hx1, hx2⟩ := hx
  rcases hk with rfl | rfl | rfl
  · left
    rw [Int.cast_zero, zero_mul, add_zero, Real.Angle.toReal_coe,
      (toIocMod_eq_self Real.two_pi_pos).mpr (by
        constructor <;> linarith)]
  · right
    rw [Int.cast_one, one_mul, Real.Angle.toReal_coe]
    by_cases hle : x + Real.pi ≤ Real.pi
    · rw [(toIocMod_eq_self Real.two_pi_pos).mpr (by
          constructor <;> linarith)]
      rw [abs_of_nonneg (by linarith),
        abs_of_nonpos (show x ≤ 0 by linarith)]
      ring
    · push Not at hle
      have hto : toIocMod Real.two_pi_pos (-Real.pi) (x + Real.pi) =
          toIocMod Real.two_pi_pos (-Real.pi) (x - Real.pi) := by
        rw [show x + Real.pi = x - Real.pi + (1 : ℤ) • (2 * Real.pi) by
          simp; ring, toIocMod_add_zsmul]
      rw [hto, (toIocMod_eq_self Real.two_pi_pos).mpr (by
        constructor <;> linarith)]
      rw [abs_of_neg (by linarith),
        abs_of_nonneg (show 0 ≤ x by linarith)]
      ring
  · right
    rw [Int.cast_neg, Int.cast_one, neg_mul, one_mul, ← sub_eq_add_neg,
      Real.Angle.toReal_coe]
    by_cases hle : -Real.pi < x - Real.pi
    · rw [(toIocMod_eq_self Real.two_pi_pos).mpr (by
          constructor <;> linarith)]
      rw [abs_of_neg (by linarith),
        abs_of_nonneg (show 0 ≤ x by linarith)]
      ring
    · push Not at hle
      have hto : toIocMod Real.two_pi_pos (-Real.pi) (x - Real.pi) =
          toIocMod Real.two_pi_pos (-Real.pi) (x + Real.pi) := by
        rw [show x - Real.pi = x + Real.pi + (-1 : ℤ) • (2 * Real.pi) by
          simp; ring, toIocMod_add_zsmul]
      rw [hto, (toIocMod_eq_self Real.two_pi_pos).mpr (by
        constructor <;> linarith)]
      rw [abs_of_nonneg (by linarith),
        abs_of_nonpos (show x ≤ 0 by linarith)]
      ring

/-- If `↑ρ ≡ d`, `↑ρ' ≡ d'` (mod `π`) with `ρ, ρ' ∈ [0, π)`, then
`|(d' - d).toReal|` is `|ρ' - ρ|` or `π - |ρ' - ρ|`. -/
lemma toReal_diff_of_class {d d' : Real.Angle} {ρ ρ' : ℝ}
    (hrho : ρ ∈ Set.Ico 0 Real.pi) (hrho' : ρ' ∈ Set.Ico 0 Real.pi)
    (hc : ((ρ : ℝ) : Real.Angle) = d ∨ ((ρ : ℝ) : Real.Angle) = d + Real.pi)
    (hc' : ((ρ' : ℝ) : Real.Angle) = d' ∨
      ((ρ' : ℝ) : Real.Angle) = d' + Real.pi) :
    |(d' - d).toReal| = |ρ' - ρ| ∨ |(d' - d).toReal| = Real.pi - |ρ' - ρ| := by
  obtain ⟨hrho0, hrhoπ⟩ := hrho
  obtain ⟨hrho'0, hrho'π⟩ := hrho'
  have hx : ρ' - ρ ∈ Set.Ioo (-Real.pi) Real.pi :=
    ⟨by linarith, by linarith⟩
  -- normalize: `d = ↑(ρ - aπ)`, `d' = ↑(ρ' - bπ)` with `a, b ∈ {0, 1}`
  have hd : ∃ a : ℤ, (a = 0 ∨ a = 1) ∧
      d = ((ρ - a * Real.pi : ℝ) : Real.Angle) := by
    rcases hc with hc | hc
    · exact ⟨0, Or.inl rfl, by rw [Int.cast_zero, zero_mul, sub_zero, hc]⟩
    · refine ⟨1, Or.inr rfl, ?_⟩
      rw [Int.cast_one, one_mul, Real.Angle.coe_sub, eq_sub_iff_add_eq]
      exact hc.symm
  have hd' : ∃ b : ℤ, (b = 0 ∨ b = 1) ∧
      d' = ((ρ' - b * Real.pi : ℝ) : Real.Angle) := by
    rcases hc' with hc' | hc'
    · exact ⟨0, Or.inl rfl, by rw [Int.cast_zero, zero_mul, sub_zero, hc']⟩
    · refine ⟨1, Or.inr rfl, ?_⟩
      rw [Int.cast_one, one_mul, Real.Angle.coe_sub, eq_sub_iff_add_eq]
      exact hc'.symm
  obtain ⟨a, ha, hd⟩ := hd
  obtain ⟨b, hb, hd'⟩ := hd'
  have hk : a - b = 0 ∨ a - b = 1 ∨ a - b = -1 := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp <;> omega
  have hdd : d' - d = ((ρ' - ρ + (a - b) * Real.pi : ℝ) : Real.Angle) := by
    rw [hd, hd', ← Real.Angle.coe_sub]
    congr 1
    push_cast
    ring
  rw [hdd]
  have hkey := abs_toReal_add_int_pi hx hk
  push_cast at hkey ⊢
  exact hkey

/-- Translating the `angle ∈ [lam, π - lam]` constraint into the
`[0, π)`-representatives: `|linRep d - linRep d'| ∈ [lam, π - lam]`. -/
lemma linRep_sub_mem_Icc {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
    (he : e ≠ 0) {u v : Plane₂} (hu : u ≠ 0) (hv : v ≠ 0) {lam : ℝ}
    (hangle : lam ≤ InnerProductGeometry.angle u v ∧
              InnerProductGeometry.angle u v ≤ Real.pi - lam) :
    lam ≤ |linRep (o.oangle e u) - linRep (o.oangle e v)| ∧
      |linRep (o.oangle e u) - linRep (o.oangle e v)| ≤ Real.pi - lam := by
  obtain ⟨ha1, ha2⟩ := hangle
  set d := o.oangle e u
  set d' := o.oangle e v
  have hov : InnerProductGeometry.angle u v = |(d' - d).toReal| := by
    rw [o.angle_eq_abs_oangle_toReal hu hv, o.oangle_sub_left he hu hv]
  have key := toReal_diff_of_class (linRep_mem_Ico d) (linRep_mem_Ico d')
    (linRep_class d) (linRep_class d')
  rcases key with hkey | hkey
  · rw [hov] at ha1 ha2
    rw [hkey] at ha1 ha2
    rw [show linRep d - linRep d' = -(linRep d' - linRep d) by ring, abs_neg]
    exact ⟨ha1, ha2⟩
  · rw [hov] at ha1 ha2
    rw [hkey] at ha1 ha2
    rw [show linRep d - linRep d' = -(linRep d' - linRep d) by ring, abs_neg]
    constructor <;> linarith

/-!
## Gap location on the projective circle

`ds ⊆ [0, π)` sorted without duplicates are the center-line directions
seen from a circle. For `ρ ∈ [0, π)` keeping margin `lam` from every
`ds`-element, the consecutive elements of the period-extended list
`dsExt = (ds - π) ++ ds ++ (ds + π)` bracketing `ρ` give a gap
`[a + lam, b - lam]` covered by `⌊(b - a)/lam⌋ - 1` wings.
-/

section GapLocation

variable {ds : List ℝ} {ρ lam : ℝ}

/-- The period-extended direction list. -/
noncomputable def dsExt (ds : List ℝ) : List ℝ :=
  ds.map (· - Real.pi) ++ ds ++ ds.map (· + Real.pi)

/-- Which block of `dsExt` contains `x`. -/
lemma dsExt_block {x : ℝ} (hx : x ∈ dsExt ds) :
    (∃ y ∈ ds, x = y - Real.pi) ∨ x ∈ ds ∨ (∃ y ∈ ds, x = y + Real.pi) := by
  unfold dsExt at hx
  rw [List.mem_append, List.mem_append] at hx
  rcases hx with (h | h) | h
  · obtain ⟨y, hy, hyx⟩ := List.mem_map.mp h
    exact Or.inl ⟨y, hy, hyx.symm⟩
  · exact Or.inr (Or.inl h)
  · obtain ⟨y, hy, hyx⟩ := List.mem_map.mp h
    exact Or.inr (Or.inr ⟨y, hy, hyx.symm⟩)

lemma dsExt_margin (hmem : ∀ x ∈ ds, x ∈ Set.Ico 0 Real.pi)
    (hmar : ∀ x ∈ ds, lam ≤ |ρ - x| ∧ |ρ - x| ≤ Real.pi - lam)
    (hrho : ρ ∈ Set.Ico 0 Real.pi) :
    ∀ x ∈ dsExt ds, lam ≤ |ρ - x| := by
  intro x hx
  rcases dsExt_block hx with ⟨y, hy, rfl⟩ | hy | ⟨y, hy, rfl⟩
  · obtain ⟨-, hhi⟩ := hmar y hy
    obtain ⟨y0, ypi⟩ := hmem y hy
    obtain ⟨ρ0, ρpi⟩ := hrho
    rw [abs_of_nonneg (by linarith)]
    by_cases hge : ρ ≥ y
    · rw [abs_of_nonneg (by linarith)] at hhi; linarith
    · rw [abs_of_neg (by linarith)] at hhi; linarith
  · exact (hmar x hy).1
  · obtain ⟨-, hhi⟩ := hmar y hy
    obtain ⟨y0, ypi⟩ := hmem y hy
    obtain ⟨ρ0, ρpi⟩ := hrho
    rw [abs_of_neg (by linarith)]
    by_cases hge : ρ ≥ y
    · rw [abs_of_nonneg (by linarith)] at hhi; linarith
    · rw [abs_of_neg (by linarith)] at hhi; linarith

lemma dsExt_margin_upper (hmar : ∀ x ∈ ds, lam ≤ |ρ - x| ∧ |ρ - x| ≤ Real.pi - lam) :
    ∀ x ∈ ds, |ρ - x| ≤ Real.pi - lam := fun x hx => (hmar x hx).2

lemma rho_not_mem_ds (hmar : ∀ x ∈ ds, lam ≤ |ρ - x| ∧ |ρ - x| ≤ Real.pi - lam)
    (hlam : 0 < lam) : ρ ∉ ds := by
  intro h
  obtain ⟨hlo, -⟩ := hmar ρ h
  rw [sub_self, abs_zero] at hlo
  linarith

lemma rho_not_mem_dsExt (hmem : ∀ x ∈ ds, x ∈ Set.Ico 0 Real.pi)
    (hmar : ∀ x ∈ ds, lam ≤ |ρ - x| ∧ |ρ - x| ≤ Real.pi - lam)
    (hrho : ρ ∈ Set.Ico 0 Real.pi) (hlam : 0 < lam) : ρ ∉ dsExt ds := by
  intro h
  rcases dsExt_block h with ⟨y, hy, heq⟩ | hy | ⟨y, hy, heq⟩
  · obtain ⟨y0, ypi⟩ := hmem y hy
    obtain ⟨ρ0, -⟩ := hrho
    linarith [Real.pi_pos]
  · exact rho_not_mem_ds hmar hlam hy
  · obtain ⟨y0, ypi⟩ := hmem y hy
    obtain ⟨-, ρpi⟩ := hrho
    linarith

/-- The gap after direction `ds[i]` in the cyclic order (wraparound
contributes `ds[0] + π`). -/
noncomputable def gapAfter (ds : List ℝ) (i : Fin ds.length) : ℝ :=
  (if h : i.1 + 1 < ds.length then ds.get ⟨i.1 + 1, h⟩
   else ds.get ⟨0, Nat.zero_lt_of_lt i.2⟩ + Real.pi) - ds.get i

lemma getElem_mem {l : List ℝ} (i : Fin l.length) : l.get i ∈ l :=
  List.getElem_mem i.2

/-- The consecutive elements of `dsExt` bracketing `ρ` yield a gap whose
ends keep margin `lam` from `ρ`, identified with `gapAfter j` for the
index `j` of `a`'s line class. -/
lemma gap_bracket (hsort : ds.SortedLE) (hnodup : ds.Nodup)
    (hmem : ∀ x ∈ ds, x ∈ Set.Ico 0 Real.pi)
    (hrho : ρ ∈ Set.Ico 0 Real.pi) (hlam : 0 < lam)
    (hmar : ∀ x ∈ ds, lam ≤ |ρ - x| ∧ |ρ - x| ≤ Real.pi - lam)
    (hne : ds ≠ []) :
    ∃ a b : ℝ, a + lam ≤ ρ ∧ ρ ≤ b - lam ∧
      ∃ j : Fin ds.length,
        (a = ds.get j ∨ a = ds.get j - Real.pi) ∧
        b - a = gapAfter ds j := by
  classical
  obtain ⟨hrho0, hrhopi⟩ := hrho
  have hds0 : 0 < ds.length :=
    Nat.pos_of_ne_zero fun h => hne (List.length_eq_zero_iff.mp h)
  set below := ((dsExt ds).filter (· < ρ)).toFinset with hbelow
  set above := ((dsExt ds).filter (ρ < ·)).toFinset with habove
  have h0lt : ds.get ⟨0, hds0⟩ < Real.pi := (hmem _ (getElem_mem _)).2
  have hbel : below.Nonempty := by
    refine ⟨ds.get ⟨0, hds0⟩ - Real.pi, ?_⟩
    rw [hbelow, List.mem_toFinset, List.mem_filter]
    refine ⟨?_, ?_⟩
    · unfold dsExt
      rw [List.mem_append, List.mem_append]
      exact Or.inl (Or.inl (List.mem_map.mpr
        ⟨ds.get ⟨0, hds0⟩, getElem_mem ⟨0, hds0⟩, rfl⟩))
    · have : ds.get ⟨0, hds0⟩ - Real.pi < ρ := by linarith
      simpa using this
  have hab : above.Nonempty := by
    refine ⟨ds.get ⟨0, hds0⟩ + Real.pi, ?_⟩
    rw [habove, List.mem_toFinset, List.mem_filter]
    refine ⟨?_, ?_⟩
    · unfold dsExt
      rw [List.mem_append]
      exact Or.inr (List.mem_map.mpr
        ⟨ds.get ⟨0, hds0⟩, getElem_mem ⟨0, hds0⟩, rfl⟩)
    · have h0' := (hmem _ (getElem_mem ⟨0, hds0⟩)).1
      have : ρ < ds.get ⟨0, hds0⟩ + Real.pi := by linarith
      simpa using this
  set a := below.max' hbel with ha
  set b := above.min' hab with hb
  have hamem : a ∈ dsExt ds := by
    have := Finset.max'_mem below hbel
    rw [← ha, hbelow] at this
    exact (List.mem_filter.mp (List.mem_toFinset.mp this)).1
  have halt : a < ρ := by
    have := Finset.max'_mem below hbel
    rw [← ha, hbelow] at this
    exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp this)).2
  have hbmem : b ∈ dsExt ds := by
    have := Finset.min'_mem above hab
    rw [← hb, habove] at this
    exact (List.mem_filter.mp (List.mem_toFinset.mp this)).1
  have hblt : ρ < b := by
    have := Finset.min'_mem above hab
    rw [← hb, habove] at this
    exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp this)).2
  have hmax : ∀ x ∈ dsExt ds, x < ρ → x ≤ a := by
    intro x hx hxlt
    have hxb : x ∈ below := by
      rw [hbelow]
      exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hx, by simpa using hxlt⟩)
    have := Finset.le_max' below x hxb
    rw [ha]
    exact this
  have hmin : ∀ x ∈ dsExt ds, ρ < x → b ≤ x := by
    intro x hx hxlt
    have hxb : x ∈ above := by
      rw [habove]
      exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hx, by simpa using hxlt⟩)
    have := Finset.min'_le above x hxb
    rw [hb]
    exact this
  -- margins at the two ends
  have haρ : a + lam ≤ ρ := by
    have h := dsExt_margin hmem hmar ⟨hrho0, hrhopi⟩ a hamem
    rw [abs_of_pos (by linarith)] at h
    linarith
  have hbρ : ρ ≤ b - lam := by
    have h := dsExt_margin hmem hmar ⟨hrho0, hrhopi⟩ b hbmem
    rw [abs_of_neg (by linarith)] at h
    linarith
  -- the class of `a` in `ds`
  have hablk : a ∈ ds ∨ ∃ y ∈ ds, a = y - Real.pi := by
    rcases dsExt_block hamem with ⟨y, hy, heq⟩ | hy | ⟨y, hy, heq⟩
    · exact Or.inr ⟨y, hy, heq⟩
    · exact Or.inl hy
    · obtain ⟨y0, -⟩ := hmem y hy
      linarith [Real.pi_pos]
  -- the index `j` of `a`'s line class in `ds`
  obtain ⟨j, hjeq⟩ : ∃ j : Fin ds.length, ds.get j = a ∨ ds.get j = a + Real.pi := by
    rcases hablk with ha' | ⟨y, hy, hay⟩
    · exact ⟨⟨ds.idxOf a, List.idxOf_lt_length_iff.2 ha'⟩,
        Or.inl (List.idxOf_get _)⟩
    · refine ⟨⟨ds.idxOf y, List.idxOf_lt_length_iff.2 hy⟩, Or.inr ?_⟩
      rw [List.idxOf_get]
      linarith [hay]
  -- the "next" element after `a` in `dsExt`, and `b` equals it
  have hsmono : Monotone ds.get := List.sortedLE_iff_monotone_get.mp hsort
  refine ⟨a, b, haρ, hbρ, j, ?_, ?_⟩
  · rcases hjeq with hje | hje
    · exact Or.inl hje.symm
    · exact Or.inr (by rw [hje]; ring)
  · -- `b - a = gapAfter ds j`
    have hinj : Function.Injective ds.get := List.nodup_iff_injective_get.mp hnodup
    have hlt' : ∀ i k : Fin ds.length, i < k → ds.get i < ds.get k :=
      fun i k h => lt_of_le_of_ne (hsmono (le_of_lt h))
        (fun he => hinj.ne (ne_of_lt h) he)
    have hlt_iff : ∀ i k : Fin ds.length, ds.get i < ds.get k → i < k :=
      fun i k h => by
        by_contra hc
        push Not at hc
        exact absurd (hsmono hc) (not_le.mpr h)
    set nextds := (if h : j.1 + 1 < ds.length then ds.get ⟨j.1 + 1, h⟩
      else ds.get ⟨0, hds0⟩ + Real.pi) with hnextds
    -- `tgt` = the next element of `dsExt` after `a`
    set tgt := a + nextds - ds.get j with htgt
    have hnext_gt : ds.get j < nextds := by
      by_cases hj : j.1 + 1 < ds.length
      · rw [hnextds, dif_pos hj]
        exact hlt' j ⟨j.1 + 1, hj⟩ (by show j.1 < j.1 + 1; omega)
      · rw [hnextds, dif_neg hj]
        have hpi := (hmem (ds.get j) (getElem_mem j)).2
        have h0' := (hmem (ds.get ⟨0, hds0⟩) (getElem_mem ⟨0, hds0⟩)).1
        linarith [Real.pi_pos]
    have htgt_mem : tgt ∈ dsExt ds := by
      rcases hjeq with hje | hje
      · -- tgt = nextds (ds.get j = a)
        rw [htgt, hje, add_sub_cancel_left]
        by_cases hj : j.1 + 1 < ds.length
        · rw [hnextds, dif_pos hj]
          simp only [dsExt, List.mem_append, List.mem_map]
          exact Or.inl (Or.inr (getElem_mem ⟨j.1 + 1, hj⟩))
        · rw [hnextds, dif_neg hj]
          simp only [dsExt, List.mem_append, List.mem_map]
          exact Or.inr ⟨ds.get ⟨0, hds0⟩, getElem_mem ⟨0, hds0⟩, rfl⟩
      · -- tgt = nextds - π (ds.get j = a + π)
        rw [htgt, hje]
        have hs : a + nextds - (a + Real.pi) = nextds - Real.pi := by ring
        rw [hs]
        by_cases hj : j.1 + 1 < ds.length
        · rw [hnextds, dif_pos hj]
          simp only [dsExt, List.mem_append, List.mem_map]
          exact Or.inl (Or.inl
            ⟨ds.get ⟨j.1 + 1, hj⟩, getElem_mem ⟨j.1 + 1, hj⟩, rfl⟩)
        · rw [hnextds, dif_neg hj]
          simp only [dsExt, List.mem_append, List.mem_map]
          have hs' : ds.get ⟨0, hds0⟩ + Real.pi - Real.pi = ds.get ⟨0, hds0⟩ := by ring
          rw [hs']
          exact Or.inl (Or.inr (getElem_mem ⟨0, hds0⟩))
    have htgt_gt : ρ < tgt := by
      have hgt : a < tgt := by
        rcases hjeq with hje | hje
        · rw [htgt, hje, add_sub_cancel_left]
          rw [hje] at hnext_gt
          exact hnext_gt
        · rw [htgt, hje]
          have hs : a + nextds - (a + Real.pi) = nextds - Real.pi := by ring
          rw [hs]
          rw [hje] at hnext_gt
          linarith
      by_cases hlt : tgt < ρ
      · exact absurd (hmax tgt htgt_mem hlt) (not_le.mpr hgt)
      · have hne' : tgt ≠ ρ := fun h =>
          rho_not_mem_dsExt hmem hmar ⟨hrho0, hrhopi⟩ hlam (h ▸ htgt_mem)
        push Not at hlt
        exact lt_of_le_of_ne hlt hne'.symm
    have hb_le : b ≤ tgt := hmin tgt htgt_mem htgt_gt
    have hnobetween : ∀ x ∈ dsExt ds, a < x → x < tgt → False := by
      intro x hx hax hxt
      rcases hjeq with hje | hje
      · -- tgt = nextds, a = ds.get j
        have htgt' : tgt = nextds := by rw [htgt, hje, add_sub_cancel_left]
        rw [htgt'] at hxt
        rcases dsExt_block hx with ⟨z, hz, hxz⟩ | hxz | ⟨z, hz, hxz⟩
        · obtain ⟨z0, zpi⟩ := hmem z hz
          have ha0 : 0 ≤ a := by
            rw [← hje]
            exact (hmem _ (getElem_mem j)).1
          linarith
        · -- x = ds[k] strictly between ds.get j and nextds
          set k := ds.idxOf x with hk
          have hkm : k < ds.length := List.idxOf_lt_length_iff.2 hxz
          have hkx : ds.get ⟨k, hkm⟩ = x := List.idxOf_get hkm
          by_cases hj : j.1 + 1 < ds.length
          · rw [hnextds, dif_pos hj] at hxt
            have h1 : j.1 < k := hlt_iff j ⟨k, hkm⟩ (by rw [hje, hkx]; exact hax)
            have h2 : k < j.1 + 1 :=
              hlt_iff ⟨k, hkm⟩ ⟨j.1 + 1, hj⟩ (by rw [hkx]; exact hxt)
            omega
          · rw [hnextds, dif_neg hj] at hxt
            have h1 : j.1 < k := hlt_iff j ⟨k, hkm⟩ (by rw [hje, hkx]; exact hax)
            push Not at hj
            omega
        · obtain ⟨z0, zpi⟩ := hmem z hz
          by_cases hj : j.1 + 1 < ds.length
          · rw [hnextds, dif_pos hj] at hxt
            have hpi' := (hmem (ds.get ⟨j.1 + 1, hj⟩)
              (getElem_mem ⟨j.1 + 1, hj⟩)).2
            linarith
          · rw [hnextds, dif_neg hj] at hxt
            -- x = z + π < ds[0] + π → z < ds[0] → k < 0
            set k := ds.idxOf z with hk
            have hkm : k < ds.length := List.idxOf_lt_length_iff.2 hz
            have hkz : ds.get ⟨k, hkm⟩ = z := List.idxOf_get hkm
            have h1 : k < 0 :=
              hlt_iff ⟨k, hkm⟩ ⟨0, hds0⟩ (by rw [hkz]; linarith)
            omega
      · -- tgt = nextds - π, ds.get j = a + π
        have htgt' : tgt = nextds - Real.pi := by rw [htgt, hje]; ring
        rw [htgt'] at hxt
        rcases dsExt_block hx with ⟨z, hz, hxz⟩ | hxz | ⟨z, hz, hxz⟩
        · -- x = z - π: a < x → ds.get j < z; x < tgt → z < nextds
          obtain ⟨z0, zpi⟩ := hmem z hz
          set k := ds.idxOf z with hk
          have hkm : k < ds.length := List.idxOf_lt_length_iff.2 hz
          have hkz : ds.get ⟨k, hkm⟩ = z := List.idxOf_get hkm
          by_cases hj : j.1 + 1 < ds.length
          · rw [hnextds, dif_pos hj] at hxt
            have h1 : j.1 < k := hlt_iff j ⟨k, hkm⟩ (by rw [hkz]; linarith)
            have h2 : k < j.1 + 1 :=
              hlt_iff ⟨k, hkm⟩ ⟨j.1 + 1, hj⟩ (by rw [hkz]; linarith)
            omega
          · rw [hnextds, dif_neg hj] at hxt
            push Not at hj
            have h1 : j.1 < k := hlt_iff j ⟨k, hkm⟩ (by rw [hkz]; linarith)
            omega
        · -- x ∈ ds, x ≥ 0 but x < tgt ≤ 0-ish
          have hx0 := (hmem x hxz).1
          by_cases hj : j.1 + 1 < ds.length
          · rw [hnextds, dif_pos hj] at hxt
            have hpi' := (hmem (ds.get ⟨j.1 + 1, hj⟩)
              (getElem_mem ⟨j.1 + 1, hj⟩)).2
            linarith
          · rw [hnextds, dif_neg hj] at hxt
            set k := ds.idxOf x with hk
            have hkm : k < ds.length := List.idxOf_lt_length_iff.2 hxz
            have hkx : ds.get ⟨k, hkm⟩ = x := List.idxOf_get hkm
            have h1 : k < 0 :=
              hlt_iff ⟨k, hkm⟩ ⟨0, hds0⟩ (by rw [hkx]; linarith)
            omega
        · -- x = z + π ≥ π > tgt
          obtain ⟨z0, zpi⟩ := hmem z hz
          by_cases hj : j.1 + 1 < ds.length
          · rw [hnextds, dif_pos hj] at hxt
            have hpi' := (hmem (ds.get ⟨j.1 + 1, hj⟩)
              (getElem_mem ⟨j.1 + 1, hj⟩)).2
            linarith
          · rw [hnextds, dif_neg hj] at hxt
            have hpi' := (hmem (ds.get ⟨0, hds0⟩) (getElem_mem ⟨0, hds0⟩)).2
            linarith
    have hge : tgt ≤ b := by
      by_contra hc
      push Not at hc
      exact hnobetween b hbmem (by linarith) hc
    have hbeq : b = tgt := le_antisymm hb_le hge
    -- `b - a = tgt - a = nextds - ds.get j = gapAfter j`
    have hgap : gapAfter ds j = nextds - ds.get j := by
      unfold gapAfter
      by_cases hj : j.1 + 1 < ds.length
      · rw [dif_pos hj, hnextds, dif_pos hj]
      · rw [dif_neg hj, hnextds, dif_neg hj]
    rw [hbeq, htgt, hgap]
    ring

end GapLocation

end Jsp404

