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

/-- Every cyclic gap is positive. -/
lemma gapAfter_pos (hsort : ds.SortedLE) (hnodup : ds.Nodup)
    (hmem : ∀ x ∈ ds, x ∈ Set.Ico 0 Real.pi) (hne : ds ≠ [])
    (j : Fin ds.length) : 0 < gapAfter ds j := by
  have hsmono := List.sortedLE_iff_monotone_get.mp hsort
  have hinj := List.nodup_iff_injective_get.mp hnodup
  have hds0 : 0 < ds.length :=
    Nat.pos_of_ne_zero fun h => hne (List.length_eq_zero_iff.mp h)
  unfold gapAfter
  by_cases hj : j.1 + 1 < ds.length
  · rw [dif_pos hj]
    have hfin : j < ⟨j.1 + 1, hj⟩ := by show j.1 < j.1 + 1; omega
    have : ds.get j < ds.get ⟨j.1 + 1, hj⟩ :=
      lt_of_le_of_ne (hsmono (le_of_lt hfin))
        (fun he => hinj.ne (ne_of_lt hfin) he)
    linarith
  · rw [dif_neg hj]
    have hpi := (hmem _ (getElem_mem j)).2
    have h0' := (hmem _ (getElem_mem ⟨0, hds0⟩)).1
    linarith [Real.pi_pos]

/-- The cyclic gaps of a nonempty direction list sum to `π`. -/
lemma gapAfter_sum (hne : ds ≠ []) :
    ∑ j : Fin ds.length, gapAfter ds j = Real.pi := by
  have hL : 0 < ds.length :=
    Nat.pos_of_ne_zero fun h => hne (List.length_eq_zero_iff.mp h)
  set f : ℕ → ℝ := fun i =>
    if h : i < ds.length then ds.get ⟨i, h⟩
    else ds.get ⟨0, hL⟩ + Real.pi with hfeq
  have hterm : ∀ j : Fin ds.length, gapAfter ds j = f (j.1 + 1) - f j.1 := by
    intro j
    by_cases hj : j.1 + 1 < ds.length
    · unfold gapAfter
      rw [dif_pos hj]
      simp only [hfeq]
      rw [dif_pos hj, dif_pos j.2]
    · unfold gapAfter
      rw [dif_neg hj]
      simp only [hfeq]
      rw [dif_neg hj, dif_pos j.2]
  calc ∑ j : Fin ds.length, gapAfter ds j
      = ∑ j : Fin ds.length, (f (j.1 + 1) - f j.1) :=
          Finset.sum_congr rfl fun j _ => hterm j
    _ = ∑ i ∈ Finset.range ds.length, (f (i + 1) - f i) :=
          Fin.sum_univ_eq_sum_range (fun i => f (i + 1) - f i) ds.length
    _ = f ds.length - f 0 := Finset.sum_range_sub f ds.length
    _ = Real.pi := by
        have e1 : f ds.length = ds.get ⟨0, hL⟩ + Real.pi := by
          rw [hfeq]; exact dif_neg (by omega)
        have e2 : f 0 = ds.get ⟨0, hL⟩ := by
          rw [hfeq]; exact dif_pos hL
        rw [e1, e2]
        ring

/-- **The `top` field of `StaircaseBound` is automatic.** For a nonempty
direction list in `[0, π)`, the circle exponent satisfies
`Σ_j (⌊g_j / lam⌋ - 1) ≤ ⌊π / lam⌋ - 1` — i.e. `k'(i) ≤ n - 1` when
`n = ⌊u/2⌋` and `lam = 2π/u`. -/
lemma exponent_le_floor (hsort : ds.SortedLE) (hnodup : ds.Nodup)
    (hmem : ∀ x ∈ ds, x ∈ Set.Ico 0 Real.pi) (hne : ds ≠ [])
    (hlam : 0 < lam) :
    ∑ j : Fin ds.length, (Nat.floor (gapAfter ds j / lam) - 1) ≤
      Nat.floor (Real.pi / lam) - 1 := by
  have hgsum := gapAfter_sum (ds := ds) hne
  have hpos : ∀ j : Fin ds.length, 0 < gapAfter ds j :=
    gapAfter_pos hsort hnodup hmem hne
  set T : Finset (Fin ds.length) :=
    Finset.univ.filter fun j => 1 ≤ Nat.floor (gapAfter ds j / lam) with hTeq
  have hTmem : ∀ j : Fin ds.length,
      (j ∈ T ↔ 1 ≤ Nat.floor (gapAfter ds j / lam)) := by
    intro j
    simp only [hTeq, Finset.mem_filter, Finset.mem_univ, true_and]
  -- Σ_j (t_j - 1) = Σ_{j ∈ T} t_j - T.card
  have hsplit : ∑ j : Fin ds.length, (Nat.floor (gapAfter ds j / lam) - 1) =
      (∑ j ∈ T, Nat.floor (gapAfter ds j / lam)) - T.card := by
    have h1 : ∑ j : Fin ds.length, (Nat.floor (gapAfter ds j / lam) - 1) =
        ∑ j ∈ T, (Nat.floor (gapAfter ds j / lam) - 1) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ T)
      intro j _ hj
      rw [hTmem j] at hj
      omega
    rw [h1]
    have h2 : (∑ j ∈ T, (Nat.floor (gapAfter ds j / lam) - 1)) + T.card =
        ∑ j ∈ T, Nat.floor (gapAfter ds j / lam) := by
      have hcard : T.card = ∑ j ∈ T, 1 := by
        rw [Finset.sum_const, smul_eq_mul, mul_one]
      rw [hcard, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hTmem j] at hj
      exact Nat.sub_add_cancel hj
    omega
  -- Σ t_j ≤ ⌊π/lam⌋ since Σ ⌊x⌋ ≤ ⌊Σ x⌋ = π/lam
  have hsumt : ∑ j : Fin ds.length, Nat.floor (gapAfter ds j / lam) ≤
      Nat.floor (Real.pi / lam) := by
    have hle : ∑ j : Fin ds.length,
        (Nat.floor (gapAfter ds j / lam) : ℝ) ≤ Real.pi / lam := by
      rw [← hgsum, Finset.sum_div]
      apply Finset.sum_le_sum
      intro j _
      exact Nat.floor_le (div_nonneg (hpos j).le hlam.le)
    apply (Nat.le_floor_iff (div_nonneg Real.pi_pos.le hlam.le)).mpr
    push_cast
    exact hle
  have hleT : ∑ j ∈ T, Nat.floor (gapAfter ds j / lam) ≤
      Nat.floor (Real.pi / lam) :=
    le_trans (Finset.sum_le_sum_of_subset (Finset.subset_univ T)) hsumt
  rw [hsplit]
  rcases Nat.eq_zero_or_pos T.card with hT | hT
  · rw [Finset.card_eq_zero.mp hT, Finset.sum_empty]
    omega
  · calc (∑ j ∈ T, Nat.floor (gapAfter ds j / lam)) - T.card
        ≤ Nat.floor (Real.pi / lam) - T.card :=
          Nat.sub_le_sub_right hleT _
      _ ≤ Nat.floor (Real.pi / lam) - 1 := Nat.sub_le_sub_left hT _

end GapLocation

/-- Bridging: if `↑ρ ≡ φ (mod π)`, `↑c ≡ θ (mod π)` and `ρ - c ∈ [0, lam)`,
then `φ` lies in the one-sided double sector `T(θ, lam)`. -/
lemma inSectorOS_of_rep {φ θ : Real.Angle} {ρ c lam : ℝ}
    (hclass : ((ρ : ℝ) : Real.Angle) = φ ∨
      ((ρ : ℝ) : Real.Angle) = φ + Real.pi)
    (hc : ((c : ℝ) : Real.Angle) = θ ∨
      ((c : ℝ) : Real.Angle) = θ + Real.pi)
    (hρ : ρ - c ∈ Set.Ico 0 lam) (hlampi : lam ≤ Real.pi) :
    inSectorOS θ lam φ := by
  obtain ⟨hρ0, hρl⟩ := hρ
  have hrep : (((ρ - c : ℝ) : Real.Angle)).toReal = ρ - c := by
    rw [Real.Angle.toReal_coe, (toIocMod_eq_self Real.two_pi_pos).mpr
      ⟨by linarith, by linarith⟩]
  rcases hclass with hcl | hcl <;> rcases hc with hct | hct
  · refine Or.inl ?_
    have e : φ - θ = ((ρ - c : ℝ) : Real.Angle) := by
      rw [← hcl, ← hct, ← Real.Angle.coe_sub]
    rw [e, hrep]
    exact ⟨hρ0, hρl⟩
  · refine Or.inr ?_
    have hθ : θ = ((c - Real.pi : ℝ) : Real.Angle) := by
      rw [(sub_eq_iff_eq_add.mpr hct).symm, ← Real.Angle.coe_sub]
    have e : φ - θ - Real.pi = ((ρ - c : ℝ) : Real.Angle) := by
      rw [← hcl, hθ, ← Real.Angle.coe_sub, ← Real.Angle.coe_sub]
      congr 1
      ring
    rw [e, hrep]
    exact ⟨hρ0, hρl⟩
  · refine Or.inr ?_
    have hφρ : φ = ((ρ - Real.pi : ℝ) : Real.Angle) := by
      rw [(sub_eq_iff_eq_add.mpr hcl).symm, ← Real.Angle.coe_sub]
    have e : φ - θ - Real.pi = ((ρ - c : ℝ) : Real.Angle) := by
      rw [hφρ, ← hct, ← Real.Angle.coe_sub, ← Real.Angle.coe_sub]
      have h2pi : ρ - Real.pi - c - Real.pi = ρ - c - 2 * Real.pi := by ring
      rw [h2pi, Real.Angle.coe_sub, Real.Angle.coe_two_pi, sub_zero]
    rw [e, hrep]
    exact ⟨hρ0, hρl⟩
  · refine Or.inl ?_
    have hφρ : φ = ((ρ - Real.pi : ℝ) : Real.Angle) := by
      rw [(sub_eq_iff_eq_add.mpr hcl).symm, ← Real.Angle.coe_sub]
    have hθ : θ = ((c - Real.pi : ℝ) : Real.Angle) := by
      rw [(sub_eq_iff_eq_add.mpr hct).symm, ← Real.Angle.coe_sub]
    have e : φ - θ = ((ρ - c : ℝ) : Real.Angle) := by
      rw [hφρ, hθ, ← Real.Angle.coe_sub]
      congr 1
      ring
    rw [e, hrep]
    exact ⟨hρ0, hρl⟩

/-- Wing-cover bound with an arbitrary finite index type. -/
theorem card_le_two_pow_of_wing_cover' {ι : Type*} [Fintype ι]
    (V : GCfg) (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (θ : ι → Real.Angle) {lam : ℝ} (hlam : lam < Real.pi)
    (Q : Finset Plane₂)
    (hGD : ∀ p ∈ Q, ∀ q ∈ Q, p ≠ q → V.GD p q ≠ 0)
    (hGA : ∀ p ∈ Q, ∀ q ∈ Q, ∀ r ∈ Q, p ≠ q → q ≠ r → p ≠ r →
      V.GA p q r ≤ Real.pi - lam)
    (hdir : ∀ p ∈ Q, ∀ q ∈ Q, p ≠ q →
      ∃ i : ι, inSectorOS (θ i) lam (o.oangle e (V.GD p q))) :
    Q.card ≤ 2 ^ Fintype.card ι := by
  apply card_le_two_pow_of_wing_cover V o e he
    (θ ∘ (Fintype.equivFin ι).symm) hlam Q hGD hGA
  intro p hp q hq hpq
  obtain ⟨i, hi⟩ := hdir p hp q hq hpq
  refine ⟨Fintype.equivFin ι i, ?_⟩
  show inSectorOS (θ ((Fintype.equivFin ι).symm (Fintype.equivFin ι i))) lam _
  rw [Equiv.symm_apply_apply]
  exact hi

/-- **Lemma 3.7 (per-circle bound).** The points of a range-1 circle are
covered by `Σ_j (⌊g_j / lam⌋ - 1)₊` wings, hence number at most `2` to
that power. -/
theorem circle_points_bound
    (V : GCfg) (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {ds : List ℝ} (hsort : ds.SortedLE) (hnodup : ds.Nodup)
    (hmem : ∀ x ∈ ds, x ∈ Set.Ico 0 Real.pi)
    {lam : ℝ} (hlam : 0 < lam) (hlampi : lam < Real.pi)
    (hne : ds ≠ [])
    {Q : Finset Plane₂}
    (hGD : ∀ p ∈ Q, ∀ q ∈ Q, p ≠ q → V.GD p q ≠ 0)
    (hGA : ∀ p ∈ Q, ∀ q ∈ Q, ∀ r ∈ Q, p ≠ q → q ≠ r → p ≠ r →
      V.GA p q r ≤ Real.pi - lam)
    (hmar : ∀ p ∈ Q, ∀ q ∈ Q, p ≠ q → ∀ x ∈ ds,
      lam ≤ |linRep (o.oangle e (V.GD p q)) - x| ∧
        |linRep (o.oangle e (V.GD p q)) - x| ≤ Real.pi - lam) :
    Q.card ≤ 2 ^ (∑ j : Fin ds.length,
      (Nat.floor (gapAfter ds j / lam) - 1)) := by
  classical
  set t : Fin ds.length → ℕ := fun j =>
    Nat.floor (gapAfter ds j / lam) - 1 with ht
  have hcard : Fintype.card (Σ j : Fin ds.length, Fin (t j)) =
      ∑ j : Fin ds.length, t j := by
    rw [Fintype.card_sigma]
    exact Finset.sum_congr rfl fun j _ => Fintype.card_fin _
  rw [← hcard]
  apply card_le_two_pow_of_wing_cover' V o e he
    (θ := fun s : (Σ j : Fin ds.length, Fin (t j)) =>
      ((ds.get s.1 + ((s.2.1 : ℝ) + 1) * lam : ℝ) : Real.Angle)) hlampi
    Q hGD hGA
  · intro p hp q hq hpq
    obtain ⟨a, b, haρ, hbρ, j, haj, hgap⟩ := gap_bracket hsort hnodup hmem
      (linRep_mem_Ico (o.oangle e (V.GD p q))) hlam
      (hmar p hp q hq hpq) hne
    have hgapos : 0 < gapAfter ds j := gapAfter_pos hsort hnodup hmem hne j
    have hfl := Nat.lt_floor_add_one (gapAfter ds j / lam)
    have hge : Nat.floor (gapAfter ds j / lam) + 1 ≤ t j + 2 := by
      show Nat.floor _ + 1 ≤ Nat.floor _ - 1 + 2
      omega
    have hspan : b - a < (2 * (t j : ℝ) + 4) * (lam / 2) := by
      have e : (2 * (t j : ℝ) + 4) * (lam / 2) = ((t j : ℝ) + 2) * lam := by
        ring
      rw [e, hgap]
      calc gapAfter ds j = gapAfter ds j / lam * lam :=
            (div_mul_cancel₀ _ hlam.ne').symm
        _ < (Nat.floor (gapAfter ds j / lam) + 1 : ℝ) * lam :=
            mul_lt_mul_of_pos_right hfl hlam
        _ ≤ ((t j : ℝ) + 2) * lam :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hge) hlam.le
    obtain ⟨l, hl1, hlt, hlmem⟩ := covered_of_gap (a := a) (b := b)
      (w := lam / 2) (t := t j) (ρ := linRep (o.oangle e (V.GD p q)))
      (by rw [show a + 2 * (lam / 2) = a + lam by ring]; exact haρ)
      (by rw [show b - 2 * (lam / 2) = b - lam by ring]; exact hbρ) hspan
    have hlmem' : linRep (o.oangle e (V.GD p q)) ∈
        Set.Ico (a + l * lam) (a + (l + 1) * lam) := by
      have e1 : a + 2 * (l : ℝ) * (lam / 2) = a + l * lam := by ring
      have e2 : a + (2 * (l : ℝ) + 2) * (lam / 2) = a + (l + 1) * lam := by ring
      rwa [e1, e2] at hlmem
    refine ⟨⟨j, ⟨l - 1, by omega⟩⟩, ?_⟩
    have hdiff : linRep (o.oangle e (V.GD p q)) - (a + l * lam) ∈
        Set.Ico 0 lam :=
      ⟨by linarith [hlmem'.1], by linarith [hlmem'.2]⟩
    apply inSectorOS_of_rep (linRep_class _) _ hdiff hlampi.le
    have hπ : ((Real.pi : ℝ) : Real.Angle) +
        ((Real.pi : ℝ) : Real.Angle) = 0 := by
      rw [← Real.Angle.coe_add, show Real.pi + Real.pi = 2 * Real.pi by ring,
        Real.Angle.coe_two_pi]
    have hπneg : -((Real.pi : ℝ) : Real.Angle) =
        ((Real.pi : ℝ) : Real.Angle) := neg_eq_of_add_eq_zero_right hπ
    have hcast : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := by
      rw [Nat.cast_sub hl1, Nat.cast_one]
    rcases haj with haj | haj
    · refine Or.inl ?_
      show ((a + l * lam : ℝ) : Real.Angle) =
        ((ds.get (⟨j, ⟨l - 1, by omega⟩⟩ :
          Σ j : Fin ds.length, Fin (t j)).1 +
          (((⟨j, ⟨l - 1, by omega⟩⟩ :
          Σ j : Fin ds.length, Fin (t j)).2.1 : ℝ) + 1) * lam : ℝ) : Real.Angle)
      rw [haj]
      have e2 : ds.get j + l * lam =
          ds.get j + (((l - 1 : ℕ) : ℝ) + 1) * lam := by
        rw [hcast]; ring
      rw [e2]
    · refine Or.inr ?_
      show ((a + l * lam : ℝ) : Real.Angle) =
        ((ds.get (⟨j, ⟨l - 1, by omega⟩⟩ :
          Σ j : Fin ds.length, Fin (t j)).1 +
          (((⟨j, ⟨l - 1, by omega⟩⟩ :
          Σ j : Fin ds.length, Fin (t j)).2.1 : ℝ) + 1) * lam : ℝ) : Real.Angle)
          + ((Real.pi : ℝ) : Real.Angle)
      rw [haj]
      have e : ds.get j - Real.pi + l * lam =
          ds.get j + l * lam - Real.pi := by ring
      rw [e, Real.Angle.coe_sub, sub_eq_add_neg, hπneg]
      have e2 : ds.get j + l * lam =
          ds.get j + (((l - 1 : ℕ) : ℝ) + 1) * lam := by
        rw [hcast]; ring
      rw [e2]

/-!
## Instantiation for a range-1 circle

For an actual range-1 circle `ci` of a GC `V` with pairwise disjoint
circles, `ds` is the sorted list of line representatives of the center
lines `o_i o_j` (Sendov's `X_i`), and `circle_points_bound` yields
`N_i ≤ 2^{k'(i)}`.
-/

section GInstantiation

open Classical

variable (V : GCfg) (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)

/-- The sorted, duplicate-free list of line representatives of the
directions from `ci`'s center to the other range-1 circle centers. -/
noncomputable def circleDirs (V : GCfg) (o : Orientation ℝ Plane₂ (Fin 2))
    (e : Plane₂) (ci : GC) : List ℝ :=
  (((V.forest.filter fun g => g ≠ ci).map fun g =>
    linRep (o.oangle e (g.centerOf - ci.centerOf))).dedup).insertionSort (· ≤ ·)

lemma mem_circleDirs {ci : GC} {x : ℝ} :
    x ∈ circleDirs V o e ci ↔
      ∃ g ∈ V.forest, g ≠ ci ∧
        x = linRep (o.oangle e (g.centerOf - ci.centerOf)) := by
  unfold circleDirs
  rw [List.mem_insertionSort, List.mem_dedup, List.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [List.mem_filter] at hg
    exact ⟨g, hg.1, decide_eq_true_iff.mp hg.2, rfl⟩
  · rintro ⟨g, hgf, hne, rfl⟩
    exact ⟨g, by rw [List.mem_filter]; exact ⟨hgf, decide_eq_true_iff.mpr hne⟩,
      rfl⟩

lemma circleDirs_sorted (ci : GC) : (circleDirs V o e ci).SortedLE := by
  unfold circleDirs
  exact (List.pairwise_insertionSort _ _).sortedLE

lemma circleDirs_nodup (ci : GC) : (circleDirs V o e ci).Nodup := by
  unfold circleDirs
  exact (List.perm_insertionSort _ _).nodup_iff.mpr (List.nodup_dedup _)

lemma circleDirs_mem_Ico {ci : GC} {x : ℝ} (hx : x ∈ circleDirs V o e ci) :
    x ∈ Set.Ico 0 Real.pi := by
  unfold circleDirs at hx
  rw [List.mem_insertionSort, List.mem_dedup, List.mem_map] at hx
  obtain ⟨g, _, rfl⟩ := hx
  exact linRep_mem_Ico _

lemma circleDirs_ne_nil (hfN : V.forest.Nodup) {ci : GC} (hci : ci ∈ V.forest) :
    circleDirs V o e ci ≠ [] := by
  obtain ⟨g, hgf, hne⟩ : ∃ g ∈ V.forest, g ≠ ci := by
    by_contra hcon
    push Not at hcon
    have h2 := V.forest_len
    rcases hl : V.forest with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;>
      rw [hl] at h2 hcon hfN
    · simp at h2
    · simp at h2
    · have ha := hcon a List.mem_cons_self
      have hb := hcon b (List.mem_cons_of_mem _ List.mem_cons_self)
      have hab : a = b := ha.trans hb.symm
      exact absurd (List.mem_cons.mpr (Or.inl hab))
        (List.nodup_cons.mp hfN).1
  intro hds
  have hmem : linRep (o.oangle e (g.centerOf - ci.centerOf)) ∈
      circleDirs V o e ci := by
    unfold circleDirs
    rw [List.mem_insertionSort, List.mem_dedup, List.mem_map]
    exact ⟨g, by rw [List.mem_filter]; exact ⟨hgf, decide_eq_true_iff.mpr hne⟩,
      rfl⟩
  rw [hds] at hmem
  exact absurd hmem (by simp)

/-- Under disjointness, the range-1 circle containing `p` is unique. -/
lemma find?_eq_of_mem (hd : V.DisjointCircles) {g : GC} {p : Plane₂}
    (hg : g ∈ V.forest) (hp : p ∈ g.points) :
    V.forest.find? (fun t => p ∈ t.points) = some g := by
  obtain ⟨g₀, hg₀, hfind, hpg₀⟩ := GCfg.find?_mem_of_mem_flatMap
    (List.mem_flatMap.mpr ⟨g, hg, hp⟩)
  by_cases h : g₀ = g
  · rwa [h] at hfind
  · exact absurd hpg₀ (V.not_mem_of_disjoint hd hg₀ hg h hp)

/-- For two points of `ci` and a point of another circle `cj`, the bound
`GA ≤ π - lam` applied in both orderings confines the angle between the
internal generalized direction `GD p p'` and the center line `o_i o_j`
to `[lam, π - lam]`. -/
lemma angle_GD_center_mem_Icc (hd : V.DisjointCircles) {ci cj : GC}
    (hci : ci ∈ V.forest) (hcj : cj ∈ V.forest) (hne : ci ≠ cj)
    {p p' q : Plane₂} (hp : p ∈ ci.points) (hp' : p' ∈ ci.points)
    (hq : q ∈ cj.points) (hpq : p ≠ p') {lam : ℝ}
    (hGA : ∀ a ∈ V.points, ∀ b ∈ V.points, ∀ c ∈ V.points,
      a ≠ b → b ≠ c → a ≠ c → V.GA a b c ≤ Real.pi - lam) :
    lam ≤ InnerProductGeometry.angle (V.GD p p') (cj.centerOf - ci.centerOf) ∧
      InnerProductGeometry.angle (V.GD p p') (cj.centerOf - ci.centerOf) ≤
        Real.pi - lam := by
  have hf_p := find?_eq_of_mem V hd hci hp
  have hf_p' := find?_eq_of_mem V hd hci hp'
  have hf_q := find?_eq_of_mem V hd hcj hq
  have hq1 : q ∉ ci.points := V.not_mem_of_disjoint hd hci hcj hne hq
  have hp2 : p ∉ cj.points := V.not_mem_of_disjoint hd hcj hci hne.symm hp
  have hp2' : p' ∉ cj.points := V.not_mem_of_disjoint hd hcj hci hne.symm hp'
  have hpV : p ∈ V.points := List.mem_flatMap.mpr ⟨ci, hci, hp⟩
  have hpV' : p' ∈ V.points := List.mem_flatMap.mpr ⟨ci, hci, hp'⟩
  have hqV : q ∈ V.points := List.mem_flatMap.mpr ⟨cj, hcj, hq⟩
  have hpq' : p ≠ q := fun h => hq1 (h ▸ hp)
  have hp'q : p' ≠ q := fun h => hq1 (h ▸ hp')
  have hup : InnerProductGeometry.angle (V.GD p p') (cj.centerOf - ci.centerOf) ≤
      Real.pi - lam := by
    have e : V.GA p' p q = _ := V.GA_two_in_one hf_p hf_q hq1 hp2
    have hb := hGA p' hpV' p hpV q hqV hpq.symm hpq' hp'q
    rwa [e] at hb
  have hlo : lam ≤ InnerProductGeometry.angle (V.GD p p')
      (cj.centerOf - ci.centerOf) := by
    have e : V.GA p p' q = _ := V.GA_two_in_one hf_p' hf_q hq1 hp2'
    have hb := hGA p hpV p' hpV' q hqV hpq hp'q hpq'
    rw [e] at hb
    have hneg : V.GD p' p = -(V.GD p p') := by
      show V.sepCenter p p' - V.sepCenter p' p =
        -(V.sepCenter p' p - V.sepCenter p p')
      rw [neg_sub]
    rw [hneg, InnerProductGeometry.angle_neg_left] at hb
    linarith
  exact ⟨hlo, hup⟩

/-- **Lemma 3.7 for a range-1 circle.** If `V` has a duplicate-free forest
of point-disjoint circles with distinct centers and nonempty point sets,
and every generalized angle is at most `π - lam`, then the number of
points of `ci` is at most `2` to `Σ_j (⌊g_j / lam⌋ - 1)₊`. -/
theorem lemma_3_7 (hd : V.DisjointCircles) (hfN : V.forest.Nodup)
    (he : e ≠ 0) {ci : GC} (hci : ci ∈ V.forest)
    (hcenters : ∀ g₁ ∈ V.forest, ∀ g₂ ∈ V.forest, g₁ ≠ g₂ →
      g₁.centerOf ≠ g₂.centerOf)
    (hnonempty : ∀ g ∈ V.forest, ∃ q, q ∈ g.points)
    {lam : ℝ} (hlam : 0 < lam) (hlampi : lam < Real.pi)
    (hGD : ∀ p ∈ ci.points, ∀ q ∈ ci.points, p ≠ q → V.GD p q ≠ 0)
    (hGA : ∀ a ∈ V.points, ∀ b ∈ V.points, ∀ c ∈ V.points,
      a ≠ b → b ≠ c → a ≠ c → V.GA a b c ≤ Real.pi - lam) :
    ci.points.toFinset.card ≤ 2 ^ (∑ j : Fin (circleDirs V o e ci).length,
      (Nat.floor (gapAfter (circleDirs V o e ci) j / lam) - 1)) := by
  classical
  refine circle_points_bound V o e he (circleDirs_sorted V o e ci)
    (circleDirs_nodup V o e ci) (fun x hx => circleDirs_mem_Ico V o e hx)
    hlam hlampi (circleDirs_ne_nil V o e hfN hci)
    (Q := ci.points.toFinset) ?_ ?_ ?_
  · intro p hp q hq hpq
    rw [List.mem_toFinset] at hp hq
    exact hGD p hp q hq hpq
  · intro p hp q hq r hr hpq hqr hpr
    rw [List.mem_toFinset] at hp hq hr
    exact hGA p (List.mem_flatMap.mpr ⟨ci, hci, hp⟩) q
      (List.mem_flatMap.mpr ⟨ci, hci, hq⟩) r
      (List.mem_flatMap.mpr ⟨ci, hci, hr⟩) hpq hqr hpr
  · intro p hp q hq hpq x hx
    rw [List.mem_toFinset] at hp hq
    obtain ⟨cj, hcj, hne, rfl⟩ := (mem_circleDirs V o e).mp hx
    obtain ⟨r, hr⟩ := hnonempty cj hcj
    have hv : cj.centerOf - ci.centerOf ≠ 0 :=
      sub_ne_zero.mpr (hcenters cj hcj ci hci hne)
    have hu : V.GD p q ≠ 0 := hGD p hp q hq hpq
    exact linRep_sub_mem_Icc he hu hv
      (angle_GD_center_mem_Icc V hd hci hcj hne.symm hp hq hr hpq hGA)

/-- Total point count decomposes over the range-1 circles. -/
theorem points_length_eq_sum :
    V.points.length = (V.forest.map fun g => g.points.length).sum :=
  List.length_flatMap

/-- **Lemma 3.7 summed over the forest.** If every circle has a
duplicate-free point list, the total number of points is at most
`Σ_i 2^{k'(i)}`. -/
theorem total_points_bound (hd : V.DisjointCircles) (hfN : V.forest.Nodup)
    (he : e ≠ 0)
    (hcenters : ∀ g₁ ∈ V.forest, ∀ g₂ ∈ V.forest, g₁ ≠ g₂ →
      g₁.centerOf ≠ g₂.centerOf)
    (hnonempty : ∀ g ∈ V.forest, ∃ q, q ∈ g.points)
    (hptN : ∀ g ∈ V.forest, g.points.Nodup)
    (hGD : ∀ ci ∈ V.forest, ∀ p ∈ ci.points, ∀ q ∈ ci.points,
      p ≠ q → V.GD p q ≠ 0)
    {lam : ℝ} (hlam : 0 < lam) (hlampi : lam < Real.pi)
    (hGA : ∀ a ∈ V.points, ∀ b ∈ V.points, ∀ c ∈ V.points,
      a ≠ b → b ≠ c → a ≠ c → V.GA a b c ≤ Real.pi - lam) :
    V.points.length ≤
      (V.forest.map fun ci => 2 ^ (∑ j : Fin (circleDirs V o e ci).length,
        (Nat.floor (gapAfter (circleDirs V o e ci) j / lam) - 1))).sum := by
  rw [points_length_eq_sum]
  apply List.sum_le_sum
  intro ci hci
  rw [← List.toFinset_card_of_nodup (hptN ci hci)]
  exact lemma_3_7 V o e hd hfN he hci hcenters hnonempty hlam hlampi
    (hGD ci hci) hGA

end GInstantiation

end Jsp404

