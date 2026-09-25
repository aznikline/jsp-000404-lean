import Jsp000404.StarReceiver

/-!
# Five points: no full-in mixed star with three defect-`2` sources

Chart as in `ProjectionDescent`: anchor `A = c v`, anchor rays
`θ_i ∈ [0, β]`, `β = π − nλ`, `n ≥ 3`.  Write `φ a b = dirRep a b`.

**Upward orientation.**  `Up a b` means the actual directed edge
`P_b − P_a` has oriented angle exactly `φ a b ∈ [0, π)`.
* `up_or_up`: every chord is upward in exactly one orientation
  (`linRep_class`).
* `up_corridor`: `Up a b ⇒ φ a b ∈ [θ_a + λ, π − λ + θ_b]`
  (endpoint caps at `a` and `b`).
* `up_of_short_first` / `up_of_short_last`: a short-first chord at `a`
  points downward (`Up b a`), a short-last chord upward (`Up a b`).
* `up_cap`: `Up a b ∧ Up b c ⇒ λ ≤ |φ b c − φ a b|` — the source-triangle
  cap `∠ a b c = π − |φ b c − φ a b| ≤ π − λ`.
* `up_trans`: `Up a b ∧ Up b c ⇒ Up a c` and `φ a c` lies strictly
  between `φ a b` and `φ b c` (`oangle_add_between`: sum of two vectors
  with directions in `(0, π)`; no wrap branch can occur).

**Five-point rows.**  `row4_defect`: a row with three distinct chords in
sorted order has defect `n − Σ gapScore` over its four actual gaps.

**Exclusion.**  `mixed_star_2F1L_core` / `mixed_star_1F2L_core` and the
orientation-free wrappers: three defect-`2` sources `P, Q, R` of a common
receiver `H` with two short-first and one short-last chord (or the
mirror) are impossible.  Consumer `five_point_high_receiver_not_full_in`:
at five points, a receiver of defect `≥ 3` whose other three rows have
defect `2` cannot receive short chords from all three.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

/-- **Sum of two vectors with nearby directions.** -/
theorem oangle_add_between (o : Orientation ℝ Plane₂ (Fin 2))
    {e a b : Plane₂} (he : e ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) {α β : ℝ}
    (hα : o.oangle e a = (α : Real.Angle)) (hβ : o.oangle e b = (β : Real.Angle))
    (hlt : α < β) (hpi : β < α + Real.pi) :
    a + b ≠ 0 ∧ ∃ γ, α < γ ∧ γ < β ∧ o.oangle e (a + b) = (γ : Real.Angle) := by
  have hab : o.oangle a b = ((β - α : ℝ) : Real.Angle) := by
    rw [← o.oangle_sub_left he ha hb, hα, hβ, Real.Angle.coe_sub]
  have hsab : (o.oangle a b).sign = 1 := by
    rw [hab, Real.Angle.sign, Real.Angle.sin_coe]
    exact sign_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  have key : ∀ θ : Real.Angle, θ.sign = 1 → 0 < θ.toReal ∧ θ.toReal < Real.pi := by
    intro θ hθ
    have hne : θ ≠ (Real.pi : Real.Angle) := by
      rintro rfl; rw [Real.Angle.sign_coe_pi] at hθ; exact absurd hθ (by decide)
    have h1 := Real.Angle.sign_toReal hne
    rw [hθ] at h1
    refine ⟨sign_eq_one_iff.mp h1, lt_of_le_of_ne (Real.Angle.toReal_le_pi θ) ?_⟩
    intro h; apply hne; rw [← Real.Angle.coe_toReal θ, h]
  have hs : a + b ≠ 0 := by
    intro h0
    have hb' : b = -a := by
      rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact h0
    rw [hb', o.oangle_neg_self_right ha, Real.Angle.sign_coe_pi] at hsab
    exact absurd hsab (by decide)
  have hs1 : (o.oangle a (a + b)).sign = 1 := by rw [o.oangle_sign_add_right, hsab]
  have hs2 : (o.oangle (a + b) b).sign = 1 := by rw [o.oangle_sign_add_left, hsab]
  obtain ⟨t0, tpi⟩ := key _ hs1
  obtain ⟨t2, _⟩ := key _ hs2
  have hsum : o.oangle e (a + b) =
      ((α + (o.oangle a (a + b)).toReal : ℝ) : Real.Angle) := by
    rw [← o.oangle_add he ha hs, hα, Real.Angle.coe_add, Real.Angle.coe_toReal]
  have h2 : o.oangle (a + b) b =
      ((β - (α + (o.oangle a (a + b)).toReal) : ℝ) : Real.Angle) := by
    rw [← o.oangle_sub_left he hs hb, hsum, hβ, Real.Angle.coe_sub]
  rw [h2, Real.Angle.toReal_coe_eq_self_iff.mpr ⟨by linarith, by linarith⟩] at t2
  exact ⟨hs, _, by linarith, by linarith, hsum⟩

/-- `linRep` of an in-range real angle. -/
theorem linRep_coe_eq_of_mem {γ : ℝ} (h0 : 0 ≤ γ) (hπ : γ < Real.pi) :
    linRep (γ : Real.Angle) = γ := by
  unfold linRep
  rw [Real.Angle.toReal_coe_eq_self_iff.mpr ⟨by linarith [Real.pi_pos], hπ.le⟩,
    if_neg (not_lt.mpr h0), if_neg (ne_of_lt hπ)]

/-- Saturated anchored chart data. -/
structure SatChart {s : ℕ} (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (n : ℕ) (lam : ℝ) (c : Fin (s + 1) → Plane₂) (v : Fin (s + 1))
    (theta : Fin s → ℝ) : Prop where
  he : e ≠ 0
  hn3 : 3 ≤ n
  hlam : 0 < lam
  hn : Nat.floor (Real.pi / lam) = n
  hleg : Section4Legality c lam
  htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
    o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle)

section Chart

variable {s n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
  {lam : ℝ} {c : Fin (s + 1) → Plane₂} {v : Fin (s + 1)}
  {theta : Fin s → ℝ}

/-- Upward orientation of the chord `a b`. -/
def Up (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin (s + 1) → Plane₂)
    (v : Fin (s + 1)) (a b : Fin s) : Prop :=
  o.oangle e (c (v.succAbove b) - c (v.succAbove a)) =
    (dirRep o e (c ∘ v.succAbove) a b : Real.Angle)

variable (C : SatChart o e n lam c v theta)
include C

theorem SatChart.hβ : Real.pi - n * lam < lam := by
  have h := Nat.lt_floor_add_one (Real.pi / lam)
  rw [C.hn, div_lt_iff₀ C.hlam] at h; linarith

theorem SatChart.hπ : Real.pi < (n + 1) * lam := by
  have h := Nat.lt_floor_add_one (Real.pi / lam)
  rw [C.hn, div_lt_iff₀ C.hlam] at h; linarith

theorem SatChart.hnl : (n : ℝ) * lam ≤ Real.pi := by
  have := Nat.floor_le (div_nonneg Real.pi_pos.le C.hlam.le)
  rw [C.hn, le_div_iff₀ C.hlam] at this; linarith

theorem SatChart.hn3' : (3 : ℝ) ≤ n := by exact_mod_cast C.hn3

theorem SatChart.pt_ne {a b : Fin s} (hab : a ≠ b) :
    c (v.succAbove a) ≠ c (v.succAbove b) :=
  fun h => hab (Fin.succAbove_right_injective (C.hleg.inj h))

theorem SatChart.pt_ne_anchor (a : Fin s) : c (v.succAbove a) ≠ c v :=
  fun h => Fin.succAbove_ne v a (C.hleg.inj h)

theorem phi_comm {a b : Fin s} (hab : a ≠ b) :
    dirRep o e (c ∘ v.succAbove) a b = dirRep o e (c ∘ v.succAbove) b a :=
  dirRep_comm o e _ C.he (C.pt_ne hab)

theorem phi_mem (a b : Fin s) :
    dirRep o e (c ∘ v.succAbove) a b ∈ Set.Ico 0 Real.pi := linRep_mem_Ico _

theorem up_or_up {a b : Fin s} (hab : a ≠ b) : Up o e c v a b ∨ Up o e c v b a := by
  rcases linRep_class (o.oangle e (c (v.succAbove b) - c (v.succAbove a))) with h | h
  · exact Or.inl h.symm
  · right
    unfold Up
    rw [show c (v.succAbove a) - c (v.succAbove b) =
        -(c (v.succAbove b) - c (v.succAbove a)) by abel,
      o.oangle_neg_right C.he (sub_ne_zero.mpr (C.pt_ne hab).symm),
      ← phi_comm C hab]
    exact h.symm

theorem up_corridor {a b : Fin s} (hab : a ≠ b) (h : Up o e c v a b) :
    theta a + lam ≤ dirRep o e (c ∘ v.succAbove) a b ∧
      dirRep o e (c ∘ v.succAbove) a b ≤ Real.pi - lam + theta b := by
  have hab' : v.succAbove a ≠ v.succAbove b :=
    fun h => hab (Fin.succAbove_right_injective h)
  have hbpi : Real.pi - n * lam < Real.pi := by
    have := C.hn3'; have := C.hlam; nlinarith
  have := directed_chord_in_corridor' o C.he (C.pt_ne_anchor a) (C.pt_ne_anchor b)
    (C.pt_ne hab) C.hβ hbpi (C.htheta a).1 (C.htheta b).1 (phi_mem C a b)
    (C.htheta a).2 (C.htheta b).2 h
    (C.hleg.triAngle v _ _ (Fin.ne_succAbove v a) hab' (Fin.ne_succAbove v b))
    (C.hleg.triAngle v _ _ (Fin.ne_succAbove v b) hab'.symm (Fin.ne_succAbove v a))
  exact this

theorem up_not_both {a b : Fin s} (hab : a ≠ b) (h1 : Up o e c v a b) :
    ¬ Up o e c v b a := by
  intro h2
  have c1 := up_corridor C hab h1
  have c2 := up_corridor C hab.symm h2
  rw [← phi_comm C hab] at c2
  -- both give φ ≥ θ + λ and the reverse direction differs by π
  unfold Up at h1 h2
  rw [show c (v.succAbove a) - c (v.succAbove b) =
      -(c (v.succAbove b) - c (v.succAbove a)) by abel,
    o.oangle_neg_right C.he (sub_ne_zero.mpr (C.pt_ne hab).symm), h1,
    ← phi_comm C hab] at h2
  have h3 : ((Real.pi : ℝ) : Real.Angle) = 0 := by
    have := congrArg (fun t => t - (dirRep o e (c ∘ v.succAbove) a b : Real.Angle)) h2
    simpa using this
  exact Real.Angle.pi_ne_zero h3

theorem up_of_short_first {a b : Fin s} (hab : a ≠ b)
    (h : dirRep o e (c ∘ v.succAbove) a b - theta a < lam) : Up o e c v b a := by
  rcases up_or_up C hab with h1 | h1
  · have := up_corridor C hab h1; linarith
  · exact h1

theorem up_of_short_last {a b : Fin s} (hab : a ≠ b)
    (h : theta a + Real.pi - dirRep o e (c ∘ v.succAbove) a b < lam) :
    Up o e c v a b := by
  rcases up_or_up C hab with h1 | h1
  · exact h1
  · have := up_corridor C hab.symm h1
    rw [← phi_comm C hab] at this; linarith

theorem up_cap {a b d : Fin s} (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d)
    (h1 : Up o e c v a b) (h2 : Up o e c v b d) :
    lam ≤ |dirRep o e (c ∘ v.succAbove) b d - dirRep o e (c ∘ v.succAbove) a b| := by
  have hcap := C.hleg.triAngle (v.succAbove a) (v.succAbove b) (v.succAbove d)
    (fun h => hab (Fin.succAbove_right_injective h))
    (fun h => hbd (Fin.succAbove_right_injective h))
    (fun h => had (Fin.succAbove_right_injective h))
  have hang := angle_eq_abs_of_half_plane_chart o C.he
    (sub_ne_zero.mpr (C.pt_ne hab).symm) (sub_ne_zero.mpr (C.pt_ne hbd).symm)
    (phi_mem C a b) (phi_mem C b d) h1 h2
  change InnerProductGeometry.angle (c (v.succAbove a) - c (v.succAbove b))
    (c (v.succAbove d) - c (v.succAbove b)) ≤ Real.pi - lam at hcap
  rw [show c (v.succAbove a) - c (v.succAbove b) =
      -(c (v.succAbove b) - c (v.succAbove a)) by abel,
    InnerProductGeometry.angle_neg_left, hang] at hcap
  linarith

theorem up_trans {a b d : Fin s} (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d)
    (h1 : Up o e c v a b) (h2 : Up o e c v b d) :
    Up o e c v a d ∧
      ((dirRep o e (c ∘ v.succAbove) a b < dirRep o e (c ∘ v.succAbove) a d ∧
          dirRep o e (c ∘ v.succAbove) a d < dirRep o e (c ∘ v.succAbove) b d) ∨
        (dirRep o e (c ∘ v.succAbove) b d < dirRep o e (c ∘ v.succAbove) a d ∧
          dirRep o e (c ∘ v.succAbove) a d < dirRep o e (c ∘ v.succAbove) a b)) := by
  have hcap := up_cap C hab hbd had h1 h2
  have hlam := C.hlam
  have m1 := phi_mem C a b
  have m2 := phi_mem C b d
  have hA : c (v.succAbove b) - c (v.succAbove a) ≠ 0 :=
    sub_ne_zero.mpr (C.pt_ne hab).symm
  have hB : c (v.succAbove d) - c (v.succAbove b) ≠ 0 :=
    sub_ne_zero.mpr (C.pt_ne hbd).symm
  have hsum : c (v.succAbove d) - c (v.succAbove a) =
      (c (v.succAbove b) - c (v.succAbove a)) +
        (c (v.succAbove d) - c (v.succAbove b)) := by abel
  have hfin : ∀ γ : ℝ, 0 ≤ γ → γ < Real.pi →
      o.oangle e (c (v.succAbove d) - c (v.succAbove a)) = (γ : Real.Angle) →
      Up o e c v a d ∧ dirRep o e (c ∘ v.succAbove) a d = γ := by
    intro γ h0 hπ hγ
    have hd : dirRep o e (c ∘ v.succAbove) a d = γ := by
      show linRep (o.oangle e (c (v.succAbove d) - c (v.succAbove a))) = γ
      rw [hγ, linRep_coe_eq_of_mem h0 hπ]
    exact ⟨by unfold Up; rw [hγ, hd], hd⟩
  rcases lt_or_gt_of_ne (show dirRep o e (c ∘ v.succAbove) a b ≠
      dirRep o e (c ∘ v.succAbove) b d by
        intro h; rw [h, sub_self, abs_zero] at hcap; linarith) with hlt | hlt
  · obtain ⟨-, γ, hg1, hg2, hγ⟩ := oangle_add_between o C.he hA hB h1 h2 hlt
      (by linarith [m1.1, m2.2])
    rw [← hsum] at hγ
    obtain ⟨hup, hd⟩ := hfin γ (by linarith [m1.1]) (by linarith [m2.2]) hγ
    exact ⟨hup, Or.inl ⟨by rw [hd]; exact hg1, by rw [hd]; exact hg2⟩⟩
  · obtain ⟨-, γ, hg1, hg2, hγ⟩ := oangle_add_between o C.he hB hA h2 h1 hlt
      (by linarith [m2.1, m1.2])
    rw [add_comm, ← hsum] at hγ
    obtain ⟨hup, hd⟩ := hfin γ (by linarith [m2.1]) (by linarith [m1.2]) hγ
    exact ⟨hup, Or.inr ⟨by rw [hd]; exact hg1, by rw [hd]; exact hg2⟩⟩

theorem phi_ge_lam {a b : Fin s} (hab : a ≠ b) :
    lam ≤ dirRep o e (c ∘ v.succAbove) a b := by
  rcases up_or_up C hab with h | h
  · linarith [up_corridor C hab h, (C.htheta a).1.1]
  · have := up_corridor C hab.symm h
    rw [← phi_comm C hab] at this
    linarith [(C.htheta b).1.1]

/-- `linearGapScore + rowDefect = n` for a non-anchor row. -/
theorem score_add_defect (hs : 2 ≤ s) (h : Fin s) :
    linearGapScore lam (theta h) (theta h + Real.pi)
        (directionRow o e (c ∘ v.succAbove) h) +
      rowDefect n lam (directionRow o e c (v.succAbove h)) = n := by
  have hlampi : lam < Real.pi := by
    have := C.hnl; have := C.hn3'; have := C.hlam; nlinarith
  have htheta' : ∀ i, theta i ∈ Set.Icc 0 lam ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle) :=
    fun i => ⟨Set.Icc_subset_Icc le_rfl C.hβ.le (C.htheta i).1, (C.htheta i).2⟩
  have hscore := anchored_rowScore_eq_linear o e C.he c C.hleg.inj v C.hlam
    hlampi theta htheta' (fun a b hab => phi_ge_lam C hab) h
  have hcells : rowCells lam (directionRow o e c (v.succAbove h)) ≤ n :=
    rowCells_directionRow_le_of_floor_eq o e c C.hlam (v.succAbove h) (by omega) C.hn
  have hsd := rowScore_eq_sub_defect lam C.hlam n _ hcells
  have hdle := rowDefect_le lam C.hlam n _ hcells
  omega

/-- **Five-point row in gap form.** -/
theorem row4_defect (hs4 : s = 4) {h a b d : Fin s}
    (hha : h ≠ a) (hhb : h ≠ b) (hhd : h ≠ d)
    (h1 : dirRep o e (c ∘ v.succAbove) h a < dirRep o e (c ∘ v.succAbove) h b)
    (h2 : dirRep o e (c ∘ v.succAbove) h b < dirRep o e (c ∘ v.succAbove) h d) :
    rowDefect n lam (directionRow o e c (v.succAbove h)) +
      ((⌊(dirRep o e (c ∘ v.succAbove) h a - theta h) / lam⌋₊ - 1) +
        ((⌊(dirRep o e (c ∘ v.succAbove) h b -
            dirRep o e (c ∘ v.succAbove) h a) / lam⌋₊ - 1) +
          ((⌊(dirRep o e (c ∘ v.succAbove) h d -
              dirRep o e (c ∘ v.succAbove) h b) / lam⌋₊ - 1) +
            (⌊(theta h + Real.pi - dirRep o e (c ∘ v.succAbove) h d) / lam⌋₊ - 1))))
      = n := by
  set A := dirRep o e (c ∘ v.succAbove) h a
  set B := dirRep o e (c ∘ v.succAbove) h b
  set D := dirRep o e (c ∘ v.succAbove) h d
  have hlen : (directionRow o e (c ∘ v.succAbove) h).length = 3 := by
    rw [directionRow_length, hs4]
  obtain ⟨p, q, r, hl⟩ := List.length_eq_three.mp hlen
  have hsort := (directionRow_sorted o e (c ∘ v.succAbove) h).pairwise
  rw [hl] at hsort
  have hpq : p ≤ q := by simp at hsort; exact hsort.1.1
  have hqr : q ≤ r := by simp at hsort; exact hsort.2
  have hmem : ∀ j, j ≠ h → dirRep o e (c ∘ v.succAbove) h j ∈ [p, q, r] := by
    intro j hj; rw [← hl]
    exact (mem_directionRow o e (c ∘ v.succAbove)).mpr ⟨j, hj, rfl⟩
  have hA := hmem a hha.symm
  have hB := hmem b hhb.symm
  have hD := hmem d hhd.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hA hB hD
  have hABD : A = p ∧ B = q ∧ D = r := by
    rcases hA with hA | hA | hA <;> rcases hB with hB | hB | hB <;>
      rcases hD with hD | hD | hD <;>
      first
      | exact ⟨hA, hB, hD⟩
      | (exfalso; linarith)
  obtain ⟨rfl, rfl, rfl⟩ := hABD
  have key := score_add_defect C (by omega) h
  rw [hl] at key
  simp only [linearGapScore, gapScore] at key
  omega

end Chart

/-! ### Floor arithmetic helpers -/

theorem fl_lt {lam g : ℝ} (hlam : 0 < lam) {K : ℕ} (hK : K ≠ 0)
    (hg : g < K * lam) : ⌊g / lam⌋₊ < K := by
  rw [Nat.floor_lt' hK, div_lt_iff₀ hlam]; exact hg

theorem fl_ge {lam g : ℝ} (hlam : 0 < lam) {K : ℕ} (hg : K * lam ≤ g) :
    K ≤ ⌊g / lam⌋₊ := by
  apply Nat.le_floor; rw [le_div_iff₀ hlam]; exact hg

theorem fl_mul_le {lam g : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g) :
    (⌊g / lam⌋₊ : ℝ) * lam ≤ g := by
  have := Nat.floor_le (div_nonneg hg hlam.le); rwa [le_div_iff₀ hlam] at this

theorem fl_sum4 {lam : ℝ} (hlam : 0 < lam) {n : ℕ}
    (hπ : Real.pi < (n + 1) * lam) {g₁ g₂ g₃ g₄ : ℝ}
    (h₁ : 0 ≤ g₁) (h₂ : 0 ≤ g₂) (h₃ : 0 ≤ g₃) (h₄ : 0 ≤ g₄)
    (hs : g₁ + g₂ + g₃ + g₄ = Real.pi) :
    ⌊g₁ / lam⌋₊ + ⌊g₂ / lam⌋₊ + ⌊g₃ / lam⌋₊ + ⌊g₄ / lam⌋₊ ≤ n := by
  have e₁ := fl_mul_le hlam h₁
  have e₂ := fl_mul_le hlam h₂
  have e₃ := fl_mul_le hlam h₃
  have e₄ := fl_mul_le hlam h₄
  have hlt : ((⌊g₁ / lam⌋₊ + ⌊g₂ / lam⌋₊ + ⌊g₃ / lam⌋₊ + ⌊g₄ / lam⌋₊ : ℕ) : ℝ) * lam <
      ((n + 1 : ℕ) : ℝ) * lam := by push_cast; linarith
  have := lt_of_mul_lt_mul_right hlt hlam.le
  have : ⌊g₁ / lam⌋₊ + ⌊g₂ / lam⌋₊ + ⌊g₃ / lam⌋₊ + ⌊g₄ / lam⌋₊ < n + 1 := by
    exact_mod_cast this
  omega

section Core

variable {n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
  {lam : ℝ} {c : Fin (4 + 1) → Plane₂} {v : Fin (4 + 1)}
  {theta : Fin 4 → ℝ}

variable (C : SatChart o e n lam c v theta)
include C

set_option maxHeartbeats 1000000 in
/-- **Two short-first sources `P, Q`, one short-last source `R`**, with the
chord `P Q` upward.  Contradiction. -/
theorem mixed_star_2F1L_core {H P Q R : Fin 4}
    (hHP : H ≠ P) (hHQ : H ≠ Q) (hHR : H ≠ R) (hPQ : P ≠ Q) (hPR : P ≠ R)
    (hQR : Q ≠ R)
    (hP : dirRep o e (c ∘ v.succAbove) P H - theta P < lam)
    (hQ : dirRep o e (c ∘ v.succAbove) Q H - theta Q < lam)
    (hR : theta R + Real.pi - dirRep o e (c ∘ v.succAbove) R H < lam)
    (hdP : rowDefect n lam (directionRow o e c (v.succAbove P)) = 2)
    (hdQ : rowDefect n lam (directionRow o e c (v.succAbove Q)) = 2)
    (hdR : rowDefect n lam (directionRow o e c (v.succAbove R)) = 2)
    (hup : Up o e c v P Q) : False := by
  have hlam := C.hlam
  have hβ := C.hβ
  have hπ := C.hπ
  have hn3 := C.hn3'
  have hn3N := C.hn3
  obtain ⟨tH0, tH1⟩ := (C.htheta H).1
  obtain ⟨tP0, tP1⟩ := (C.htheta P).1
  obtain ⟨tQ0, tQ1⟩ := (C.htheta Q).1
  obtain ⟨tR0, tR1⟩ := (C.htheta R).1
  -- Stage 1: geometry, stated on `dirRep` terms.
  have uHP : Up o e c v H P := up_of_short_first C hHP.symm hP
  have uHQ : Up o e c v H Q := up_of_short_first C hHQ.symm hQ
  have uRH : Up o e c v R H := up_of_short_last C hHR.symm hR
  obtain ⟨cHP1, cHP2⟩ := up_corridor C hHP uHP
  obtain ⟨cHQ1, cHQ2⟩ := up_corridor C hHQ uHQ
  obtain ⟨cRH1, cRH2⟩ := up_corridor C hHR.symm uRH
  obtain ⟨cPQ1, cPQ2⟩ := up_corridor C hPQ hup
  obtain ⟨uRP, bx⟩ := up_trans C hHR.symm hHP hPR.symm uRH uHP
  obtain ⟨-, byy⟩ := up_trans C hHR.symm hHQ hQR.symm uRH uHQ
  obtain ⟨-, bv⟩ := up_trans C hHP hPQ hHQ uHP hup
  obtain ⟨-, bz⟩ := up_trans C hPR.symm hPQ hQR.symm uRP hup
  have k1 := up_cap C hHP hPQ hHQ uHP hup
  have k2 := up_cap C hPR.symm hPQ hQR.symm uRP hup
  obtain ⟨cRP1, cRP2⟩ := up_corridor C hPR.symm uRP
  have eP := phi_comm C hHP.symm
  have eQ := phi_comm C hHQ.symm
  have ePR := phi_comm C hPR
  have eQR := phi_comm C hQR
  have eQP := phi_comm C hPQ.symm
  rw [eP] at hP
  rw [eQ] at hQ
  have rPA := row4_defect C rfl hHP.symm hPQ hPR
  have rPB := row4_defect C rfl hHP.symm hPR hPQ
  have rRB := row4_defect C rfl hPR.symm hQR.symm hHR.symm
  have rQB := row4_defect C rfl hHQ.symm hQR hPQ.symm
  rw [eP, ePR] at rPA rPB
  rw [eQ, eQR, eQP] at rQB
  rw [hdP] at rPA rPB
  rw [hdR] at rRB
  rw [hdQ] at rQB
  -- Stage 2: names.
  set u := dirRep o e (c ∘ v.succAbove) H P with hu
  set vv := dirRep o e (c ∘ v.succAbove) H Q with hvv
  set w := dirRep o e (c ∘ v.succAbove) R H with hw
  set x := dirRep o e (c ∘ v.succAbove) R P with hx
  set y := dirRep o e (c ∘ v.succAbove) R Q with hy
  set z := dirRep o e (c ∘ v.succAbove) P Q with hz
  -- Stage 3: order and arithmetic.
  have hnl : 3 * lam ≤ n * lam := mul_le_mul_of_nonneg_right hn3 hlam.le
  have huw : u < w := by linarith [tP1, tR0]
  have hvw : vv < w := by linarith [tQ1, tR0]
  have hx1 : u < x ∧ x < w := by
    rcases bx with h | h
    · exfalso; linarith [h.1, h.2]
    · exact h
  have hy1 : vv < y ∧ y < w := by
    rcases byy with h | h
    · exfalso; linarith [h.1, h.2]
    · exact h
  have hv1 : u < vv ∧ vv < z := by
    rcases bv with h | h
    · exact h
    · exfalso
      rw [abs_of_neg (by linarith [h.1, h.2] : z - u < 0)] at k1
      linarith [cPQ1]
  have hzu : lam ≤ z - u := by
    rw [abs_of_pos (by linarith [hv1.1, hv1.2] : 0 < z - u)] at k1; exact k1
  have hxz : x ≠ z := by
    intro h; rw [h, sub_self, abs_zero] at k2; linarith
  rcases lt_or_gt_of_ne hxz with hxz | hzx
  · -- Branch B: `x < z`.
    have hy2 : x < y ∧ y < z := by
      rcases bz with h | h
      · exact h
      · exfalso; linarith [h.1, h.2]
    rw [abs_of_pos (by linarith : 0 < z - x)] at k2
    -- Row `R` forces `x − θ_R ≥ 2λ`.
    have eR := rRB hy2.1 hy1.2
    have hxR : 2 * lam ≤ x - theta R := by
      by_contra hc
      push_neg at hc
      have f1 := fl_lt (g := x - theta R) (K := 2) hlam two_ne_zero
        (by push_cast; linarith)
      have f4 := fl_lt (g := theta R + Real.pi - w) (K := 1) hlam one_ne_zero
        (by push_cast; linarith)
      have e2 := fl_mul_le hlam (by linarith : (0 : ℝ) ≤ y - x)
      have e3 := fl_mul_le hlam (by linarith : (0 : ℝ) ≤ w - y)
      have hmid : ((⌊(y - x) / lam⌋₊ + ⌊(w - y) / lam⌋₊ + 1 : ℕ) : ℝ) * lam <
          (n : ℝ) * lam := by
        push_cast; linarith [cRH2, cHP1]
      have hmid' := lt_of_mul_lt_mul_right hmid hlam.le
      have hmid'' : ⌊(y - x) / lam⌋₊ + ⌊(w - y) / lam⌋₊ + 1 < n := by
        exact_mod_cast hmid'
      omega
    -- Row `P` forces a short last gap.
    have eP' := rPB hx1.1 hxz
    have hPl : theta P + Real.pi - z < lam := by
      by_contra hc
      push_neg at hc
      have f1 := fl_lt (g := u - theta P) (K := 1) hlam one_ne_zero
        (by push_cast; linarith)
      have f3 := fl_ge (g := z - x) (K := 1) hlam (by push_cast; linarith)
      have f4 := fl_ge (g := theta P + Real.pi - z) (K := 1) hlam
        (by push_cast; linarith)
      have hs := fl_sum4 hlam hπ (by linarith : (0 : ℝ) ≤ u - theta P)
        (by linarith : (0 : ℝ) ≤ x - u) (by linarith : (0 : ℝ) ≤ z - x)
        (by linarith : (0 : ℝ) ≤ theta P + Real.pi - z) (by ring)
      have h34 : ⌊(z - x) / lam⌋₊ + ⌊(theta P + Real.pi - z) / lam⌋₊ = n := by
        omega
      have e3 := fl_mul_le hlam (by linarith : (0 : ℝ) ≤ z - x)
      have e4 := fl_mul_le hlam (by linarith : (0 : ℝ) ≤ theta P + Real.pi - z)
      have hc34 : ((⌊(z - x) / lam⌋₊ : ℕ) : ℝ) +
          ((⌊(theta P + Real.pi - z) / lam⌋₊ : ℕ) : ℝ) = n := by
        exact_mod_cast h34
      have hm : (((⌊(z - x) / lam⌋₊ : ℕ) : ℝ) +
          ((⌊(theta P + Real.pi - z) / lam⌋₊ : ℕ) : ℝ)) * lam = n * lam := by
        rw [hc34]
      linarith
    -- Row `Q`: the huge gap is pinned at `z − y`, total length exceeds `π`.
    have eQ' := rQB hy1.1 hy2.2
    have f1 := fl_lt (g := vv - theta Q) (K := 1) hlam one_ne_zero
      (by push_cast; linarith)
    have f4a := fl_ge (g := theta Q + Real.pi - z) (K := 1) hlam
      (by push_cast; linarith [cPQ2])
    have f4b := fl_lt (g := theta Q + Real.pi - z) (K := 2) hlam two_ne_zero
      (by push_cast; linarith [tQ1, tP0])
    have f2 := fl_lt (g := y - vv) (K := n - 1) hlam (by omega)
      (by push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; linarith [cRH2, cHQ1])
    have hs := fl_sum4 hlam hπ (by linarith : (0 : ℝ) ≤ vv - theta Q)
      (by linarith : (0 : ℝ) ≤ y - vv) (by linarith : (0 : ℝ) ≤ z - y)
      (by linarith : (0 : ℝ) ≤ theta Q + Real.pi - z) (by ring)
    have hq3 : n - 1 ≤ ⌊(z - y) / lam⌋₊ := by omega
    have e3 := fl_mul_le hlam (by linarith : (0 : ℝ) ≤ z - y)
    have hq3' : ((n - 1 : ℕ) : ℝ) ≤ ((⌊(z - y) / lam⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast hq3
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at hq3'
    have hm := mul_le_mul_of_nonneg_right hq3' hlam.le
    linarith [hy2.1]
  · -- Branch A: `z < x`.
    rw [abs_of_neg (by linarith : z - x < 0)] at k2
    have eP' := rPA (by linarith [hv1.1, hv1.2]) hzx
    have f1 := fl_lt (g := u - theta P) (K := 1) hlam one_ne_zero
      (by push_cast; linarith)
    have f2 := fl_ge (g := z - u) (K := 1) hlam (by push_cast; linarith)
    have f3 := fl_ge (g := x - z) (K := 1) hlam (by push_cast; linarith)
    have f4 := fl_ge (g := theta P + Real.pi - x) (K := 1) hlam
      (by push_cast; linarith [cRP2])
    have hs := fl_sum4 hlam hπ (by linarith : (0 : ℝ) ≤ u - theta P)
      (by linarith : (0 : ℝ) ≤ z - u) (by linarith : (0 : ℝ) ≤ x - z)
      (by linarith [cRP2] : (0 : ℝ) ≤ theta P + Real.pi - x) (by ring)
    omega

set_option maxHeartbeats 1000000 in
/-- **Mirror: one short-first source `R`, two short-last sources `P, Q`**,
with the chord `Q P` upward.  Contradiction. -/
theorem mixed_star_1F2L_core {H P Q R : Fin 4}
    (hHP : H ≠ P) (hHQ : H ≠ Q) (hHR : H ≠ R) (hPQ : P ≠ Q) (hPR : P ≠ R)
    (hQR : Q ≠ R)
    (hP : theta P + Real.pi - dirRep o e (c ∘ v.succAbove) P H < lam)
    (hQ : theta Q + Real.pi - dirRep o e (c ∘ v.succAbove) Q H < lam)
    (hR : dirRep o e (c ∘ v.succAbove) R H - theta R < lam)
    (hdP : rowDefect n lam (directionRow o e c (v.succAbove P)) = 2)
    (hdQ : rowDefect n lam (directionRow o e c (v.succAbove Q)) = 2)
    (hdR : rowDefect n lam (directionRow o e c (v.succAbove R)) = 2)
    (hup : Up o e c v Q P) : False := by
  have hlam := C.hlam
  have hβ := C.hβ
  have hπ := C.hπ
  have hn3 := C.hn3'
  have hn3N := C.hn3
  obtain ⟨tH0, tH1⟩ := (C.htheta H).1
  obtain ⟨tP0, tP1⟩ := (C.htheta P).1
  obtain ⟨tQ0, tQ1⟩ := (C.htheta Q).1
  obtain ⟨tR0, tR1⟩ := (C.htheta R).1
  -- Stage 1.
  have uPH : Up o e c v P H := up_of_short_last C hHP.symm hP
  have uQH : Up o e c v Q H := up_of_short_last C hHQ.symm hQ
  have uHR : Up o e c v H R := up_of_short_first C hHR.symm hR
  obtain ⟨cPH1, cPH2⟩ := up_corridor C hHP.symm uPH
  obtain ⟨cQH1, cQH2⟩ := up_corridor C hHQ.symm uQH
  obtain ⟨cHR1, cHR2⟩ := up_corridor C hHR uHR
  obtain ⟨cQP1, cQP2⟩ := up_corridor C hPQ.symm hup
  obtain ⟨uPR, bx⟩ := up_trans C hHP.symm hHR hPR uPH uHR
  obtain ⟨-, byy⟩ := up_trans C hHQ.symm hHR hQR uQH uHR
  obtain ⟨-, bv⟩ := up_trans C hPQ.symm hHP.symm hHQ.symm hup uPH
  obtain ⟨-, bz⟩ := up_trans C hPQ.symm hPR hQR hup uPR
  have k1 := up_cap C hPQ.symm hHP.symm hHQ.symm hup uPH
  have k2 := up_cap C hPQ.symm hPR hQR hup uPR
  obtain ⟨cPR1, cPR2⟩ := up_corridor C hPR uPR
  have eRH := phi_comm C hHR.symm
  have eRQ := phi_comm C hQR.symm
  have eRP := phi_comm C hPR.symm
  have ePQ := phi_comm C hPQ
  rw [eRH] at hR
  have rPA := row4_defect C rfl hPR hPQ hHP.symm
  have rPB := row4_defect C rfl hPQ hPR hHP.symm
  have rRB := row4_defect C rfl hHR.symm hQR.symm hPR.symm
  have rQB := row4_defect C rfl hPQ.symm hQR hHQ.symm
  rw [ePQ] at rPA rPB
  rw [eRH, eRQ, eRP] at rRB
  rw [hdP] at rPA rPB
  rw [hdR] at rRB
  rw [hdQ] at rQB
  -- Stage 2.
  set u := dirRep o e (c ∘ v.succAbove) P H with hu
  set vv := dirRep o e (c ∘ v.succAbove) Q H with hvv
  set w := dirRep o e (c ∘ v.succAbove) H R with hw
  set x := dirRep o e (c ∘ v.succAbove) P R with hx
  set y := dirRep o e (c ∘ v.succAbove) Q R with hy
  set z := dirRep o e (c ∘ v.succAbove) Q P with hz
  -- Stage 3.
  have hnl : 3 * lam ≤ n * lam := mul_le_mul_of_nonneg_right hn3 hlam.le
  have hwu : w < u := by linarith [tR1, tP0]
  have hwv : w < vv := by linarith [tR1, tQ0]
  have hx1 : w < x ∧ x < u := by
    rcases bx with h | h
    · exfalso; linarith [h.1, h.2]
    · exact h
  have hy1 : w < y ∧ y < vv := by
    rcases byy with h | h
    · exfalso; linarith [h.1, h.2]
    · exact h
  have hv1 : z < vv ∧ vv < u := by
    rcases bv with h | h
    · exact h
    · exfalso
      rw [abs_of_neg (by linarith [h.1, h.2] : u - z < 0)] at k1
      linarith [cQP2]
  have hzu : lam ≤ u - z := by
    rw [abs_of_pos (by linarith [hv1.1, hv1.2] : 0 < u - z)] at k1; exact k1
  have hxz : x ≠ z := by
    intro h; rw [h, sub_self, abs_zero] at k2; linarith
  rcases lt_or_gt_of_ne hxz with hxz | hzx
  · -- Branch A': `x < z`.
    rw [abs_of_neg (by linarith : x - z < 0)] at k2
    have eP' := rPA hxz (by linarith [hv1.1, hv1.2])
    have f1 := fl_ge (g := x - theta P) (K := 1) hlam
      (by push_cast; linarith [cPR1])
    have f2 := fl_ge (g := z - x) (K := 1) hlam (by push_cast; linarith)
    have f3 := fl_ge (g := u - z) (K := 1) hlam (by push_cast; linarith)
    have f4 := fl_lt (g := theta P + Real.pi - u) (K := 1) hlam one_ne_zero
      (by push_cast; linarith)
    have hs := fl_sum4 hlam hπ (by linarith [cPR1] : (0 : ℝ) ≤ x - theta P)
      (by linarith : (0 : ℝ) ≤ z - x) (by linarith : (0 : ℝ) ≤ u - z)
      (by linarith [cPH2] : (0 : ℝ) ≤ theta P + Real.pi - u) (by ring)
    omega
  · -- Branch B': `z < x`.
    have hy2 : z < y ∧ y < x := by
      rcases bz with h | h
      · exact h
      · exfalso; linarith [h.1, h.2]
    rw [abs_of_pos (by linarith : 0 < x - z)] at k2
    -- Row `R` forces `θ_R + π − x ≥ 2λ`.
    have eR := rRB hy1.1 hy2.2
    have hxR : 2 * lam ≤ theta R + Real.pi - x := by
      by_contra hc
      push_neg at hc
      have f1 := fl_lt (g := w - theta R) (K := 1) hlam one_ne_zero
        (by push_cast; linarith)
      have f4 := fl_lt (g := theta R + Real.pi - x) (K := 2) hlam two_ne_zero
        (by push_cast; linarith)
      have e2 := fl_mul_le hlam (by linarith : (0 : ℝ) ≤ y - w)
      have e3 := fl_mul_le hlam (by linarith : (0 : ℝ) ≤ x - y)
      have hmid : ((⌊(y - w) / lam⌋₊ + ⌊(x - y) / lam⌋₊ + 1 : ℕ) : ℝ) * lam <
          (n : ℝ) * lam := by
        push_cast; linarith [cPH2, cHR1]
      have hmid' := lt_of_mul_lt_mul_right hmid hlam.le
      have hmid'' : ⌊(y - w) / lam⌋₊ + ⌊(x - y) / lam⌋₊ + 1 < n := by
        exact_mod_cast hmid'
      omega
    -- Row `P` forces a short first gap.
    have eP' := rPB hzx (by linarith [hx1.1, hx1.2])
    have hPf : z - theta P < lam := by
      by_contra hc
      push_neg at hc
      have f1 := fl_ge (g := z - theta P) (K := 1) hlam (by push_cast; linarith)
      have f2 := fl_ge (g := x - z) (K := 1) hlam (by push_cast; linarith)
      have f4 := fl_lt (g := theta P + Real.pi - u) (K := 1) hlam one_ne_zero
        (by push_cast; linarith)
      have hs := fl_sum4 hlam hπ (by linarith : (0 : ℝ) ≤ z - theta P)
        (by linarith : (0 : ℝ) ≤ x - z) (by linarith : (0 : ℝ) ≤ u - x)
        (by linarith [cPH2] : (0 : ℝ) ≤ theta P + Real.pi - u) (by ring)
      have h12 : ⌊(z - theta P) / lam⌋₊ + ⌊(x - z) / lam⌋₊ = n := by
        omega
      have e1 := fl_mul_le hlam (by linarith : (0 : ℝ) ≤ z - theta P)
      have e2 := fl_mul_le hlam (by linarith : (0 : ℝ) ≤ x - z)
      have hc12 : ((⌊(z - theta P) / lam⌋₊ : ℕ) : ℝ) +
          ((⌊(x - z) / lam⌋₊ : ℕ) : ℝ) = n := by
        exact_mod_cast h12
      have hm : (((⌊(z - theta P) / lam⌋₊ : ℕ) : ℝ) +
          ((⌊(x - z) / lam⌋₊ : ℕ) : ℝ)) * lam = n * lam := by
        rw [hc12]
      linarith
    -- Row `Q`: the huge gap is pinned at `y − z`.
    have eQ' := rQB hy2.1 hy1.2
    have f1a := fl_ge (g := z - theta Q) (K := 1) hlam
      (by push_cast; linarith [cQP1])
    have f1b := fl_lt (g := z - theta Q) (K := 2) hlam two_ne_zero
      (by push_cast; linarith [tQ0, tP1])
    have f4 := fl_lt (g := theta Q + Real.pi - vv) (K := 1) hlam one_ne_zero
      (by push_cast; linarith)
    have f3 := fl_lt (g := vv - y) (K := n - 1) hlam (by omega)
      (by push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; linarith [cQH2, cHR1])
    have hs := fl_sum4 hlam hπ (by linarith [cQP1] : (0 : ℝ) ≤ z - theta Q)
      (by linarith : (0 : ℝ) ≤ y - z) (by linarith : (0 : ℝ) ≤ vv - y)
      (by linarith [cQH2] : (0 : ℝ) ≤ theta Q + Real.pi - vv) (by ring)
    have hq2 : n - 1 ≤ ⌊(y - z) / lam⌋₊ := by omega
    have e2 := fl_mul_le hlam (by linarith : (0 : ℝ) ≤ y - z)
    have hq2' : ((n - 1 : ℕ) : ℝ) ≤ ((⌊(y - z) / lam⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast hq2
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at hq2'
    have hm := mul_le_mul_of_nonneg_right hq2' hlam.le
    linarith [hy2.2]

/-- **Two short-first, one short-last defect-`2` sources: impossible.** -/
theorem mixed_star_2F1L {H P Q R : Fin 4}
    (hHP : H ≠ P) (hHQ : H ≠ Q) (hHR : H ≠ R) (hPQ : P ≠ Q) (hPR : P ≠ R)
    (hQR : Q ≠ R)
    (hP : dirRep o e (c ∘ v.succAbove) P H - theta P < lam)
    (hQ : dirRep o e (c ∘ v.succAbove) Q H - theta Q < lam)
    (hR : theta R + Real.pi - dirRep o e (c ∘ v.succAbove) R H < lam)
    (hdP : rowDefect n lam (directionRow o e c (v.succAbove P)) = 2)
    (hdQ : rowDefect n lam (directionRow o e c (v.succAbove Q)) = 2)
    (hdR : rowDefect n lam (directionRow o e c (v.succAbove R)) = 2) : False := by
  rcases up_or_up C hPQ with h | h
  · exact mixed_star_2F1L_core C hHP hHQ hHR hPQ hPR hQR hP hQ hR hdP hdQ hdR h
  · exact mixed_star_2F1L_core C hHQ hHP hHR hPQ.symm hQR hPR hQ hP hR hdQ hdP hdR h

/-- **One short-first, two short-last defect-`2` sources: impossible.** -/
theorem mixed_star_1F2L {H P Q R : Fin 4}
    (hHP : H ≠ P) (hHQ : H ≠ Q) (hHR : H ≠ R) (hPQ : P ≠ Q) (hPR : P ≠ R)
    (hQR : Q ≠ R)
    (hP : theta P + Real.pi - dirRep o e (c ∘ v.succAbove) P H < lam)
    (hQ : theta Q + Real.pi - dirRep o e (c ∘ v.succAbove) Q H < lam)
    (hR : dirRep o e (c ∘ v.succAbove) R H - theta R < lam)
    (hdP : rowDefect n lam (directionRow o e c (v.succAbove P)) = 2)
    (hdQ : rowDefect n lam (directionRow o e c (v.succAbove Q)) = 2)
    (hdR : rowDefect n lam (directionRow o e c (v.succAbove R)) = 2) : False := by
  rcases up_or_up C hPQ with h | h
  · exact mixed_star_1F2L_core C hHQ hHP hHR hPQ.symm hQR hPR hQ hP hR hdQ hdP hdR h
  · exact mixed_star_1F2L_core C hHP hHQ hHR hPQ hPR hQR hP hQ hR hdP hdQ hdR h

/-- **Consumer (five points).**  A receiver of defect `≥ 3` whose three
other non-anchor rows have defect `2` cannot receive short chords from all
three of them. -/
theorem five_point_high_receiver_not_full_in (H : Fin 4)
    (hhigh : 3 ≤ rowDefect n lam (directionRow o e c (v.succAbove H)))
    (hlow : ∀ j, j ≠ H →
      rowDefect n lam (directionRow o e c (v.succAbove j)) = 2) :
    ¬ ∀ j, j ≠ H → ShortWitness (lam := lam) (c := c) o e v theta j H := by
  intro hstar
  have hn2 : 2 ≤ n := by have := C.hn3; omega
  obtain ⟨⟨j1, hj1, hlt1⟩, ⟨j2, hj2, hlt2⟩, -⟩ := star_receiver_high_is_mixed C.he
    C.hn3 C.hlam C.hn C.hleg C.htheta (by norm_num) H hstar hhigh
  have hf1 : dirRep o e (c ∘ v.succAbove) j1 H - theta j1 < lam := by
    obtain ⟨-, h | h⟩ := hstar j1 hj1
    · exact h
    · exfalso
      have := saturated_row_top_sliver_forces_high o e C.he hn2 C.hlam C.hn
        C.hleg v C.htheta j1 H hj1 le_rfl (by linarith)
      linarith
  have hl2 : theta j2 + Real.pi - dirRep o e (c ∘ v.succAbove) j2 H < lam := by
    obtain ⟨-, h | h⟩ := hstar j2 hj2
    · exfalso
      have := saturated_row_bot_sliver_forces_low o e C.he hn2 C.hlam C.hn
        C.hleg v C.htheta j2 H hj2 le_rfl (by linarith)
      linarith
    · exact h
  have h12 : j1 ≠ j2 := by rintro rfl; linarith
  have key : ∀ a b d : Fin 4, ∃ x : Fin 4, x ≠ a ∧ x ≠ b ∧ x ≠ d := by decide
  obtain ⟨j3, h3H, h31, h32⟩ := key H j1 j2
  obtain ⟨-, h3 | h3⟩ := hstar j3 h3H
  · exact mixed_star_2F1L C hj1.symm h3H.symm hj2.symm h31.symm h12 h32 hf1 h3 hl2
      (hlow j1 hj1) (hlow j3 h3H) (hlow j2 hj2)
  · exact mixed_star_1F2L C hj2.symm h3H.symm hj1.symm h32.symm h12.symm h31 hl2 h3
      hf1 (hlow j2 hj2) (hlow j3 h3H) (hlow j1 hj1)

end Core

#print axioms oangle_add_between
#print axioms up_trans
#print axioms up_cap
#print axioms row4_defect
#print axioms mixed_star_2F1L
#print axioms mixed_star_1F2L
#print axioms five_point_high_receiver_not_full_in

end Jsp404
