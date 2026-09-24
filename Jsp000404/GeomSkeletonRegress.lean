import Jsp000404.GeomSkeleton
import Jsp000404.MaxGapCountermodel2

/-!
# Geometry→Skeleton bridge regression fixture
(JSP404-GEOMETRY-SKELETON-BRIDGE-01)

Concrete-data checks for `Jsp000404.GeomSkeleton` on the proved-legal
square configuration `sq` of `MaxGapCountermodel2.lean` at
`λ = 5π/12` (`⌊π/λ⌋₊ = 2`, `δ = 2/5`):

* `Proper` / `ModeA` / `Consistent` on the square;
* `q`/`r` bounds and `q + r = gapAfter / λ` (floor binding `⌊π/λ⌋₊ = 2`
  and `δ` binding `δ = 2/5`);
* arc telescoping, including the cyclic-cut (descending `pos`) branch;
* `angleExpr` ↔ geometric angle, including the self-slot reduction;
* lift-bit controls: `rawBit 0 1 = false` (negative control),
  `rawBit 1 0 = true` (positive control);
* `kexp = 0`, `d = 1`, `W = 2 = potential / 2^{n-1}` — the exact `W/K`
  factor — plus `potential = 4`;
* degenerate `s = 2` rows (single wrap-around gap, `Fin 1` positions).

`#print axioms` at the end pins the bridge to the classical axioms only.
-/

namespace Jsp404

open Classical Finset
open scoped EuclideanGeometry EuclideanSpace

noncomputable section

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}

/-- The square's bridged skeleton (`s = 4`, `λ = 5π/12`). -/
abbrev sqSk (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) : Skeleton 4 :=
  bridgeSkeleton o e (sq o e) sqLam (by decide)

/-- The square's canonical `ModeA` remainders. -/
abbrev sqR (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) :
    Fin 4 → Fin 3 → ℝ :=
  bridgeR o e (sq o e) sqLam (by decide)

/-! ### Strip and scale bindings -/

/-- `π/λ = 12/5` on the square scale. -/
lemma pi_div_sqLam : Real.pi / sqLam = 12 / 5 := by
  unfold sqLam
  rw [div_eq_iff (ne_of_gt (by positivity : (0:ℝ) < 5 * Real.pi / 12))]
  ring

/-- Floor binding: the square sits in the `n = 2` strip. -/
lemma hn_sq : ⌊Real.pi / sqLam⌋₊ = 2 := by
  rw [pi_div_sqLam,
    Nat.floor_eq_iff (by norm_num : (0:ℝ) ≤ 12 / 5)]
  exact ⟨by norm_num, by norm_num⟩

lemma sqLam_le_pi : sqLam ≤ Real.pi := by
  unfold sqLam; linarith [Real.pi_pos]

/-- `δ` binding: `δ = π/λ − n = 2/5` on the square. -/
lemma sq_delta : bridgeDelta sqLam 2 = 2 / 5 := by
  unfold bridgeDelta
  rw [pi_div_sqLam]
  norm_num

/-! ### `Proper`, `ModeA`, `Consistent` on the square -/

lemma sq_proper : (sqSk o e).Proper :=
  bridgeSkeleton_proper o e (sq o e) sqLam (by decide)

lemma sq_modeA (he : e ≠ 0) :
    ModeA 2 (sqSk o e) (sqR o e) (bridgeDelta sqLam 2) :=
  geomSkeleton_modeA o e (sq o e) sqLam 2 (by decide) he
    (sq_legal he) sqLam_le_pi hn_sq

lemma sq_consistent (he : e ≠ 0) : (sqSk o e).Consistent 2 :=
  geomSkeleton_consistent o e (sq o e) sqLam 2 (by decide) he
    (sq_legal he) sqLam_le_pi hn_sq

/-! ### `q`/`r` canonical decomposition on the square -/

lemma sq_r_nonneg (x : Fin 4) (g : Fin 3) : 0 ≤ sqR o e x g :=
  r_nn o e (sq o e) sqLam sqLam_pos (by decide) x g

lemma sq_r_lt_one (x : Fin 4) (g : Fin 3) : sqR o e x g < 1 :=
  r_lt_one o e (sq o e) sqLam (by decide) x g

lemma sq_q_add_r (x : Fin 4) (g : Fin 3) :
    (((sqSk o e).vtx x).q g : ℝ) + sqR o e x g =
      gapAfter (directionRow o e (sq o e) x)
        ⟨g.1, by rw [directionRow_length]; exact g.2⟩ / sqLam :=
  q_add_r o e (sq o e) sqLam (by decide) x g

lemma sq_fan (x : Fin 4) :
    (∑ g, sqR o e x g) - bridgeDelta sqLam 2 =
      (2 : ℝ) - ↑(∑ g, ((sqSk o e).vtx x).q g) :=
  fan_eq o e (sq o e) sqLam 2 (by decide) x

/-! ### Arc telescoping: cyclic-cut (descending `pos`) branch

`pos 0 3 = 2 > pos 0 1 = 0`, so `arc 0 3 1 = Ico 0 2` exercises the
`inr` branch of `arc_gapAfter`: the wrap-around sum equals
`|d_{1} − d_{3}|`. -/

lemma sq_arc_desc :
    ∑ g ∈ ((sqSk o e).vtx 0).arc 3 1,
        gapAfter (directionRow o e (sq o e) 0)
          ⟨g.1, by rw [directionRow_length]; exact g.2⟩ =
      |dirRep o e (sq o e) 0 (selfIdx (by decide : 2 ≤ 4) 0 1) -
        dirRep o e (sq o e) 0 (selfIdx (by decide : 2 ≤ 4) 0 3)| :=
  arc_gapAfter o e (sq o e) sqLam (by decide) 0 3 1

lemma sq_arcSum_desc :
    ∑ g ∈ ((sqSk o e).vtx 0).arc 3 1,
        ((((sqSk o e).vtx 0).q g : ℝ) + sqR o e 0 g) =
      |dirRep o e (sq o e) 0 (selfIdx (by decide : 2 ≤ 4) 0 1) -
        dirRep o e (sq o e) 0 (selfIdx (by decide : 2 ≤ 4) 0 3)| /
        sqLam :=
  arcSum_qr o e (sq o e) sqLam (by decide) 0 3 1

lemma sq_arc_desc_val (he : e ≠ 0) :
    |dirRep o e (sq o e) 0 (selfIdx (by decide : 2 ≤ 4) 0 1) -
      dirRep o e (sq o e) 0 (selfIdx (by decide : 2 ≤ 4) 0 3)| =
      Real.pi / 2 := by
  rw [selfIdx_of_ne (by decide : 2 ≤ 4) (by decide : (1 : Fin 4) ≠ 0),
    selfIdx_of_ne (by decide : 2 ≤ 4) (by decide : (3 : Fin 4) ≠ 0),
    dirRep_sq_01 he, dirRep_sq_03 he]
  rw [abs_of_neg (by linarith [Real.pi_pos] : (0:ℝ) - Real.pi / 2 < 0)]
  ring

/-! ### `angleExpr` ↔ geometric angle, self-slot reduction -/

lemma sq_angle (he : e ≠ 0) (a b : Fin 4) :
    angleExpr 2 (sqSk o e) (sqR o e) (bridgeDelta sqLam 2) 0 a b =
      ∠ ((sq o e) (selfIdx (by decide : 2 ≤ 4) 0 a)) ((sq o e) 0)
        ((sq o e) (selfIdx (by decide : 2 ≤ 4) 0 b)) / sqLam :=
  angleExpr_eq o e (sq o e) sqLam 2 (by decide) he (sq_inj he) 0 a b

/-- Self-slot domain: `angleExpr x x b` reduces to the geometric angle at
the substituted `other x` index — no silent self-angle. -/
lemma sq_self_angle (he : e ≠ 0) (b : Fin 4) (hb : b ≠ 0) :
    angleExpr 2 (sqSk o e) (sqR o e) (bridgeDelta sqLam 2) 0 0 b =
      ∠ ((sq o e) (other (by decide : 2 ≤ 4) 0)) ((sq o e) 0)
        ((sq o e) b) / sqLam := by
  rw [angleExpr_eq o e (sq o e) sqLam 2 (by decide) he (sq_inj he) 0 0 b,
    selfIdx_self, selfIdx_of_ne (by decide : 2 ≤ 4) hb]

/-- Both slots self: the substituted indices coincide and the expression
vanishes (empty arc). -/
lemma sq_self_zero :
    angleExpr 2 (sqSk o e) (sqR o e) (bridgeDelta sqLam 2) 0 0
        (other (by decide : 2 ≤ 4) 0) = 0 := by
  apply angleExpr_eq_zero_of_selfIdx_eq o e (sq o e) sqLam 2
    (by decide : 2 ≤ 4)
  rw [selfIdx_self, selfIdx_of_ne _ (other_ne _ 0)]

/-! ### Lift-bit controls -/

/-- Negative control: `rawBit 0 1 = false` — the `dirRep` lift agrees
with the oriented angle (no `+π` shift). -/
lemma sq_rawBit_01 (he : e ≠ 0) : rawBit o e (sq o e) 0 1 = false := by
  have h0 : ¬ (((dirRep o e (sq o e) 0 1 : ℝ) : Real.Angle) =
      o.oangle e ((sq o e) 1 - (sq o e) 0) +
        ((Real.pi : ℝ) : Real.Angle)) := by
    rw [dirRep_sq_01 he]
    have hsub : (sq o e) 1 - (sq o e) 0 = e := by simp [sq]
    rw [hsub, o.oangle_self, Real.Angle.coe_zero, zero_add]
    intro hcon
    exact Real.Angle.pi_ne_zero hcon.symm
  unfold rawBit
  rw [if_neg h0]

/-- Positive control: `rawBit 1 0 = true` — the antipodal direction
`−e` has `dirRep = 0` while its oriented angle is `π`, so the lift
differs by `+π`. -/
lemma sq_rawBit_10 (he : e ≠ 0) : rawBit o e (sq o e) 1 0 = true := by
  have h0 : (((dirRep o e (sq o e) 1 0 : ℝ) : Real.Angle) =
      o.oangle e ((sq o e) 0 - (sq o e) 1) +
        ((Real.pi : ℝ) : Real.Angle)) := by
    rw [dirRep_sq_10 he]
    have hsub : (sq o e) 0 - (sq o e) 1 = -e := by simp [sq]
    rw [hsub, o.oangle_neg_right he he, o.oangle_self,
      Real.Angle.coe_zero, zero_add]
    exact Real.Angle.coe_pi_add_coe_pi.symm
  unfold rawBit
  rw [if_pos h0]

/-! ### Exponents, defect, weight -/

/-- `kexp = rowScore = 0` on every square row. -/
lemma sq_kexp (he : e ≠ 0) (x : Fin 4) : ((sqSk o e).vtx x).kexp = 0 := by
  rw [bridgeVtx_kexp o e (sq o e) sqLam (by decide) x]
  rcases sq_row_mem (o := o) he x with h | h
  · simp [h, rowScore_sq_0245]
  · simp [h, rowScore_sq_0267]

/-- `d` correspondence on the square: `d = rowDefect − 1`. -/
lemma sq_d_corr (x : Fin 4) :
    (sqSk o e).d 2 x =
      (rowDefect 2 sqLam (directionRow o e (sq o e) x) : ℤ) - 1 :=
  bridgeSkeleton_d o e (sq o e) sqLam 2 sqLam_pos (by decide) hn_sq x

/-- `d = 1` on every square row (`kexp = 0`, `n = 2`). -/
lemma sq_d (he : e ≠ 0) (x : Fin 4) : (sqSk o e).d 2 x = 1 := by
  unfold Skeleton.d
  rw [sq_kexp he x]
  norm_num

/-- Exact `W/K` factor: `W = potential / 2^{n-1} = 4 / 2 = 2`. -/
lemma sq_W (he : e ≠ 0) : (sqSk o e).W 2 = 2 := by
  rw [bridgeSkeleton_W o e (sq o e) sqLam 2 sqLam_pos (by decide) hn_sq
    (by norm_num)]
  rw [sq_potential_eq he]
  norm_num

/-! ### Degenerate `s = 2` rows -/

/-- `s = 2` gives single-slot rows (`Fin 1` positions and arcs): the
bridge is still `Proper`. -/
lemma deg2_proper (c : Fin 2 → Plane₂) (lam : ℝ) :
    (bridgeSkeleton o e c lam (by norm_num : 2 ≤ 2)).Proper :=
  bridgeSkeleton_proper o e c lam (by norm_num)

/-- Every position in a degenerate row is `0`. -/
lemma deg2_pos (c : Fin 2 → Plane₂) (lam : ℝ) (x a : Fin 2) :
    ((bridgeSkeleton o e c lam (by norm_num : 2 ≤ 2)).vtx x).pos a = 0 := by
  apply Fin.ext
  have hlt := (((bridgeSkeleton o e c lam
    (by norm_num : 2 ≤ 2)).vtx x).pos a).2
  omega

end

end Jsp404

/-! ### Axiom audit -/

#print axioms Jsp404.bridgeSkeleton_proper
#print axioms Jsp404.angleExpr_eq
#print axioms Jsp404.geomSkeleton_modeA
#print axioms Jsp404.geomSkeleton_consistent
#print axioms Jsp404.bridgeVtx_kexp
#print axioms Jsp404.bridgeSkeleton_d
#print axioms Jsp404.bridgeSkeleton_W
#print axioms Jsp404.gadgetSelection_of_selectionP
#print axioms Jsp404.sq_proper
#print axioms Jsp404.sq_modeA
#print axioms Jsp404.sq_consistent
#print axioms Jsp404.sq_W
