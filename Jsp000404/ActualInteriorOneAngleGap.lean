import Jsp000404.ActualInteriorOneRuns

set_option autoImplicit false

/-! The actual interior-one angle gap.
The necessary actual window and finite-ray extraction proofs are repeated
locally from the frozen c8cf8f2b source, rather than referring to generated
private names or changing that checked source. Actual lift alternation uses
the stable public theorem from ActualInteriorOneRuns. No flip-odd/count
proof or nearest-neighbor wrapper is repeated here.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualInteriorOneAngleGap

private theorem actual_angle_eq_bits {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    {p a b : Fin s} (hpa : p ≠ a) (hpb : p ≠ b) :
    ∠ (c a) (c p) (c b) =
      if rawBit o e c p a = rawBit o e c p b
      then |dirRep o e c p b - dirRep o e c p a|
      else Real.pi - |dirRep o e c p b - dirRep o e c p a| := by
  have h := angle_eq_dirRep o e c hs he hleg.inj p a b
  simpa only [selfIdx_of_ne hs hpa.symm, selfIdx_of_ne hs hpb.symm] using h

private theorem actual_dirRep_ne {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    {p a b : Fin s} (hpa : p ≠ a) (hpb : p ≠ b) (hab : a ≠ b) :
    dirRep o e c p a ≠ dirRep o e c p b := by
  intro heq
  have hang := actual_angle_eq_bits hs o e he hleg hpa hpb
  rw [heq, sub_self, abs_zero] at hang
  have hpos := EuclideanGeometry.angle_pos_of_not_collinear
    (legal_triple_not_collinear hleg hpa.symm hab hpb)
  have hcap := hleg.triAngle a p b hpa.symm hpb hab
  split_ifs at hang <;> linarith [hleg.lam_pos]

private noncomputable def rayKey {s : ℕ} (o : Orientation ℝ Plane₂ (Fin 2))
    (e : Plane₂) (c : Fin s → Plane₂) (p a : Fin s) : ℝ :=
  if a = p then Real.pi else dirRep o e c p a

private theorem rayKey_injective {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (p : Fin s) : Function.Injective (rayKey o e c p) := by
  intro a b heq
  by_cases ha : a = p
  · subst a
    by_contra hb
    have hpb : p ≠ b := hb
    have hbp : b ≠ p := hpb.symm
    have hlt : dirRep o e c p b < Real.pi := (linRep_mem_Ico _).2
    simp [rayKey, hbp] at heq
    linarith
  · have hap : a ≠ p := ha
    by_cases hb : b = p
    · subst b
      have hlt : dirRep o e c p a < Real.pi := (linRep_mem_Ico _).2
      simp [rayKey, hap] at heq
      linarith
    · have hbp : b ≠ p := hb
      simp only [rayKey, ite_eq_right hap, ite_eq_right hbp] at heq
      by_contra hab
      exact actual_dirRep_ne hs o e he hleg hap.symm hbp.symm hab heq

private theorem exists_actual_interior_alternating_fan {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (p : Fin s) (hnot : ¬ IsHullVertex c p) :
    ∃ x y z : Fin s, x ≠ p ∧ y ≠ p ∧ z ≠ p ∧
      dirRep o e c p x < dirRep o e c p y ∧
      dirRep o e c p y < dirRep o e c p z ∧
      (rawBit o e c p x = rawBit o e c p z ∧
        rawBit o e c p y = !(rawBit o e c p x)) ∧
      ([x,y,z] : List (Fin s)).Sublist (fanOrder o e c p) := by
  classical
  have hmem : c p ∈ convexHull ℝ (c '' ({p} : Set (Fin s))ᶜ) := by
    by_contra hno
    exact hnot (FullHullInteriorDefect.isHullVertex_of_not_mem_hull_others c p hno)
  obtain ⟨a, b, d, hpa, hpb, hpd, hab, had, hbd, htri⟩ :=
    InteriorRowDefect.exists_containing_actual_triangle hleg p hmem
  let key := rayKey o e c p
  let R : Fin s → Fin s → Prop := fun a b => key a ≤ key b
  let : Std.Total R := ⟨fun a b => le_total (key a) (key b)⟩
  let : IsTrans (Fin s) R := ⟨fun _ _ _ hab hbd => le_trans hab hbd⟩
  let : Std.Antisymm R := ⟨fun a b hab hba =>
    rayKey_injective hs o e he hleg p (le_antisymm hab hba)⟩
  let l := ([a, b, d] : List (Fin s)).insertionSort R
  have hperm : l.Perm [a, b, d] := List.perm_insertionSort _ _
  have hlen : l.length = 3 := by
    simp only [l, List.length_insertionSort, List.length_cons, List.length_nil]
  obtain ⟨x, y, z, hl⟩ := List.length_eq_three.mp hlen
  have hsorted : l.Pairwise R := List.pairwise_insertionSort _ _
  have hkeymap : (fanOrder o e c p).map key =
      (fanOrder o e c p).map (dirRep o e c p) := by
    apply List.map_congr_left
    intro a ha
    exact ite_eq_right ((mem_fanOrder o e c).mp ha)
  have hfan : (fanOrder o e c p).Pairwise R := by
    have hm := (fanOrder_map_sorted o e c p).pairwise
    rw [← hkeymap] at hm
    exact List.pairwise_map.mp hm
  have hsub0 : ([a,b,d] : List (Fin s)).Subperm (fanOrder o e c p) := by
    apply List.subperm_of_subset (by simp [hab, had, hbd])
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact (mem_fanOrder o e c).mpr hpa.symm
    · exact (mem_fanOrder o e c).mpr hpb.symm
    · exact (mem_fanOrder o e c).mpr hpd.symm
  have hsub : l.Sublist (fanOrder o e c p) :=
    List.sublist_of_subperm_of_pairwise (hperm.subperm.trans hsub0) hsorted hfan
  rw [hl] at hperm hsorted hsub
  have hx : x ≠ p := (mem_fanOrder o e c).mp (hsub.mem (by simp))
  have hy : y ≠ p := (mem_fanOrder o e c).mp (hsub.mem (by simp))
  have hz : z ≠ p := (mem_fanOrder o e c).mp (hsub.mem (by simp))
  have hnd : ([x,y,z] : List (Fin s)).Nodup :=
    (fanOrder_nodup o e c p).sublist hsub
  have hnd' : (x ≠ y ∧ x ≠ z) ∧ y ≠ z := by simpa using hnd
  have hxy : x ≠ y := hnd'.1.1
  have hxz : x ≠ z := hnd'.1.2
  have hyz : y ≠ z := hnd'.2
  have hsort : dirRep o e c p x ≤ dirRep o e c p y ∧
      dirRep o e c p x ≤ dirRep o e c p z ∧
      dirRep o e c p y ≤ dirRep o e c p z := by
    simpa [R, key, rayKey, hx, hy, hz, and_assoc] using hsorted
  have hxy' : dirRep o e c p x < dirRep o e c p y :=
    lt_of_le_of_ne hsort.1 (actual_dirRep_ne hs o e he hleg hx.symm hy.symm hxy)
  have hyz' : dirRep o e c p y < dirRep o e c p z :=
    lt_of_le_of_ne hsort.2.2 (actual_dirRep_ne hs o e he hleg hy.symm hz.symm hyz)
  have hset : ({c x,c y,c z} : Set Plane₂) = {c a,c b,c d} := by
    ext u
    have hm := (hperm.map c).mem_iff (a := u)
    simpa only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false, Set.mem_insert_iff, Set.mem_singleton_iff] using hm
  have htri' : c p ∈ convexHull ℝ ({c x,c y,c z} : Set Plane₂) := by
    rw [hset]
    exact htri
  obtain ⟨E, hE, hp⟩ := strict_nested_of_mem_convexHull htri' (hleg.inj.ne hz.symm)
    (legal_triple_not_collinear hleg hz hxz.symm hx.symm)
    (legal_triple_not_collinear hleg hz hyz.symm hy.symm)
    (legal_triple_not_collinear hleg hx hxy hy.symm)
  have hbits := ActualInteriorOneRuns.actual_ordered_surrounding_bits hs o e he hleg
    hx.symm hy.symm hz.symm hxy' hyz' (angle_sum_eq_two_pi_of_nested hE hp)
  exact ⟨x,y,z,hx,hy,hz,hxy',hyz',hbits,hsub⟩

private theorem narrow_window_small_expr {ι : Type*} (x : ι → ℝ) (bit : ι → Bool)
    {lam H : ℝ} (hlam : 0 < lam) (hH : H < 3 * lam)
    (hwidth : H ≤ Real.pi-2*lam)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ H)
    (hop : ∀ i j, bit i ≠ bit j → lam ≤ |x i - x j|)
    (z m r : ι) (hz : x z = 0) (hbz : bit z = false)
    (hbm : bit m = true) (hbr : bit r = false) (hmr : x m < x r) :
    ∀ i j,
      (if bit i = bit j then |x i-x j| else Real.pi-|x i-x j|) < 2*lam →
      (if bit i = bit j then |x i-x j| else Real.pi-|x i-x j|) ≤ H-2*lam := by
  have hlow (i : ι) (hi : bit i = true) : lam ≤ x i := by
    have h := hop z i (by rw [hbz, hi]; decide)
    rw [hz, zero_sub, abs_neg, abs_of_nonneg (hx i).1] at h
    exact h
  have hr2 : 2 * lam ≤ x r := by
    have h := hop m r (by rw [hbm, hbr]; decide)
    rw [abs_of_nonpos (sub_nonpos.mpr hmr.le)] at h
    linarith [hlow m hbm]
  have hupper (i : ι) (hi : bit i = true) : x i ≤ H-lam := by
    have h := hop r i (by rw [hbr, hi]; decide)
    by_cases hir : x i ≤ x r
    · rw [abs_of_nonneg (sub_nonneg.mpr hir)] at h
      linarith [(hx r).2]
    · have hri : x r < x i := lt_of_not_ge hir
      rw [abs_of_nonpos (sub_nonpos.mpr hri.le)] at h
      linarith [(hx i).2]
  have hmlo := hlow m hbm
  have hmhi := hupper m hbm
  intro i j hsmall
  by_cases hsame : bit i = bit j
  · simp only [ite_eq_left hsame] at hsmall ⊢
    cases hi : bit i with
    | true =>
      have hj : bit j = true := by simpa only [hi] using hsame.symm
      apply abs_sub_le_iff.mpr
      constructor <;> linarith [hlow i hi, hupper i hi, hlow j hj, hupper j hj]
    | false =>
      have hj : bit j = false := by simpa only [hi] using hsame.symm
      have him := hop i m (by rw [hi, hbm]; decide)
      have hjm := hop j m (by rw [hj, hbm]; decide)
      by_cases hip : x i ≤ x m
      · rw [abs_of_nonpos (sub_nonpos.mpr hip)] at him
        by_cases hjp : x j ≤ x m
        · rw [abs_of_nonpos (sub_nonpos.mpr hjp)] at hjm
          apply abs_sub_le_iff.mpr
          constructor <;> linarith [(hx i).1, (hx j).1]
        · have hmj : x m < x j := lt_of_not_ge hjp
          rw [abs_of_nonneg (sub_nonneg.mpr hmj.le)] at hjm
          have hij : x i ≤ x j := hip.trans hmj.le
          rw [abs_of_nonpos (sub_nonpos.mpr hij)] at hsmall
          linarith
      · have hmi : x m < x i := lt_of_not_ge hip
        rw [abs_of_nonneg (sub_nonneg.mpr hmi.le)] at him
        by_cases hjp : x j ≤ x m
        · rw [abs_of_nonpos (sub_nonpos.mpr hjp)] at hjm
          have hji : x j ≤ x i := hjp.trans hmi.le
          rw [abs_of_nonneg (sub_nonneg.mpr hji)] at hsmall
          linarith
        · have hmj : x m < x j := lt_of_not_ge hjp
          rw [abs_of_nonneg (sub_nonneg.mpr hmj.le)] at hjm
          apply abs_sub_le_iff.mpr
          constructor <;> linarith [(hx i).2, (hx j).2]
  · simp only [ite_eq_right hsame] at hsmall ⊢
    have habs : |x i-x j| ≤ H-lam := by
      cases hi : bit i <;> cases hj : bit j
      · exact False.elim (hsame (by simp [hi,hj]))
      · apply abs_sub_le_iff.mpr
        constructor <;> linarith [(hx i).1, (hx i).2, hlow j hj, hupper j hj]
      · apply abs_sub_le_iff.mpr
        constructor <;> linarith [(hx j).1, (hx j).2, hlow i hi, hupper i hi]
      · exact False.elim (hsame (by simp [hi,hj]))
    exfalso
    linarith

private theorem list_has_positive (l : List ℕ) :
    0 < l.sum → ∃ a ∈ l, 0 < a := by
  induction l with
  | nil => simp
  | cons a as ih =>
    intro hpos
    by_cases ha : 0 < a
    · exact ⟨a, by simp, ha⟩
    · have ha0 : a = 0 := by omega
      obtain ⟨b,hb,hbpos⟩ := ih (by simpa [ha0] using hpos)
      exact ⟨b, by simp [hb], hbpos⟩

private theorem exists_actual_score_one_window {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (p : Fin s) (hscore : rowScore lam (directionRow o e c p) = 1) :
    ∃ f : Plane₂, f ≠ 0 ∧ ∃ H : ℝ, H ≤ Real.pi-2*lam ∧
      ∃ z : Fin s, z ≠ p ∧ dirRep o f c p z = 0 ∧
        rawBit o f c p z = false ∧
        ∀ i : Fin s, i ≠ p → dirRep o f c p i ∈ Set.Icc 0 H := by
  classical
  have hpos : 0 < ((cycGaps (directionRow o e c p)).map (gapScore lam)).sum := by
    change 0 < rowScore lam (directionRow o e c p)
    omega
  obtain ⟨a,ha,hapos⟩ := list_has_positive _ hpos
  obtain ⟨G,hG,rfl⟩ := List.mem_map.mp ha
  have hne : directionRow o e c p ≠ [] := by
    intro heq
    have hlen := directionRow_length o e c p
    rw [heq] at hlen
    simp only [List.length_nil] at hlen
    omega
  have hG0 : 0 ≤ G := cycGaps_nonneg (directionRow_sorted o e c p)
    (fun x hx => directionRow_mem_Ico o e c hx) hne G hG
  have hf : 2 ≤ ⌊G/lam⌋₊ := by
    change 0 < ⌊G/lam⌋₊-1 at hapos
    omega
  have hf' : (2 : ℝ) ≤ (⌊G/lam⌋₊ : ℝ) := by exact_mod_cast hf
  have hG2 : 2 * lam ≤ G := by
    have h := hf'.trans (Nat.floor_le (div_nonneg hG0 hleg.lam_pos.le))
    exact (le_div_iff₀ hleg.lam_pos).mp h
  obtain ⟨cut,hcut,hwindow⟩ := PositiveRowFan.exists_shift_window_of_gap
    (directionRow_sorted o e c p) (fun x hx => directionRow_mem_Ico o e c hx) hG
  obtain ⟨z,hzp,hz⟩ := (mem_directionRow o e c).mp hcut
  let f := c z-c p
  have hfne : f ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hzp)
  have hcut' : linRep (o.oangle e f) = cut := by
    simpa only [f, dirRep] using hz.symm
  have hz0 : dirRep o f c p z = 0 := by
    change linRep (o.oangle f f) = 0
    simp [linRep]
  have hbz : rawBit o f c p z = false := by
    unfold rawBit
    rw [hz0]
    change (if (0 : Real.Angle) = o.oangle f f + (Real.pi : Real.Angle)
      then true else false) = false
    rw [o.oangle_self, zero_add, ite_eq_right (Ne.symm Real.Angle.pi_ne_zero)]
  refine ⟨f,hfne,Real.pi-G,by linarith,z,hzp,hz0,hbz,?_⟩
  intro i hip
  have href := dirRep_reference_shift o e f he hfne c hleg.inj hip.symm
  rw [hcut'] at href
  rw [href]
  exact hwindow _ ((mem_directionRow o e c).mpr ⟨i,hip,rfl⟩)

/-- Below twice the legal scale, actual interior score-one angles
are bounded by the original period remainder. All scalar window data
and the alternating actual rays are selected inside the proof. -/
theorem actual_interior_one_angle_lt_twice_le_remainder {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlo : 2*Real.pi/9 < lam) (p : Fin s) (hnot : ¬ IsHullVertex c p)
    (hscore : rowScore lam (directionRow o e c p) = 1)
    {i j : Fin s} (hip : i ≠ p) (hjp : j ≠ p)
    (hsmall : ∠ (c i) (c p) (c j) < 2*lam) :
    ∠ (c i) (c p) (c j) ≤ Real.pi-4*lam := by
  classical
  obtain ⟨f,hf,H,hwidth,z,hzp,hz,hbz,hwindow⟩ :=
    exists_actual_score_one_window hs o e he hleg p hscore
  let I := {a : Fin s // a ≠ p}
  let x (a : I) : ℝ := dirRep o f c p a
  let bit (a : I) : Bool := rawBit o f c p a
  have hx : ∀ a : I, 0 ≤ x a ∧ x a ≤ H :=
    fun a => hwindow a a.property
  have hH : H < 3*lam := by linarith [hleg.lam_pos]
  have hop : ∀ a b : I, bit a ≠ bit b → lam ≤ |x a-x b| := by
    intro a b hab
    have hne : (a : Fin s) ≠ b := by
      intro heq
      apply hab
      exact congrArg (rawBit o f c p) heq
    have hang := actual_angle_eq_bits hs o f hf hleg a.property.symm b.property.symm
    have hcap := hleg.triAngle a p b a.property b.property.symm hne
    change bit a ≠ bit b at hab
    change ∠ (c a) (c p) (c b) =
      (if bit a = bit b then |x b-x a| else Real.pi-|x b-x a|) at hang
    rw [ite_eq_right hab, abs_sub_comm] at hang
    linarith
  obtain ⟨a,b,d,ha,hb,hd,hab,hbd,hbits,hsub⟩ :=
    exists_actual_interior_alternating_fan hs o f hf hleg p hnot
  have ha0 : rawBit o f c p a = false := by
    by_cases hba : rawBit o f c p a = false
    · exact hba
    · have hba' : rawBit o f c p a = true := by
        cases h : rawBit o f c p a <;> simp_all
      have hbb : rawBit o f c p b = false := by simpa [hba'] using hbits.2
      have hbd' : rawBit o f c p d = true := hbits.1.symm.trans hba'
      have hza := hop ⟨z,hzp⟩ ⟨a,ha⟩ (by
        change rawBit o f c p z ≠ rawBit o f c p a
        rw [hbz,hba']; decide)
      change lam ≤ |dirRep o f c p z-dirRep o f c p a| at hza
      rw [hz, zero_sub, abs_neg, abs_of_nonneg (hwindow a ha).1] at hza
      have hab' := hop ⟨a,ha⟩ ⟨b,hb⟩ (by
        change rawBit o f c p a ≠ rawBit o f c p b
        rw [hba',hbb]; decide)
      have hbd'' := hop ⟨b,hb⟩ ⟨d,hd⟩ (by
        change rawBit o f c p b ≠ rawBit o f c p d
        rw [hbb,hbd']; decide)
      change lam ≤ |dirRep o f c p a-dirRep o f c p b| at hab'
      change lam ≤ |dirRep o f c p b-dirRep o f c p d| at hbd''
      rw [abs_of_nonpos (sub_nonpos.mpr hab.le)] at hab'
      rw [abs_of_nonpos (sub_nonpos.mpr hbd.le)] at hbd''
      linarith [(hwindow d hd).2]
  have hb1 : rawBit o f c p b = true := by simpa [ha0] using hbits.2
  have hd0 : rawBit o f c p d = false := hbits.1.symm.trans ha0
  have hangle := actual_angle_eq_bits hs o f hf hleg hip.symm hjp.symm
  rw [abs_sub_comm] at hangle
  have hsmall' : (if bit ⟨i,hip⟩ = bit ⟨j,hjp⟩ then |x ⟨i,hip⟩-x ⟨j,hjp⟩|
    else Real.pi-|x ⟨i,hip⟩-x ⟨j,hjp⟩|) < 2*lam := by
    simpa only [x, bit, ← hangle] using hsmall
  have hbound := narrow_window_small_expr x bit hleg.lam_pos hH hwidth hx hop
    ⟨z,hzp⟩ ⟨b,hb⟩ ⟨d,hd⟩ hz hbz hb1 hd0 hbd ⟨i,hip⟩ ⟨j,hjp⟩ hsmall'
  change (if rawBit o f c p i = rawBit o f c p j then |dirRep o f c p i-dirRep o f c p j|
    else Real.pi-|dirRep o f c p i-dirRep o f c p j|) ≤ H-2*lam at hbound
  rw [← hangle] at hbound
  linarith

/-- Every pair of original rays at an interior original score-one
center is either within the sharp remainder or separated by twice lambda.
The endpoints and reference window come from the original actual points. -/
theorem actual_interior_one_angle_gap {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlo : 2*Real.pi/9 < lam) (p : Fin s) (hnot : ¬ IsHullVertex c p)
    (hscore : rowScore lam (directionRow o e c p) = 1)
    {i j : Fin s} (hip : i ≠ p) (hjp : j ≠ p) :
    ∠ (c i) (c p) (c j) ≤ Real.pi-4*lam ∨ 2*lam ≤ ∠ (c i) (c p) (c j) := by
  by_cases hsmall : ∠ (c i) (c p) (c j) < 2*lam
  · exact Or.inl (actual_interior_one_angle_lt_twice_le_remainder
      hs o e he hleg hlo p hnot hscore hip hjp hsmall)
  · exact Or.inr (le_of_not_gt hsmall)

#print axioms actual_interior_one_angle_lt_twice_le_remainder
#print axioms actual_interior_one_angle_gap

end Jsp404.ActualInteriorOneAngleGap
