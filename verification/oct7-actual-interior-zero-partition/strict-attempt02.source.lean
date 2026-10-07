import Jsp000404.ActualInteriorOneRuns
import Jsp000404.PositiveRowFan
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

/-! SOURCE_ONLY: actual score-zero interior partition construction.
The actual flip-gap/window bridge is built locally from original fan rays.
No generated private name or caller angular/partition oracle is used.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualInteriorZeroPartition

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


private theorem adjacent_change_of_mixed {α : Type*} (bit : α → Bool) (l : List α) :
    (∃ a ∈ l, ∃ b ∈ l, bit a ≠ bit b) →
      ∃ pre a b suf, l = pre ++ a :: b :: suf ∧ bit a ≠ bit b := by
  induction l with
  | nil => simp
  | cons u l ih =>
      intro hmixed
      cases l with
      | nil => simp at hmixed
      | cons v vs =>
          by_cases huv : bit u = bit v
          · have htail : ∃ a ∈ v :: vs, ∃ b ∈ v :: vs, bit a ≠ bit b := by
              have hreplace (a : α) (ha : a ∈ u :: v :: vs) :
                  ∃ a' ∈ v :: vs, bit a' = bit a := by
                rcases List.mem_cons.mp ha with ha | ha
                · subst a
                  exact ⟨v,by simp,huv.symm⟩
                · exact ⟨a,ha,rfl⟩
              obtain ⟨a, ha, b, hb, hab⟩ := hmixed
              obtain ⟨a',ha',hea⟩ := hreplace a ha
              obtain ⟨b',hb',heb⟩ := hreplace b hb
              exact ⟨a',ha',b',hb',by rw [hea,heb]; exact hab⟩
            obtain ⟨pre, a, b, suf, hlist, hbits⟩ := ih htail
            refine ⟨u :: pre,a,b,suf,?_,hbits⟩
            simpa only [List.cons_append] using congrArg (List.cons u) hlist
          · exact ⟨[], u, v, vs, rfl, huv⟩

private noncomputable def innerGaps (l : List ℝ) : List ℝ :=
  (l.dropLast.zip l.tail).map (fun ab => cyclicDiff ab.1 ab.2)

private theorem innerGaps_cons (a b : ℝ) (l : List ℝ) :
    innerGaps (a :: b :: l) = cyclicDiff a b :: innerGaps (b :: l) := by
  simp [innerGaps, List.dropLast_cons_cons]

private theorem innerGaps_mem_cons (a : ℝ) (l : List ℝ) {g : ℝ}
    (hg : g ∈ innerGaps l) : g ∈ innerGaps (a :: l) := by
  cases l with
  | nil => simp [innerGaps] at hg
  | cons b bs =>
      rw [innerGaps_cons]
      exact List.mem_cons_of_mem _ hg

private theorem innerGaps_adjacent (pre : List ℝ) (a b : ℝ) (suf : List ℝ) :
    cyclicDiff a b ∈ innerGaps (pre ++ a :: b :: suf) := by
  induction pre with
  | nil => rw [List.nil_append, innerGaps_cons]; exact List.mem_cons_self
  | cons u pre ih =>
      simp only [List.cons_append]
      exact innerGaps_mem_cons u _ ih

private theorem adjacent_sublist {α : Type*} (pre : List α) (a b : α) (suf : List α) :
    [a,b].Sublist (pre ++ a :: b :: suf) := by
  induction pre with
  | nil =>
      exact List.Sublist.cons_cons a (List.Sublist.cons_cons b (List.nil_sublist suf))
  | cons u pre ih => exact List.Sublist.cons u ih

private theorem cyclicDiff_eq_sub_of_le {a b : ℝ} (hab : a ≤ b) :
    cyclicDiff a b = b-a := by
  by_cases h : a = b
  · simp [cyclicDiff,h]
  · have hlt : a < b := lt_of_le_of_ne hab h
    simp [cyclicDiff,h,hlt]

/-- An actual original adjacent lift change supplies a real cyclic gap.
This bridge does not assume a chart-rotation rule for the lift bits. -/
theorem exists_actual_flip_gap {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (p : Fin s) (hnot : ¬ IsHullVertex c p) :
    ∃ G ∈ cycGaps (directionRow o e c p), lam ≤ G := by
  classical
  obtain ⟨a,b,d,ha,hb,hd,hab,hbd,hbits,hsub⟩ :=
    exists_actual_interior_alternating_fan hs o e he hleg p hnot
  have habits : rawBit o e c p a ≠ rawBit o e c p b := by
    rw [hbits.2]
    cases rawBit o e c p a <;> decide
  have hmixed : ∃ a ∈ fanOrder o e c p, ∃ b ∈ fanOrder o e c p,
      rawBit o e c p a ≠ rawBit o e c p b :=
    ⟨a, hsub.mem (by simp), b, hsub.mem (by simp), habits⟩
  obtain ⟨pre,u,v,suf,hlist,huvbit⟩ :=
    adjacent_change_of_mixed (rawBit o e c p) (fanOrder o e c p) hmixed
  have humem : u ∈ fanOrder o e c p := by rw [hlist]; simp
  have hvmem : v ∈ fanOrder o e c p := by rw [hlist]; simp
  have hup : u ≠ p := (mem_fanOrder o e c).mp humem
  have hvp : v ≠ p := (mem_fanOrder o e c).mp hvmem
  have huv : u ≠ v := by
    intro h
    exact huvbit (congrArg (rawBit o e c p) h)
  have hrow : directionRow o e c p =
      pre.map (dirRep o e c p) ++ dirRep o e c p u :: dirRep o e c p v ::
        suf.map (dirRep o e c p) := by
    rw [← fanOrder_map_eq o e c p,hlist,List.map_append,List.map_cons,List.map_cons]
  have hpair : [dirRep o e c p u,dirRep o e c p v].Pairwise (· ≤ ·) := by
    have hsub : [dirRep o e c p u,dirRep o e c p v].Sublist (directionRow o e c p) := by
      rw [hrow]
      exact adjacent_sublist _ _ _ _
    exact List.Pairwise.sublist hsub (directionRow_sorted o e c p).pairwise
  have huvle : dirRep o e c p u ≤ dirRep o e c p v := by simpa using hpair
  have hang := actual_angle_eq_bits hs o e he hleg hup.symm hvp.symm
  rw [ite_eq_right huvbit,abs_of_nonneg (sub_nonneg.mpr huvle)] at hang
  have hcap := hleg.triAngle u p v hup hvp.symm huv
  have hbig : lam ≤ dirRep o e c p v-dirRep o e c p u := by linarith
  have hinner : cyclicDiff (dirRep o e c p u) (dirRep o e c p v) ∈
      innerGaps (directionRow o e c p) := by
    rw [hrow]
    exact innerGaps_adjacent _ _ _ _
  have hne : directionRow o e c p ≠ [] :=
    List.ne_nil_of_mem ((mem_directionRow o e c).mpr ⟨u,hup,rfl⟩)
  refine ⟨cyclicDiff (dirRep o e c p u) (dirRep o e c p v), ?_, ?_⟩
  · rw [cycGaps_eq_map_append_wrap _ hne]
    exact List.mem_append_left _ hinner
  · rw [cyclicDiff_eq_sub_of_le huvle]
    exact hbig

/-- A genuine actual gap gives the weaker score-zero projective window.
The new reference is an original ray, whose new lift bit is false. -/
theorem exists_actual_interior_flip_window {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (p : Fin s) (hnot : ¬ IsHullVertex c p) :
    ∃ f : Plane₂, f ≠ 0 ∧ ∃ H : ℝ, H ≤ Real.pi-lam ∧
      ∃ z : Fin s, z ≠ p ∧ dirRep o f c p z = 0 ∧ rawBit o f c p z = false ∧
        ∀ i : Fin s, i ≠ p → dirRep o f c p i ∈ Set.Icc 0 H := by
  classical
  obtain ⟨G,hG,hbig⟩ := exists_actual_flip_gap hs o e he hleg p hnot
  obtain ⟨cut,hcut,hwindow⟩ := PositiveRowFan.exists_shift_window_of_gap
    (directionRow_sorted o e c p) (fun x hx => directionRow_mem_Ico o e c hx) hG
  obtain ⟨z,hzp,hz⟩ := (mem_directionRow o e c).mp hcut
  let f := c z-c p
  have hfne : f ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hzp)
  have hcut' : linRep (o.oangle e f) = cut := by
    simpa only [f,dirRep] using hz.symm
  have hz0 : dirRep o f c p z = 0 := by
    change linRep (o.oangle f f) = 0
    simp [linRep]
  have hbz : rawBit o f c p z = false := by
    unfold rawBit
    rw [hz0]
    change (if (0 : Real.Angle) = o.oangle f f + (Real.pi : Real.Angle)
      then true else false) = false
    rw [o.oangle_self,zero_add,ite_eq_right (Ne.symm Real.Angle.pi_ne_zero)]
  refine ⟨f,hfne,Real.pi-G,by linarith,z,hzp,hz0,hbz,?_⟩
  intro i hip
  have href := dirRep_reference_shift o e f he hfne c hleg.inj hip.symm
  rw [hcut'] at href
  rw [href]
  exact hwindow _ ((mem_directionRow o e c).mpr ⟨i,hip,rfl⟩)

private noncomputable def angleExpr {ι : Type*} (x : ι → ℝ) (bit : ι → Bool)
    (i j : ι) : ℝ :=
  if bit i = bit j then |x i-x j| else Real.pi-|x i-x j|

private structure ScalarData {ι : Type*} (x : ι → ℝ) (bit : ι → Bool) (lam : ℝ) where
  code : ι → Fin 3
  witness : Fin 3 → ι
  witness_code : ∀ k, code (witness k) = k
  span : Fin 3 → ℝ
  span_nonneg : ∀ k, 0 ≤ span k
  span_total : (∑ k : Fin 3, span k) ≤ Real.pi-3*lam
  left : Fin 3 → ι
  right : Fin 3 → ι
  left_code : ∀ k, code (left k) = k
  right_code : ∀ k, code (right k) = k
  span_expr : ∀ k, angleExpr x bit (left k) (right k) = span k
  same_span : ∀ i j, code i = code j → angleExpr x bit i j ≤ span (code i)
  different_angle : ∀ i j, code i ≠ code j → 2*lam ≤ angleExpr x bit i j

/-- The class through the cut can use both sheets. Its negative tail is
joined to the initial false-bit interval; no bit-rotation oracle is used. -/
private theorem wrapped_window_classifier {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (bit : ι → Bool) {lam H : ℝ}
    (hlam : 0 < lam) (hH : H < 4*lam) (hwidth : H ≤ Real.pi-lam)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ H)
    (hop : ∀ i j, bit i ≠ bit j → lam ≤ |x i-x j|)
    (z m r : ι) (hz : x z = 0) (hbz : bit z = false)
    (hbm : bit m = true) (hbr : bit r = false) (hmr : x m < x r) :
    Nonempty (ScalarData x bit lam) := by
  classical
  have hft : (false = true) ↔ False := by decide
  have htf : (true = false) ↔ False := by decide
  have hlow (i : ι) (hi : bit i = true) : lam ≤ x i := by
    have h := hop z i (by rw [hbz,hi]; decide)
    rw [hz,zero_sub,abs_neg,abs_of_nonneg (hx i).1] at h
    exact h
  have hmrGap : x m+lam ≤ x r := by
    have h := hop m r (by rw [hbm,hbr]; decide)
    rw [abs_of_nonpos (sub_nonpos.mpr hmr.le)] at h
    linarith
  have hmlo := hlow m hbm
  have hmhi : x m ≤ H-lam := by linarith [(hx r).2]
  have hrhi : x r ≤ H := (hx r).2
  have hleft (i : ι) (hi : bit i = false) (hle : x i ≤ x m) :
      x i ≤ x m-lam := by
    have h := hop i m (by rw [hi,hbm]; decide)
    rw [abs_of_nonpos (sub_nonpos.mpr hle)] at h
    linarith
  have hmiddle (i : ι) (hi : bit i = true) (hle : x i ≤ x r) :
      x i ≤ x r-lam := by
    have h := hop i r (by rw [hi,hbr]; decide)
    rw [abs_of_nonpos (sub_nonpos.mpr hle)] at h
    linarith
  have hhigh (i : ι) (hi : bit i = false) (hlt : x m < x i) :
      x m+lam ≤ x i := by
    have h := hop i m (by rw [hi,hbm]; decide)
    rw [abs_of_nonneg (sub_nonneg.mpr hlt.le)] at h
    linarith
  have htail (i : ι) (hi : bit i = true) (hlt : x r < x i) :
      x r+lam ≤ x i := by
    have h := hop i r (by rw [hi,hbr]; decide)
    rw [abs_of_nonneg (sub_nonneg.mpr hlt.le)] at h
    linarith
  let code : ι → Fin 3 := fun i =>
    if bit i = true then (if x i ≤ x r then 1 else 0)
    else if x i ≤ x m then 0 else 2
  let coord (i : ι) : ℝ := if bit i = true then x i-Real.pi else x i
  have htag (i : ι) :
      (code i = 0 ∧ bit i = false ∧ 0 ≤ x i ∧ x i ≤ x m-lam) ∨
      (code i = 1 ∧ bit i = true ∧ lam ≤ x i ∧ x i ≤ x r-lam) ∨
      (code i = 2 ∧ bit i = false ∧ x m+lam ≤ x i ∧ x i ≤ H) ∨
      (code i = 0 ∧ bit i = true ∧ x r+lam ≤ x i ∧ x i ≤ H) := by
    by_cases hi : bit i = true
    · by_cases hir : x i ≤ x r
      · exact Or.inr (Or.inl ⟨by simp [code,hi,hir],hi,hlow i hi,hmiddle i hi hir⟩)
      · exact Or.inr (Or.inr (Or.inr
          ⟨by simp [code,hi,hir],hi,htail i hi (lt_of_not_ge hir),(hx i).2⟩))
    · have hif : bit i = false := by cases h : bit i <;> simp_all
      by_cases him : x i ≤ x m
      · exact Or.inl ⟨by simp [code,hi,him],hif,(hx i).1,hleft i hif him⟩
      · exact Or.inr (Or.inr (Or.inl
          ⟨by simp [code,hi,him],hif,hhigh i hif (lt_of_not_ge him),(hx i).2⟩))
  have h01 (i j : ι) (hbi : bit i = false) (hbj : bit j = true)
      (hi : x i ≤ x m-lam) (hj : lam ≤ x j) : lam ≤ x j-x i := by
    have h := hop i j (by rw [hbi,hbj]; decide)
    by_cases hij : x i ≤ x j
    · rw [abs_of_nonpos (sub_nonpos.mpr hij)] at h
      linarith
    · have hji : x j < x i := lt_of_not_ge hij
      rw [abs_of_nonneg (sub_nonneg.mpr hji.le)] at h
      linarith [(hx r).2]
  have h12 (i j : ι) (hbi : bit i = true) (hbj : bit j = false)
      (hi : x i ≤ x r-lam) (hj : x m+lam ≤ x j) : lam ≤ x j-x i := by
    have h := hop i j (by rw [hbi,hbj]; decide)
    by_cases hij : x i ≤ x j
    · rw [abs_of_nonpos (sub_nonpos.mpr hij)] at h
      linarith
    · have hji : x j < x i := lt_of_not_ge hij
      rw [abs_of_nonneg (sub_nonneg.mpr hji.le)] at h
      linarith [(hx r).2]
  have h23 (i j : ι) (hbi : bit i = false) (hbj : bit j = true)
      (hi : x i ≤ H) (hj : x r+lam ≤ x j) : lam ≤ x j-x i := by
    have h := hop i j (by rw [hbi,hbj]; decide)
    by_cases hij : x i ≤ x j
    · rw [abs_of_nonpos (sub_nonpos.mpr hij)] at h
      linarith
    · have hji : x j < x i := lt_of_not_ge hij
      rw [abs_of_nonneg (sub_nonneg.mpr hji.le)] at h
      linarith
  have hsameCoord (i j : ι) (hsame : code i = code j) :
      angleExpr x bit i j = |coord i-coord j| := by
    rcases htag i with hi | hi | hi | hi <;>
      rcases htag j with hj | hj | hj | hj
    all_goals rcases hi with ⟨hci,hbi,hli,hui⟩
    all_goals rcases hj with ⟨hcj,hbj,hlj,huj⟩
    all_goals simp [hci,hcj] at hsame
    all_goals simp only [angleExpr,coord,hbi,hbj,hft,htf,ite_true,ite_false]
    all_goals
      first
      | solve | congr 1 <;> ring
      | rw [abs_of_nonpos (by linarith : x i-x j ≤ 0),
          abs_of_nonneg (by linarith : 0 ≤ x i-(x j-Real.pi))]
        ring
      | rw [abs_of_nonneg (by linarith : 0 ≤ x i-x j),
          abs_of_nonpos (by linarith : (x i-Real.pi)-x j ≤ 0)]
        ring
  have hdifferent (i j : ι) (hdiff : code i ≠ code j) :
      2*lam ≤ angleExpr x bit i j := by
    rcases htag i with hi | hi | hi | hi <;>
      rcases htag j with hj | hj | hj | hj
    all_goals rcases hi with ⟨hci,hbi,hli,hui⟩
    all_goals rcases hj with ⟨hcj,hbj,hlj,huj⟩
    all_goals simp [hci,hcj,angleExpr,hbi,hbj] at hdiff ⊢
    all_goals
      first
      | have habs : |x i-x j| ≤ H-lam := by
          apply abs_sub_le_iff.mpr
          constructor <;> linarith
        linarith
      | linarith [le_abs_self (x i-x j),neg_le_abs (x i-x j)]
  have hcz : code z = 0 := by
    have hzle : x z ≤ x m := by rw [hz]; linarith
    simp [code,hbz,hzle]
  have hcm : code m = 1 := by simp [code,hbm,hmr.le]
  have hcr : code r = 2 := by simp [code,hbr,not_le.mpr hmr]
  let witness : Fin 3 → ι := ![z,m,r]
  have hwitness : ∀ k : Fin 3, code (witness k) = k := by
    intro k
    fin_cases k
    · exact hcz
    · exact hcm
    · exact hcr
  have hbounds (k : Fin 3) : ∃ a b : ι, code a = k ∧ code b = k ∧
      ∀ i : ι, code i = k → coord a ≤ coord i ∧ coord i ≤ coord b := by
    let C := {i : ι // code i = k}
    let : Nonempty C := ⟨⟨witness k,hwitness k⟩⟩
    obtain ⟨a,ha⟩ := Finite.exists_min (fun i : C => coord i)
    obtain ⟨b,hb⟩ := Finite.exists_max (fun i : C => coord i)
    exact ⟨a,b,a.property,b.property,fun i hi => ⟨ha ⟨i,hi⟩,hb ⟨i,hi⟩⟩⟩
  choose lo hi hlo hhi hbounds using hbounds
  let span (k : Fin 3) : ℝ := coord (hi k)-coord (lo k)
  have hspan0 (k : Fin 3) : 0 ≤ span k :=
    sub_nonneg.mpr (hbounds k (hi k) (hhi k)).1
  have hinfo1 (i : ι) (hc : code i = 1) :
      bit i = true ∧ lam ≤ x i ∧ x i ≤ x r-lam := by
    rcases htag i with h | h | h | h
    all_goals rcases h with ⟨hci,hbi,hli,hui⟩
    all_goals
      first
      | exact ⟨hbi,hli,hui⟩
      | have hbad := hci.symm.trans hc
        norm_num at hbad
  have hinfo2 (i : ι) (hc : code i = 2) :
      bit i = false ∧ x m+lam ≤ x i ∧ x i ≤ H := by
    rcases htag i with h | h | h | h
    all_goals rcases h with ⟨hci,hbi,hli,hui⟩
    all_goals
      first
      | exact ⟨hbi,hli,hui⟩
      | have hbad := hci.symm.trans hc
        norm_num at hbad
  have h0lo : coord (lo 0) ≤ 0 := by
    simpa only [coord,hbz,hft,ite_false,hz] using (hbounds 0 z hcz).1
  have h0hi : 0 ≤ coord (hi 0) := by
    simpa only [coord,hbz,hft,ite_false,hz] using (hbounds 0 z hcz).2
  have hhi0info : bit (hi 0) = false ∧ 0 ≤ x (hi 0) ∧ x (hi 0) ≤ x m-lam := by
    rcases htag (hi 0) with h | h | h | h
    · exact h.2
    · have hbad := h.1.symm.trans (hhi 0)
      norm_num at hbad
    · have hbad := h.1.symm.trans (hhi 0)
      norm_num at hbad
    · have hbit := h.2.1
      have hupper := h.2.2.2
      rw [show coord (hi 0) = x (hi 0)-Real.pi by simp [coord,hbit]] at h0hi
      linarith
  have h1lo := hinfo1 (lo 1) (hlo 1)
  have h1hi := hinfo1 (hi 1) (hhi 1)
  have h2lo := hinfo2 (lo 2) (hlo 2)
  have h2hi := hinfo2 (hi 2) (hhi 2)
  have hg01 := h01 (hi 0) (lo 1) hhi0info.1 h1lo.1 hhi0info.2.2 h1lo.2.1
  have hg12 := h12 (hi 1) (lo 2) h1hi.1 h2lo.1 h1hi.2.2 h2lo.2.1
  have htotal : (∑ k : Fin 3, span k) ≤ Real.pi-3*lam := by
    rcases htag (lo 0) with h | h | h | h
    · have hbit := h.2.1
      have hnonneg := h.2.2.1
      have hzlo : x (lo 0) = 0 := by
        rw [show coord (lo 0) = x (lo 0) by simp [coord,hbit]] at h0lo
        linarith
      simp only [Fin.sum_univ_three,span,coord,hhi0info.1,hbit,h1lo.1,h1hi.1,
        h2lo.1,h2hi.1,hft,ite_true,ite_false,hzlo]
      linarith [h2hi.2.2]
    · have hbad := h.1.symm.trans (hlo 0)
      norm_num at hbad
    · have hbad := h.1.symm.trans (hlo 0)
      norm_num at hbad
    · have hbit := h.2.1
      have htailLo := h.2.2.1
      have hg23 := h23 (hi 2) (lo 0) h2hi.1 hbit h2hi.2.2 htailLo
      simp only [Fin.sum_univ_three,span,coord,hhi0info.1,hbit,h1lo.1,h1hi.1,
        h2lo.1,h2hi.1,hft,ite_true,ite_false]
      linarith
  refine ⟨{
    code := code
    witness := witness
    witness_code := hwitness
    span := span
    span_nonneg := hspan0
    span_total := htotal
    left := lo
    right := hi
    left_code := hlo
    right_code := hhi
    span_expr := ?_
    same_span := ?_
    different_angle := hdifferent }⟩
  · intro k
    rw [hsameCoord (lo k) (hi k) ((hlo k).trans (hhi k).symm)]
    rw [abs_of_nonpos (sub_nonpos.mpr (hbounds k (hi k) (hhi k)).1)]
    dsimp only [span]
    ring
  · intro i j hsame
    rw [hsameCoord i j hsame]
    have hiBounds := hbounds (code i) i rfl
    have hjBounds := hbounds (code i) j hsame.symm
    dsimp only [span]
    apply abs_sub_le_iff.mpr
    constructor <;> linarith [hiBounds.1,hiBounds.2,hjBounds.1,hjBounds.2]

/-- Actual classes with internally selected physical diameter endpoints.
The nonnegative spans are realized actual angles and have total at most T. -/
structure Data {s : ℕ} (c : Fin s → Plane₂) (lam : ℝ) (p : Fin s) where
  classOf : {i : Fin s // i ≠ p} → Fin 3
  witness : Fin 3 → {i : Fin s // i ≠ p}
  witness_class : ∀ k, classOf (witness k) = k
  span : Fin 3 → ℝ
  span_nonneg : ∀ k, 0 ≤ span k
  span_total : (∑ k : Fin 3, span k) ≤ Real.pi-3*lam
  left : Fin 3 → {i : Fin s // i ≠ p}
  right : Fin 3 → {i : Fin s // i ≠ p}
  left_class : ∀ k, classOf (left k) = k
  right_class : ∀ k, classOf (right k) = k
  span_eq_angle : ∀ k, span k = ∠ (c (left k)) (c p) (c (right k))
  same_span : ∀ i j, classOf i = classOf j →
    ∠ (c i) (c p) (c j) ≤ span (classOf i)
  different_angle : ∀ i j, classOf i ≠ classOf j →
    2*lam ≤ ∠ (c i) (c p) (c j)

theorem Data.same_angle_le {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (D : Data c lam p) (i j : {i : Fin s // i ≠ p}) (h : D.classOf i = D.classOf j) :
    ∠ (c i) (c p) (c j) ≤ Real.pi-3*lam := by
  have hspan : D.span (D.classOf i) ≤ ∑ k : Fin 3, D.span k :=
    Finset.single_le_sum (fun k _ => D.span_nonneg k) (Finset.mem_univ _)
  exact (D.same_span i j h).trans (hspan.trans D.span_total)

/-- Actual data are selected internally from the original interior row.
The construction in fact gives this coarse T partition for every original
interior LOW row; the score-zero argument is retained in this interface. -/
theorem actual_partition_nonempty {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlo : 2*Real.pi/9 < lam) (p : Fin s) (hnot : ¬ IsHullVertex c p)
    (_hscore : rowScore lam (directionRow o e c p) = 0) : Nonempty (Data c lam p) := by
  classical
  obtain ⟨f,hf,H,hwidth,z,hzp,hz,hbz,hwindow⟩ :=
    exists_actual_interior_flip_window hs o e he hleg p hnot
  let I := {i : Fin s // i ≠ p}
  let x (i : I) : ℝ := dirRep o f c p i
  let bit (i : I) : Bool := rawBit o f c p i
  have hx : ∀ i : I, 0 ≤ x i ∧ x i ≤ H := fun i => hwindow i i.property
  have hH : H < 4*lam := by linarith [hleg.lam_pos]
  have hop : ∀ i j : I, bit i ≠ bit j → lam ≤ |x i-x j| := by
    intro i j hbits
    have hij : (i : Fin s) ≠ j := by
      intro h
      exact hbits (congrArg (rawBit o f c p) h)
    have hang := actual_angle_eq_bits hs o f hf hleg i.property.symm j.property.symm
    have hcap := hleg.triAngle i p j i.property j.property.symm hij
    change ∠ (c i) (c p) (c j) =
      (if bit i = bit j then |x j-x i| else Real.pi-|x j-x i|) at hang
    rw [ite_eq_right hbits,abs_sub_comm] at hang
    linarith
  obtain ⟨a,b,d,ha,hb,hd,hab,hbd,hbits,hsub⟩ :=
    exists_actual_interior_alternating_fan hs o f hf hleg p hnot
  have hmr : ∃ m r : Fin s, m ≠ p ∧ r ≠ p ∧
      rawBit o f c p m = true ∧ rawBit o f c p r = false ∧
      dirRep o f c p m < dirRep o f c p r := by
    cases hba : rawBit o f c p a
    · have hbb : rawBit o f c p b = true := by simpa [hba] using hbits.2
      have hdd : rawBit o f c p d = false := hbits.1.symm.trans hba
      exact ⟨b,d,hb,hd,hbb,hdd,hbd⟩
    · have hbb : rawBit o f c p b = false := by simpa [hba] using hbits.2
      exact ⟨a,b,ha,hb,hba,hbb,hab⟩
  obtain ⟨m,r,hmp,hrp,hbm,hbr,hmr⟩ := hmr
  obtain ⟨D⟩ := wrapped_window_classifier x bit hleg.lam_pos hH hwidth hx hop
    ⟨z,hzp⟩ ⟨m,hmp⟩ ⟨r,hrp⟩ hz hbz hbm hbr hmr
  have hang (i j : I) : ∠ (c i) (c p) (c j) = angleExpr x bit i j := by
    have h := actual_angle_eq_bits hs o f hf hleg i.property.symm j.property.symm
    rw [abs_sub_comm] at h
    exact h
  refine ⟨{
    classOf := D.code
    witness := D.witness
    witness_class := D.witness_code
    span := D.span
    span_nonneg := D.span_nonneg
    span_total := D.span_total
    left := D.left
    right := D.right
    left_class := D.left_code
    right_class := D.right_code
    span_eq_angle := ?_
    same_span := ?_
    different_angle := ?_ }⟩
  · intro k
    rw [hang]
    exact (D.span_expr k).symm
  · intro i j hsame
    rw [hang]
    exact D.same_span i j hsame
  · intro i j hdiff
    rw [hang]
    exact D.different_angle i j hdiff

noncomputable def actualPartition {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlo : 2*Real.pi/9 < lam) (p : Fin s) (hnot : ¬ IsHullVertex c p)
    (hscore : rowScore lam (directionRow o e c p) = 0) : Data c lam p :=
  Classical.choice (actual_partition_nonempty hs o e he hleg hlo p hnot hscore)

/-- Singleton emission applies to every target. Only a later original
minimum-counter budget can forbid it for a zero-score target. -/
theorem singleton_in_class_actual_gain {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlo : 2*Real.pi/9 < lam) (p : Fin s) (hnot : ¬ IsHullVertex c p)
    (hscore : rowScore lam (directionRow o e c p) = 0)
    (q : {i : Fin s // i ≠ p})
    (hsingle : ∀ j : {i : Fin s // i ≠ p},
      (actualPartition (by omega : 2 ≤ s) o e he hleg hlo p hnot hscore).classOf j =
        (actualPartition (by omega : 2 ≤ s) o e he hleg hlo p hnot hscore).classOf q → j = q) :
    1 ≤ rowGain lam (directionRow o e c p) (deleteIndex o e c q p) := by
  let D := actualPartition (by omega : 2 ≤ s) o e he hleg hlo p hnot hscore
  apply rowGain_pos_of_forall_angle_ge o e c hleg he q.property.symm hs
  intro j hjp hjq
  have hne : D.classOf q ≠ D.classOf ⟨j,hjp⟩ := by
    intro h
    exact hjq (congrArg Subtype.val (hsingle ⟨j,hjp⟩ h.symm))
  have hangle := D.different_angle q ⟨j,hjp⟩ hne
  linarith [hleg.lam_pos]

#print axioms exists_actual_flip_gap
#print axioms exists_actual_interior_flip_window
#print axioms Data.same_angle_le
#print axioms actual_partition_nonempty
#print axioms actualPartition
#print axioms singleton_in_class_actual_gain

end Jsp404.ActualInteriorZeroPartition
