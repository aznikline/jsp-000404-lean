import Jsp000404.ActualInteriorOneNearest
import Jsp000404.GeomSkeleton
import Jsp000404.SharpNearestGeometry
import Jsp000404.PositiveRowFan
import Jsp000404.ActualMinimalBandCounterexample

set_option autoImplicit false

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualInteriorOneRuns

private def bitStep (a b : Bool) : ℕ := if a = b then 0 else 1

private def changesFrom (a : Bool) : List Bool → ℕ
  | [] => 0
  | b :: bs => bitStep a b + changesFrom b bs

private def changes : List Bool → ℕ
  | [] => 0
  | a :: bs => changesFrom a bs

/-- The closing endpoint is the opposite lift of the initial ray. -/
private def twistedChanges : List Bool → ℕ
  | [] => 0
  | a :: bs => changesFrom a (bs ++ [!a])

private theorem bitStep_triangle (a b d : Bool) :
    bitStep a d ≤ bitStep a b + bitStep b d := by
  cases a <;> cases b <;> cases d <;> decide

private theorem changesFrom_le_step (a b : Bool) (l : List Bool) :
    changesFrom a l ≤ bitStep a b + changesFrom b l := by
  cases l with
  | nil => simp [changesFrom]
  | cons d ds =>
    have h := bitStep_triangle a b d
    simp only [changesFrom]
    omega

private theorem changesFrom_mono {small large : List Bool}
    (h : small.Sublist large) (a : Bool) :
    changesFrom a small ≤ changesFrom a large := by
  induction h generalizing a with
  | slnil => simp [changesFrom]
  | @cons small large b h ih =>
    exact (ih a).trans (changesFrom_le_step a b large)
  | @cons_cons small large b h ih =>
    simp only [changesFrom]
    exact Nat.add_le_add_left (ih b) _

private theorem changes_le_changesFrom (a : Bool) (l : List Bool) :
    changes l ≤ changesFrom a l := by
  cases l <;> simp [changes, changesFrom]

private theorem changes_mono {small large : List Bool}
    (h : small.Sublist large) : changes small ≤ changes large := by
  cases large with
  | nil => have hs := h.length_le; simp only [List.length_nil] at hs
           have he : small = [] := List.length_eq_zero_iff.mp (by omega)
           simp [he]
  | cons a as =>
    have hm := changesFrom_mono h a
    exact (changes_le_changesFrom a small).trans (by
      simpa [changes, changesFrom, bitStep] using hm)

private theorem changesFrom_final_parity (a b : Bool) (l : List Bool) :
    changesFrom a (l ++ [b]) % 2 = bitStep a b := by
  induction l generalizing a with
  | nil => cases a <;> cases b <;> decide
  | cons d ds ih =>
    have h := ih d
    simp only [List.cons_append, changesFrom]
    cases a <;> cases b <;> cases d <;>
      simp_all [bitStep, Nat.add_mod]

private theorem twistedChanges_odd {l : List Bool} (hne : l ≠ []) :
    twistedChanges l % 2 = 1 := by
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons a as =>
    have h := changesFrom_final_parity a (!a) as
    cases a <;> simpa [twistedChanges, bitStep] using h

private theorem changes_le_twistedChanges (l : List Bool) :
    changes l ≤ twistedChanges l := by
  cases l with
  | nil => rfl
  | cons a as =>
    exact changesFrom_mono (List.prefix_append as [!a]).sublist a

private theorem twistedChanges_ge_three_of_alternating_sublist
    {l : List Bool} (a : Bool) (h : [a, !a, a].Sublist l) :
    3 ≤ twistedChanges l := by
  have h2 : 2 ≤ changes l := by
    have hm := changes_mono h
    cases a <;> simpa [changes, changesFrom, bitStep] using hm
  have hne : l ≠ [] := by intro he; rw [he] at h; have := h.length_le; simp at this
  have hp := twistedChanges_odd hne
  have hm := changes_le_twistedChanges l
  omega

private noncomputable def actualBits {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin s → Plane₂) (p : Fin s) : List Bool :=
  (fanOrder o e c p).map (rawBit o e c p)

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

private theorem actual_directionRow_nodup {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (p : Fin s) : (directionRow o e c p).Nodup := by
  rw [← fanOrder_map_eq o e c p]
  apply List.Nodup.map_on ?_ (fanOrder_nodup o e c p)
  intro a ha b hb heq
  by_contra hab
  exact actual_dirRep_ne hs o e he hleg
    ((mem_fanOrder o e c).mp ha).symm ((mem_fanOrder o e c).mp hb).symm hab heq

/-- Three actual ordered rays surrounding the original center have
alternating actual lift bits. The actual angle sum excludes the other
six bit patterns, including every one-flip semicircle case. -/
theorem actual_ordered_surrounding_bits {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    {p a b d : Fin s} (hpa : p ≠ a) (hpb : p ≠ b) (hpd : p ≠ d)
    (hab : dirRep o e c p a < dirRep o e c p b)
    (hbd : dirRep o e c p b < dirRep o e c p d)
    (hsum : ∠ (c a) (c p) (c b) + ∠ (c a) (c p) (c d) +
      ∠ (c b) (c p) (c d) = 2 * Real.pi) :
    rawBit o e c p a = rawBit o e c p d ∧
      rawBit o e c p b = !(rawBit o e c p a) := by
  have hAB := actual_angle_eq_bits hs o e he hleg hpa hpb
  have hAD := actual_angle_eq_bits hs o e he hleg hpa hpd
  have hBD := actual_angle_eq_bits hs o e he hleg hpb hpd
  have ha0 := (linRep_mem_Ico (o.oangle e (c a - c p))).1
  have hdpi := (linRep_mem_Ico (o.oangle e (c d - c p))).2
  change 0 ≤ dirRep o e c p a at ha0
  change dirRep o e c p d < Real.pi at hdpi
  rw [abs_of_pos (sub_pos.mpr hab)] at hAB
  rw [abs_of_pos (sub_pos.mpr (hab.trans hbd))] at hAD
  rw [abs_of_pos (sub_pos.mpr hbd)] at hBD
  cases ha : rawBit o e c p a <;>
    cases hb : rawBit o e c p b <;>
    cases hd : rawBit o e c p d <;>
    simp_all <;> linarith

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

/-- This count is computed from the actual sorted index list and actual
oriented lift bits. No caller supplies a sign list or a flip count. -/
noncomputable def actualTwistedFlipCount {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin s → Plane₂) (p : Fin s) : ℕ :=
  twistedChanges (actualBits o e c p)

/-- A nonempty actual fan has an odd twisted flip count. -/
theorem actual_twisted_flip_count_odd {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin s → Plane₂) (p : Fin s) :
    actualTwistedFlipCount o e c p % 2 = 1 := by
  apply twistedChanges_odd
  intro heq
  have hlen : (actualBits o e c p).length = s - 1 := by
    simp only [actualBits, List.length_map, fanOrder_length]
  rw [heq] at hlen
  simp only [List.length_nil] at hlen
  omega

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
  have hbits := actual_ordered_surrounding_bits hs o e he hleg
    hx.symm hy.symm hz.symm hxy' hyz' (angle_sum_eq_two_pi_of_nested hE hp)
  exact ⟨x,y,z,hx,hy,hz,hxy',hyz',hbits,hsub⟩

/-- The original full-hull nonvertex produces at least three actual
twisted flips. Its actual containing triangle produces the alternating
sublist internally; no angular window or flip-count premise is supplied. -/
theorem actual_interior_twisted_flip_count_ge_three {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (p : Fin s) (hnot : ¬ IsHullVertex c p) :
    3 ≤ actualTwistedFlipCount o e c p := by
  obtain ⟨x,y,z,hx,hy,hz,hxy,hyz,hbits,hsub⟩ :=
    exists_actual_interior_alternating_fan hs o e he hleg p hnot
  have hbsub := hsub.map (rawBit o e c p)
  change [rawBit o e c p x, rawBit o e c p y, rawBit o e c p z].Sublist
    (actualBits o e c p) at hbsub
  rw [hbits.2, ← hbits.1] at hbsub
  exact twistedChanges_ge_three_of_alternating_sublist (rawBit o e c p x) hbsub

private theorem narrow_window_small_expr {ι : Type*} (x : ι → ℝ) (bit : ι → Bool)
    {lam H : ℝ} (hlam : 0 < lam) (hH : H < 3 * lam)
    (hwidth : H ≤ Real.pi-2*lam)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ H)
    (hop : ∀ i j, bit i ≠ bit j → lam ≤ |x i - x j|)
    (z m r : ι) (hz : x z = 0) (hbz : bit z = false)
    (hbm : bit m = true) (hbr : bit r = false) (hmr : x m < x r) :
    ∀ i j,
      (if bit i = bit j then |x i-x j| else Real.pi-|x i-x j|) < lam →
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

/-- Actual small angles at an interior score-one center obey the sharp
remainder bound. The reference, window and alternating actual rays are
all produced internally from the original configuration. -/
theorem actual_interior_one_small_angle_le_remainder {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlo : 2*Real.pi/9 < lam) (p : Fin s) (hnot : ¬ IsHullVertex c p)
    (hscore : rowScore lam (directionRow o e c p) = 1)
    {i j : Fin s} (hip : i ≠ p) (hjp : j ≠ p)
    (hsmall : ∠ (c i) (c p) (c j) < lam) :
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
    else Real.pi-|x ⟨i,hip⟩-x ⟨j,hjp⟩|) < lam := by
    simpa only [x, bit, ← hangle] using hsmall
  have hbound := narrow_window_small_expr x bit hleg.lam_pos hH hwidth hx hop
    ⟨z,hzp⟩ ⟨b,hb⟩ ⟨d,hd⟩ hz hbz hb1 hd0 hbd ⟨i,hip⟩ ⟨j,hjp⟩ hsmall'
  change (if rawBit o f c p i = rawBit o f c p j then |dirRep o f c p i-dirRep o f c p j|
    else Real.pi-|dirRep o f c p i-dirRep o f c p j|) ≤ H-2*lam at hbound
  rw [← hangle] at hbound
  linarith

/-- The actual zero-gain row now supplies a genuine half-scale witness
at arbitrary cardinality. No run, angle array or nearest fact is supplied. -/
theorem actual_interior_one_zero_gain_half_angle {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlo : 2*Real.pi/9 < lam) (p : Fin s) (hnot : ¬ IsHullVertex c p)
    (hscore : rowScore lam (directionRow o e c p) = 1)
    {q : Fin s} (hpq : p ≠ q)
    (hzero : rowGain lam (directionRow o e c p) (deleteIndex o e c q p) = 0) :
    ∃ j : Fin s, j ≠ p ∧ j ≠ q ∧ ∠ (c q) (c p) (c j) < lam/2 := by
  obtain ⟨j,hjp,hjq,hsmall⟩ :=
    (emit_or_near_collinear o e c hleg he hpq hs).resolve_left (by
      intro hpos
      rw [hzero] at hpos
      omega)
  have hbound := actual_interior_one_small_angle_le_remainder (by omega : 2 ≤ s)
    o e he hleg hlo p hnot hscore hpq.symm hjp hsmall
  exact ⟨j,hjp,hjq,by linarith⟩

/-- The resulting metric comparison has common endpoint q, matching
the actual nearest-neighbor direction used by the light deletion debt. -/
theorem actual_interior_one_zero_gain_has_closer_point {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlo : 2*Real.pi/9 < lam) (p : Fin s) (hnot : ¬ IsHullVertex c p)
    (hscore : rowScore lam (directionRow o e c p) = 1)
    {q : Fin s} (hpq : p ≠ q)
    (hzero : rowGain lam (directionRow o e c p) (deleteIndex o e c q p) = 0) :
    ∃ j : Fin s, j ≠ p ∧ j ≠ q ∧ dist (c q) (c j) < dist (c q) (c p) := by
  obtain ⟨j,hjp,hjq,hsmall⟩ := actual_interior_one_zero_gain_half_angle
    hs o e he hleg hlo p hnot hscore hpq hzero
  exact ⟨j,hjp,hjq,SharpNearestGeometry.actual_third_point_closer_of_half_scale_angle
    hleg hpq hjp.symm hjq.symm hsmall⟩

/-- A light target whose actual nearest neighbor is an interior score-one
center is actually removable. Zero gain is ruled out by the metric
producer; positive gain supplies the real certificate-A charge. -/
theorem actual_interior_one_nearest_light_removable {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlo : 2*Real.pi/9 < lam) (p : Fin s) (hnot : ¬ IsHullVertex c p)
    (hscore : rowScore lam (directionRow o e c p) = 1)
    {q : Fin s} (hpq : p ≠ q) (hlight : rowScore lam (directionRow o e c q) ≤ 1)
    (hnear : ∀ j : Fin s, q ≠ j → dist (c q) (c p) ≤ dist (c q) (c j)) :
    Removable lam (fun v i => deleteIndex o e c v i) (directionRows o e c) q := by
  by_cases hzero : rowGain lam (directionRow o e c p) (deleteIndex o e c q p) = 0
  · obtain ⟨j,hjp,hjq,hcloser⟩ := actual_interior_one_zero_gain_has_closer_point
      hs o e he hleg hlo p hnot hscore hpq hzero
    exact False.elim ((not_lt_of_ge (hnear j hjq.symm)) hcloser)
  · have hpos : 1 ≤ rowGain lam (directionRow o e c p) (deleteIndex o e c q p) := by omega
    apply removable_of_gain1_ge hleg.lam_pos
      (fun v i => deleteIndex o e c v i) (directionRows o e c) q
      (fun i => directionRow_sorted o e c i)
      (fun i x hx => Set.mem_Ico.mp (directionRow_mem_Ico o e c hx))
      (fun i => by change 2 ≤ (directionRow o e c i).length
                   rw [directionRow_length]; omega)
      (fun i hi => deleteIndex_lt o e c hi) p hpq hpos
    change rowScore lam (directionRow o e c q) ≤ rowScore lam (directionRow o e c p)
    omega

/-- In the genuine n4 LOW minimal counter-model of potential eighteen,
every actual nearest neighbor of a light target belongs to the full
original hull. The minimum score and actual strip are derived internally. -/
theorem actual_low_four_F18_light_nearest_full_hull {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    {q p : Fin (s+1)} (hq : rowScore lam (directionRow o e c q) = 1) (hpq : p ≠ q)
    (hnear : ∀ j : Fin (s+1), q ≠ j → dist (c q) (c p) ≤ dist (c q) (c j)) :
    IsHullVertex c p := by
  by_contra hnot
  obtain ⟨m,hmin⟩ := Finite.exists_min (fun i : Fin (s+1) => rowScore lam (directionRow o e c i))
  have hcrit := ActualMinimalBandCounterexample.low_minimum_score_critical_form
    (n := 4) hs (by decide : 2 ≤ 4) o e H m hmin
  have hpow : 2 ^ rowScore lam (directionRow o e c m) = 2 := by
    have h := hcrit.1
    rw [hF] at h
    norm_num at h
    omega
  have hm : rowScore lam (directionRow o e c m) = 1 :=
    Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) (by simpa using hpow)
  have hall (i : Fin (s+1)) : 1 ≤ rowScore lam (directionRow o e c i) := by
    simpa only [hm] using hmin i
  obtain ⟨hn,_,_⟩ := ActualMinimumCardBandMaximizer.low_band_strip
    (n := 4) (by decide : 2 ≤ 4) H.legality.lam_pos H.scale_lower H.scale_upper
  have hdef := FullHullInteriorDefect.rowDefect_ge_three_of_not_hull_vertex
    o e he H.legality hn p hnot
  have hcells := rowCells_directionRow_le_of_floor_eq o e c H.legality.lam_pos p
    (by omega : 2 ≤ s+1) hn
  have hrow := rowScore_eq_sub_defect lam H.legality.lam_pos 4 _ hcells
  have hp : rowScore lam (directionRow o e c p) = 1 := by have := hall p; omega
  have hrho : Real.pi/((4 : ℝ)+1/2) = 2*Real.pi/9 := by ring
  have hlo : 2*Real.pi/9 < lam := by rw [← hrho]; exact H.scale_lower
  have hrem := actual_interior_one_nearest_light_removable (by omega : 3 ≤ s+1)
    o e he H.legality hlo p hnot hp hpq hq.le hnear
  exact ActualMinimalBandCounterexample.not_actual_removable hs o e H q hrem

/-- The nearest neighbor is selected by the finite family of original
distances; its full-hull membership follows from the actual F18 model. -/
theorem exists_actual_low_four_F18_light_nearest_full_hull {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (q : Fin (s+1)) (hq : rowScore lam (directionRow o e c q) = 1) :
    ∃ p : Fin (s+1), p ≠ q ∧ IsHullVertex c p ∧
      ∀ j : Fin (s+1), q ≠ j → dist (c q) (c p) ≤ dist (c q) (c j) := by
  classical
  let I := {i : Fin (s+1) // i ≠ q}
  let z : Fin (s+1) := q.succAbove ⟨0,by omega⟩
  have hz : z ≠ q := Fin.succAbove_ne q _
  let : Nonempty I := ⟨⟨z,hz⟩⟩
  obtain ⟨p,hmin⟩ := Finite.exists_min (fun i : I => dist (c q) (c i))
  have hnear : ∀ j : Fin (s+1), q ≠ j → dist (c q) (c p) ≤ dist (c q) (c j) :=
    fun j hj => hmin ⟨j,hj.symm⟩
  exact ⟨p,p.property,actual_low_four_F18_light_nearest_full_hull
    hs o e he H hF hq p.property hnear,hnear⟩

#print axioms actual_ordered_surrounding_bits
#print axioms actual_twisted_flip_count_odd
#print axioms actual_interior_twisted_flip_count_ge_three
#print axioms actual_interior_one_small_angle_le_remainder
#print axioms actual_interior_one_zero_gain_half_angle
#print axioms actual_interior_one_zero_gain_has_closer_point
#print axioms actual_interior_one_nearest_light_removable
#print axioms actual_low_four_F18_light_nearest_full_hull
#print axioms exists_actual_low_four_F18_light_nearest_full_hull

end Jsp404.ActualInteriorOneRuns
