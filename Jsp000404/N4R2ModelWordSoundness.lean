import Jsp000404.N4R2SharedCycleChecker
import Jsp000404.N4R2WordDefinitions
import Jsp000404.N4R2WordTree

/-!
# Actual model directions and complete six-chord rows

The 35 bits are chosen internally from the actual strict-between triangle
alternatives.  A word determines a computable order of all six labels in each
row.  Sound words make these orders actual scalar orders, so all seven gaps
(including both endpoints) agree with the model's existing complete rows.
-/

set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.N4R2ModelWordSoundness

open SatScalarModel N4R2CriticalReifiedRow

abbrev Word := N4R2WordDefinitions.Word

/-- Lexicographic `combinations(range(7), 3)` order. -/
abbrev triples := N4R2WordDefinitions.triples

theorem triples_ordered : ∀ t : Fin 35,
    (triples t).1 < (triples t).2.1 ∧ (triples t).2.1 < (triples t).2.2 := by
  decide

/-- False is the forward arm, and true is the reverse arm. -/
def TriArm (M : GenericModel 7 4) (t : Fin 35) (bit : Bool) : Prop :=
  let a := (triples t).1
  let b := (triples t).2.1
  let c := (triples t).2.2
  if bit then
    M.d b c + 1 ≤ M.d a b ∧ M.d b c < M.d a c ∧ M.d a c < M.d a b
  else
    M.d a b + 1 ≤ M.d b c ∧ M.d a b < M.d a c ∧ M.d a c < M.d b c

def WordSound (M : GenericModel 7 4) (w : Word) : Prop :=
  ∀ t, TriArm M t (w t)

/-- No orientation oracle is supplied by a caller. -/
theorem exists_model_word (M : GenericModel 7 4) : ∃ w : Word, WordSound M w := by
  classical
  have hex : ∀ t : Fin 35, ∃ bit : Bool, TriArm M t bit := by
    intro t
    have ho := triples_ordered t
    rcases M.triangle (triples t).1 (triples t).2.1 (triples t).2.2 ho.1 ho.2 with
      hf | hr
    · exact ⟨false, by simpa only [TriArm, Bool.false_eq_true, ↓reduceIte] using hf⟩
    · exact ⟨true, by simpa only [TriArm, ↓reduceIte] using hr⟩
  exact ⟨fun t => Classical.choose (hex t), fun t => Classical.choose_spec (hex t)⟩

/-- The canonical unordered-triple index.  The arithmetic counts preceding
lexicographic first and second entries; duplicate inputs are harmless defaults. -/
abbrev tripleIndex := N4R2WordDefinitions.tripleIndex

set_option maxRecDepth 100000 in
theorem tripleIndex_incident : ∀ i u v : Fin 7, u < v → u ≠ i → v ≠ i →
    triples (tripleIndex i u v) =
      if i < u then (i,u,v) else if i < v then (u,i,v) else (u,v,i) := by
  decide

theorem tripleIndex_ordered (a b c : Fin 7) (hab : a < b) (hbc : b < c) :
    triples (tripleIndex a b c) = (a,b,c) := by
  have h := tripleIndex_incident a b c hbc (ne_of_gt hab) (ne_of_gt (lt_trans hab hbc))
  simpa only [hab, ↓reduceIte] using h

/-- One triangle bit compares any two distinct incident chords.  Symmetry
handles the middle and last vertices of the canonical ordered triangle. -/
theorem incident_comparison (M : GenericModel 7 4) (w : Word)
    (h : WordSound M w) (i u v : Fin 7) (huv : u < v) (hui : u ≠ i) (hvi : v ≠ i) :
    if w (tripleIndex i u v) then M.d i v < M.d i u else M.d i u < M.d i v := by
  have ht := h (tripleIndex i u v)
  have he := tripleIndex_incident i u v huv hui hvi
  by_cases hiu : i < u
  · have he' : triples (tripleIndex i u v) = (i,u,v) := by
      simpa only [hiu, ↓reduceIte] using he
    unfold TriArm at ht
    rw [he'] at ht
    cases hb : w (tripleIndex i u v) <;>
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at ht ⊢
    · exact ht.2.1
    · exact ht.2.2
  · by_cases hiv : i < v
    · have he' : triples (tripleIndex i u v) = (u,i,v) := by
        simpa only [hiu, hiv, ↓reduceIte] using he
      unfold TriArm at ht
      rw [he'] at ht
      rw [M.symm i u hui.symm]
      cases hb : w (tripleIndex i u v) <;>
        simp only [hb, Bool.false_eq_true, ↓reduceIte] at ht ⊢
      all_goals linarith only [ht.1]
    · have he' : triples (tripleIndex i u v) = (u,v,i) := by
        simpa only [hiu, hiv, ↓reduceIte] using he
      unfold TriArm at ht
      rw [he'] at ht
      rw [M.symm i u hui.symm, M.symm i v hvi.symm]
      cases hb : w (tripleIndex i u v) <;>
        simp only [hb, Bool.false_eq_true, ↓reduceIte] at ht ⊢
      · exact ht.2.2
      · exact ht.2.1

/-- The diagonal is a first-position sentinel used only to make the finite
comparison total on Fin 7.  It is erased before any row is sorted. -/
def rowCompare (w : Word) (i u v : Fin 7) : Bool :=
  if u = v then true else if u = i then true else if v = i then false
  else if u < v then !(w (tripleIndex i u v)) else w (tripleIndex i v u)

noncomputable def rowKey (M : GenericModel 7 4) (i u : Fin 7) : ℝ :=
  if u = i then 0 else M.d i u

/-- Actual chord bounds and triangle directions interpret the complete
finite comparator, including its unused diagonal sentinel. -/
theorem rowCompare_iff (M : GenericModel 7 4) (w : Word) (h : WordSound M w)
    (i u v : Fin 7) : rowCompare w i u v = true ↔ rowKey M i u ≤ rowKey M i v := by
  by_cases huv : u = v
  · subst v
    simp [rowCompare]
  · by_cases hui : u = i
    · subst u
      have hvi : v ≠ i := Ne.symm huv
      have hd := (chord_bounds M i v hvi.symm).1
      have hnonneg : 0 ≤ M.d i v := by linarith
      simp [rowCompare, rowKey, huv, hvi, hnonneg]
    · by_cases hvi : v = i
      · subst v
        have hd := (chord_bounds M i u (Ne.symm hui)).1
        have hnot : ¬ M.d i u ≤ 0 := by linarith
        simp [rowCompare, rowKey, huv, hnot]
      · simp only [rowCompare, huv, hui, hvi, ↓reduceIte, rowKey]
        rcases lt_or_gt_of_ne huv with huv' | hvu'
        · have hc := incident_comparison M w h i u v huv' hui hvi
          simp only [huv', ↓reduceIte]
          cases hb : w (tripleIndex i u v)
          · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hc
            simp [le_of_lt hc]
          · simp only [hb, ↓reduceIte] at hc
            simp [not_le.mpr hc]
        · have hc := incident_comparison M w h i v u hvu' hvi hui
          have hnot : ¬ u < v := not_lt.mpr (le_of_lt hvu')
          simp only [hnot, ↓reduceIte]
          cases hb : w (tripleIndex i v u)
          · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hc
            simp [not_le.mpr hc]
          · simp only [hb, ↓reduceIte] at hc
            simp [le_of_lt hc]

def rowLabels (w : Word) (i : Fin 7) : List (Fin 7) :=
  ((List.finRange 7).erase i).mergeSort (rowCompare w i)

theorem rowLabels_perm (w : Word) (i : Fin 7) :
    (rowLabels w i).Perm ((List.finRange 7).erase i) :=
  List.mergeSort_perm _ _

theorem rowLabels_length (w : Word) (i : Fin 7) : (rowLabels w i).length = 6 := by
  have hl := (rowLabels_perm w i).length_eq
  simpa only [List.length_erase_of_mem (List.mem_finRange i), List.length_finRange] using hl

/-- Computable complete six-label order determined solely by the word. -/
def rows (w : Word) (i : Fin 7) (k : Fin 6) : Fin 7 :=
  (rowLabels w i).get (Fin.cast (rowLabels_length w i).symm k)

theorem ofFn_rows (w : Word) (i : Fin 7) : List.ofFn (rows w i) = rowLabels w i := by
  have h := List.ofFn_congr (rowLabels_length w i) (rowLabels w i).get
  exact h.symm.trans (List.ofFn_get (rowLabels w i))

theorem rowLabels_sorted (M : GenericModel 7 4) (w : Word) (h : WordSound M w)
    (i : Fin 7) : ((rowLabels w i).map (M.d i)).Pairwise (· ≤ ·) := by
  have htrans : ∀ a b c : Fin 7, rowCompare w i a b → rowCompare w i b c →
      rowCompare w i a c := by
    intro a b c hab hbc
    exact (rowCompare_iff M w h i a c).mpr
      (le_trans ((rowCompare_iff M w h i a b).mp hab)
        ((rowCompare_iff M w h i b c).mp hbc))
  have htotal : ∀ a b : Fin 7, rowCompare w i a b || rowCompare w i b a := by
    intro a b
    rcases le_total (rowKey M i a) (rowKey M i b) with hab | hba
    · simp only [(rowCompare_iff M w h i a b).mpr hab, Bool.true_or]
    · simp only [(rowCompare_iff M w h i b a).mpr hba, Bool.or_true]
  have hs : (rowLabels w i).Pairwise (fun a b => rowCompare w i a b = true) := by
    unfold rowLabels
    exact List.pairwise_mergeSort htrans htotal _
  have hmem : ∀ a ∈ rowLabels w i, a ≠ i := by
    intro a ha
    have ha' := (rowLabels_perm w i).mem_iff.mp ha
    exact ((List.nodup_finRange 7).mem_erase_iff.mp ha').1
  rw [List.pairwise_map]
  apply hs.imp_of_mem
  intro a b ha hb hab
  have hh := (rowCompare_iff M w h i a b).mp hab
  simpa only [rowKey, hmem a ha, hmem b hb, ↓reduceIte] using hh

/-- Every sound word supplies its own full permutation and actual sorting;
neither fact is a caller premise. -/
theorem row_order_perm_sorted (M : GenericModel 7 4) (w : Word) (h : WordSound M w)
    (i : Fin 7) :
    (List.ofFn (rows w i)).Perm ((List.finRange 7).erase i) ∧
    (List.ofFn (fun k => M.d i (rows w i k))).Pairwise (· ≤ ·) := by
  constructor
  · rw [ofFn_rows]
    exact rowLabels_perm w i
  · have hs := rowLabels_sorted M w h i
    rw [← ofFn_rows w i] at hs
    simpa only [List.map_ofFn, Function.comp_def] using hs

theorem rows_fullGaps_eq_modelGap (M : GenericModel 7 4) (w : Word)
    (h : WordSound M w) (i : Fin 7) : fullGaps M i (rows w i) = modelGap M i :=
  fullGaps_eq_modelGap_of_perm_sorted M i (rows w i)
    (row_order_perm_sorted M w h i).1 (row_order_perm_sorted M w h i).2

/-- The finite packet coordinates are the four actual triples of its
quadruple.  This is a small checked coordinate identity, not catalog coverage. -/
theorem packetBits_triples : ∀ q : Fin 35,
    triples (N4R2WordTree.packetBits q 0) =
      (N4R2WordTree.quadLabels q 0, N4R2WordTree.quadLabels q 1,
        N4R2WordTree.quadLabels q 2) ∧
    triples (N4R2WordTree.packetBits q 1) =
      (N4R2WordTree.quadLabels q 0, N4R2WordTree.quadLabels q 1,
        N4R2WordTree.quadLabels q 3) ∧
    triples (N4R2WordTree.packetBits q 2) =
      (N4R2WordTree.quadLabels q 0, N4R2WordTree.quadLabels q 2,
        N4R2WordTree.quadLabels q 3) ∧
    triples (N4R2WordTree.packetBits q 3) =
      (N4R2WordTree.quadLabels q 1, N4R2WordTree.quadLabels q 2,
        N4R2WordTree.quadLabels q 3) := by
  decide

theorem packetPattern_eq (w : Word) (q : Fin 35) :
    N4R2WordTree.packetPattern w q = ![
      w (N4R2WordTree.packetBits q 0), w (N4R2WordTree.packetBits q 1),
      w (N4R2WordTree.packetBits q 2), w (N4R2WordTree.packetBits q 3)] := by
  funext k
  fin_cases k <;> rfl

/-- Actual strict-between arms imply every four-point packet restriction.
The eight forbidden bit patterns contradict the actual shared chord order. -/
theorem wordSound_packetValid (M : GenericModel 7 4) (w : Word)
    (h : WordSound M w) : N4R2WordTree.PacketValid w := by
  intro q
  have ht0 := h (N4R2WordTree.packetBits q 0)
  have ht1 := h (N4R2WordTree.packetBits q 1)
  have ht2 := h (N4R2WordTree.packetBits q 2)
  have ht3 := h (N4R2WordTree.packetBits q 3)
  obtain ⟨he0, he1, he2, he3⟩ := packetBits_triples q
  unfold TriArm at ht0 ht1 ht2 ht3
  rw [he0] at ht0
  rw [he1] at ht1
  rw [he2] at ht2
  rw [he3] at ht3
  rw [packetPattern_eq]
  cases hb0 : w (N4R2WordTree.packetBits q 0) <;>
    cases hb1 : w (N4R2WordTree.packetBits q 1) <;>
    cases hb2 : w (N4R2WordTree.packetBits q 2) <;>
    cases hb3 : w (N4R2WordTree.packetBits q 3)
  all_goals simp only [hb0, hb1, hb2, hb3] at ht0 ht1 ht2 ht3 ⊢
  all_goals first
    | decide
    | exfalso
      simp only [Bool.false_eq_true, ↓reduceIte] at ht0 ht1 ht2 ht3
      linarith only [ht0.2.1, ht0.2.2, ht1.2.1, ht1.2.2,
        ht2.2.1, ht2.2.2, ht3.2.1, ht3.2.2]

#print axioms exists_model_word
#print axioms tripleIndex_incident
#print axioms incident_comparison
#print axioms rowCompare_iff
#print axioms row_order_perm_sorted
#print axioms rows_fullGaps_eq_modelGap
#print axioms packetBits_triples
#print axioms wordSound_packetValid

end Jsp404.N4R2ModelWordSoundness
